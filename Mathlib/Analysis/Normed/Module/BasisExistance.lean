/-
Copyright (c) 2026 Michał Świętek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michał Świętek
-/
module

public import Mathlib.Analysis.Normed.Module.Bases
public import Mathlib.Analysis.Normed.Module.BasicSequences
public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.Data.ENNReal.Real
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.Neighborhoods
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.UniformSpace.UniformEmbedding
public import Mathlib.Topology.Algebra.Module.WeakDual
public import Mathlib.Topology.Maps.Basic


/-!
# Basic Sequences in Banach Spaces
-/

noncomputable section

open Submodule Set WeakDual Metric Filter Topology BasicSequences

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- Helper lemma: a coordinate functional vanishes on the span of basis elements with larger index.
    This is extracted to reduce elaboration overhead in the main theorem. -/
private lemma coord_vanish_on_tail_span {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [CompleteSpace E] {Y : Submodule 𝕜 E}
    (basis_Z : SchauderBasis 𝕜 Y.topologicalClosure)
    (b : ℕ → E) (_hb_in_Y : ∀ n, b n ∈ Y)
    (h_basis_coe : ∀ n, (basis_Z n : E) = b n)
    (k N : ℕ) (hN : k < N)
    (tail_span : Submodule 𝕜 E)
    (h_tail_span_eq : tail_span = Submodule.span 𝕜 (Set.range (fun n => b (n + N))))
    (h_tail_in_Y : tail_span ≤ Y)
    (v : E) (hv : v ∈ tail_span) :
    basis_Z.coord k ⟨v, Y.le_topologicalClosure (h_tail_in_Y hv)⟩ = 0 := by
  -- First prove coord_k vanishes on basis elements with index > k
  have h_vanish_basis : ∀ j > k, basis_Z.coord k (basis_Z j) = 0 := by
    intro j hj
    rw [basis_Z.ortho k j, Pi.single_apply, if_neg (ne_of_gt hj).symm]
  -- Rewrite the membership using tail_span_eq so span_induction works
  rw [h_tail_span_eq] at hv
  -- Use span induction
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨n, rfl⟩ := hx
    have h_mem' : b (n + N) ∈ tail_span := by
      rw [h_tail_span_eq]; exact Submodule.subset_span ⟨n, rfl⟩
    have h_eq : (⟨b (n + N), Y.le_topologicalClosure (h_tail_in_Y h_mem')⟩ : Y.topologicalClosure)
        = basis_Z (n + N) := Subtype.ext (h_basis_coe (n + N)).symm
    rw [h_eq]
    exact h_vanish_basis (n + N) (by omega)
  | zero =>
    have h0 : (0 : E) ∈ tail_span := Submodule.zero_mem _
    convert map_zero (basis_Z.coord k)
  | add x y hx' hy' hx hy =>
    have hx_tail : x ∈ tail_span := by rw [h_tail_span_eq]; exact hx'
    have hy_tail : y ∈ tail_span := by rw [h_tail_span_eq]; exact hy'
    have hxy_tail : x + y ∈ tail_span := Submodule.add_mem _ hx_tail hy_tail
    have hx_Y : x ∈ Y.topologicalClosure := Y.le_topologicalClosure (h_tail_in_Y hx_tail)
    have hy_Y : y ∈ Y.topologicalClosure := Y.le_topologicalClosure (h_tail_in_Y hy_tail)
    have hxy_Y : x + y ∈ Y.topologicalClosure := Submodule.add_mem _ hx_Y hy_Y
    have h_eq : basis_Z.coord k ⟨x + y, hxy_Y⟩ =
        basis_Z.coord k ⟨x, hx_Y⟩ + basis_Z.coord k ⟨y, hy_Y⟩ := by
      convert map_add (basis_Z.coord k) ⟨x, hx_Y⟩ ⟨y, hy_Y⟩ using 2
    rw [h_eq, hx hx_tail, hy hy_tail, add_zero]
  | smul c x hx' hx =>
    have hx_tail : x ∈ tail_span := by rw [h_tail_span_eq]; exact hx'
    have hcx_tail : c • x ∈ tail_span := Submodule.smul_mem _ c hx_tail
    have hx_Y : x ∈ Y.topologicalClosure := Y.le_topologicalClosure (h_tail_in_Y hx_tail)
    have hcx_Y : c • x ∈ Y.topologicalClosure := Submodule.smul_mem _ c hx_Y
    have h_eq : basis_Z.coord k ⟨c • x, hcx_Y⟩ = c • basis_Z.coord k ⟨x, hx_Y⟩ := by
      convert map_smul (basis_Z.coord k) c ⟨x, hx_Y⟩ using 2
    rw [h_eq, hx hx_tail, smul_zero]

/-- The inclusion of a normed space into its double dual is an embedding
    from the weak topology to the weak-star topology. -/
theorem NormedSpace.inclusionInDoubleDual_isEmbedding_weak
    (𝕜 : Type*) [RCLike 𝕜] (X : Type*) [NormedAddCommGroup X] [NormedSpace 𝕜 X] :
    IsEmbedding (fun x : WeakSpace 𝕜 X =>
      StrongDual.toWeakDual (NormedSpace.inclusionInDoubleDual 𝕜 X x)) := by
  let J := NormedSpace.inclusionInDoubleDual 𝕜 X
  let ι := fun x : WeakSpace 𝕜 X => StrongDual.toWeakDual (J x)
  -- Both topologies are induced by the same family of maps: x ↦ (fun f => f x)
  -- WeakSpace 𝕜 X: induced by topDualPairing.flip; WeakDual 𝕜 X**: induced by eval
  -- Composition: (ι x)(f) = (J x)(f) = f(x), so evalWeakDual ∘ ι = evalWeakSpace
  let evalWeakSpace : WeakSpace 𝕜 X → (StrongDual 𝕜 X → 𝕜) := fun x f => f x
  let evalWeakDual : WeakDual 𝕜 (StrongDual 𝕜 X) → (StrongDual 𝕜 X → 𝕜) := fun φ f => φ f
  have h_commute : evalWeakDual ∘ ι = evalWeakSpace := by ext x f; rfl
  -- Injectivity: J is injective (isometry) and toWeakDual is injective
  have h_inj : Function.Injective ι := by
    intro x y hxy
    simp only [ι] at hxy
    have h1 : J x = J y := StrongDual.toWeakDual.injective hxy
    exact (NormedSpace.inclusionInDoubleDualLi (𝕜 := 𝕜) (E := X)).injective h1
  -- Inducing: both topologies are induced from Pi, and evalWeakDual ∘ ι = evalWeakSpace
  have h_ind : IsInducing ι := by
    constructor; symm
    calc TopologicalSpace.induced ι (TopologicalSpace.induced evalWeakDual Pi.topologicalSpace)
        = TopologicalSpace.induced (evalWeakDual ∘ ι) Pi.topologicalSpace := induced_compose
      _ = TopologicalSpace.induced evalWeakSpace Pi.topologicalSpace := by rw [h_commute]
  exact ⟨h_ind, h_inj⟩

/-- The inclusion of a normed space into its double dual is a homeomorphism
    from the weak topology to the weak-star topology on the range. -/
noncomputable def NormedSpace.inclusionInDoubleDual_homeomorph_weak
    (𝕜 : Type*) [RCLike 𝕜] (X : Type*) [NormedAddCommGroup X] [NormedSpace 𝕜 X] :
    WeakSpace 𝕜 X ≃ₜ Set.range (fun x : WeakSpace 𝕜 X =>
      StrongDual.toWeakDual (NormedSpace.inclusionInDoubleDual 𝕜 X x)) := by
  let emb := NormedSpace.inclusionInDoubleDual_isEmbedding_weak 𝕜 X
  -- Construct the equiv using injectivity
  let e : WeakSpace 𝕜 X ≃ Set.range (fun x : WeakSpace 𝕜 X =>
      StrongDual.toWeakDual (NormedSpace.inclusionInDoubleDual 𝕜 X x)) :=
    Equiv.ofInjective _ emb.injective
  -- The embedding induces the topology, so e is a homeomorphism
  exact e.toHomeomorphOfIsInducing (IsInducing.subtypeVal.of_comp_iff.mp emb.toIsInducing)

set_option maxHeartbeats 800000 in
-- Complex nested proof with Hahn-Banach separation and bidual embedding arguments
theorem no_basic_sequence_implies_relatively_weakly_compact [CompleteSpace X]
    {S : Set X} (hS_ne : S.Nonempty) (h_norm : (0 : X) ∉ closure S)
    (h_bounded : Bornology.IsBounded S)
    (h_no_basic : ∀ (e : ℕ → X), (∀ n, e n ∈ S) → ¬ IsBasicSequence 𝕜 e) :
    IsCompact (closure (toWeakSpace 𝕜 X '' S)) :=

    let Xbidual : Type _ := StrongDual 𝕜 (StrongDual 𝕜 X)
    let J : X →L[𝕜] Xbidual := NormedSpace.inclusionInDoubleDual 𝕜 X
    let S_bidual : Set Xbidual := J '' S

    have h_S_bidual_bounded : Bornology.IsBounded S_bidual := by
      rw [Metric.isBounded_iff_subset_closedBall 0] at h_bounded ⊢
      obtain ⟨R, hR⟩ := h_bounded
      use R
      intro y hy
      obtain ⟨x, hxS, rfl⟩ := hy
      have hxS_norm : x ∈ closedBall 0 R := hR hxS
      rw [Metric.mem_closedBall, dist_zero_right] at *
      have hJ_iso : ‖J x‖ = ‖x‖ := (NormedSpace.inclusionInDoubleDualLi (𝕜 := 𝕜) (E := X)).norm_map x
      exact hJ_iso.le.trans hxS_norm

    let K : Set (WeakDual 𝕜 (StrongDual 𝕜 X)) := closure (StrongDual.toWeakDual '' S_bidual)

    have hK_subset :  K ⊆ StrongDual.toWeakDual '' (J '' (Set.univ)) := by
      by_contra h_not_subset
      rw [Set.subset_def] at h_not_subset
      push_neg at h_not_subset
      obtain ⟨w, hwK, hw_not_JX⟩ := h_not_subset

      -- Define S' in StrongDual (Xbidual) space as translation of S_bidual by -w'
      let w' : Xbidual := WeakDual.toStrongDual w
      let S' : Set Xbidual := (fun y => y - w') '' S_bidual

      have h_weak_starS' : (0 : WeakDual 𝕜 (StrongDual 𝕜 X)) ∈ closure (StrongDual.toWeakDual '' S') := by
        let A := StrongDual.toWeakDual '' S_bidual
        let T : WeakDual 𝕜 (StrongDual 𝕜 X) ≃ₜ WeakDual 𝕜 (StrongDual 𝕜 X) :=
          Homeomorph.addRight (-w)
        have h_image : StrongDual.toWeakDual '' S' = T '' A := by
          simp only [S', A, S_bidual, image_image]
          apply image_congr
          intro x _
          simp only [T, Homeomorph.coe_addRight, sub_eq_add_neg, w']
          rfl
        rw [h_image, ← Homeomorph.image_closure]
        have h_zero : (0 : WeakDual 𝕜 (StrongDual 𝕜 X)) = T w := by
          simp only [T, Homeomorph.coe_addRight, add_neg_cancel]
        rw [h_zero]
        apply mem_image_of_mem
        exact hwK

      have h_normS' : (0 : Xbidual) ∉ closure S' := by
        -- We proceed by contradiction. Assume 0 ∈ closure S'.
        intro h0

        -- S' is the translation of S_bidual by -w'.
        -- Since translation is a homeomorphism, w' must be in the closure of S_bidual.
        have hw_cl : w' ∈ closure S_bidual := by
          -- Define the homeomorphism T(z) = z - w' on Xbidual
          let T := Homeomorph.addRight (-w' : Xbidual)
          -- S' = T '' S_bidual (by definition of S')
          have h_image : S' = T '' S_bidual := by
            simp only [S', S_bidual, T, Homeomorph.coe_addRight, sub_eq_add_neg, image_image]
          rw [h_image, ← Homeomorph.image_closure] at h0
          -- 0 ∈ T '' (closure S_bidual) means T.symm 0 ∈ closure S_bidual
          obtain ⟨y, hy_mem, hy_eq⟩ := h0
          have h_y_eq_w' : y = w' := by
            have : T.symm (T y) = T.symm 0 := by rw [hy_eq]
            rw [Homeomorph.symm_apply_apply] at this
            simp only [T, Homeomorph.addRight_symm, Homeomorph.coe_addRight, zero_add] at this
            rw [neg_neg] at this
            exact this
          rw [← h_y_eq_w']
          exact hy_mem

        -- The range of J is closed in X** because X is complete and J is an isometry.
        have h_JX_closed : IsClosed (range J) :=
          (NormedSpace.inclusionInDoubleDualLi (𝕜 := 𝕜) (E := X)).isometry.isClosedEmbedding.isClosed_range

        -- S_bidual is contained in range J, so its norm closure is also contained in range J.
        have h_subset : closure S_bidual ⊆ range J :=
          closure_minimal (image_subset_range J S) h_JX_closed

        -- Therefore w' ∈ range J.
        have hw_in_JX : w' ∈ range J := h_subset hw_cl

        -- This contradicts the choice of w (hw_not_JX).
        apply hw_not_JX
        -- Reformulate w' ∈ range J to match hw_not_JX
        rw [image_univ]
        obtain ⟨x, hx⟩ := hw_in_JX
        use J x
        constructor
        · exact mem_range_self x
        · -- Show toWeakDual (J x) = w.
          simp only [w'] at hx
          rw [hx]
          rfl

      have h_basicS' : ∃ e : ℕ → Xbidual, (∀ n, e n ∈ S') ∧ IsBasicSequence 𝕜 e := by
        obtain ⟨b, hb_mem, -⟩ := basic_sequence_selection_dual h_weak_starS' h_normS' zero_lt_one
        use b
        constructor
        · exact hb_mem
        · exact ⟨b, rfl⟩

      obtain ⟨e, he_S', he_basic⟩ := h_basicS'
      rcases he_basic with ⟨b, rfl⟩

      have h_w_span : ∃ N : ℕ, w' ∉ closure (Submodule.span 𝕜 (Set.range (fun n => b (n+N)))) := by
        -- 1. w is non-zero (since w ∉ J(X) and 0 ∈ J(X))
        have hw_ne : w' ≠ 0 := by
          intro h
          apply hw_not_JX
          have hw0 : w = 0 := by
            apply WeakDual.toStrongDual.injective
            simp only [w'] at h
            rw [h, map_zero]
          rw [hw0, image_univ]
          exact ⟨J 0, ⟨0, rfl⟩, by simp⟩

        -- 2. Assume for contradiction that w is in the closure of *all* tail spans
        by_contra h_contra
        push_neg at h_contra

        -- 3. Get the basis structure for the closure of the span
        let Y : Submodule 𝕜 Xbidual := Submodule.span 𝕜 (Set.range b.toFun)
        let Z : Submodule 𝕜 Xbidual := Y.topologicalClosure

        -- Since h_contra holds for N=0, w is in the closure of the whole span
        have h_w'_in_Z : w' ∈ Z := by
          simpa using h_contra 0

        -- Lift w to the subspace K = closure Y
        let w'_Z : Z := ⟨w', h_w'_in_Z⟩
        have hw'_Z_ne : w'_Z ≠ 0 := fun h => hw_ne (congrArg Subtype.val h)

        -- Use the theorem to treat b as a Schauder basis for K
        let basis_Z : SchauderBasis 𝕜 Z :=
          SchauderBasis_of_closure (Y := Y) b.basis b.basisConstant_lt_top

        -- 4. Since w ≠ 0, it must have a non-zero coordinate k
        have h_exists_coord : ∃ k, basis_Z.coord k w'_Z ≠ 0 := by
          by_contra! h_all_zero
          apply hw'_Z_ne
          -- If all coords are 0, the vector is 0 by the expansion property
          have h_exp := basis_Z.expansion w'_Z
          have h_zero : (fun i ↦ (basis_Z.coord i) w'_Z • basis_Z i) = fun _ ↦ 0 := by
            ext i
            simp [h_all_zero i]
          rw [h_zero] at h_exp
          exact HasSum.unique h_exp hasSum_zero

        obtain ⟨k, hk_ne⟩ := h_exists_coord

        -- 5. Use the hypothesis for N = k + 1 to derive a contradiction
        -- The contradiction is: w ∈ closure(tail) implies coord k w = 0
        specialize h_contra (k + 1)

        -- The k-th coordinate functional is continuous on K
        let coord_k : Z →L[𝕜] 𝕜 := basis_Z.coord k

        -- We show coord_k vanishes on the tail span
        -- The tail span is generated by b_{k+1}, b_{k+2}, ...
        let tail_span : Submodule 𝕜 Xbidual :=
          Submodule.span 𝕜 (Set.range (fun n => b.toFun (n + (k + 1))))

        -- First show tail_span ⊆ Y
        have h_tail_in_Y : tail_span ≤ Y := by
          apply Submodule.span_mono
          intro x hx
          obtain ⟨n, rfl⟩ := hx
          exact ⟨n + (k + 1), rfl⟩

        -- Prove b.toFun n ∈ Y and basis coercion property for the helper
        have hb_in_Y : ∀ n, b.toFun n ∈ Y := fun n => Submodule.subset_span ⟨n, rfl⟩
        have h_basis_coe : ∀ n, (basis_Z n : Xbidual) = b.toFun n := fun n => by
          rw [SchauderBasis_of_closure_apply]; simp only [b.eq_basis]; rfl

        -- Use the extracted helper lemma for span_induction
        have h_vanish_on_tail : ∀ v (hv : v ∈ tail_span),
            coord_k ⟨v, Y.le_topologicalClosure (h_tail_in_Y hv)⟩ = 0 :=
          coord_vanish_on_tail_span basis_Z b.toFun hb_in_Y h_basis_coe k (k + 1)
            (Nat.lt_succ_self k) tail_span rfl h_tail_in_Y

        -- 6. By continuity, coord_k w must be 0
        have h_coord_w_zero : coord_k w'_Z = 0 := by
          -- w is a limit of a sequence in tail_span
          rw [mem_closure_iff_seq_limit] at h_contra
          obtain ⟨u, hu_tail, hu_lim⟩ := h_contra

          -- Lift the sequence to K
          let u_K (n : ℕ) : Y.topologicalClosure :=
            ⟨u n, Y.le_topologicalClosure (h_tail_in_Y (hu_tail n))⟩

          -- Convergence in K is equivalent to convergence in Xbidual for the subtype
          have h_lim_K : Filter.Tendsto u_K Filter.atTop (nhds w'_Z) := by
            rw [Topology.IsEmbedding.tendsto_nhds_iff Topology.IsEmbedding.subtypeVal]
            exact hu_lim

          -- coord_k is continuous, so coord_k (lim u_n) = lim (coord_k u_n)
          have h_tendsto := ((ContinuousLinearMap.continuous coord_k).tendsto w'_Z).comp h_lim_K

          -- But coord_k (u_n) is constantly 0
          have h_vals : ∀ n, coord_k (u_K n) = 0 := fun n ↦ h_vanish_on_tail (u n) (hu_tail n)

          -- The sequence coord_k ∘ u_K = fun _ => 0
          have h_const : (coord_k ∘ u_K) = fun _ => 0 := by
            ext n
            exact h_vals n
          rw [h_const] at h_tendsto
          -- Now h_tendsto says: (fun _ => 0) tends to coord_k w'_Z
          -- So coord_k w'_Z must be 0
          exact (tendsto_const_nhds_iff.mp h_tendsto).symm

        -- 7. Contradiction
        exact hk_ne h_coord_w_zero


      obtain ⟨N, h_w_notin_span⟩ := h_w_span
      let e : ℕ → Xbidual := fun n => b (n + N)

      have h_sep : ∃ f : StrongDual 𝕜 Xbidual, (∀ n, f (e n) = 1) ∧ f w' = -1 := by
        -- Step 1: Show w' ∉ range J
        have hw'_not_in_JX : w' ∉ range J := by
          intro ⟨x, hx⟩
          apply hw_not_JX
          rw [image_univ]
          exact ⟨J x, mem_range_self x, by simp [w', hx]⟩

        -- Step 2: range J is closed and convex (it's a subspace)
        have h_JX_closed : IsClosed (range J) :=
          (NormedSpace.inclusionInDoubleDualLi (𝕜 := 𝕜) (E := X)).isometry.isClosedEmbedding.isClosed_range
        have h_JX_convex : Convex ℝ (range J) := by
          -- range J is a subspace, hence convex
          intro x hx y hy a b ha hb hab
          obtain ⟨x', rfl⟩ := hx
          obtain ⟨y', rfl⟩ := hy
          refine ⟨(a : 𝕜) • x' + (b : 𝕜) • y', ?_⟩
          simp only [map_add, map_smul, RCLike.real_smul_eq_coe_smul (K := 𝕜)]

        -- Step 3: Construct LocallyConvexSpace instance for Hahn-Banach
        haveI : LocallyConvexSpace ℝ Xbidual := by
          refine LocallyConvexSpace.ofBasisZero ℝ Xbidual
            (fun (r : ℝ) => Metric.closedBall (0 : Xbidual) r) (fun r => 0 < r) ?_ ?_
          · exact @Metric.nhds_basis_closedBall Xbidual _ (0 : Xbidual)
          · intro r _
            exact @convex_closedBall Xbidual _ _ (0 : Xbidual) r

        -- Step 4: Apply Hahn-Banach separation
        obtain ⟨g, u, hg_w', hg_JX⟩ := @RCLike.geometric_hahn_banach_point_closed 𝕜 Xbidual _ _ _
          (range J) w' _ _ _ _ _ _ h_JX_convex h_JX_closed hw'_not_in_JX
        -- hg_w' : re(g w') < u
        -- hg_JX : ∀ b ∈ range J, u < re(g b)

        -- Step 5: Since 0 ∈ range J, we have u < re(g 0) = 0, so u < 0
        have hu_neg : u < 0 := by
          have h0 : (0 : Xbidual) ∈ range J := ⟨0, map_zero J⟩
          have h_bound := hg_JX 0 h0
          simp only [map_zero, RCLike.zero_re] at h_bound
          exact h_bound

        -- Step 6: Show g vanishes on range J (subspace argument)
        -- If g(y) ≠ 0 for some y ∈ range J, then by scaling we can make re(g(c•y))
        -- arbitrarily negative, contradicting the bound u < re(g(b)) for all b ∈ range J.
        have hg_vanish : ∀ y ∈ range J, g y = 0 := by
          intro y hy
          by_contra h_ne
          -- If g(y) ≠ 0, then by scaling y ∈ range J (a subspace), we can make
          -- re(g(c • y)) arbitrarily negative, contradicting hg_JX.
          let gy := g y
          have hnorm_pos : 0 < ‖gy‖ := norm_pos_iff.mpr h_ne
          have hnorm_ne : ‖gy‖ ≠ 0 := ne_of_gt hnorm_pos
          -- Choose c such that c * gy is a negative real number
          -- c = -star(gy) / |gy| gives c * gy = -|gy|² / |gy| = -|gy| (negative real)
          let c : 𝕜 := -star gy / ‖gy‖
          -- c • y ∈ range J since range J is a subspace
          have hcy_mem : c • y ∈ range J := by
            obtain ⟨x, rfl⟩ := hy
            exact ⟨c • x, by simp⟩
          -- Compute g(c • y) = c * g(y)
          have h_gc : g (c • y) = c * gy := by simp [gy, smul_eq_mul]
          -- re(c * gy) = re((-star(gy) / ‖gy‖) * gy) = -‖gy‖
          have h_re : RCLike.re (c * gy) = -‖gy‖ := by
            simp only [c, neg_div, neg_mul, div_mul_eq_mul_div]
            simp only [map_neg, neg_inj]
            -- star gy * gy = ‖gy‖²
            have h_conj : star gy * gy = (‖gy‖ : 𝕜)^2 := by
              rw [RCLike.star_def, RCLike.conj_mul, sq]
            rw [h_conj, sq]
            have h_simpl : (‖gy‖ : 𝕜) * ‖gy‖ / (‖gy‖ : 𝕜) = ‖gy‖ := by
              field_simp
            rw [h_simpl, RCLike.ofReal_re]
          -- Scale further to make re(g(t • c • y)) = -t‖gy‖ arbitrarily negative
          let t : ℝ := (|u| + 1) / ‖gy‖ + 1
          have ht_pos : 0 < t := by positivity
          have htcy_mem : (t : 𝕜) • (c • y) ∈ range J := by
            obtain ⟨x, rfl⟩ := hy
            use (t : 𝕜) • c • x
            simp [smul_smul]
          have h_gtc : g ((t : 𝕜) • (c • y)) = (t : 𝕜) * (c * gy) := by
            simp only [map_smul, smul_eq_mul, h_gc]
          have h_re_t : RCLike.re ((t : 𝕜) * (c * gy)) = t * (-‖gy‖) := by
            rw [RCLike.re_ofReal_mul, h_re]
          have h_bound' := hg_JX ((t : 𝕜) • (c • y)) htcy_mem
          rw [h_gtc, h_re_t] at h_bound'
          -- h_bound' : u < t * (-‖gy‖) = -t * ‖gy‖
          -- But we'll show t * (-‖gy‖) < u, giving contradiction
          have h_neg : t * (-‖gy‖) < u := by
            have h1 : ((|u| + 1) / ‖gy‖ + 1) * ‖gy‖ = |u| + 1 + ‖gy‖ := by
              field_simp
            calc t * (-‖gy‖) = -(((|u| + 1) / ‖gy‖ + 1) * ‖gy‖) := by ring
              _ = -(|u| + 1 + ‖gy‖) := by rw [h1]
              _ < -(|u| + 1) := by linarith
              _ ≤ u - 1 := by linarith [neg_abs_le u]
              _ < u := by linarith
          linarith

        -- Step 7: g w' ≠ 0 (since re(g w') < u < 0)
        have hg_w'_ne : g w' ≠ 0 := by
          intro h
          simp [h] at hg_w'
          linarith

        -- Step 8: Scale g to get f with f(e n) = 1
        -- e n = b(n+N) and b(n+N) ∈ S' = (· - w') '' S_bidual
        -- So e n = J(x) - w' for some x ∈ S
        -- We want f(e n) = f(J x - w') = f(J x) - f(w') = 0 - f(w') = -f(w') = 1
        -- So we need f(w') = -1, i.e., f = (-1 / g(w')) • g
        let f := (-(g w')⁻¹) • g
        use f
        constructor
        · -- First part: ∀ n, f (e n) = 1
          intro n
          -- e n = b(n+N) ∈ S', so e n = t - w' for some t ∈ S_bidual = J '' S
          have h_mem : b.toFun (n + N) ∈ S' := he_S' (n + N)
          rw [Set.mem_image] at h_mem
          obtain ⟨t, ht_mem, ht_eq⟩ := h_mem
          -- t ∈ S_bidual = J '' S
          obtain ⟨x, _, rfl⟩ := ht_mem
          -- ht_eq : J x - w' = b(n+N) = e n
          have he_eq : e n = J x - w' := ht_eq.symm
          -- f(e n) = f(J x - w') = f(J x) - f(w')
          calc f (e n) = f (J x - w') := by rw [he_eq]
            _ = f (J x) - f w' := by rw [map_sub]
            _ = (-(g w')⁻¹) • g (J x) - (-(g w')⁻¹) • g w' := rfl
            _ = (-(g w')⁻¹) * g (J x) - (-(g w')⁻¹) * g w' := by simp [smul_eq_mul]
            _ = (-(g w')⁻¹) * 0 - (-(g w')⁻¹) * g w' := by rw [hg_vanish (J x) (mem_range_self x)]
            _ = 0 - (-(g w')⁻¹) * g w' := by ring
            _ = (g w')⁻¹ * g w' := by ring
            _ = 1 := inv_mul_cancel₀ hg_w'_ne
        · -- Second part: f w' = -1
          calc f w' = (-(g w')⁻¹) • g w' := rfl
            _ = (-(g w')⁻¹) * g w' := by simp [smul_eq_mul]
            _ = -((g w')⁻¹ * g w') := by ring
            _ = -(1 : 𝕜) := by rw [inv_mul_cancel₀ hg_w'_ne]
            _ = -1 := by ring


      obtain ⟨f, hf_e⟩ := h_sep


      -- Let's define the correct sequence that's in S_bidual
      let s : ℕ → Xbidual := fun n => e n + w'
      have hs_in_S_bidual : ∀ n, s n ∈ S_bidual := fun n => by
        -- e n = b.toFun (n + N), so we need he_S' (n + N)
        -- he_S' (n+N) : b.toFun (n+N) ∈ S' where S' = (fun y => y - w') '' S_bidual
        -- So there exists t ∈ S_bidual such that b.toFun (n+N) = t - w'
        -- Thus t = b.toFun (n+N) + w' = e n + w' = s n ∈ S_bidual
        have h_mem : b.toFun (n + N) ∈ S' := he_S' (n + N)
        rw [Set.mem_image] at h_mem
        obtain ⟨t, ht_mem, ht_eq⟩ := h_mem
        -- ht_eq : t - w' = b.toFun (n+N), so t = b.toFun (n+N) + w' = e n + w' = s n
        simp only [s, e]
        convert ht_mem using 1
        -- Goal: b.toFun (n + N) + w' = t
        -- From ht_eq: t - w' = b.toFun (n + N), so t = b.toFun (n + N) + w'
        rw [sub_eq_iff_eq_add] at ht_eq
        exact ht_eq.symm

      -- If s = b + w' is basic, we can pull back to S and contradict h_no_basic
      -- Use perturb_basic_sequence: if e is basic, f(e n) = 1, f(w') = -1, and w' ∉ closure(span e),
      -- then e + w' is basic.
      have h_basicS : IsBasicSequence 𝕜 s := by
        -- Use perturb_basic_sequence: the tail e is basic, and adding w' preserves basicness
        -- under the conditions f(e n) = 1, f(w') = -1, w' ∉ closure(span e)
        have he_basic : IsBasicSequence 𝕜 e := tail_basic_sequence b N
        obtain ⟨b_tail, hb_tail_eq⟩ := he_basic
        convert perturb_basic_sequence b_tail w' f ?_ hf_e.2 ?_ using 1
        · funext n; exact congrArg (· + w') (congrFun hb_tail_eq n).symm
        · intro n
          have : b_tail.toFun n = e n := congrFun hb_tail_eq n
          rw [this]; exact hf_e.1 n
        · rw [congrArg Set.range hb_tail_eq]; exact h_w_notin_span

      have h_in_S : ∀ n, s n ∈ S_bidual := hs_in_S_bidual

      --transfer back the basic sequence to S and get a contradiction with h_no_basic
      -- Since s n ∈ S_bidual = J '' S, there exists x_n ∈ S with J(x_n) = s n
      have h_preimage : ∀ n, ∃ x ∈ S, J x = s n := fun n => h_in_S n

      let x : ℕ → X := fun n => (h_preimage n).choose
      have hx_S : ∀ n, x n ∈ S := fun n => (h_preimage n).choose_spec.1
      have hx_J : ∀ n, J (x n) = s n := fun n => (h_preimage n).choose_spec.2

      -- J is an isometric embedding, so J preserves the Grünblum condition
      -- If s is basic in Xbidual, then x is basic in X
      have hx_basic : IsBasicSequence 𝕜 x := by
        -- Use isometry of J and transfer from h_basicS
        -- J is an isometry
        have hJ_iso : ∀ y, ‖J y‖ = ‖y‖ := fun y =>
          (NormedSpace.inclusionInDoubleDualLi (𝕜 := 𝕜) (E := X)).norm_map y
        -- h_basicS gives us a basic sequence structure on s
        rcases h_basicS with ⟨b_s, hb_s_eq⟩
        -- s n ≠ 0 since b_s is a basic sequence (has linearly independent basis)
        have hs_nz : ∀ n, s n ≠ 0 := fun n hs0 => by
          -- b_s.basis.linearIndependent gives linear independence on the submodule
          have h_indep := b_s.basis.linearIndependent
          have h_ne := h_indep.ne_zero n
          -- b_s.eq_basis : b_s.basis = Set.codRestrict b_s.toFun ...
          -- So b_s.basis n = ⟨b_s n, _⟩
          -- b_s n = s n via hb_s_eq
          have hbn : b_s.toFun n = s n := congrFun hb_s_eq n
          -- Unfold the codRestrict to get (b_s.basis n).1 = b_s n
          have h_basis_val : (b_s.basis n : Xbidual) = b_s.toFun n := by
            simp only [b_s.eq_basis]; rfl
          -- If s n = 0, then (b_s.basis n).1 = 0, so b_s.basis n = 0
          have h_zero : b_s.basis n = 0 := Subtype.ext (h_basis_val.trans (hbn.trans hs0))
          exact h_ne h_zero
        -- x n ≠ 0 since s n = J(x n) ≠ 0 and J is injective
        have hx_nz : ∀ n, x n ≠ 0 := fun n hx0 => by
          have := hs_nz n
          rw [← hx_J n, hx0, map_zero] at this
          exact this rfl
        -- Bound on sums transfers via J being an isometry
        have h_sum_eq : ∀ (a : ℕ → 𝕜) k, J (∑ i ∈ Finset.range k, a i • x i) = ∑ i ∈ Finset.range k, a i • s i := by
          intro a k
          simp only [map_sum, ContinuousLinearMap.map_smul, hx_J]
        -- Transfer Grünblum bound
        have h_bound : ∀ n m (a : ℕ → 𝕜), m ≤ n →
            ‖∑ i ∈ Finset.range m, a i • x i‖ ≤ grunblumConstant b_s * ‖∑ i ∈ Finset.range n, a i • x i‖ := by
          intro n m a hmn
          calc ‖∑ i ∈ Finset.range m, a i • x i‖
              = ‖J (∑ i ∈ Finset.range m, a i • x i)‖ := (hJ_iso _).symm
            _ = ‖∑ i ∈ Finset.range m, a i • s i‖ := by rw [h_sum_eq]
            _ = ‖∑ i ∈ Finset.range m, a i • b_s i‖ := by simp only [← hb_s_eq]
            _ ≤ grunblumConstant b_s * ‖∑ i ∈ Finset.range n, a i • b_s i‖ :=
                grunblum_bound_of_basic b_s n m a hmn
            _ = grunblumConstant b_s * ‖∑ i ∈ Finset.range n, a i • s i‖ := by simp only [← hb_s_eq]
            _ = grunblumConstant b_s * ‖J (∑ i ∈ Finset.range n, a i • x i)‖ := by rw [h_sum_eq]
            _ = grunblumConstant b_s * ‖∑ i ∈ Finset.range n, a i • x i‖ := by rw [hJ_iso]
        exact isBasicSequence_of_grunblum ⟨grunblumConstant b_s, grunblumConstant_ge_one b_s, h_bound⟩ hx_nz

      exact h_no_basic x hx_S hx_basic

    -- transfer compactness back to X via weak-weak* correspondence
    have hK_closed : IsClosed K := isClosed_closure
    have hK_bounded_preimage : Bornology.IsBounded (StrongDual.toWeakDual ⁻¹' K) := by
      have h1 : Bornology.IsBounded (StrongDual.toWeakDual ⁻¹' K) := by
        rw [Metric.isBounded_iff_subset_closedBall 0]
        rw [Metric.isBounded_iff_subset_closedBall 0] at h_S_bidual_bounded
        obtain ⟨R, hR⟩ := h_S_bidual_bounded
        use R
        intro x hx
        rw [Set.mem_preimage] at hx
        rw [Metric.mem_closedBall, dist_zero_right]
        have h_sub : StrongDual.toWeakDual '' S_bidual ⊆ WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 R := by
          intro y hy
          obtain ⟨z, hzS, rfl⟩ := hy
          simp only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right,
            WeakDual.coe_toStrongDual, StrongDual.coe_toWeakDual]
          -- Now need: ‖z‖ ≤ R
          have hz_ball := hR hzS
          rw [Metric.mem_closedBall, dist_zero_right] at hz_ball
          exact hz_ball
        have h_closed : IsClosed (WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : Xbidual) R) :=
          WeakDual.isClosed_closedBall (0 : Xbidual) R
        have h_K_sub : K ⊆ WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 R :=
          closure_minimal h_sub h_closed
        have hxK' : StrongDual.toWeakDual x ∈ WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 R :=
          h_K_sub hx
        simp only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right,
          WeakDual.coe_toStrongDual, StrongDual.coe_toWeakDual] at hxK'
        exact hxK'
      exact h1
    have hK_compact : IsCompact K := WeakDual.isCompact_of_bounded_of_closed hK_bounded_preimage hK_closed

    let emb := NormedSpace.inclusionInDoubleDual_isEmbedding_weak 𝕜 X
    let ι := fun x : WeakSpace 𝕜 X => StrongDual.toWeakDual (J x)

    have hK_in_range : K ⊆ Set.range ι := by
      intro y hy
      have h := hK_subset hy
      simp only [Set.mem_image, Set.mem_univ, true_and] at h
      obtain ⟨z, ⟨x, hx⟩, hz⟩ := h
      exact ⟨x, hz ▸ hx ▸ rfl⟩

    haveI : T2Space (WeakSpace 𝕜 X) := emb.t2Space

    let homeo := NormedSpace.inclusionInDoubleDual_homeomorph_weak 𝕜 X
    let K_in_range : Set (Set.range ι) := Subtype.val ⁻¹' K
    have hK_in_range_compact : IsCompact K_in_range := by
      rw [IsEmbedding.subtypeVal.isCompact_iff]
      convert hK_compact using 1
      ext y
      simp only [K_in_range, Set.mem_image, Set.mem_preimage]
      exact ⟨fun ⟨⟨_, _⟩, hK, rfl⟩ => hK, fun hy => ⟨⟨y, hK_in_range hy⟩, hy, rfl⟩⟩

    let K_weak : Set (WeakSpace 𝕜 X) := homeo.symm '' K_in_range
    have hK_weak_compact : IsCompact K_weak := hK_in_range_compact.image homeo.symm.continuous

    have h_closure_subset : closure (toWeakSpace 𝕜 X '' S) ⊆ K_weak := by
      have h_S_subset : toWeakSpace 𝕜 X '' S ⊆ K_weak := by
        intro z hz
        obtain ⟨x, hxS, rfl⟩ := hz
        have h_in_K : ι x ∈ K := subset_closure ⟨J x, ⟨x, hxS, rfl⟩, rfl⟩
        have h_in_K_range : (⟨ι x, x, rfl⟩ : Set.range ι) ∈ K_in_range := h_in_K
        simp only [K_weak, Set.mem_image]
        use ⟨ι x, x, rfl⟩, h_in_K_range
        have h_homeo : homeo (toWeakSpace 𝕜 X x) = ⟨ι x, x, rfl⟩ := by
          apply Subtype.ext; rfl
        rw [← h_homeo, Homeomorph.symm_apply_apply]
      have h_closed : IsClosed K_weak := hK_weak_compact.isClosed
      exact closure_minimal h_S_subset h_closed

    hK_weak_compact.of_isClosed_subset isClosed_closure h_closure_subset

--
