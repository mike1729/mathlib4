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

/-- If a vector has all zero coordinates in a Schauder basis, it must be zero.
    Extracted to reduce elaboration overhead. -/
private lemma nonzero_has_nonzero_coord {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [CompleteSpace E] (basis : SchauderBasis 𝕜 E) (x : E) (hx : x ≠ 0) :
    ∃ k, basis.coord k x ≠ 0 := by
  by_contra! h_all_zero
  have h_exp := basis.expansion x
  have h_zero : (fun i ↦ basis.coord i x • basis i) = fun _ ↦ 0 := by
    ext i; simp [h_all_zero i]
  rw [h_zero] at h_exp
  exact hx (HasSum.unique h_exp hasSum_zero)

/-- A nonzero element in the closure of a basic sequence's span cannot be in the closure of all
    tail spans. This is because some Schauder coordinate must be nonzero, but that coordinate
    vanishes on sufficiently late tails. Extracted to reduce elaboration overhead. -/
private lemma nonzero_not_in_all_tail_closures {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [CompleteSpace E] (b : BasicSequence 𝕜 E)
    (w : E) (hw_in : w ∈ (Submodule.span 𝕜 (Set.range b.toFun)).topologicalClosure)
    (hw_ne : w ≠ 0) :
    ∃ N, w ∉ closure (Submodule.span 𝕜 (Set.range (fun n => b (n + N))) : Set E) := by
  -- Setup: Y = span(b), Z = closure(Y)
  let Y : Submodule 𝕜 E := Submodule.span 𝕜 (Set.range b.toFun)
  let Z : Submodule 𝕜 E := Y.topologicalClosure
  let w_Z : Z := ⟨w, hw_in⟩
  have hw_Z_ne : w_Z ≠ 0 := fun h => hw_ne (congrArg Subtype.val h)
  -- Build Schauder basis for Z from b
  let basis_Z : SchauderBasis 𝕜 Z :=
    BasicSequences.SchauderBasis_of_closure (Y := Y) b.basis b.basisConstant_lt_top
  have h_basis_coe : ∀ n, (basis_Z n : E) = b.toFun n := fun n => by
    rw [BasicSequences.SchauderBasis_of_closure_apply]; simp only [b.eq_basis]; rfl
  -- w_Z ≠ 0 implies some coordinate is nonzero
  have h_exists_coord : ∃ k, basis_Z.coord k w_Z ≠ 0 :=
    nonzero_has_nonzero_coord basis_Z w_Z hw_Z_ne
  obtain ⟨k, hk_ne⟩ := h_exists_coord
  -- Use N = k + 1
  use k + 1
  intro h_contra
  -- Define tail span
  let tail_span : Submodule 𝕜 E := Submodule.span 𝕜 (Set.range (fun n => b.toFun (n + (k + 1))))
  have h_tail_in_Y : tail_span ≤ Y := by
    apply Submodule.span_mono; intro x hx; obtain ⟨n, rfl⟩ := hx; exact ⟨n + (k + 1), rfl⟩
  have hb_in_Y : ∀ n, b.toFun n ∈ Y := fun n => Submodule.subset_span ⟨n, rfl⟩
  -- Use helper lemma for coord vanishing on tail
  have h_vanish_on_tail : ∀ v (hv : v ∈ tail_span),
      basis_Z.coord k ⟨v, Y.le_topologicalClosure (h_tail_in_Y hv)⟩ = 0 :=
    coord_vanish_on_tail_span basis_Z b.toFun hb_in_Y h_basis_coe k (k + 1)
      (Nat.lt_succ_self k) tail_span rfl h_tail_in_Y
  -- By continuity, coord_k w_Z = 0
  have h_coord_w_zero : basis_Z.coord k w_Z = 0 := by
    rw [mem_closure_iff_seq_limit] at h_contra
    obtain ⟨u, hu_tail, hu_lim⟩ := h_contra
    let u_Z : ℕ → Z := fun n => ⟨u n, Y.le_topologicalClosure (h_tail_in_Y (hu_tail n))⟩
    have h_lim_Z : Filter.Tendsto u_Z Filter.atTop (nhds w_Z) := by
      rw [Topology.IsEmbedding.tendsto_nhds_iff Topology.IsEmbedding.subtypeVal]; exact hu_lim
    have h_tendsto :=
      ((ContinuousLinearMap.continuous (basis_Z.coord k)).tendsto w_Z).comp h_lim_Z
    have h_vals : ∀ n, basis_Z.coord k (u_Z n) = 0 := fun n => h_vanish_on_tail (u n) (hu_tail n)
    have h_const : (basis_Z.coord k ∘ u_Z) = fun _ => 0 := by ext n; exact h_vals n
    rw [h_const] at h_tendsto
    exact (tendsto_const_nhds_iff.mp h_tendsto).symm
  -- Contradiction
  exact hk_ne h_coord_w_zero

/-- If 0 ∈ closure of a translated set S - w, then w ∈ closure S.
    Extracted to reduce elaboration overhead in the main theorem. -/
private lemma mem_closure_of_zero_in_translated_closure {E : Type*} [NormedAddCommGroup E]
    {S : Set E} {w : E} (h0 : (0 : E) ∈ closure ((fun y => y - w) '' S)) : w ∈ closure S := by
  let T : E ≃ₜ E := Homeomorph.addRight (-w)
  have h_image : (fun y => y - w) '' S = T '' S := by
    simp only [T, Homeomorph.coe_addRight, sub_eq_add_neg]
  rw [h_image, ← Homeomorph.image_closure] at h0
  obtain ⟨y, hy_mem, hy_eq⟩ := h0
  have h_y_eq_w : y = w := by
    have : T.symm (T y) = T.symm 0 := by rw [hy_eq]
    rw [Homeomorph.symm_apply_apply] at this
    simp only [T, Homeomorph.addRight_symm, Homeomorph.coe_addRight, zero_add] at this
    rw [neg_neg] at this
    exact this
  rw [← h_y_eq_w]
  exact hy_mem

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

/-- Elements of a basic sequence are nonzero because the underlying Schauder basis is linearly
    independent. Extracted to reduce elaboration overhead in the main theorem. -/
private lemma basic_sequence_element_nonzero {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (b : BasicSequence 𝕜 E) (n : ℕ) : b n ≠ 0 := fun hb0 => by
  have h_indep := b.basis.linearIndependent
  have h_ne := h_indep.ne_zero n
  have h_basis_val : (b.basis n : E) = b.toFun n := by simp only [b.eq_basis]; rfl
  exact h_ne (Subtype.ext (h_basis_val.trans hb0))

/-- The Grünblum bound transfers through an isometry: if `b` is a basic sequence in `Y` and
    `J : X →L[𝕜] Y` is an isometry with `J (x n) = b n`, then the Grünblum bound for `b`
    implies the same bound for `x`. Extracted to reduce elaboration overhead. -/
private lemma grunblum_bound_transfer_via_isometry {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (b : BasicSequence 𝕜 Y) (x : ℕ → X) (J : X →L[𝕜] Y)
    (hJ_iso : ∀ y, ‖J y‖ = ‖y‖) (hx_J : ∀ n, J (x n) = b n)
    (n m : ℕ) (a : ℕ → 𝕜) (hmn : m ≤ n) :
    ‖∑ i ∈ Finset.range m, a i • x i‖ ≤ grunblumConstant b * ‖∑ i ∈ Finset.range n, a i • x i‖ := by
  have h_sum_eq : ∀ k, J (∑ i ∈ Finset.range k, a i • x i) = ∑ i ∈ Finset.range k, a i • b i := by
    intro k; simp only [map_sum, ContinuousLinearMap.map_smul, hx_J]
  calc ‖∑ i ∈ Finset.range m, a i • x i‖
      = ‖J (∑ i ∈ Finset.range m, a i • x i)‖ := (hJ_iso _).symm
    _ = ‖∑ i ∈ Finset.range m, a i • b i‖ := by rw [h_sum_eq]
    _ ≤ grunblumConstant b * ‖∑ i ∈ Finset.range n, a i • b i‖ :=
        grunblum_bound_of_basic b n m a hmn
    _ = grunblumConstant b * ‖J (∑ i ∈ Finset.range n, a i • x i)‖ := by rw [h_sum_eq]
    _ = grunblumConstant b * ‖∑ i ∈ Finset.range n, a i • x i‖ := by rw [hJ_iso]

--  set_option trace.profiler true in
set_option maxHeartbeats 720000 in
-- Complex nested proof with Hahn-Banach separation and bidual embedding arguments
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
        let A : Set (WeakDual 𝕜 (StrongDual 𝕜 X)) := StrongDual.toWeakDual '' S_bidual
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
        intro h0
        -- Use helper lemma: 0 ∈ closure S' implies w' ∈ closure S_bidual
        have hw_cl : w' ∈ closure S_bidual := mem_closure_of_zero_in_translated_closure h0
        -- The range of J is closed (isometry from complete space)
        have h_JX_closed : IsClosed (range J) :=
          (NormedSpace.inclusionInDoubleDualLi (𝕜 := 𝕜) (E := X)).isometry.isClosedEmbedding.isClosed_range
        -- S_bidual ⊆ range J, so closure S_bidual ⊆ range J
        have hw_in_JX : w' ∈ range J :=
          closure_minimal (image_subset_range J S) h_JX_closed hw_cl
        -- This contradicts w ∉ J(X)
        apply hw_not_JX
        rw [image_univ]
        obtain ⟨x, hx⟩ := hw_in_JX
        refine ⟨J x, mem_range_self x, ?_⟩
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
        -- w is non-zero (since w ∉ J(X) and 0 ∈ J(X))
        have hw_ne : w' ≠ 0 := by
          intro h
          apply hw_not_JX
          have hw0 : w = 0 := by
            apply WeakDual.toStrongDual.injective
            simp only [w'] at h
            rw [h, map_zero]
          rw [hw0, image_univ]
          exact ⟨J 0, ⟨0, rfl⟩, by simp⟩
        -- If w is in closure of all tails, it's in the full closure (N=0), so apply helper
        by_contra h_contra
        push_neg at h_contra
        have hw_in : w' ∈ (Submodule.span 𝕜 (Set.range b.toFun)).topologicalClosure := by
          simpa using h_contra 0
        exact (nonzero_not_in_all_tail_closures b w' hw_in hw_ne).elim (fun N hN => hN (h_contra N))


      obtain ⟨N, h_w_notin_span⟩ := h_w_span
      let e : ℕ → Xbidual := fun n => b (n + N)

      have h_sep : ∃ f : StrongDual 𝕜 Xbidual, (∀ n, f (e n) = 1) ∧ f w' = -1 := by
        -- range J as a submodule
        let M := LinearMap.range (J : X →L[𝕜] Xbidual).toLinearMap
        have hM_eq : (M : Set Xbidual) = range J := LinearMap.coe_range _
        have hM_closed : IsClosed (M : Set Xbidual) := by
          rw [hM_eq]
          exact (NormedSpace.inclusionInDoubleDualLi (𝕜 := 𝕜) (E := X)).isometry
            |>.isClosedEmbedding.isClosed_range
        have hw'_not_in_M : w' ∉ (M : Set Xbidual) := by
          rw [hM_eq]
          intro ⟨x, hx⟩
          apply hw_not_JX
          rw [image_univ]
          exact ⟨J x, mem_range_self x, by simp [w', hx]⟩
        -- Apply the shared Hahn-Banach lemma
        obtain ⟨f, hf_w', hf_vanish⟩ :=
          BasicSequences.exists_functional_neg_one_and_vanishes_on_closed_submodule
            M hM_closed w' hw'_not_in_M
        use f
        constructor
        · -- ∀ n, f (e n) = 1: e n = J x - w' for some x, so f(e n) = 0 - (-1) = 1
          intro n
          have h_mem : b.toFun (n + N) ∈ S' := he_S' (n + N)
          obtain ⟨t, ht_mem, ht_eq⟩ := h_mem
          obtain ⟨x, _, rfl⟩ := ht_mem
          have he_eq : e n = J x - w' := ht_eq.symm
          calc f (e n) = f (J x - w') := by rw [he_eq]
            _ = f (J x) - f w' := by rw [map_sub]
            _ = 0 - (-1) := by rw [hf_vanish (J x) (by rw [hM_eq]; exact mem_range_self x), hf_w']
            _ = 1 := by ring
        · exact hf_w'


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
        have hJ_iso : ∀ y, ‖J y‖ = ‖y‖ := fun y =>
          (NormedSpace.inclusionInDoubleDualLi (𝕜 := 𝕜) (E := X)).norm_map y
        rcases h_basicS with ⟨b_s, hb_s_eq⟩
        -- x n ≠ 0 since s n = J(x n) = b_s n ≠ 0 (by extracted lemma) and J is injective
        have hx_nz : ∀ n, x n ≠ 0 := fun n hx0 => by
          have := basic_sequence_element_nonzero b_s n
          rw [congrFun hb_s_eq n, ← hx_J n, hx0, map_zero] at this
          exact this rfl
        -- Transfer Grünblum bound using extracted lemma
        have hx_J' : ∀ n, J (x n) = b_s n := fun n => (hx_J n).trans (congrFun hb_s_eq n).symm
        have h_bound : ∀ n m (a : ℕ → 𝕜), m ≤ n →
            ‖∑ i ∈ Finset.range m, a i • x i‖ ≤
            grunblumConstant b_s * ‖∑ i ∈ Finset.range n, a i • x i‖ :=
          fun n m a hmn => grunblum_bound_transfer_via_isometry b_s x J hJ_iso hx_J' n m a hmn
        exact isBasicSequence_of_grunblum
          ⟨grunblumConstant b_s, grunblumConstant_ge_one b_s, h_bound⟩ hx_nz

      exact h_no_basic x hx_S hx_basic

    -- transfer compactness back to X via weak-weak* correspondence
    have hK_closed : IsClosed K := isClosed_closure
    have hK_bounded_preimage : Bornology.IsBounded (StrongDual.toWeakDual ⁻¹' K) := by
      rw [Metric.isBounded_iff_subset_closedBall 0]
      rw [Metric.isBounded_iff_subset_closedBall 0] at h_S_bidual_bounded
      obtain ⟨R, hR⟩ := h_S_bidual_bounded
      use R
      intro x hx
      rw [Set.mem_preimage] at hx
      rw [Metric.mem_closedBall, dist_zero_right]
      have h_sub :
          StrongDual.toWeakDual '' S_bidual ⊆ WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 R := by
        intro y hy
        obtain ⟨z, hzS, rfl⟩ := hy
        simp only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right,
          WeakDual.coe_toStrongDual, StrongDual.coe_toWeakDual]
        have hz_ball := hR hzS
        rw [Metric.mem_closedBall, dist_zero_right] at hz_ball
        exact hz_ball
      have h_closed : IsClosed (WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : Xbidual) R) :=
        WeakDual.isClosed_closedBall (0 : Xbidual) R
      have hxK' :=
        (closure_minimal h_sub h_closed : K ⊆ WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 R) hx
      simp only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right,
        WeakDual.coe_toStrongDual, StrongDual.coe_toWeakDual] at hxK'
      exact hxK'
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
