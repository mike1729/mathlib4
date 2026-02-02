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


/-!
# Basic Sequences in Banach Spaces
-/

noncomputable section

open Submodule Set WeakDual Metric Filter Topology

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]




theorem no_basic_sequence_implies_relatively_weakly_compact [CompleteSpace X]
    {S : Set X} (hS_ne : S.Nonempty) (h_norm : (0 : X) ∉ closure S)
    (h_bounded : Bornology.IsBounded S)
    (h_no_basic : ∀ (e : ℕ → X), (∀ n, e n ∈ S) → ¬ IsBasicSequence 𝕜 e) :
    IsCompact (closure (toWeakSpace 𝕜 X '' S)) :=

    let Xbidual := StrongDual 𝕜 (StrongDual 𝕜 X)
    let J := NormedSpace.inclusionInDoubleDual 𝕜 X
    let S_bidual := J '' S

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

    let K := closure (StrongDual.toWeakDual '' S_bidual)

    have hK_subset :  K ⊆ StrongDual.toWeakDual '' (J '' (Set.univ)) := by
      by_contra h_not_subset
      rw [Set.subset_def] at h_not_subset
      push_neg at h_not_subset
      obtain ⟨w, hwK, hw_not_JX⟩ := h_not_subset

      -- Define S' in StrongDual (Xbidual) space as translation of S_bidual by -w'
      let w' : Xbidual := WeakDual.toStrongDual w
      let S' := (fun y => y - w') '' S_bidual

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
        let Y := Submodule.span 𝕜 (Set.range b.toFun)
        let Z := Y.topologicalClosure

        -- Since h_contra holds for N=0, w is in the closure of the whole span
        have h_w'_in_Z : w' ∈ Z := by
          simpa using h_contra 0

        -- Lift w to the subspace K = closure Y
        let w'_Z : Z := ⟨w', h_w'_in_Z⟩
        have hw'_Z_ne : w'_Z ≠ 0 := fun h => hw_ne (congrArg Subtype.val h)

        -- Use the theorem to treat b as a Schauder basis for K
        -- (Assuming SchauderBasis_of_closure is available as discussed)
        let basis_Z :=
        -- let basis_K : SchauderBasis 𝕜 Y.topologicalClosure :=
          SchauderBasis_of_closure b.basis b.basisConstant_lt_top

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
        let coord_k := basis_Z.coord k

        -- We show coord_k vanishes on the tail span
        -- The tail span is generated by b_{k+1}, b_{k+2}, ...
        let tail_span := Submodule.span 𝕜 (Set.range (fun n => b.toFun (n + (k + 1))))

        -- First show tail_span ⊆ Y
        have h_tail_in_Y : tail_span ≤ Y := by
          apply Submodule.span_mono
          intro x hx
          obtain ⟨n, rfl⟩ := hx
          exact ⟨n + (k + 1), rfl⟩

        -- First prove a simpler lemma: coord_k vanishes on basis elements with index > k
        have h_vanish_basis : ∀ j > k, basis_Z.coord k (basis_Z j) = 0 := by
          intro j hj
          rw [basis_Z.ortho k j, Pi.single_apply, if_neg (ne_of_gt hj).symm]

        -- The coordinate functional coord_k vanishes on elements of tail_span
        have h_vanish_on_tail : ∀ v (hv : v ∈ tail_span), coord_k ⟨v, Y.le_topologicalClosure (h_tail_in_Y hv)⟩ = 0 := by
          intro v hv
          -- For v in tail_span, show coord_k applied to the lifted element is 0
          -- Use span induction with the dependent predicate
          induction hv using Submodule.span_induction with
          | mem x hx =>
            -- Base case: generators b_{n + (k+1)}
            obtain ⟨n, rfl⟩ := hx
            -- x = b.toFun (n + (k + 1)), which corresponds to basis_Z (n + (k + 1))
            have h_eq : (⟨b.toFun (n + (k + 1)), Y.le_topologicalClosure (h_tail_in_Y (Submodule.subset_span ⟨n, rfl⟩))⟩ : Z)
                      = basis_Z (n + (k + 1)) := by
              rw [SchauderBasis_of_closure_apply]
              -- The result follows from b.eq_basis which says ⇑basis = Set.codRestrict ...
              congr 1
              simp only [b.eq_basis]
              rfl
            rw [h_eq]
            exact h_vanish_basis (n + (k + 1)) (by omega)
          | zero =>
            convert map_zero coord_k
          | add x y hx' hy' hx hy =>
            have hx_Y : x ∈ Y.topologicalClosure := Y.le_topologicalClosure (h_tail_in_Y hx')
            have hy_Y : y ∈ Y.topologicalClosure := Y.le_topologicalClosure (h_tail_in_Y hy')
            have hxy_Y : x + y ∈ Y.topologicalClosure := Submodule.add_mem _ hx_Y hy_Y
            have h_eq : coord_k ⟨x + y, hxy_Y⟩ = coord_k ⟨x, hx_Y⟩ + coord_k ⟨y, hy_Y⟩ := by
              convert map_add coord_k ⟨x, hx_Y⟩ ⟨y, hy_Y⟩ using 2 <;> rfl
            rw [h_eq, hx, hy, add_zero]
          | smul c x hx' hx =>
            have hx_Y : x ∈ Y.topologicalClosure := Y.le_topologicalClosure (h_tail_in_Y hx')
            have hcx_Y : c • x ∈ Y.topologicalClosure := Submodule.smul_mem _ c hx_Y
            have h_eq : coord_k ⟨c • x, hcx_Y⟩ = c • coord_k ⟨x, hx_Y⟩ := by
              convert map_smul coord_k c ⟨x, hx_Y⟩ using 2 <;> rfl
            rw [h_eq, hx, smul_zero]

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
      let e := fun n => b (n + N)

      have h_sep : ∃ f : StrongDual 𝕜 Xbidual, ∀ n, f (e n) = 1 := by
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
          -- If g(y) ≠ 0, then either re(g y) ≠ 0 or im(g y) ≠ 0.
          -- In either case, scaling arguments lead to a contradiction with hg_JX.
          -- The key is: for a 𝕜-subspace, if we can scale to get arbitrarily negative
          -- real parts, but hg_JX says u < re(g b) for all b in the subspace, contradiction.
          sorry

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


      obtain ⟨f, hf_e⟩ := h_sep


      -- Let's define the correct sequence that's in S_bidual
      let s := fun n => e n + w'
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
      -- For now, assume the basicness (TODO: prove using similar Grünblum argument)
      have h_basicS : IsBasicSequence 𝕜 s := by
        sorry

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
        -- J is an isometry, so the Grünblum condition transfers from s to x
        -- Since s = J ∘ x and J preserves norms, ‖∑ aᵢ xᵢ‖ = ‖∑ aᵢ sᵢ‖
        sorry

      -- Contradiction: x is a basic sequence in S, but h_no_basic says there's no such sequence
      exact h_no_basic x hx_S hx_basic

    -- transfer compactness back to X via weak-weak* correspondence
    sorry

--
