/-
Copyright (c) 2026 Michał Świętek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michał Świętek
-/
module

public import Mathlib.Analysis.Normed.Module.SchauderBasis.Closure
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Algebra.Module.WeakDual
public import Mathlib.Topology.Maps.Basic


/-!
# Basic Sequences in Banach Spaces
-/
@[expose] public section

noncomputable section

open Submodule Set WeakDual Metric Filter Topology

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

namespace BasicSequence

/-- Helper lemma: a coordinate functional vanishes on the span of basis elements with larger index.
    This is extracted to reduce elaboration overhead in the main theorem. -/
private lemma coord_vanish_on_tail_span {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [CompleteSpace E] {Y : Submodule 𝕜 E}
    (basis_Z : SchauderBasis 𝕜 Y.topologicalClosure)
    (b : ℕ → E)
    (h_basis_coe : ∀ n, (basis_Z n : E) = b n)
    (k N : ℕ) (hN : k < N)
    (tail_span : Submodule 𝕜 E)
    (h_tail_span_eq : tail_span = Submodule.span 𝕜 (Set.range (fun n => b (n + N))))
    (h_tail_in_Y : tail_span ≤ Y)
    (v : E) (hv : v ∈ tail_span) :
    basis_Z.coord k ⟨v, Y.le_topologicalClosure (h_tail_in_Y hv)⟩ = 0 := by
  rw [h_tail_span_eq] at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨n, rfl⟩ := hx
    have h_mem : b (n + N) ∈ Y.topologicalClosure :=
      Y.le_topologicalClosure (h_tail_in_Y (h_tail_span_eq ▸ Submodule.subset_span ⟨n, rfl⟩))
    have h_eq : (⟨b (n + N), h_mem⟩ : Y.topologicalClosure) = basis_Z (n + N) :=
      Subtype.ext (h_basis_coe (n + N)).symm
    rw [h_eq]; simp [basis_Z.ortho k (n + N), ne_of_gt (by omega : k < n + N)]
  | zero => exact map_zero _
  | add x y hx' hy' hx hy =>
    have hx_tc : x ∈ Y.topologicalClosure :=
      Y.le_topologicalClosure (h_tail_in_Y (h_tail_span_eq ▸ hx'))
    have hy_tc : y ∈ Y.topologicalClosure :=
      Y.le_topologicalClosure (h_tail_in_Y (h_tail_span_eq ▸ hy'))
    calc basis_Z.coord k ⟨x + y, _⟩
        = basis_Z.coord k ((⟨x, hx_tc⟩ : Y.topologicalClosure) + ⟨y, hy_tc⟩) := rfl
      _ = basis_Z.coord k ⟨x, hx_tc⟩ + basis_Z.coord k ⟨y, hy_tc⟩ := map_add ..
      _ = 0 + 0 := by rw [hx (h_tail_span_eq ▸ hx'), hy (h_tail_span_eq ▸ hy')]
      _ = 0 := add_zero 0
  | smul c x hx' hx =>
    have hx_tc : x ∈ Y.topologicalClosure :=
      Y.le_topologicalClosure (h_tail_in_Y (h_tail_span_eq ▸ hx'))
    calc basis_Z.coord k ⟨c • x, _⟩
        = basis_Z.coord k (c • (⟨x, hx_tc⟩ : Y.topologicalClosure)) := rfl
      _ = c • basis_Z.coord k ⟨x, hx_tc⟩ := map_smul ..
      _ = c • 0 := by rw [hx (h_tail_span_eq ▸ hx')]
      _ = 0 := smul_zero c

/-- A nonzero element in the closure of a basic sequence's span cannot be in the closure of all
    tail spans. This is because some Schauder coordinate must be nonzero, but that coordinate
    vanishes on sufficiently late tails. Extracted to reduce elaboration overhead. -/
private lemma nonzero_not_in_all_tail_closures {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [CompleteSpace E] (b : BasicSequence 𝕜 E) (h_bound : b.basis.enormProjBound < ⊤)
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
    schauderBasisOfClosure (Y := Y) b.basis h_bound
  have h_basis_coe : ∀ n, (basis_Z n : E) = b.toFun n := fun n => by
    rw [schauderBasisOfClosure_apply]
    exact b.basis_eq n
  -- w_Z ≠ 0 implies some coordinate is nonzero
  have ⟨k, hk_ne⟩ : ∃ k, basis_Z.coord k w_Z ≠ 0 := by
    by_contra! h
    exact hw_Z_ne (HasSum.unique (by simpa [h] using basis_Z.expansion w_Z) hasSum_zero)
  -- Use N = k + 1
  use k + 1
  intro h_contra
  -- Define tail span
  let tail_span : Submodule 𝕜 E := Submodule.span 𝕜 (Set.range (fun n => b.toFun (n + (k + 1))))
  have h_tail_in_Y : tail_span ≤ Y := by
    apply Submodule.span_mono; intro x hx; obtain ⟨n, rfl⟩ := hx; exact ⟨n + (k + 1), rfl⟩
  -- Use helper lemma for coord vanishing on tail
  have h_vanish_on_tail : ∀ v (hv : v ∈ tail_span),
      basis_Z.coord k ⟨v, Y.le_topologicalClosure (h_tail_in_Y hv)⟩ = 0 :=
    coord_vanish_on_tail_span basis_Z b.toFun h_basis_coe k (k + 1)
      (Nat.lt_succ_self k) tail_span rfl h_tail_in_Y
  -- By closure_minimal: {v : Z | coord k v = 0} is closed and contains the tail span
  have h_coord_w_zero : basis_Z.coord k w_Z = 0 :=
    closure_minimal (fun (v : Z) (hv : v.val ∈ tail_span) => h_vanish_on_tail v.val hv)
      (isClosed_eq (basis_Z.coord k).continuous continuous_const)
      (by rw [closure_subtype]; refine closure_mono (fun x hx => ?_) h_contra
          exact ⟨⟨x, Y.le_topologicalClosure (h_tail_in_Y hx)⟩, hx, rfl⟩)
  -- Contradiction
  exact hk_ne h_coord_w_zero

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

instance WeakSpace.instT2Space (𝕜 : Type*) [RCLike 𝕜] (X : Type*) [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] : T2Space (WeakSpace 𝕜 X) :=
  (NormedSpace.inclusionInDoubleDual_homeomorph_weak 𝕜 X).isEmbedding.t2Space

/-- Construct a functional that separates a basic sequence tail from w'.
    Given J : X →L[𝕜] E with closed range, w' ∉ range J, and a sequence e where
    each e n = J x - w' for some x, there exists f with f(e n) = 1 and f(w') = -1.
    Extracted to reduce elaboration overhead. -/
private lemma separation_functional_for_translated_sequence
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    (J : X →L[𝕜] E) (hJ_closed : IsClosed (range J))
    (w' : E) (hw'_not_in_range : w' ∉ range J)
    (e : ℕ → E) (he_form : ∀ n, ∃ x, e n = J x - w') :
    ∃ f : StrongDual 𝕜 E, (∀ n, f (e n) = 1) ∧ f w' = -1 := by
  let M := LinearMap.range (J : X →L[𝕜] E).toLinearMap
  have hM_eq : (M : Set E) = range J := LinearMap.coe_range _
  have hw'_not_in_M : w' ∉ (M : Set E) := hM_eq ▸ hw'_not_in_range
  obtain ⟨f, hf_w', hf_vanish⟩ :=
    exists_functional_neg_one_and_vanishes_on_closed_submodule
      M (hM_eq ▸ hJ_closed) w' hw'_not_in_M
  exact ⟨f, fun n => by
    obtain ⟨x, hx⟩ := he_form n
    rw [hx, map_sub, hf_vanish (J x) (hM_eq ▸ mem_range_self x), hf_w']; ring, hf_w'⟩

/-- A translated tail of a basic sequence is still basic, under suitable functional conditions.
    If b is a basic sequence, w' ∉ closure(span(tail)), and there exists f with f(b n) = 1
    and f(w') = -1, then n ↦ b(n+N) + w' is basic. Extracted to reduce elaboration overhead. -/
private lemma translated_tail_is_basic {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [CompleteSpace E] (b : BasicSequence 𝕜 E)
    (N : ℕ) (w' : E)
    (f : StrongDual 𝕜 E) (hf_e : ∀ n, f (b (n + N)) = 1) (hf_w : f w' = -1)
    (h_w_notin_span : w' ∉ closure (Submodule.span 𝕜 (Set.range (fun n => b (n + N))))) :
    IsBasicSequence 𝕜 (fun n => b (n + N) + w') := by
  have he_basic : IsBasicSequence 𝕜 (fun n => b (n + N)) := tail_basic_sequence b N
  let b_tail := he_basic.toBasicSequence
  have hb_tail_eq : ⇑b_tail = fun n => b (n + N) := he_basic.coe_toBasicSequence
  convert perturbBasicSequence b_tail b_tail.basisConstant_lt_top w' f ?_ hf_w ?_ using 1
  · funext n; exact congrArg (· + w') (congrFun hb_tail_eq n).symm
  · intro n; rw [congrFun hb_tail_eq n]; exact hf_e n
  · rw [congrArg Set.range hb_tail_eq]; exact h_w_notin_span

/-- Transfer compactness from the weak-star topology on the bidual back to the weak topology on X.
    Given a compact set K in the weak-star bidual that contains the image of S, the preimage
    in the weak topology on X is compact. Extracted to reduce context bloat. -/
lemma compactness_transfer_from_bidual
    (S : Set X) (S_bidual : Set (StrongDual 𝕜 (StrongDual 𝕜 X)))
    (hS_eq : S_bidual = NormedSpace.inclusionInDoubleDual 𝕜 X '' S)
    (K : Set (WeakDual 𝕜 (StrongDual 𝕜 X)))
    (hK_eq : K = closure (StrongDual.toWeakDual '' S_bidual))
    (h_S_bidual_bounded : Bornology.IsBounded S_bidual)
    (hK_subset : K ⊆ StrongDual.toWeakDual '' (NormedSpace.inclusionInDoubleDual 𝕜 X '' Set.univ)) :
    IsCompact (closure (toWeakSpace 𝕜 X '' S)) := by
  -- Key: inclusionInDoubleDual is a homeomorphism WeakSpace X ≃ₜ range(ι)
  let J := NormedSpace.inclusionInDoubleDual 𝕜 X
  let ι := fun x : WeakSpace 𝕜 X => StrongDual.toWeakDual (J x)
  let homeo := NormedSpace.inclusionInDoubleDual_homeomorph_weak 𝕜 X
  have hK_bounded_preimage : Bornology.IsBounded (StrongDual.toWeakDual ⁻¹' K) := by
    obtain ⟨R, hR⟩ := Metric.isBounded_iff_subset_closedBall 0 |>.mp h_S_bidual_bounded
    refine Metric.isBounded_iff_subset_closedBall 0 |>.mpr ⟨R, fun x hx => ?_⟩
    have h_sub : StrongDual.toWeakDual '' S_bidual ⊆
        WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 R := by
      rintro _ ⟨z, hz, rfl⟩
      simpa [Metric.mem_closedBall, dist_zero_right] using hR hz
    exact closure_minimal h_sub (WeakDual.isClosed_closedBall 0 R) (hK_eq ▸ hx)
  have hK_compact : IsCompact K :=
    WeakDual.isCompact_of_bounded_of_closed hK_bounded_preimage (hK_eq ▸ isClosed_closure)
  -- K ⊆ range(ι), so we can pull back via the homeomorphism
  have hK_in_range : K ⊆ Set.range ι := fun y hy => by
    obtain ⟨z, hzJ, hz⟩ := hK_subset hy
    obtain ⟨x, _, hx⟩ := hzJ
    exact ⟨x, hz ▸ hx ▸ rfl⟩
  let K_in_range : Set (Set.range ι) := Subtype.val ⁻¹' K
  have hK_in_range_compact : IsCompact K_in_range := by
    rw [IsEmbedding.subtypeVal.isCompact_iff]
    convert hK_compact using 1
    exact Set.eq_of_subset_of_subset
      (fun _ ⟨⟨_, _⟩, hK, rfl⟩ => hK) (fun y hy => ⟨⟨y, hK_in_range hy⟩, hy, rfl⟩)
  have hK_weak_compact : IsCompact (homeo.symm '' K_in_range) :=
    hK_in_range_compact.image homeo.symm.continuous
  -- closure(toWeakSpace '' S) ⊆ homeo.symm '' K_in_range
  refine hK_weak_compact.of_isClosed_subset isClosed_closure
    (closure_minimal ?_ hK_weak_compact.isClosed)
  intro z hz
  obtain ⟨x, hxS, rfl⟩ := hz
  have h_in_K : ι x ∈ K := by
    rw [hK_eq]; apply subset_closure
    exact ⟨J x, hS_eq ▸ ⟨x, hxS, rfl⟩, rfl⟩
  have h_homeo : homeo (toWeakSpace 𝕜 X x) = ⟨ι x, x, rfl⟩ := Subtype.ext rfl
  exact ⟨⟨ι x, x, rfl⟩, h_in_K, by rw [← h_homeo, Homeomorph.symm_apply_apply]⟩

set_option maxHeartbeats 250000 in
-- TODO contrapose the statement
/-- Main theorem: in a Banach space, a set S that is bounded
    and does not contain any basic sequence, has relatively weakly compact closure in the weak
    topology. -/
theorem no_basic_sequence_implies_relatively_weakly_compact [CompleteSpace X]
    {S : Set X} (_hS_ne : S.Nonempty) (h_bounded : Bornology.IsBounded S)
    (h_no_basic : ∀ (e : ℕ → X), (∀ n, e n ∈ S) → ¬ IsBasicSequence 𝕜 e) :
    IsCompact (closure (toWeakSpace 𝕜 X '' S)) :=
    let Xbidual : Type _ := StrongDual 𝕜 (StrongDual 𝕜 X)
    -- Cache expensive instances for dual and bidual to avoid repeated synthesis
    letI : NormedAddCommGroup (StrongDual 𝕜 X) := inferInstance
    letI : NormedSpace 𝕜 (StrongDual 𝕜 X) := inferInstance
    letI : NormedAddCommGroup (StrongDual 𝕜 (StrongDual 𝕜 X)) := inferInstance
    letI : NormedSpace 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 X)) := inferInstance
    letI : CompleteSpace (StrongDual 𝕜 (StrongDual 𝕜 X)) := inferInstance
    let J : X →L[𝕜] Xbidual := NormedSpace.inclusionInDoubleDual 𝕜 X
    have hJ_iso : ∀ y, ‖J y‖ = ‖y‖ := fun y =>
      (NormedSpace.inclusionInDoubleDualLi (𝕜 := 𝕜) (E := X)).norm_map y
    let S_bidual : Set Xbidual := J '' S
    have h_S_bidual_bounded : Bornology.IsBounded S_bidual := by
      obtain ⟨R, hR⟩ := Metric.isBounded_iff_subset_closedBall 0 |>.mp h_bounded
      exact Metric.isBounded_iff_subset_closedBall 0 |>.mpr ⟨R, fun z hz => by
        obtain ⟨x, hxS, rfl⟩ := hz
        rw [mem_closedBall_zero_iff, hJ_iso]
        exact mem_closedBall_zero_iff.mp (hR hxS)⟩
    let K : Set (WeakDual 𝕜 (StrongDual 𝕜 X)) := closure (StrongDual.toWeakDual '' S_bidual)
    have hK_subset :  K ⊆ StrongDual.toWeakDual '' (J '' (Set.univ)) := by
      by_contra h_not_subset
      rw [Set.subset_def] at h_not_subset
      push_neg at h_not_subset
      obtain ⟨w, hwK, hw_not_JX⟩ := h_not_subset
      -- Define S' in StrongDual (Xbidual) space as translation of S_bidual by -w'
      let w' : Xbidual := WeakDual.toStrongDual w
      let S' : Set Xbidual := (fun y => y - w') '' S_bidual
      have h_weak_starS' : (0 : WeakDual 𝕜 (StrongDual 𝕜 X)) ∈
          closure (StrongDual.toWeakDual '' S') := by
        let Tw : WeakDual 𝕜 (StrongDual 𝕜 X) ≃ₜ _ := Homeomorph.addRight (-w)
        rw [show StrongDual.toWeakDual '' S' = Tw '' (StrongDual.toWeakDual '' S_bidual) from by
          simp only [S', image_image]
          exact image_congr fun x _ => by simp [Tw, sub_eq_add_neg, w']]
        rw [← Tw.image_closure,
          show (0 : WeakDual 𝕜 _) = Tw w from by
            simp only [Tw, Homeomorph.coe_addRight, add_neg_cancel]]
        exact mem_image_of_mem _ hwK
      -- The range of J is closed (isometry from complete space)
      have hJ_closed : IsClosed (range J) := by
        have : IsClosedEmbedding (NormedSpace.inclusionInDoubleDualLi (𝕜 := 𝕜) (E := X)) := by
          let li := NormedSpace.inclusionInDoubleDualLi (𝕜 := 𝕜) (E := X)
          have : @Isometry X (StrongDual 𝕜 (StrongDual 𝕜 X))
              EMetricSpace.toPseudoEMetricSpace EMetricSpace.toPseudoEMetricSpace li :=
            fun x y => li.isometry.edist_eq x y
          exact this.isClosedEmbedding
        exact this.isClosed_range
      have h_normS' : (0 : Xbidual) ∉ closure S' := by
        intro h0
        -- 0 ∈ closure (S_bidual - w') implies w' ∈ closure S_bidual ⊆ range J
        have hw_in_closure : w' ∈ closure (S_bidual : Set Xbidual) := by
          let T : Xbidual ≃ₜ Xbidual := Homeomorph.addRight (-w')
          rw [show S' = T '' S_bidual from by
            ext x; simp [S', T, sub_eq_add_neg], ← T.image_closure] at h0
          obtain ⟨y, hy_mem, hy_eq⟩ := h0
          have hTw : T w' = (0 : Xbidual) := by
            simp only [T, Homeomorph.coe_addRight]; exact add_neg_cancel w'
          rwa [← T.injective (hy_eq.trans hTw.symm)]
        have hw_in_JX : w' ∈ range J :=
          closure_minimal (image_subset_range J S) hJ_closed hw_in_closure
        exact hw_not_JX <| by
          rw [image_univ]; obtain ⟨x, hx⟩ := hw_in_JX
          exact ⟨J x, mem_range_self x, by
            simp only [w'] at hx; exact hx ▸ rfl⟩
      have h_basicS' : ∃ e : ℕ → Xbidual, (∀ n, e n ∈ S') ∧ IsBasicSequence 𝕜 e := by
        obtain ⟨b, hb_mem, -⟩ := basic_sequence_selection_dual h_weak_starS' h_normS' zero_lt_one
        exact ⟨⇑b, hb_mem, ⟨b, rfl⟩⟩
      obtain ⟨e, he_S', he_basic⟩ := h_basicS'
      rcases he_basic with ⟨b, rfl⟩
      have h_w_span : ∃ N : ℕ, w' ∉ closure (Submodule.span 𝕜 (Set.range (fun n => b (n+N)))) := by
        have hw_ne : w' ≠ 0 := fun h => hw_not_JX <| by
          rw [show w = 0 from
            WeakDual.toStrongDual.injective (h.trans (map_zero _).symm), image_univ]
          exact ⟨J 0, mem_range_self 0, by simp only [map_zero]⟩
        by_contra h_contra; push_neg at h_contra
        exact (nonzero_not_in_all_tail_closures b b.basisConstant_lt_top w'
          (by simpa using h_contra 0) hw_ne).elim (fun N hN => hN (h_contra N))
      obtain ⟨N, h_w_notin_span⟩ := h_w_span
      let e : ℕ → Xbidual := fun n => b (n + N)
      have h_sep : ∃ f : StrongDual 𝕜 Xbidual, (∀ n, f (e n) = 1) ∧ f w' = -1 := by
        have hw'_not_in_range : w' ∉ range J := fun ⟨x, hx⟩ => by
          apply hw_not_JX; rw [image_univ]
          exact ⟨J x, mem_range_self x, by simp [w', hx]⟩
        exact separation_functional_for_translated_sequence J hJ_closed w' hw'_not_in_range e
          (fun n => by obtain ⟨t, ⟨x, _, rfl⟩, ht_eq⟩ := he_S' (n + N); exact ⟨x, ht_eq.symm⟩)
      obtain ⟨f, hf_e⟩ := h_sep
      -- Define the correct sequence that's in S_bidual
      let s : ℕ → Xbidual := fun n => e n + w'
      have hs_in_S_bidual : ∀ n, s n ∈ S_bidual := fun n => by
        obtain ⟨t, ht_mem, ht_eq⟩ := he_S' (n + N)
        simp only at ht_eq; rwa [show s n = t from by dsimp [s, e]; rw [← ht_eq, sub_add_cancel]]
      -- s = e + w' is basic by the extracted helper lemma
      have h_basicS : IsBasicSequence 𝕜 s :=
        translated_tail_is_basic (E := Xbidual) b N w' f hf_e.1 hf_e.2 h_w_notin_span
      -- Pull back the basic sequence from the bidual to X using the pullback lemma
      obtain ⟨x, hx_S, hx_basic⟩ := h_basicS.pullback J hJ_iso hs_in_S_bidual
      exact h_no_basic x hx_S hx_basic
    -- Transfer compactness back to X via the extracted helper lemma
    compactness_transfer_from_bidual S S_bidual rfl K rfl h_S_bidual_bounded hK_subset

end BasicSequence
