/-
Copyright (c) 2026 Michał Świętek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michał Świętek
-/
module

public import Mathlib.Analysis.Normed.Module.SchauderBasis.BasicSequence
public import Mathlib.Data.ENNReal.Real


/-!
# Grünblum Condition and Basic Sequence Construction

This file defines the Grünblum condition for sequences in Banach spaces and provides
the fundamental construction of basic sequences from the Grünblum condition.

## Main Definitions

* `SatisfiesGrunblumCondition`: A sequence satisfies the Grünblum condition with constant `K`.
* `grunblumConstant`: The Grünblum constant for a basic sequence.
* `GeneralSatisfiesGrunblumCondition`: The generalized Grünblum condition for arbitrary index sets.

## Main Results

* `satisfiesGrunblum`: A basic sequence with finite projection bound satisfies the Grünblum condition.
* `grunblum_bound_of_basic`: The explicit Grünblum bound using `grunblumConstant`.
* `linearIndependent_of_grunblum`: Linear independence from the Grünblum condition.
* `isBasicSequence_of_grunblum_with_bound`: Construction of a basic sequence from the Grünblum
  condition, with an explicit bound on the basis constant.
* `isBasicSequence_of_grunblum`: Convenience wrapper as a predicate.
* `tail_basic_sequence`: The tail of a basic sequence is also a basic sequence.
-/

@[expose] public section

noncomputable section

open Submodule Set WeakDual Metric Filter Topology

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

namespace BasicSequences




/-- A basic sequence with finite projection bound satisfies the Grünblum condition. -/
theorem satisfiesGrunblum (bs : BasicSequence 𝕜 X)
    (h_bound : bs.basis.enormProjBound < ⊤) :
    SatisfiesGrunblumCondition 𝕜 bs (grunblumConstant bs) := by
  -- Use K = max(1, enormProjBound.toReal) to ensure K ≥ 1
  let K := max 1 bs.basis.enormProjBound.toReal
  have hK_ge : 1 ≤ K := le_max_left 1 _
  have hK_lt_top : bs.basis.enormProjBound ≠ ⊤ := h_bound.ne
  refine ⟨hK_ge, fun n m a hmn => ?_⟩
  -- The key idea: the partial sum up to m is the projection P_m applied to the full sum
  -- and ‖P_m‖ ≤ basisConstant ≤ K
  let S := Submodule.span 𝕜 (Set.range bs.toFun)
  have hsum_mem (k : ℕ) : ∑ i ∈ Finset.range k, a i • bs i ∈ S :=
    Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
  -- The projection bound: ‖P_m‖ ≤ basisConstant ≤ K
  have h_proj_bound : ‖bs.basis.proj m‖ ≤ K := by
    have h := bs.basis.norm_proj_le_enormProjBound m
    rw [← ENNReal.toReal_le_toReal ENNReal.coe_ne_top hK_lt_top] at h
    simp only [ENNReal.coe_toReal, coe_nnnorm] at h
    exact h.trans (le_max_right _ _)
  -- The rest requires showing P_m(∑_{i< n} a_i • e_i) = ∑_{i< m} a_i • e_i
  -- This is a standard property of Schauder basis projections
  -- First, lift the sums to the subspace S
  let sum_n : S := ⟨∑ i ∈ Finset.range n, a i • bs i, hsum_mem n⟩
  let sum_m : S := ⟨∑ i ∈ Finset.range m, a i • bs i, hsum_mem m⟩
  -- Show that basis i = codRestrict bs.toFun ... i, so (basis i : X) = bs i
  have h_basis_eq : ∀ i, (bs.basis i : X) = bs i := fun i ↦ by
    have h := congrFun bs.basis_eq i
    simp only at h
    rw [h]
    rfl
  -- Express sum_n as a sum of basis elements in S
  have h_sum_n_basis : sum_n = ∑ j ∈ Finset.range n, a j • bs.basis j := by
    apply Subtype.ext
    simp only [sum_n, Submodule.coe_sum, Submodule.coe_smul, h_basis_eq]
  -- Key: proj m (sum_n) = sum_m
  have h_proj_eq : bs.basis.proj m sum_n = sum_m := by
    -- Use proj_apply: proj m x = ∑ i ∈ range m, coord i x • basis i
    rw [SchauderBasis.proj_apply]
    -- For sum_n = ∑_{i< n} a_i • basis_i, coord j (sum_n) = a_j for j < n
    -- Since m ≤ n, for all j < m we have j < n, so coord j (sum_n) = a_j
    ext
    simp only [Submodule.coe_sum, Submodule.coe_smul, h_basis_eq]
    apply Finset.sum_congr rfl
    intro i hi
    have hi_lt_n : i < n := Nat.lt_of_lt_of_le (Finset.mem_range.mp hi) hmn
    -- Show: coord i (sum_n) = a_i
    have h_coord : bs.basis.coord i sum_n = a i := by
      rw [h_sum_n_basis]
      rw [map_sum]
      -- coord i (∑_j a_j • basis_j) = ∑_j a_j • coord i (basis_j) = ∑_j a_j • δ_{ij} = a_i
      simp only [map_smul]
      rw [Finset.sum_eq_single_of_mem i (Finset.mem_range.mpr hi_lt_n)]
      · -- When j = i: a_i • coord i (basis i) = a_i • 1 = a_i
        have h_ortho : bs.basis.coord i (bs.basis i) = 1 := by
          simp only [bs.basis.ortho, Pi.single_eq_same]
        rw [h_ortho, smul_eq_mul, mul_one]
      · -- When j ≠ i: a_j • coord i (basis j) = a_j • 0 = 0
        intro j _ hji
        have h_ortho : bs.basis.coord i (bs.basis j) = 0 := by
          simp only [bs.basis.ortho, Pi.single_apply, if_neg (Ne.symm hji)]
        rw [h_ortho, smul_zero]
    rw [h_coord]
  -- Now use the operator norm bound
  calc ‖∑ i ∈ Finset.range m, a i • bs i‖
    _ = ‖(sum_m : X)‖ := rfl
    _ = ‖sum_m‖ := (norm_coe sum_m).symm
    _ = ‖bs.basis.proj m sum_n‖ := by rw [h_proj_eq]
    _ ≤ ‖bs.basis.proj m‖ * ‖sum_n‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ K * ‖sum_n‖ := by apply mul_le_mul_of_nonneg_right h_proj_bound (norm_nonneg _)
    _ = K * ‖(sum_n : X)‖ := by rw [norm_coe]
    _ = K * ‖∑ i ∈ Finset.range n, a i • bs i‖ := rfl

/-- The explicit Grünblum bound using `grunblumConstant`. -/
theorem grunblum_bound_of_basic (bs : BasicSequence 𝕜 X)
    (h_bound : bs.basis.enormProjBound < ⊤) (n m : ℕ) (a : ℕ → 𝕜) (hmn : m ≤ n) :
    ‖∑ i ∈ Finset.range m, a i • bs i‖ ≤
    grunblumConstant bs * ‖∑ i ∈ Finset.range n, a i • bs i‖ := by
  -- Directly prove the bound using the same technique as satisfiesGrunblum
  let K := grunblumConstant bs
  have hK_lt_top : bs.basis.enormProjBound ≠ ⊤ := h_bound.ne
  let S := Submodule.span 𝕜 (Set.range bs.toFun)
  have hsum_mem (k : ℕ) : ∑ i ∈ Finset.range k, a i • bs i ∈ S :=
    Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
  have h_proj_bound : ‖bs.basis.proj m‖ ≤ K := by
    have h := bs.basis.norm_proj_le_enormProjBound m
    rw [← ENNReal.toReal_le_toReal ENNReal.coe_ne_top hK_lt_top] at h
    simp only [ENNReal.coe_toReal, coe_nnnorm] at h
    exact h.trans (le_max_right _ _)
  let sum_n : S := ⟨∑ i ∈ Finset.range n, a i • bs i, hsum_mem n⟩
  let sum_m : S := ⟨∑ i ∈ Finset.range m, a i • bs i, hsum_mem m⟩
  have h_basis_eq : ∀ i, (bs.basis i : X) = bs i := fun i ↦ by
    have h := congrFun bs.basis_eq i
    simp only at h
    rw [h]
    rfl
  have h_sum_n_basis : sum_n = ∑ j ∈ Finset.range n, a j • bs.basis j := by
    apply Subtype.ext
    simp only [sum_n, Submodule.coe_sum, Submodule.coe_smul, h_basis_eq]
  have h_proj_eq : bs.basis.proj m sum_n = sum_m := by
    rw [SchauderBasis.proj_apply]
    ext
    simp only [Submodule.coe_sum, Submodule.coe_smul, h_basis_eq]
    apply Finset.sum_congr rfl
    intro i hi
    have hi_lt_n : i < n := Nat.lt_of_lt_of_le (Finset.mem_range.mp hi) hmn
    have h_coord : bs.basis.coord i sum_n = a i := by
      rw [h_sum_n_basis]
      rw [map_sum]
      simp only [map_smul]
      rw [Finset.sum_eq_single_of_mem i (Finset.mem_range.mpr hi_lt_n)]
      · have h_ortho : bs.basis.coord i (bs.basis i) = 1 := by
          simp only [bs.basis.ortho, Pi.single_eq_same]
        rw [h_ortho, smul_eq_mul, mul_one]
      · intro j _ hji
        have h_ortho : bs.basis.coord i (bs.basis j) = 0 := by
          simp only [bs.basis.ortho, Pi.single_apply, if_neg (Ne.symm hji)]
        rw [h_ortho, smul_zero]
    rw [h_coord]
  calc ‖∑ i ∈ Finset.range m, a i • bs i‖
    _ = ‖(sum_m : X)‖ := rfl
    _ = ‖sum_m‖ := (norm_coe sum_m).symm
    _ = ‖bs.basis.proj m sum_n‖ := by rw [h_proj_eq]
    _ ≤ ‖bs.basis.proj m‖ * ‖sum_n‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ K * ‖sum_n‖ := by apply mul_le_mul_of_nonneg_right h_proj_bound (norm_nonneg _)
    _ = K * ‖(sum_n : X)‖ := by rw [norm_coe]
    _ = K * ‖∑ i ∈ Finset.range n, a i • bs i‖ := rfl

lemma linearIndependent_of_grunblum {e : ℕ → X} {K : ℝ}
    (h_grunblum : SatisfiesGrunblumCondition 𝕜 e K)
    (h_nz : ∀ n, e n ≠ 0) : LinearIndependent 𝕜 e := by
  obtain ⟨-, hK⟩ := h_grunblum
  rw [linearIndependent_iff']
  intros s g hg_sum i hi_s
  -- 1. Define coefficients 'c' globally and pick a sufficiently large N
  let c := fun j ↦ if j ∈ s then g j else 0
  let N := s.sup id + 1
  have h_bound : ∀ j ∈ s, j < N := fun j hj ↦ Nat.lt_succ_of_le (Finset.le_sup hj (f := id))
  -- 2. Show the sum over 'range N' is zero (because it matches 's' where c=g, and is 0 elsewhere)
  have h_total : ∑ j ∈ Finset.range N, c j • e j = 0 := by
    rw [← Finset.sum_subset (fun j hj ↦ Finset.mem_range.2 (h_bound j hj))
      (fun x _ hj ↦ by simp [c, hj])]
    convert hg_sum using 1
    exact Finset.sum_congr rfl (fun j hj ↦ by simp [c, hj])
  -- 3. Use Grünblum to show ALL partial sums up to N are zero
  have h_partial : ∀ m ≤ N, ∑ j ∈ Finset.range m, c j • e j = 0 := fun m hm ↦
    norm_le_zero_iff.1 <| by simpa [h_total] using hK N m c hm
  -- 4. The term at 'i' is the difference of two zero partial sums (S_{i+1} - S_i)
  have h_term : c i • e i = 0 := by
    rw [← Finset.sum_range_succ_sub_sum (fun j ↦ c j • e j),
        h_partial (i + 1) (h_bound i hi_s),
        h_partial i (le_of_lt (h_bound i hi_s)), sub_zero]
  -- 5. Conclude g i = 0
  simpa [c, hi_s, h_nz i] using h_term

/-- A version of `isBasicSequence_of_grunblum` that also provides an explicit bound
    on the basis constant. If a sequence satisfies the Grünblum condition with constant K,
    the resulting basic sequence has basis constant at most K. -/
theorem isBasicSequence_of_grunblum_with_bound [CompleteSpace X] {e : ℕ → X} {K : ℝ}
    (hK_ge : 1 ≤ K)
    (hK_bound : ∀ (n m : ℕ) (a : ℕ → 𝕜), m ≤ n →
      ‖∑ i ∈ Finset.range m, a i • e i‖ ≤ K * ‖∑ i ∈ Finset.range n, a i • e i‖)
    (h_nz : ∀ n, e n ≠ 0) :
    ∃ (b : BasicSequence 𝕜 X), ⇑b = e ∧ b.basis.enormProjBound < ⊤ ∧
      basicSequenceConstant b ≤ K := by
  have h_grunblum : SatisfiesGrunblumCondition 𝕜 e K := ⟨hK_ge, hK_bound⟩
  have h_indep := linearIndependent_of_grunblum h_grunblum h_nz
  let S := Submodule.span 𝕜 (Set.range e)
  let b_S := Module.Basis.span h_indep
  let e_Y : ℕ → S := b_S
  have hbS : ∀ n, (b_S n : X) = e n := Module.Basis.span_apply h_indep
  let P_span (k : ℕ) : S →ₗ[𝕜] S := b_S.constr 𝕜 (fun i => if i < k then b_S i else 0)
  have h_P_span_apply (k : ℕ) (x : S) :
      P_span k x = ∑ i ∈ Finset.range k, b_S.repr x i • b_S i := by
    rw [Module.Basis.constr_apply, Finsupp.sum]
    refine Finset.sum_congr_of_eq_on_inter ?_ ?_ ?_ <;> intro i h1 h2
    · rw [if_neg (by simpa using h2), smul_zero]
    · rw [Finsupp.notMem_support_iff.mp h2, zero_smul]
    · rw [if_pos (by simpa using h2)]
  have h_P_span_bound (k : ℕ) (x : S) : ‖P_span k x‖ ≤ K * ‖x‖ := by
    let a := b_S.repr x
    let N := max k (a.support.sup id + 1)
    have hk_le_N : k ≤ N := le_max_left _ _
    have hx : (x : X) = ∑ i ∈ Finset.range N, (b_S.repr x) i • b_S i := by
      nth_rw 1 [← b_S.linearCombination_repr x]
      rw [Finsupp.linearCombination_apply]
      rw [← h_P_span_apply N x]
      dsimp only [P_span]
      rw [b_S.constr_apply, Finsupp.sum_congr]
      intro i hi
      rw [if_pos]
      calc i
        _ ≤ (b_S.repr x).support.sup id   := Finset.le_sup hi (f := id)
        _ < (b_S.repr x).support.sup id + 1 := Nat.lt_succ_self _
        _ ≤ N                    := le_max_right _ _
    rw [← norm_coe, ← norm_coe, hx, h_P_span_apply]
    simp_rw [Submodule.coe_sum, Submodule.coe_smul, hbS]
    exact hK_bound N k (b_S.repr x) hk_le_N
  let P (k : ℕ) : S →L[𝕜] S := LinearMap.mkContinuous (P_span k) K (h_P_span_bound k)
  have h0 : P 0 = 0 := by
    have : P_span 0 = 0 := by
      ext; simp_rw [h_P_span_apply, Finset.range_zero, Finset.sum_empty]; rfl
    ext _
    dsimp only [P]
    simp only [LinearMap.mkContinuous_apply, ContinuousLinearMap.zero_apply, ZeroMemClass.coe_zero,
      ZeroMemClass.coe_eq_zero]
    rw [h_P_span_apply]
    simp only [Finset.range_zero, Finset.sum_empty]
  have hdim (n : ℕ) : Module.finrank 𝕜 (LinearMap.range (P n).toLinearMap) = n := by
    let W := Submodule.span 𝕜 (Set.range (fun i : Fin n ↦ b_S i))
    have h_range : LinearMap.range (P n).toLinearMap = W := by
      apply le_antisymm
      · rintro _ ⟨x, rfl⟩
        simp only [ContinuousLinearMap.coe_coe, P, LinearMap.mkContinuous_apply]
        rw [h_P_span_apply]
        refine Submodule.sum_mem _ (fun i hi ↦ ?_)
        apply Submodule.smul_mem
        apply Submodule.subset_span
        exact ⟨⟨i, Finset.mem_range.mp hi⟩, rfl⟩
      · rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        use b_S i
        simp only [ContinuousLinearMap.coe_coe]
        dsimp only [P]
        simp only [LinearMap.mkContinuous_apply]
        dsimp only [P_span]
        rw [b_S.constr_basis]
        rw [if_pos i.isLt]
    rw [h_range, finrank_span_eq_card]
    · exact Fintype.card_fin n
    · exact b_S.linearIndependent.comp (fun i : Fin n => i.val) Fin.val_injective
  have hcomp (n m : ℕ) (y : S) : P n (P m y) = P (min n m) y := by
    simp only [P, LinearMap.mkContinuous_apply]
    conv_lhs => rw [h_P_span_apply m y, h_P_span_apply]
    rw [h_P_span_apply]
    simp only [map_sum, map_smul, Module.Basis.repr_self]
    simp_rw [Finsupp.finset_sum_apply, Finsupp.smul_apply, Finsupp.single_apply,
             smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_range]
    simp_rw [ite_smul, zero_smul]
    rw [← Finset.sum_filter]
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, lt_min_iff]
  have h_bound_P : ∀ n, ‖P n‖ ≤ K := fun n ↦ by
    refine ContinuousLinearMap.opNorm_le_bound _ (zero_le_one.trans hK_ge) (fun x ↦ ?_)
    exact h_P_span_bound n x
  have hlim (x : S) : Filter.Tendsto (fun n ↦ P n x) Filter.atTop (nhds x) := by
    let N := (b_S.repr x).support.sup id + 1
    rw [Metric.tendsto_atTop]
    intro ε hε
    use N
    intro n hn
    dsimp only [P]
    simp only [LinearMap.mkContinuous_apply]
    rw [dist_eq_norm]
    have h_eq : P_span n x = x := by
      rw [h_P_span_apply]
      conv_rhs => rw [← b_S.linearCombination_repr x, Finsupp.linearCombination_apply]
      symm
      apply Finset.sum_subset
      · intro i hi
        apply Finset.mem_range.mpr
        calc i ≤ (b_S.repr x).support.sup id := Finset.le_sup hi (f := id)
          _ < N := Nat.lt_succ_self _
          _ ≤ n := hn
      · intro i _ hi
        simp [Finsupp.notMem_support_iff.mp hi]
    rw [h_eq, sub_self, norm_zero]
    exact hε
  have hbS_eq : ∀ n, b_S n = ⟨e n, subset_span (mem_range_self n)⟩ := fun n ↦
    Subtype.ext (hbS n)
  have he_in_range : ∀ n, ⟨e n, subset_span (mem_range_self n)⟩ ∈
      LinearMap.range (SchauderBasis.succSub P n).toLinearMap := fun n ↦ by
    rw [← hbS_eq, LinearMap.mem_range]
    use b_S n
    simp only [SchauderBasis.succSub, ContinuousLinearMap.coe_sub, P,
               LinearMap.mkContinuous_coe, LinearMap.sub_apply]
    rw [h_P_span_apply, h_P_span_apply, Finset.sum_range_succ, add_sub_cancel_left]
    simp only [Module.Basis.repr_self, Finsupp.single_eq_same, one_smul]
  have he_ne : ∀ n, (⟨e n, subset_span (mem_range_self n)⟩ : S) ≠ 0 := fun n h ↦
    h_nz n (by simpa using congrArg Subtype.val h)
  let D : SchauderBasis.ProjectionData 𝕜 S := {
    P := P
    e := e_Y
    projZero := h0
    finrankRange := hdim
    hcomp := hcomp
    hlim := hlim
    heInRange := fun n ↦ by dsimp only [e_Y]; rw [hbS_eq]; exact he_in_range n
    heNe := fun n ↦ by dsimp only [e_Y]; rw [hbS_eq]; exact he_ne n
  }
  let b_basis := D.basis
  let seq : BasicSequence 𝕜 X := {
    toFun := e
    basis := b_basis
    basis_eq := by
      ext n
      rw [SchauderBasis.ProjectionData.basis_coe D]
      dsimp only [val_codRestrict_apply]
      exact hbS n
  }
  have h_lt_top : b_basis.enormProjBound < ⊤ :=
    b_basis.enormProjBound_lt_top_of_bound (fun n ↦ by
      change ‖D.basis.proj n‖ ≤ K
      rw [SchauderBasis.ProjectionData.basis_proj D]; exact h_bound_P n)
  refine ⟨seq, rfl, h_lt_top, ?_⟩
  dsimp only [basicSequenceConstant]
  have h_K_nonneg : 0 ≤ K := by linarith
  -- enormProjBound ≤ K.toNNReal (as ENNReal)
  have h_bound_ennreal : b_basis.enormProjBound ≤ ENNReal.ofReal K := by
    simp only [SchauderBasis.enormProjBound]
    apply iSup_le; intro n
    rw [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_le_ofReal_iff h_K_nonneg]
    simp only [coe_nnnorm]
    rw [SchauderBasis.ProjectionData.basis_proj D]
    exact h_bound_P n
  calc b_basis.enormProjBound.toReal
    _ ≤ (ENNReal.ofReal K).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top h_bound_ennreal
    _ = K := ENNReal.toReal_ofReal h_K_nonneg

/-- Convenience wrapper: the Grünblum criterion as a predicate. -/
theorem isBasicSequence_of_grunblum [CompleteSpace X] {e : ℕ → X} {K : ℝ}
    (h : SatisfiesGrunblumCondition 𝕜 e K) (h_nz : ∀ n, e n ≠ 0) :
    IsBasicSequence 𝕜 e := by
  obtain ⟨b, hb_eq, hb_bound, _⟩ := isBasicSequence_of_grunblum_with_bound h.1 h.2 h_nz
  exact ⟨b, hb_eq, hb_bound⟩

/-- The tail of a basic sequence (starting from index N) is also a basic sequence. -/
theorem tail_basic_sequence [CompleteSpace X] (bs : BasicSequence 𝕜 X)
    (h_bound : bs.basis.enormProjBound < ⊤) (N : ℕ) :
    IsBasicSequence 𝕜 (fun n => bs (n + N)) := by
  obtain ⟨hK_ge, hK_bound⟩ := satisfiesGrunblum bs h_bound
  let K := grunblumConstant bs
  have h_nz : ∀ n, bs (n + N) ≠ 0 := by
    intro n h_zero
    have hb_indep := bs.basis.linearIndependent
    have hb_nz := hb_indep.ne_zero (n + N)
    have h_eq : (bs.basis (n + N) : X) = bs (n + N) := by
      have := congrFun bs.basis_eq (n + N)
      exact congrArg Subtype.val this
    rw [h_zero] at h_eq
    exact hb_nz (Subtype.val_injective h_eq)
  refine isBasicSequence_of_grunblum ⟨hK_ge, ?_⟩ h_nz
  intro n m a hnm
  let a' : ℕ → 𝕜 := fun i => if N ≤ i then a (i - N) else 0
  have h_sum_eq (k : ℕ) : ∑ i ∈ Finset.range k, a i • bs (i + N) =
      ∑ i ∈ Finset.range (k + N), a' i • bs i := by
    have h_split : ∑ i ∈ Finset.range (k + N), a' i • bs i =
        ∑ i ∈ Finset.range N, a' i • bs i +
        ∑ i ∈ Finset.Ico N (k + N), a' i • bs i := by
      rw [Finset.sum_range_add_sum_Ico _ (Nat.le_add_left N k)]
    have h_zero : ∑ i ∈ Finset.range N, a' i • bs i = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hi_lt : i < N := Finset.mem_range.mp hi
      simp only [a', if_neg (not_le.mpr hi_lt), zero_smul]
    have h_Ico : ∑ i ∈ Finset.Ico N (k + N), a' i • bs i =
        ∑ i ∈ Finset.range k, a i • bs (i + N) := by
      conv_lhs =>
        rw [show Finset.Ico N (k + N) = (Finset.range k).map
            ⟨(· + N), fun _ _ h => Nat.add_right_cancel h⟩ from by
          ext j
          simp only [Finset.mem_map, Finset.mem_range, Finset.mem_Ico,
            Function.Embedding.coeFn_mk]
          constructor
          · intro ⟨hN, hk⟩; exact ⟨j - N, by omega, by omega⟩
          · rintro ⟨i, hi, rfl⟩; omega]
        rw [Finset.sum_map]
      apply Finset.sum_congr rfl
      intro i _
      simp only [Function.Embedding.coeFn_mk, a', if_pos (Nat.le_add_left N i)]
      simp only [Nat.add_sub_cancel_right]
    rw [h_split, h_zero, zero_add, h_Ico]
  rw [h_sum_eq m, h_sum_eq n]
  exact hK_bound (n + N) (m + N) a' (by omega)

end BasicSequences
