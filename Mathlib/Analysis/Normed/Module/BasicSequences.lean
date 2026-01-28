/-
Copyright (c) 2026 Michał Świętek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michał Świętek
-/
module

public import Mathlib.Analysis.Normed.Module.Bases
public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Data.ENNReal.Real
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.Neighborhoods
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.UniformSpace.UniformEmbedding

/-!
# Basic Sequences in Banach Spaces
-/

noncomputable section

open Submodule Set WeakDual Metric

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/--
A sequence `e` is a **Basic Sequence** if it forms a Schauder Basis for its linear span.
Usually, we consider the closed span but here we use the (algebraic) span for simplicity and
require
-/
def IsBasicSequence (𝕜 : Type*) {X : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] (e : ℕ → X) : Prop :=
  let Y := span 𝕜 (range e)
  let e_Y : ℕ → Y := fun n ↦ ⟨e n, subset_span (mem_range_self n)⟩
  ∃ b : SchauderBasis 𝕜 e_Y, b.basisConstant < ⊤

namespace BasicSequences

variable {e : ℕ → X}

/-- Every Schauder Basis of the whole space `X` is a basic sequence. -/
theorem isBasicSequence_self (b : SchauderBasis 𝕜 e) : IsBasicSequence 𝕜 e := sorry

/-- The **Basis Constant** of a basic sequence. -/
noncomputable def basicSequenceConstant (he : IsBasicSequence 𝕜 e) : ℝ :=
  (Classical.choice he).basisConstant


/-- A sequence satisfies the **Grünblum Condition** if the norms of the projections
onto the span of its first `n` elements are uniformly bounded. -/
def SatisfiesGrunblumCondition (𝕜 : Type*) {X : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] (e : ℕ → X) : Prop :=
  ∃ K, 1 ≤ K ∧ ∀ (n m : ℕ) (a : ℕ → 𝕜), m ≤ n →
    ‖∑ i ∈ Finset.range m, a i • e i‖ ≤ K * ‖∑ i ∈ Finset.range n, a i • e i‖

/-- A basic sequence implies the Grünblum inequality holds for its basis constant. -/
theorem grunblum_of_basic (he : IsBasicSequence 𝕜 e) : SatisfiesGrunblumCondition 𝕜 e := by
    sorry

lemma linearIndependent_of_grunblum (h_grunblum : SatisfiesGrunblumCondition 𝕜 e)
    (h_nz : ∀ n, e n ≠ 0) : LinearIndependent 𝕜 e := by
  rcases h_grunblum with ⟨K, -, hK⟩
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


/--
**The Grünblum Criterion**:
If a sequence satisfies the Grünblum condition (bounded projections on the span),
and the elements are non-zero, then it is a Basic Sequence.
-/
theorem isBasicSequence_of_grunblum [CompleteSpace X]
    (h_grunblum : SatisfiesGrunblumCondition 𝕜 e)
    (h_nz : ∀ n, e n ≠ 0) : IsBasicSequence 𝕜 e := by
  have h_indep := linearIndependent_of_grunblum h_grunblum h_nz
  rcases h_grunblum with ⟨K, hK_ge_1, hK⟩
  -- 1. Prove Linear Independence
  -- The Grünblum condition implies that if a finite combination is 0,
  -- its partial sums must have norm 0.
  let S := Submodule.span 𝕜 (Set.range e)
  let b_S := Module.Basis.span h_indep
  let e_Y : ℕ → S := b_S
  have hbS : ∀ n, (b_S n : X) = e n := Module.Basis.span_apply h_indep
  let P_span (k : ℕ) : S →ₗ[𝕜] S := b_S.constr 𝕜 (fun i => if i < k then b_S i else 0)
  have h_P_span_apply (k : ℕ) (x : S) :
      P_span k x = ∑ i ∈ Finset.range k, b_S.repr x i • b_S i := by
    rw [Module.Basis.constr_apply, Finsupp.sum]
    refine Finset.sum_congr_of_eq_on_inter ?_ ?_ ?_ <;> intro i h1 h2
    · -- Case: i ∈ supp \ range k
      rw [if_neg (by simpa using h2), smul_zero]
    · -- Case: i ∈ range k \ supp
      rw [Finsupp.notMem_support_iff.mp h2, zero_smul]
    · -- Case: i ∈ supp ∩ range k
      rw [if_pos (by simpa using h2)]
  have h_P_span_bound (k : ℕ) (x : S) : ‖P_span k x‖ ≤ K * ‖x‖ := by
    let a := b_S.repr x
    let N := max k (a.support.sup id + 1)
    have hk_le_N : k ≤ N := le_max_left _ _
    -- 1. Express x as a sum in X
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
    rw [← norm_coe, ← norm_coe, hx,  h_P_span_apply]
    simp_rw [Submodule.coe_sum, Submodule.coe_smul, hbS]
    exact hK N k (b_S.repr x) hk_le_N
  let P (k : ℕ) : S →L[𝕜] S := LinearMap.mkContinuous (P_span k) K (h_P_span_bound k)
  -- Verify Schauder Basis Conditions
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
    -- Define the target span W
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
    -- Simplify the inner sum: (∑ k in range m, coeff k • δ_k) evaluated at j
    simp_rw [Finsupp.finset_sum_apply, Finsupp.smul_apply, Finsupp.single_apply,
             smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_range]
    -- Convert (if ... then c else 0) • x to if ... then c • x else 0
    simp_rw [ite_smul, zero_smul]
    rw [← Finset.sum_filter]
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, lt_min_iff]
  have hlim (x : S) : Filter.Tendsto (fun n ↦ P n x) Filter.atTop (nhds x) := by
    have h_unif : ∀ n, ‖P n‖ ≤ K := by
      intro n
      apply ContinuousLinearMap.opNorm_le_bound _ (le_trans (by norm_num) hK_ge_1)
      intro s
      have h_cont : Continuous (fun y => ‖P n y‖ - K * ‖y‖) :=
        (P n).continuous.norm.sub (continuous_const.mul continuous_norm)
      dsimp only [P]
      simp only [LinearMap.mkContinuous_apply, AddSubgroupClass.coe_norm]
      calc ‖P_span n s‖
        _ = ‖P_span n s‖ := rfl
        _ ≤ K * ‖s‖ := h_P_span_bound n s
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
  -- Conclusion: use basis_of_canonical_projections
  -- Key: b_S n = ⟨e n, _⟩ as elements of S
  have hbS_eq : ∀ n, b_S n = ⟨e n, subset_span (mem_range_self n)⟩ := fun n ↦
    Subtype.ext (hbS n)
  -- The goal's e_Y is definitionally fun n ↦ ⟨e n, _⟩
  -- Show this is in the range of Q n = P (n+1) - P n
  have he_in_range : ∀ n, ⟨e n, subset_span (mem_range_self n)⟩ ∈
      LinearMap.range (SchauderBasis.Q P n).toLinearMap := fun n ↦ by
    rw [← hbS_eq, LinearMap.mem_range]
    use b_S n
    simp only [SchauderBasis.Q, ContinuousLinearMap.coe_sub, P,
               LinearMap.mkContinuous_coe, LinearMap.sub_apply]
    rw [h_P_span_apply, h_P_span_apply, Finset.sum_range_succ, add_sub_cancel_left]
    simp only [Module.Basis.repr_self, Finsupp.single_eq_same, one_smul]
  -- ⟨e n, _⟩ ≠ 0 follows from h_nz
  have he_ne : ∀ n, (⟨e n, subset_span (mem_range_self n)⟩ : S) ≠ 0 := fun n h ↦
    h_nz n (by simpa using congrArg Subtype.val h)
  exact ⟨SchauderBasis.basis_of_canonical_projections h0 hdim hcomp hlim he_in_range he_ne⟩

lemma perturbation_finite_dimensional {S : Set (StrongDual 𝕜 X)}
    (h_weak_star : (0 : WeakDual 𝕜 X) ∈ closure (StrongDual.toWeakDual '' S))
    (h_norm : (0 : StrongDual 𝕜 X) ∉ closure S)
    (E : Subspace 𝕜 (StrongDual 𝕜 X)) (he : Nontrivial E)
    (hefind : FiniteDimensional 𝕜 E)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ x ∈ S, ∀ (e : E) (c : 𝕜), ‖(e : StrongDual 𝕜 X) + c • x‖ ≥ (1 - ε) * ‖e‖ := by
  -- 0. Handle trivial ε case
  rcases le_or_gt 1 ε with hε1 | hε1
  · -- If ε ≥ 1, any x ∈ S works
    obtain ⟨-, -, x, hxS, -⟩ := mem_closure_iff.mp h_weak_star _ isOpen_univ trivial
    use x, hxS
    intro e c
    -- Since ε ≥ 1, (1-ε) ≤ 0. The inequality holds trivially as LHS ≥ 0 and RHS ≤ 0.
    refine le_trans ?_ (norm_nonneg _)
    apply mul_nonpos_of_nonpos_of_nonneg
    · linarith [hε1]
    · exact norm_nonneg _

  -- 1. Setup constants based on distance to S
  obtain ⟨δ, hδ, hδS⟩ := Metric.exists_real_pos_lt_infEDist_of_notMem_closure h_norm
  let M := 2 / δ
  let γ := ε * δ / 4

  have h_norm_S : ∀ x ∈ S, δ ≤ ‖x‖ := by
    intro x hx
    have : ENNReal.ofReal δ < edist (0 : StrongDual 𝕜 X) x :=
      lt_of_lt_of_le hδS (Metric.infEDist_le_edist_of_mem hx)
    rw [edist_dist, dist_zero_left] at this
    exact (ENNReal.ofReal_le_ofReal_iff (norm_nonneg x)).mp this.le
  -- 2. Use compactness of the sphere in E to find a finite "test set" F ⊂ X
  let sphere := Metric.sphere (0 : E) 1
  -- Define the open sets covering the sphere, indexed by the unit ball of vectors X.
  let U (v : {v : X // ‖v‖ ≤ 1}) : Set E := {e | 1 - ε / 2 < ‖(e : StrongDual 𝕜 X) v‖}

  have h_cover : sphere ⊆ ⋃ v, U v := by
    intro e he
    rw [mem_sphere_zero_iff_norm] at he
    -- We have ‖e‖ = 1 and ε > 0, so 1 - ε/2 < ‖e‖
    have h_lt : 1 - ε / 2 < ‖(e : StrongDual 𝕜 X)‖ := by
      rw [norm_coe, he]
      linarith
    -- Find a vector v with ||v|| ≤ 1 that "witnesses" the norm of e
    obtain ⟨v, hv, hv_val⟩ := ContinuousLinearMap.exists_lt_apply_of_lt_opNorm (e : StrongDual 𝕜 X) h_lt
    exact Set.mem_iUnion.mpr ⟨⟨v, hv.le⟩, hv_val⟩

  have h_open (v : {v : X // ‖v‖ ≤ 1}) : IsOpen (U v) := by
    have : Continuous fun (e : E) => (e : StrongDual 𝕜 X) v.val :=
      (ContinuousLinearMap.apply 𝕜 𝕜 v.val).continuous.comp continuous_subtype_val
    exact isOpen_Ioi.preimage (Continuous.norm this)

  -- Extract finite subcover
  obtain ⟨F, hF_cover⟩ := (isCompact_sphere (0 : E) 1).elim_finite_subcover U h_open h_cover

  -- 3. Find perturbation x ∈ S small on F (using weak* closure)
  let W := {w : WeakDual 𝕜 X | ∀ v ∈ F, ‖w v‖ < γ}
  have hW_open : IsOpen W := by
    rw [show W = ⋂ v ∈ F, {w | ‖w v‖ < γ} by ext; simp [W]]
    apply isOpen_biInter_finset
    intro v _
    refine isOpen_lt (continuous_norm.comp (WeakDual.eval_continuous (v : X))) continuous_const
  have hγ : 0 < γ := by
    dsimp [γ]
    nlinarith [hε, hδ]

  have hW0 : (0 : WeakDual 𝕜 X) ∈ W := by
    simp only [W, Set.mem_setOf_eq]
    intro v _
    rw [ContinuousLinearMap.zero_apply, norm_zero]
    exact hγ

  -- Use weak-star density to find x ∈ S that is small on F
  obtain ⟨_, hwW, ⟨x, hxS, rfl⟩⟩ : ∃ w ∈ W, ∃ x ∈ S, StrongDual.toWeakDual x = w :=
      (_root_.mem_closure_iff).mp h_weak_star W hW_open hW0

  -- 4. Verify the inequality
  refine ⟨x, hxS, fun e c ↦ ?_⟩
  rcases eq_or_ne e 0 with rfl | he_ne; · simp [norm_nonneg]
  -- Scale e to the sphere
  let e_norm := ‖e‖
  let e' : E := (e_norm⁻¹ : 𝕜) • e
  have he'_norm : ‖e'‖ = 1 := norm_smul_inv_norm he_ne

  -- Main estimate logic
  have estimate : ‖e'  + (e_norm⁻¹ * c) • x‖ ≥ 1 - ε := by
    let c' := e_norm⁻¹ * c
    rcases le_or_gt M ‖c'‖ with h_large | h_small
    ·  -- Case 1: c' is large, c' • x dominates
      calc ‖e' + c' • x‖
        _ = ‖c' • x + e'‖                       := by rw [add_comm]
        _ ≥ ‖c' • x‖ - ‖(e' : StrongDual 𝕜 X)‖  := norm_sub_le_norm_add _ _
        _ = ‖c'‖ * ‖x‖ - 1                      := by rw [norm_smul, norm_coe, he'_norm]
        _ ≥ M * δ - 1                           := by gcongr; exact h_norm_S x hxS
        _ = (2 / δ) * δ - 1                     := rfl
        _ = 1                                   := by field_simp [hδ]; ring
        _ ≥ 1 - ε                               := by linarith
    · -- Case 2: c' is small, e dominates
      obtain this := hF_cover (mem_sphere_zero_iff_norm.mpr he'_norm)
      rw [Set.mem_iUnion₂] at this
      obtain ⟨v, hvF, hv_lower⟩ := this

      calc ‖e' + c' • x‖
        _ ≥ ‖(e' + c' • x) v‖               := ContinuousLinearMap.unit_le_opNorm _ _ v.property
        _ = ‖(e' : StrongDual 𝕜 X) v + (c' • x) v‖          := by simp only
          [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]
        _ ≥ ‖(e' : StrongDual 𝕜 X) v‖ - ‖c' • x v‖          := norm_sub_le_norm_add _ _
        _ ≥ ‖(e' : StrongDual 𝕜 X) v‖ - ‖c'‖ * ‖x v‖        := by rw [norm_smul]
        _ ≥ (1 - ε / 2) - M * γ          := by
            have : ‖x v‖ < γ := hwW v (Finset.mem_coe.mp hvF)
            gcongr
            exact hv_lower.le
        _ = 1 - ε                        := by dsimp [M, γ]; field_simp [hδ.ne']; ring

  -- Reconstruct for original e and c
  have h_norm_ne : (e_norm : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr he_ne)
  -- Key: e = e_norm • e' and c = e_norm * (e_norm⁻¹ * c)
  have he_eq : (e : StrongDual 𝕜 X) = (e_norm : 𝕜) • (e' : StrongDual 𝕜 X) := by
    simp only [e', Submodule.coe_smul, smul_smul, mul_inv_cancel₀ h_norm_ne, one_smul]
  have hc_eq : c = (e_norm : 𝕜) * ((e_norm⁻¹ : 𝕜) * c) := by
    rw [← mul_assoc, mul_inv_cancel₀ h_norm_ne, one_mul]
  calc ‖(e : StrongDual 𝕜 X) + c • x‖
    _ = ‖(e_norm : 𝕜) • (e' : StrongDual 𝕜 X) + ((e_norm : 𝕜) * ((e_norm⁻¹ : 𝕜) * c)) • x‖ := by
      conv_lhs => rw [he_eq, hc_eq]
    _ = ‖(e_norm : 𝕜) • ((e' : StrongDual 𝕜 X) + ((e_norm⁻¹ : 𝕜) * c) • x)‖ := by
      rw [smul_add, smul_smul]
    _ = ‖(e_norm : 𝕜)‖ * ‖(e' : StrongDual 𝕜 X) + ((e_norm⁻¹ : 𝕜) * c) • x‖ := by
      rw [norm_smul]
    _ = ‖e‖ * ‖(e' : StrongDual 𝕜 X) + ((e_norm⁻¹ : 𝕜) * c) • x‖ := by
      simp only [e_norm, RCLike.norm_ofReal, abs_norm]
    _ ≥ ‖e‖ * (1 - ε) := by
      gcongr
      -- estimate uses (↑(e_norm⁻¹) * c), but here we have ((↑e_norm)⁻¹ * c)
      -- These are equal by RCLike.ofReal_inv
      rw [← RCLike.ofReal_inv]
      exact estimate
    _ = (1 - ε) * ‖e‖ := mul_comm _ _

/-- Given a set in the dual that is bounded away from 0 in norm but has 0 in its
    weak-star closure, we can select a basic sequence with basis constant close to 1. -/
theorem basic_sequence_selection_dual {S : Set (StrongDual 𝕜 X)}
    (h_weak_star : (0 : StrongDual 𝕜 X) ∈ closure (StrongDual.toWeakDual '' S))
    (h_norm : (0 : StrongDual 𝕜 X) ∉ closure S)
    {ε : ℝ} (hε : ε > 0) :
    ∃ (f : ℕ → StrongDual 𝕜 X) (hf : IsBasicSequence 𝕜 f), (∀ n, f n ∈ S) ∧
    basicSequenceConstant hf < 1 + ε := by
  sorry

/-- In an infinite-dimensional normed space, we can find basic sequences
    with basis constant arbitrarily close to 1. -/
theorem exists_basic_sequence (hinf : ¬ FiniteDimensional 𝕜 X) {ε : ℝ} (hε : 0 < ε) :
    ∃ (x : ℕ → X) (hx : IsBasicSequence 𝕜 x), basicSequenceConstant hx < 1 + ε := by
  sorry

/-- Perturbing a basic sequence by an element outside its closed span
    yields another basic sequence. -/
lemma perturb_basic_sequence {e : ℕ → X} (he : IsBasicSequence 𝕜 e) (f : StrongDual 𝕜 X)
    (hf : ∀ n, f (e n) = 0) (u : X) (hu : u ∉ (span 𝕜 (range e)).topologicalClosure) :
    IsBasicSequence 𝕜 (fun n ↦ e n + u) := by
    sorry

/-- There are no basic sequences in a subset `S` of `X` if and only if
    the weak-star closure of the `S` is weakly-compact and does not contain `0`. -/
theorem no_basic_sequence_iff_zero_not_in_weak_star_closure {S : Set X} :
    (∀ (e : ℕ → X), ¬ IsBasicSequence 𝕜 e) ↔ (0 : X) ∉ closure ((toWeakSpace 𝕜 X )'' S) := by
  sorry

end BasicSequences
