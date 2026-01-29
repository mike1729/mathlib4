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

/-- A `BasicSequence` is a bundled sequence that forms a Schauder basis
    for its algebraic span, with a finite basis constant.
    TODO add a comment about closed span version -/
structure BasicSequence (𝕜 : Type*) (X : Type*) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] where
  toFun : ℕ → X
  -- The basis field now just takes the types, not the sequence function
  basis : SchauderBasis 𝕜 (Submodule.span 𝕜 (Set.range toFun))
  -- We explicitly link the basis vectors to the sequence
  eq_basis : ⇑basis = Set.codRestrict toFun (Submodule.span 𝕜 (Set.range toFun))
                        (fun n ↦ Submodule.subset_span (Set.mem_range_self n))
  basisConstant_lt_top : basis.basisConstant < ⊤

-- Enable treating the BasicSequence as a function `ℕ → X`
instance : CoeFun (BasicSequence 𝕜 X) (fun _ ↦ ℕ → X) where
  coe b := b.toFun

/-- A sequence `e` is a basic sequence if there exists a `BasicSequence` structure
    whose underlying sequence is equal to `e`. -/
def IsBasicSequence (𝕜 : Type*) {X : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] (e : ℕ → X) : Prop :=
  ∃ b : BasicSequence 𝕜 X, ⇑b = e

-- TODO check where complete space is needed
namespace BasicSequences

/-- The **Basis Constant** of a basic sequence. -/
noncomputable def basicSequenceConstant (bs : BasicSequence 𝕜 X) : ℝ :=
  bs.basis.basisConstant.toReal

/-- A sequence satisfies the **Grünblum Condition** if the norms of the projections
onto the span of its first `n` elements are uniformly bounded. -/
def SatisfiesGrunblumCondition (𝕜 : Type*) {X : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] (e : ℕ → X) : Prop :=
  ∃ K, 1 ≤ K ∧ ∀ (n m : ℕ) (a : ℕ → 𝕜), m ≤ n →
    ‖∑ i ∈ Finset.range m, a i • e i‖ ≤ K * ‖∑ i ∈ Finset.range n, a i • e i‖

/-- The Grünblum constant for a basic sequence is max(1, basicSequenceConstant). -/
def grunblumConstant (bs : BasicSequence 𝕜 X) : ℝ := max 1 (basicSequenceConstant bs)

theorem grunblumConstant_ge_one (bs : BasicSequence 𝕜 X) : 1 ≤ grunblumConstant bs :=
  le_max_left 1 _

/-- A basic sequence implies the Grünblum inequality holds for its basis constant. -/
theorem grunblum_of_basic (bs : BasicSequence 𝕜 X) : SatisfiesGrunblumCondition 𝕜 bs := by
  -- Use K = max(1, basisConstant) to ensure K ≥ 1
  let K := max 1 bs.basis.basisConstant.toReal
  have hK_ge : 1 ≤ K := le_max_left 1 _
  have hK_lt_top : bs.basis.basisConstant ≠ ⊤ := bs.basisConstant_lt_top.ne
  refine ⟨K, hK_ge, fun n m a hmn => ?_⟩
  -- The key idea: the partial sum up to m is the projection P_m applied to the full sum
  -- and ‖P_m‖ ≤ basisConstant ≤ K
  let S := Submodule.span 𝕜 (Set.range bs.toFun)
  have hsum_mem (k : ℕ) : ∑ i ∈ Finset.range k, a i • bs i ∈ S :=
    Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
  -- The projection bound: ‖P_m‖ ≤ basisConstant ≤ K
  have h_proj_bound : ‖bs.basis.proj m‖ ≤ K := by
    have h := bs.basis.norm_proj_le_basisConstant m
    rw [← ENNReal.toReal_le_toReal ENNReal.coe_ne_top hK_lt_top] at h
    simp only [ENNReal.coe_toReal, coe_nnnorm] at h
    exact h.trans (le_max_right _ _)
  -- The rest requires showing P_m(∑_{i<n} a_i • e_i) = ∑_{i<m} a_i • e_i
  -- This is a standard property of Schauder basis projections
  -- First, lift the sums to the subspace S
  let sum_n : S := ⟨∑ i ∈ Finset.range n, a i • bs i, hsum_mem n⟩
  let sum_m : S := ⟨∑ i ∈ Finset.range m, a i • bs i, hsum_mem m⟩
  -- Show that basis i = codRestrict bs.toFun ... i, so (basis i : X) = bs i
  have h_basis_eq : ∀ i, (bs.basis i : X) = bs i := fun i ↦ by
    have h := congrFun bs.eq_basis i
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
    -- For sum_n = ∑_{i<n} a_i • basis_i, coord j (sum_n) = a_j for j < n
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
          rw [bs.basis.ortho i i, Pi.single_eq_same]
        rw [h_ortho, smul_eq_mul, mul_one]
      · -- When j ≠ i: a_j • coord i (basis j) = a_j • 0 = 0
        intro j _ hji
        have h_ortho : bs.basis.coord i (bs.basis j) = 0 := by
          rw [bs.basis.ortho i j, Pi.single_apply, if_neg (Ne.symm hji)]
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
theorem grunblum_bound_of_basic (bs : BasicSequence 𝕜 X) (n m : ℕ) (a : ℕ → 𝕜) (hmn : m ≤ n) :
    ‖∑ i ∈ Finset.range m, a i • bs i‖ ≤
    grunblumConstant bs * ‖∑ i ∈ Finset.range n, a i • bs i‖ := by
  -- Directly prove the bound using the same technique as grunblum_of_basic
  let K := grunblumConstant bs
  have hK_lt_top : bs.basis.basisConstant ≠ ⊤ := bs.basisConstant_lt_top.ne
  let S := Submodule.span 𝕜 (Set.range bs.toFun)
  have hsum_mem (k : ℕ) : ∑ i ∈ Finset.range k, a i • bs i ∈ S :=
    Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
  have h_proj_bound : ‖bs.basis.proj m‖ ≤ K := by
    have h := bs.basis.norm_proj_le_basisConstant m
    rw [← ENNReal.toReal_le_toReal ENNReal.coe_ne_top hK_lt_top] at h
    simp only [ENNReal.coe_toReal, coe_nnnorm] at h
    exact h.trans (le_max_right _ _)
  let sum_n : S := ⟨∑ i ∈ Finset.range n, a i • bs i, hsum_mem n⟩
  let sum_m : S := ⟨∑ i ∈ Finset.range m, a i • bs i, hsum_mem m⟩
  have h_basis_eq : ∀ i, (bs.basis i : X) = bs i := fun i ↦ by
    have h := congrFun bs.eq_basis i
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
          rw [bs.basis.ortho i i, Pi.single_eq_same]
        rw [h_ortho, smul_eq_mul, mul_one]
      · intro j _ hji
        have h_ortho : bs.basis.coord i (bs.basis j) = 0 := by
          rw [bs.basis.ortho i j, Pi.single_apply, if_neg (Ne.symm hji)]
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

lemma linearIndependent_of_grunblum {e : ℕ → X} (h_grunblum : SatisfiesGrunblumCondition 𝕜 e)
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
theorem isBasicSequence_of_grunblum [CompleteSpace X] {e : ℕ → X}
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
  have h_bound_P : ∀ n, ‖P n‖ ≤ K := fun n ↦ by
    refine ContinuousLinearMap.opNorm_le_bound _ (zero_le_one.trans hK_ge_1) (fun x ↦ ?_)
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
  -- 2. Obtain the bundled SchauderBasis on the subspace S
-- 1. Bundle all the subspace data into our structure
  -- Note: 'e_Y' is 'e' lifted to S, and 'P' is the sequence of projections on S
  let D : SchauderBasis.CanonicalProjectionProperties 𝕜 S := {
    P := P
    e := e_Y
    h0 := h0
    hdim := hdim
    hcomp := hcomp
    hlim := hlim
    he_in_range := fun n ↦ by
      -- Rewrite b_S n to ⟨e n, ...⟩ so it matches your local proof
      dsimp only [e_Y]
      rw [hbS_eq]
      exact he_in_range n
    he_ne := fun n ↦ by
      -- Rewrite b_S n to ⟨e n, ...⟩
      dsimp only [e_Y]
      rw [hbS_eq]
      exact he_ne n
  }
  -- 2. Construct the Schauder Basis on S
  let b_S := D.basis
  -- 3. Construct the BasicSequence on X
  let seq : BasicSequence 𝕜 X := {
    toFun := e
    basis := b_S

    eq_basis := by
      -- Goal: ⇑b_S = e_Y (roughly)
      -- D.basis_coe gives us: ⇑b_S = D.e
      ext n
      rw [SchauderBasis.CanonicalProjectionProperties.basis_coe D]
      -- D.e is defined as e_Y, which is e lifted to S
      dsimp only [val_codRestrict_apply]
      exact hbS n

    basisConstant_lt_top := by
      -- Goal: b_S.basisConstant < ⊤
      apply SchauderBasis.basisConstant_lt_top_uniform_bound
      · intro n
        -- Use the simplification lemma to switch from basis.proj to P
        rw [SchauderBasis.CanonicalProjectionProperties.basis_proj D]
      -- Use the bound we proved earlier (renamed from h_unif to h_bound_P)
        exact h_bound_P n
  }
  -- 4. Conclude
  use seq

/-- A version of `isBasicSequence_of_grunblum` that also provides an explicit bound
    on the basis constant. If a sequence satisfies the Grünblum condition with constant K,
    the resulting basic sequence has basis constant at most K. -/
theorem isBasicSequence_of_grunblum_with_bound [CompleteSpace X] {e : ℕ → X} {K : ℝ}
    (hK_ge : 1 ≤ K)
    (hK_bound : ∀ (n m : ℕ) (a : ℕ → 𝕜), m ≤ n →
      ‖∑ i ∈ Finset.range m, a i • e i‖ ≤ K * ‖∑ i ∈ Finset.range n, a i • e i‖)
    (h_nz : ∀ n, e n ≠ 0) :
    ∃ (b : BasicSequence 𝕜 X), ⇑b = e ∧ basicSequenceConstant b ≤ K := by
  have h_grunblum : SatisfiesGrunblumCondition 𝕜 e := ⟨K, hK_ge, hK_bound⟩
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
      LinearMap.range (SchauderBasis.Q P n).toLinearMap := fun n ↦ by
    rw [← hbS_eq, LinearMap.mem_range]
    use b_S n
    simp only [SchauderBasis.Q, ContinuousLinearMap.coe_sub, P,
               LinearMap.mkContinuous_coe, LinearMap.sub_apply]
    rw [h_P_span_apply, h_P_span_apply, Finset.sum_range_succ, add_sub_cancel_left]
    simp only [Module.Basis.repr_self, Finsupp.single_eq_same, one_smul]
  have he_ne : ∀ n, (⟨e n, subset_span (mem_range_self n)⟩ : S) ≠ 0 := fun n h ↦
    h_nz n (by simpa using congrArg Subtype.val h)
  let D : SchauderBasis.CanonicalProjectionProperties 𝕜 S := {
    P := P
    e := e_Y
    h0 := h0
    hdim := hdim
    hcomp := hcomp
    hlim := hlim
    he_in_range := fun n ↦ by dsimp only [e_Y]; rw [hbS_eq]; exact he_in_range n
    he_ne := fun n ↦ by dsimp only [e_Y]; rw [hbS_eq]; exact he_ne n
  }
  let b_basis := D.basis
  let seq : BasicSequence 𝕜 X := {
    toFun := e
    basis := b_basis
    eq_basis := by
      ext n
      rw [SchauderBasis.CanonicalProjectionProperties.basis_coe D]
      dsimp only [val_codRestrict_apply]
      exact hbS n
    basisConstant_lt_top := by
      apply SchauderBasis.basisConstant_lt_top_uniform_bound
      intro n
      rw [SchauderBasis.CanonicalProjectionProperties.basis_proj D]
      exact h_bound_P n
  }
  refine ⟨seq, rfl, ?_⟩
  -- Show basicSequenceConstant seq ≤ K
  -- basisConstant = iSup_n (‖proj n‖₊)
  -- Since ‖proj n‖ ≤ K for all n, basisConstant ≤ K
  dsimp only [basicSequenceConstant]
  have h_lt_top : b_basis.basisConstant ≠ ⊤ := seq.basisConstant_lt_top.ne
  have h_K_nonneg : 0 ≤ K := by linarith
  -- basisConstant ≤ K.toNNReal (as ENNReal)
  have h_bound_ennreal : b_basis.basisConstant ≤ ENNReal.ofReal K := by
    rw [SchauderBasis.basisConstant, iSup_le_iff]
    intro n
    rw [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_le_ofReal_iff h_K_nonneg]
    simp only [coe_nnnorm]
    rw [SchauderBasis.CanonicalProjectionProperties.basis_proj D]
    exact h_bound_P n
  calc b_basis.basisConstant.toReal
    _ ≤ (ENNReal.ofReal K).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top h_bound_ennreal
    _ = K := ENNReal.toReal_ofReal h_K_nonneg

lemma perturbation_finite_dimensional {S : Set (StrongDual 𝕜 X)}
    (h_weak_star : (0 : WeakDual 𝕜 X) ∈ closure (StrongDual.toWeakDual '' S))
    (h_norm : (0 : StrongDual 𝕜 X) ∉ closure S)
    (E : Subspace 𝕜 (StrongDual 𝕜 X))
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

theorem basic_sequence_selection_dual {S : Set (StrongDual 𝕜 X)}
    (h_weak_star : (0 : WeakDual 𝕜 X) ∈ closure (StrongDual.toWeakDual '' S))
    (h_norm : (0 : StrongDual 𝕜 X) ∉ closure S)
    {ε : ℝ} (hε : ε > 0) :
    -- We assert existence of the STRUCTURE 'b', which bundles the function and the constant
    ∃ (b : BasicSequence 𝕜 (StrongDual 𝕜 X)),
      (∀ n, b n ∈ S) ∧
      basicSequenceConstant b < 1 + ε := by
  -- Use ε/2 in the construction so that the Grünblum constant is 1 + ε/2 < 1 + ε
  let ε' := ε / 2
  have hε' : ε' > 0 := by simp only [ε']; linarith
  have hε'_lt : 1 + ε' < 1 + ε := by simp only [ε']; linarith
  -- 1. Setup control sequence `δ` using a telescoping product `u`.
  let u (n : ℕ) := 1 + ε' * (1 - (1/2) ^ n)
  let δ (n : ℕ) := 1 - u n / u (n + 1)
  have hu : ∀ n, 1 ≤ u n ∧ u n < 1 + ε' := fun n ↦ by
    have hp : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hp' : 0 < (1 / 2 : ℝ) ^ n := pow_pos (by norm_num) n
    constructor <;> { dsimp [u, ε']; nlinarith }
  have hδ_pos : ∀ n, 0 < δ n := fun n ↦ by
    have hp_n1 : (1 / 2 : ℝ) ^ (n + 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hpos_un1 : 0 < u (n + 1) := by nlinarith [(hu (n + 1)).1]
    dsimp [δ, u, ε']
    rw [sub_pos, div_lt_one hpos_un1]
    have hp' : 0 < (1 / 2 : ℝ) ^ n := pow_pos (by norm_num) n
    have : (1 / 2 : ℝ) ^ (n + 1) = (1 / 2) * (1 / 2 : ℝ) ^ n := by ring
    have hpow_lt : (1 / 2 : ℝ) ^ (n + 1) < (1 / 2 : ℝ) ^ n := by
      rw [this]
      have : (1/2 : ℝ) * (1/2)^n < 1 * (1/2)^n := by nlinarith
      linarith
    simp only [u, ε']
    nlinarith [hε, hpow_lt]

  -- 2. Construct the sequence `f` via strong recursion.
  let f : ℕ → StrongDual 𝕜 X := fun n => Nat.strongRecOn n (fun k prev ↦
    let E := Submodule.span 𝕜 (Set.range (fun i : Fin k ↦ prev i i.isLt))
    Classical.choose (perturbation_finite_dimensional h_weak_star h_norm E
      (FiniteDimensional.span_of_finite 𝕜 (Set.finite_range _)) (hδ_pos k)))

  -- 3. Extract properties of `f`.
  have hf_spec (n : ℕ) :
      f n ∈ S ∧ ∀ (e : Submodule.span 𝕜 (Set.range (fun i : Fin n ↦ f i))) (c : 𝕜),
        (1 - δ n) * ‖e‖ ≤ ‖(e : StrongDual 𝕜 X) + c • f n‖ := by
    -- Rewriting `f n` definition to match the `prev` in recursion
    have hfn : f n = Classical.choose (perturbation_finite_dimensional h_weak_star h_norm
        (Submodule.span 𝕜 (Set.range (fun i : Fin n ↦ f i)))
        (FiniteDimensional.span_of_finite 𝕜 (Set.finite_range _)) (hδ_pos n)) := by
      unfold f; rw [Nat.strongRecOn_eq]
    rw [hfn]
    exact Classical.choose_spec (perturbation_finite_dimensional h_weak_star h_norm
        (Submodule.span 𝕜 (Set.range (fun i : Fin n ↦ f i)))
        (FiniteDimensional.span_of_finite 𝕜 (Set.finite_range _)) (hδ_pos n))

  -- 4. Prove the Grünblum condition via telescoping product.
  -- Keep the explicit bound with K = 1 + ε' for later use
  have h_grunblum_bound : ∀ n m (a : ℕ → 𝕜), m ≤ n →
      ‖∑ i ∈ Finset.range m, a i • f i‖ ≤ (1 + ε') * ‖∑ i ∈ Finset.range n, a i • f i‖ := by
    intro n m a hnm
    let S (k : ℕ) := ∑ i ∈ Finset.range k, a i • f i
    have h_step (k) (hk : k < n) : ‖S k‖ ≤ (1 - δ k)⁻¹ * ‖S (k + 1)‖ := by
      have hSk_mem : S k ∈ Submodule.span 𝕜 (Set.range (fun i : Fin k ↦ f i)) :=
        Submodule.sum_mem _ (fun i hi ↦ Submodule.smul_mem _ _ <|
          Submodule.subset_span ⟨⟨i, Finset.mem_range.mp hi⟩, rfl⟩)
      let e : Submodule.span 𝕜 (Set.range (fun i : Fin k ↦ f i)) := ⟨S k, hSk_mem⟩
      have h := (hf_spec k).2 e (a k)
      simp only [e, S] at h
      have h1δ : 0 < 1 - δ k := by
        simp only [δ, sub_sub_cancel]
        exact div_pos (lt_of_lt_of_le (by linarith) (hu k).1)
          (lt_of_lt_of_le (by linarith) (hu (k+1)).1)
      rw [le_inv_mul_iff₀ h1δ]
      calc (1 - δ k) * ‖S k‖ ≤ ‖S k + a k • f k‖ := h
        _ = ‖S (k + 1)‖ := by simp only [S, Finset.sum_range_succ]

    -- The key bound: ‖S m‖ ≤ (1 + ε) * ‖S n‖ via telescoping product
    -- Each step gives ‖S k‖ ≤ (1 - δ k)⁻¹ * ‖S (k+1)‖
    -- Product of (1 - δ k)⁻¹ from m to n-1 equals u n / u m ≤ (1 + ε)
    have hu_pos : ∀ k, 0 < u k := fun k => lt_of_lt_of_le (by linarith) (hu k).1
    -- Key identity: (1 - δ k)⁻¹ = u (k+1) / u k
    have h_inv : ∀ k, (1 - δ k)⁻¹ = u (k + 1) / u k := fun k => by
      simp only [δ, sub_sub_cancel]; rw [inv_div]
    -- Chain the inequalities via induction
    have h_chain : ‖S m‖ ≤ (u n / u m) * ‖S n‖ := by
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
      induction d with
      | zero => simp [(hu_pos m).ne']
      | succ d ih =>
        have h_step' : ∀ k < m + d, ‖S k‖ ≤ (1 - δ k)⁻¹ * ‖S (k + 1)‖ :=
          fun k hk => h_step k (Nat.lt_add_right 1 hk)
        calc ‖S m‖ ≤ (u (m + d) / u m) * ‖S (m + d)‖ := ih (Nat.le_add_right m d) h_step'
          _ ≤ (u (m + d) / u m) * ((1 - δ (m + d))⁻¹ * ‖S (m + d + 1)‖) := by
              gcongr
              · exact div_nonneg (le_of_lt (hu_pos _)) (le_of_lt (hu_pos _))
              · exact h_step (m + d) (by omega)
          _ = (u (m + d) / u m) * (u (m + d + 1) / u (m + d)) * ‖S (m + d + 1)‖ := by
              rw [h_inv]; ring
          _ = (u (m + (d + 1)) / u m) * ‖S (m + (d + 1))‖ := by
              rw [show m + d + 1 = m + (d + 1) by ring]
              field_simp [(hu_pos _).ne']
    -- Finally bound u n / u m ≤ (1 + ε')
    calc ‖S m‖ ≤ (u n / u m) * ‖S n‖ := h_chain
      _ ≤ (1 + ε') * ‖S n‖ := by
          gcongr
          calc u n / u m
            _ ≤ u n := div_le_self (le_of_lt (hu_pos n)) (hu m).1
            _ ≤ 1 + ε' := le_of_lt (hu n).2
  -- Package into SatisfiesGrunblumCondition for isBasicSequence_of_grunblum
  have h_grunblum : SatisfiesGrunblumCondition 𝕜 f :=
    ⟨1 + ε', by linarith [hε'], h_grunblum_bound⟩

  -- 5. Final assembly.
  have h_nz n : f n ≠ 0 := by
    intro hfn
    apply h_norm
    rw [← hfn]
    exact subset_closure (hf_spec n).1

  obtain ⟨b, hb⟩ := isBasicSequence_of_grunblum h_grunblum h_nz
  refine ⟨b, ?_, ?_⟩
  · -- Show ∀ n, b n ∈ S
    intro n
    rw [show b n = f n from congrFun hb n]
    exact (hf_spec n).1
  · -- Show basicSequenceConstant b < 1 + ε
    -- The basisConstant is bounded by the Grünblum constant 1 + ε'
    -- This follows from the SchauderBasis projection bound
    have hK_pos : (0 : ℝ) ≤ 1 + ε' := by linarith
    -- Key: b.basis vectors equal f (via eq_basis)
    have heq : ∀ i, (b.basis i : StrongDual 𝕜 X) = f i := fun i => by
      have h1 := congrFun b.eq_basis i
      rw [← hb]; exact congrArg Subtype.val h1
    -- The projection bound follows from Grünblum applied to basis expansions
    have h_proj_bound : ∀ m, ‖b.basis.proj m‖ ≤ 1 + ε' := fun m => by
      apply ContinuousLinearMap.opNorm_le_bound _ hK_pos
      intro x
      rw [SchauderBasis.proj_apply]
      -- The sum in the subspace has the same norm as its coercion
      have hsum_coe : ∀ N, ‖∑ i ∈ Finset.range N, (b.basis.coord i) x • b.basis i‖ =
                          ‖∑ i ∈ Finset.range N, (b.basis.coord i) x • f i‖ := fun N => by
        rw [← norm_coe, Submodule.coe_sum]
        congr 1
        apply Finset.sum_congr rfl; intro i _
        rw [Submodule.coe_smul, heq]
      rw [hsum_coe]
      -- The partial sums converge to x (in the subspace)
      have hexp := b.basis.expansion x
      rw [HasSum, SummationFilter.conditional_filter_eq_map_range] at hexp
      -- Convert to convergence of the coerced sums to x (in the ambient space)
      have hconv_x : Filter.Tendsto (fun N => ∑ i ∈ Finset.range N, (b.basis.coord i) x • f i)
                     Filter.atTop (nhds (x : StrongDual 𝕜 X)) := by
        -- Show functions are equal
        have hfun_eq :
            (fun N => ∑ i ∈ Finset.range N, (b.basis.coord i) x • f i) =
            ((Subtype.val ∘ (fun s => ∑ i ∈ s, (b.basis.coord i) x • b.basis i)) ∘
              Finset.range) := by
          funext N
          simp only [Function.comp_apply, Submodule.coe_sum]
          apply Finset.sum_congr rfl; intro i _
          rw [Submodule.coe_smul, heq]
        rw [hfun_eq]
        simp only [Filter.Tendsto]
        exact continuous_subtype_val.continuousAt.tendsto.comp hexp
      have hconv : Filter.Tendsto
          (fun N => (1 + ε') * ‖∑ i ∈ Finset.range N, (b.basis.coord i) x • f i‖)
          Filter.atTop (nhds ((1 + ε') * ‖(x : StrongDual 𝕜 X)‖)) :=
        hconv_x.norm.const_mul (1 + ε')
      apply ge_of_tendsto hconv
      filter_upwards [Filter.eventually_ge_atTop m] with N hN
      exact h_grunblum_bound N m (fun i => b.basis.coord i x) hN
    -- Bound basisConstant
    calc basicSequenceConstant b
      _ = b.basis.basisConstant.toReal := rfl
      _ ≤ 1 + ε' := by
          apply ENNReal.toReal_le_of_le_ofReal hK_pos
          rw [SchauderBasis.basisConstant]
          apply iSup_le; intro n
          rw [← ENNReal.ofReal_coe_nnreal]
          exact ENNReal.ofReal_le_ofReal (h_proj_bound n)
      _ < 1 + ε := hε'_lt

lemma weak_closure_sphere_contains_zero (hinf : ¬ FiniteDimensional 𝕜 X) :
    (0 : WeakDual 𝕜 (StrongDual 𝕜 X)) ∈
    closure (StrongDual.toWeakDual '' (NormedSpace.inclusionInDoubleDual 𝕜 X '' Metric.sphere 0 1)) := by
  -- Let J be the canonical embedding X → X**
  let J := NormedSpace.inclusionInDoubleDual 𝕜 X
  let S := StrongDual.toWeakDual '' (J '' Metric.sphere 0 1)
  -- Use: 0 ∈ closure S iff every neighborhood intersects S
  rw [_root_.mem_closure_iff]
  intro U hU_open hU_zero
  -- The weak* topology is the induced topology from F → 𝕜 (pointwise convergence)
  -- So there exists V open in (StrongDual 𝕜 X → 𝕜) with U = preimage of V
  rw [isOpen_induced_iff] at hU_open
  obtain ⟨V, hV_open, hV_eq⟩ := hU_open
  -- 0 ∈ U means the zero functional is in the preimage
  have h0V : (fun f => (0 : WeakDual 𝕜 (StrongDual 𝕜 X)) f) ∈ V := by
    rw [← hV_eq] at hU_zero
    exact hU_zero
  -- V is open in the product topology, so it contains a basic open neighborhood of 0
  -- Basic open sets in the product topology are determined by finitely many coordinates
  rw [isOpen_pi_iff] at hV_open
  obtain ⟨F, t, ht_cond, hFt_sub⟩ := hV_open _ h0V
  -- F is a finite set of functionals in X*, and t gives open neighborhoods in 𝕜 for each
  -- Consider the intersection of kernels K = ⋂_{f ∈ F} ker f
  let K := ⨅ f ∈ F, LinearMap.ker (f : X →ₗ[𝕜] 𝕜)
  -- K has finite codimension, so since X is infinite-dimensional, K ≠ {0}
  have hK_nontrivial : K ≠ ⊥ := by
    -- The quotient X/K embeds into 𝕜^F via the map x ↦ (f(x))_{f ∈ F}
    -- Since X is infinite-dimensional and 𝕜^F is finite-dimensional, K must be nontrivial
    by_contra h_bot
    -- If K = ⊥, then the map x ↦ (f(x))_{f ∈ F} is injective
    -- This gives an embedding X ↪ 𝕜^F, contradicting infinite-dimensionality
    have : FiniteDimensional 𝕜 X := by
      have hfin : FiniteDimensional 𝕜 (F → 𝕜) := inferInstance
      -- Define a linear map from X to F → 𝕜
      let φ : X →ₗ[𝕜] (F → 𝕜) := {
        toFun := fun x f => (f : StrongDual 𝕜 X) x
        map_add' := fun x y => by ext f; simp [map_add]
        map_smul' := fun c x => by ext f; simp [map_smul]
      }
      apply Module.Finite.of_injective φ
      intro x y hxy
      simp only [LinearMap.coe_mk, AddHom.coe_mk, funext_iff] at hxy
      have hmem : x - y ∈ K := by
        rw [Submodule.mem_iInf]
        intro f
        rw [Submodule.mem_iInf]
        intro hf
        rw [LinearMap.mem_ker, map_sub, sub_eq_zero]
        exact hxy ⟨f, hf⟩
      rw [h_bot, Submodule.mem_bot] at hmem
      exact sub_eq_zero.mp hmem
    exact hinf this
  -- Pick nonzero v ∈ K and normalize to unit sphere
  obtain ⟨v, hvK, hv_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hK_nontrivial
  let x := (‖v‖⁻¹ : 𝕜) • v
  have hx_norm : ‖x‖ = 1 := by
    rw [norm_smul]
    have : ‖(‖v‖ : 𝕜)⁻¹‖ = ‖v‖⁻¹ := by
      rw [norm_inv, RCLike.norm_ofReal, abs_norm]
    rw [this, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv_ne)]
  have hx_K : x ∈ K := K.smul_mem _ hvK
  -- x satisfies f(x) = 0 for all f ∈ F
  have h_vanish : ∀ f ∈ F, (f : StrongDual 𝕜 X) x = 0 := fun f hf => by
    have hmem : x ∈ K := hx_K
    rw [Submodule.mem_iInf] at hmem
    have := hmem f
    rw [Submodule.mem_iInf] at this
    exact LinearMap.mem_ker.mp (this hf)
  -- J(x) is in the set S (image of the sphere)
  have hJx_S : StrongDual.toWeakDual (J x) ∈ S :=
    ⟨J x, ⟨x, mem_sphere_zero_iff_norm.mpr hx_norm, rfl⟩, rfl⟩
  -- J(x) is in U because it evaluates to 0 on all f ∈ F, which puts it in V
  have hJx_U : StrongDual.toWeakDual (J x) ∈ U := by
    rw [← hV_eq]
    apply hFt_sub
    intro f hf
    -- topDualPairing evaluates the double dual at a functional
    change topDualPairing 𝕜 (StrongDual 𝕜 X) (StrongDual.toWeakDual (J x)) f ∈ t f
    simp only [topDualPairing_apply, StrongDual.coe_toWeakDual]
    -- J x evaluates to f x by definition (dual_def)
    simp only [J, NormedSpace.dual_def]
    rw [h_vanish f hf]
    -- 0 ∈ t f because the zero functional evaluates to 0 there
    exact (ht_cond f hf).2
  exact ⟨StrongDual.toWeakDual (J x), hJx_U, hJx_S⟩

/-- Corollary 1.5.3: Every infinite-dimensional Banach space contains a basic sequence
    with basis constant arbitrarily close to 1. -/
theorem exists_basic_sequence [CompleteSpace X] (hinf : ¬ FiniteDimensional 𝕜 X) {ε : ℝ}
    (hε : 0 < ε) : ∃ (b : BasicSequence 𝕜 X), basicSequenceConstant b < 1 + ε := by
  -- 1. Setup the Embedding J : X → X**
  let J := NormedSpace.inclusionInDoubleDual 𝕜 X
  let S_bidual := J '' (Metric.sphere 0 1)
  -- 2. Verify hypotheses for the selection theorem (applied to X* as the base space)
  -- Hypothesis 1: 0 is in the weak* closure of S_bidual
  have h_weak : (0 : WeakDual 𝕜 (StrongDual 𝕜 X)) ∈
      closure (StrongDual.toWeakDual '' S_bidual) :=
    weak_closure_sphere_contains_zero hinf
  -- Hypothesis 2: 0 is not in the norm closure of S_bidual
  have h_norm : (0 : StrongDual 𝕜 (StrongDual 𝕜 X)) ∉ closure S_bidual := by
    rw [Metric.mem_closure_iff]
    push_neg
    use 1, zero_lt_one
    rintro _ ⟨x, hx, rfl⟩
    -- J is an isometry, so ||J x|| = ||x|| = 1
    have hJ_iso : ‖J x‖ = ‖x‖ := (NormedSpace.inclusionInDoubleDualLi (𝕜 := 𝕜) (E := X)).norm_map x
    rw [dist_zero_left, hJ_iso, mem_sphere_zero_iff_norm.mp hx]
  -- 3. Apply the Dual Selection Principle to get a basic sequence in the bidual X**
  obtain ⟨b_bidual, hb_mem, hb_const⟩ := basic_sequence_selection_dual h_weak h_norm hε
  -- 4. Pull back the sequence to X using the isometry J
  -- Each b_bidual n ∈ J '' sphere, so find the preimage
  have h_preimage (n : ℕ) : ∃ x ∈ Metric.sphere (0 : X) 1, J x = b_bidual n := hb_mem n
  let seq (n : ℕ) : X := (h_preimage n).choose
  have h_seq_sphere (n : ℕ) : seq n ∈ Metric.sphere (0 : X) 1 := (h_preimage n).choose_spec.1
  have h_seq_eq (n : ℕ) : J (seq n) = b_bidual n := (h_preimage n).choose_spec.2
  -- 5. The sequence (seq n) satisfies the Grünblum condition with the same constant
  -- Because J is an isometry: ‖∑ aᵢ • seq i‖ = ‖J(∑ aᵢ • seq i)‖ = ‖∑ aᵢ • J(seq i)‖
  --                                           = ‖∑ aᵢ • b_bidual i‖
  have h_nz : ∀ n, seq n ≠ 0 := fun n h => by
    have := h_seq_sphere n
    rw [mem_sphere_zero_iff_norm, h, norm_zero] at this
    exact one_ne_zero this.symm
  -- Use grunblumConstant which is definitionally max(1, basicSequenceConstant)
  let K := grunblumConstant b_bidual
  have hK_ge : 1 ≤ K := grunblumConstant_ge_one b_bidual
  have hK_lt : K < 1 + ε := by
    simp only [K, grunblumConstant, max_lt_iff]
    exact ⟨by linarith, hb_const⟩
  -- The Grünblum condition for seq with constant K
  have hK_bound_seq : ∀ (n m : ℕ) (a : ℕ → 𝕜), m ≤ n →
      ‖∑ i ∈ Finset.range m, a i • seq i‖ ≤ K * ‖∑ i ∈ Finset.range n, a i • seq i‖ := by
    intro n m a hmn
    -- Use that J is an isometry to transfer the inequality
    have h_J_sum (k : ℕ) : J (∑ i ∈ Finset.range k, a i • seq i) =
        ∑ i ∈ Finset.range k, a i • b_bidual i := by
      simp only [map_sum, map_smul, h_seq_eq]
    have hJ_norm : ∀ y : X, ‖J y‖ = ‖y‖ :=
      (NormedSpace.inclusionInDoubleDualLi (𝕜 := 𝕜) (E := X)).norm_map
    calc ‖∑ i ∈ Finset.range m, a i • seq i‖
      _ = ‖J (∑ i ∈ Finset.range m, a i • seq i)‖ := (hJ_norm _).symm
      _ = ‖∑ i ∈ Finset.range m, a i • b_bidual i‖ := by rw [h_J_sum]
      _ ≤ K * ‖∑ i ∈ Finset.range n, a i • b_bidual i‖ := grunblum_bound_of_basic b_bidual n m a hmn
      _ = K * ‖J (∑ i ∈ Finset.range n, a i • seq i)‖ := by rw [h_J_sum]
      _ = K * ‖∑ i ∈ Finset.range n, a i • seq i‖ := by rw [hJ_norm]
  -- 6. Apply the Grünblum criterion with bound to get a basic sequence
  obtain ⟨b, hb_eq, hb_bound⟩ := isBasicSequence_of_grunblum_with_bound hK_ge hK_bound_seq h_nz
  use b
  -- 7. Bound the basis constant: basicSequenceConstant b ≤ K < 1 + ε
  calc basicSequenceConstant b
    _ ≤ K := hb_bound
    _ < 1 + ε := hK_lt

lemma perturb_basic_sequence [CompleteSpace X] (b : BasicSequence 𝕜 X) (u : X)
    (f : StrongDual 𝕜 X) (hf : ∀ n, f (b n) = 1) (hu0 : f u = 0) :
    IsBasicSequence 𝕜 (fun n ↦ b n + u) := by
  let y := fun n ↦ b n + u
  -- 1. Elements are non-zero because f(y n) = 1
  have h_nz : ∀ n, y n ≠ 0 := fun n h_zero ↦ by
    have h_val : f (y n) = 1 := by simp [y, f.map_add, hf, hu0]
    rw [h_zero, f.map_zero] at h_val
    exact zero_ne_one h_val
    -- fun h => by simpa [y, hf, hu0, h] using f.map_zero

  -- 2. Grünblum Condition
  obtain ⟨K, hK⟩ := grunblum_of_basic b
  -- Define the distortion constant C
  let C := 1 + ‖f‖ * ‖u‖
  have hC : 0 ≤ C := add_nonneg zero_le_one (mul_nonneg (norm_nonneg f) (norm_nonneg u))
  have hC_ge_one : 1 ≤ C := le_add_of_nonneg_right (mul_nonneg (norm_nonneg f) (norm_nonneg u))

  refine isBasicSequence_of_grunblum ⟨K * C ^ 2, ?_⟩ h_nz
  · refine ⟨one_le_mul_of_one_le_of_one_le hK.1 (one_le_pow₀ hC_ge_one), fun n m a hnm ↦ ?_⟩
    let Y k := ∑ i ∈ Finset.range k, a i • y i
    let E k := ∑ i ∈ Finset.range k, a i • b i

    -- Key geometric relations
    have h_rel (k) : Y k = E k + f (Y k) • u := by
      simp only [Y, E, y, smul_add, Finset.sum_add_distrib, ← Finset.sum_smul]
      congr 1
      simp only [map_add, map_sum, map_smul, hf, hu0, smul_eq_mul, mul_one, mul_zero, add_zero]

    -- We bound E by Y (projection onto span(e)) and Y by E (injecting back)
    have h_E_Y (k) : ‖E k‖ ≤ C * ‖Y k‖ := by
      have hE_eq : E k = Y k - f (Y k) • u := (sub_eq_of_eq_add (h_rel k)).symm
      calc ‖E k‖
        _ = ‖Y k - f (Y k) • u‖ := by rw [hE_eq]
        _ ≤ ‖Y k‖ + ‖f (Y k) • u‖ := norm_sub_le _ _
        _ = ‖Y k‖ + ‖f (Y k)‖ * ‖u‖ := by rw [norm_smul]
        _ ≤ ‖Y k‖ + ‖f‖ * ‖Y k‖ * ‖u‖ := by gcongr; exact f.le_opNorm _
        _ = C * ‖Y k‖ := by ring

    have h_Y_E (k) : ‖Y k‖ ≤ C * ‖E k‖ := by
      have hfY_eq : f (Y k) = f (E k) := by
        rw [h_rel k, map_add, map_smul, hu0, smul_zero, add_zero]
      rw [h_rel k, hfY_eq]
      calc ‖E k + f (E k) • u‖
        _ ≤ ‖E k‖ + ‖f (E k) • u‖ := norm_add_le _ _
        _ = ‖E k‖ + ‖f (E k)‖ * ‖u‖ := by rw [norm_smul]
        _ ≤ ‖E k‖ + ‖f‖ * ‖E k‖ * ‖u‖ := by gcongr; exact f.le_opNorm _
        _ = C * ‖E k‖ := by ring

    -- Combine bounds
    calc ‖Y m‖
      _ ≤ C * ‖E m‖ := h_Y_E m
      _ ≤ C * (K * ‖E n‖) := by gcongr; exact hK.2 n m a hnm
      _ = C * K * ‖E n‖ := by ring
      _ ≤ C * K * (C * ‖Y n‖) := by
          apply mul_le_mul_of_nonneg_left (h_E_Y n)
          exact mul_nonneg hC (le_of_lt (lt_of_lt_of_le zero_lt_one hK.1))
      _ = (K * C ^ 2) * ‖Y n‖ := by ring

/-- There are no basic sequences in a subset `S` of `X` if and only if
    the weak-star closure of the `S` is weakly-compact and does not contain `0`. -/
theorem no_basic_sequence_iff_zero_not_in_weak_star_closure {S : Set X} :
    (∀ (e : ℕ → X), ¬ IsBasicSequence 𝕜 e) ↔ (0 : X) ∉ closure ((toWeakSpace 𝕜 X )'' S) := by
  sorry

end BasicSequences
