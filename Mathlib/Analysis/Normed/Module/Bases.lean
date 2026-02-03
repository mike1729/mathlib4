/-
Copyright (c) 2025 Michał Świętek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michał Świętek
-/
module

public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Schauder bases in normed spaces

This file defines Schauder bases in a normed space and develops their basic theory.

## Main definitions

* `SchauderBasis' β 𝕜 X L`: A structure representing a generalized Schauder basis for a
  normed space `X` over a field `𝕜`, indexed by a type `β` with a `SummationFilter L`.
  It includes:
  - `basis`: The basis vectors indexed by `β`.
  - `coord`: The coordinate functionals (elements of the dual space).
  - `ortho`: The biorthogonality condition $f_i(e_j) = \delta_{ij}$.
  - `expansion`: The requirement that for every $x \in X$, the series converges to $x$
    along the summation filter `L`.

* `SchauderBasis 𝕜 X`: The classical Schauder basis, an abbreviation for
  `SchauderBasis' ℕ 𝕜 X (SummationFilter.conditional ℕ)`.

* `UnconditionalSchauderBasis 𝕜 X`: An unconditional Schauder basis, an abbreviation for
  `SchauderBasis' ℕ 𝕜 X (SummationFilter.unconditional ℕ)`.

* `SchauderBasis'.proj' b A`: The projection onto a finite set `A` of basis vectors,
  defined as $P_A(x) = \sum_{i \in A} f_i(x)e_i$.

* `SchauderBasis.proj b n`: The $n$-th canonical projection $P_n: X \to X$,
  defined as $P_n(x) = \sum_{i < n} f_i(x)e_i$ (equals `proj' (Finset.range n)`).

* `SchauderBasis.basisConstant`: The supremum of the norms of the canonical projections
  (often called the "basis constant").

## Main results

* `SchauderBasis'.linearIndependent`: A Schauder basis is linearly independent.
* `SchauderBasis'.proj'_tendsto_id`: The projections `proj' A` converge to identity
  along the summation filter.
* `SchauderBasis'.range_proj'`: The range of `proj' A` is the span of the basis elements in `A`.
* `SchauderBasis'.proj'_comp`: Composition of projections satisfies
  `proj' A (proj' B x) = proj' (A ∩ B) x`.
* `SchauderBasis.proj_tendsto_id`: The canonical projections $P_n$ converge pointwise
  to the identity operator.
* `SchauderBasis.proj_uniform_bound`: In a Banach space, the canonical projections
  are uniformly bounded (a consequence of the Banach-Steinhaus Theorem).
* `ProjectionData.basis`: Constructs a Schauder basis from a `ProjectionData` bundle
  containing projections satisfying rank, composition, and convergence properties.

## Notation

The file uses the `SummationFilter.conditional ℕ` to handle the convergence of the
infinite sum, which corresponds to the convergence of partial sums.

## Bibliography

Based on Chapter 1. from Albiac, F., & Kalton, N. J. (2016). Topics in Banach Space Theory.
-/

@[expose] public section

noncomputable section

open Filter Topology LinearMap Set ENNReal

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/--
A generalized Schauder basis indexed by `β` using a `SummationFilter`.

See `SchauderBasis` for the classical ℕ-indexed case with conditional convergence,
and `UnconditionalSchauderBasis` for the unconditional case.
-/
structure SchauderBasis' (β : Type*) [Preorder β] [LocallyFiniteOrder β] [DecidableEq β] (𝕜 : Type*)
  (X : Type*) [NontriviallyNormedField 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  (L : SummationFilter β) where
  /-- The basis vectors. -/
  basis : β → X
  /-- Coordinate functionals -/
  coord : β → StrongDual 𝕜 X
  /-- Biorthogonality -/
  ortho : ∀ i j, coord i (basis j) = (Pi.single j (1 : 𝕜) : β → 𝕜) i
  /-- The sum converges to `x` along the provided `SummationFilter L`. -/
  expansion : ∀ x : X, HasSum (fun i ↦ (coord i) x • basis i) x L


variable {β : Type*} [Preorder β] [LocallyFiniteOrder β] [DecidableEq β]
variable {L : SummationFilter β}

/-- A classical Schauder basis indexed by ℕ with conditional convergence. -/
abbrev SchauderBasis (𝕜 : Type*) (X : Type*) [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] :=
  SchauderBasis' ℕ 𝕜 X (SummationFilter.conditional ℕ)

/-- An unconditional Schauder basis indexed by ℕ with unconditional convergence. -/
abbrev UnconditionalSchauderBasis (𝕜 : Type*) (X : Type*) [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] :=
  SchauderBasis' ℕ 𝕜 X (SummationFilter.unconditional ℕ)

instance : CoeFun (SchauderBasis' β 𝕜 X L) (fun _ ↦ β → X) where
  coe b := b.basis

namespace SchauderBasis'

variable (b : SchauderBasis' β 𝕜 X L)

/-- The basis vectors are linearly independent. -/
theorem linearIndependent : LinearIndependent 𝕜 b := by
  rw [linearIndependent_iff]
  intro l hl
  ext i
  have hsum : ∑ i ∈ l.support, l i • b i = 0 := hl
  -- Apply the i-th coordinate functional to the linear combination
  have happ : b.coord i (∑ j ∈ l.support, l j • b j) = 0 := by rw [hsum, map_zero]
  rw [map_sum] at happ
  simp_rw [ContinuousLinearMap.map_smul] at happ
  rw [Finset.sum_eq_single i, b.ortho i i] at happ
  · simpa using happ
  · intro j _ hji; rw [b.ortho i j, Pi.single_apply, if_neg hji.symm, smul_eq_mul, mul_zero]
  · intro hi; simp only [Finsupp.notMem_support_iff.mp hi, smul_eq_mul, zero_mul]

/-- Projection onto a finite set of basis vectors. -/
def proj' (A : Finset β) : X →L[𝕜] X := ∑ i ∈ A, (b.coord i).smulRight (b i)

/-- The canonical projection on the empty set is the zero map. -/
@[simp]
theorem proj'_empty : b.proj' ∅ = 0 := by simp [proj']

/-- The action of the projection on a vector x. -/
@[simp]
theorem proj'_apply (A : Finset β) (x : X) : b.proj' A x = ∑ i ∈ A, b.coord i x • b i := by
  simp only [proj', ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply]

/-- The action of the projection on a basis element e i. -/
theorem proj'_basis_element (A : Finset β) (i : β) :
    b.proj' A (b i) = if i ∈ A then b i else 0 := by
  rw [proj'_apply]
  by_cases hiA : i ∈ A
  · rw [Finset.sum_eq_single_of_mem i hiA]
    · simp only [b.ortho, Pi.single_apply, ↓reduceIte, one_smul, if_pos hiA]
    · intro j _ hji; rw [b.ortho j i, Pi.single_apply, if_neg hji, zero_smul]
  rw [if_neg hiA, Finset.sum_eq_zero]
  intro j hj
  rw [b.ortho j i, Pi.single_apply, if_neg, zero_smul]
  exact fun h => hiA (h ▸ hj)

/-- Projections converge to identity along the summation filter. -/
theorem proj'_tendsto_id (x : X) : Tendsto (fun A ↦ b.proj' A x) L.filter (𝓝 x) := by
  simp only [proj'_apply]
  exact b.expansion x

/-- The range of the projection is the span of the basis elements in A. -/
theorem range_proj' (A : Finset β) : LinearMap.range (b.proj' A).toLinearMap =
    Submodule.span 𝕜 (b '' A) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    rw [ContinuousLinearMap.coe_coe, proj'_apply]
    apply Submodule.sum_mem
    intros i hi
    apply Submodule.smul_mem
    apply Submodule.subset_span
    exact ⟨i, hi, rfl⟩
  · rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    use b i
    rw [ContinuousLinearMap.coe_coe, proj'_basis_element, if_pos (Finset.mem_coe.mp hi)]

/-- Composition of projections: `proj' A (proj' B x) = proj' (A ∩ B) x`. -/
theorem proj'_comp (A B : Finset β) (x : X) : b.proj' A (b.proj' B x) = b.proj' (A ∩ B) x := by
  simp only [proj'_apply, map_sum, map_smul]
  have h_ortho : ∀ i j, (b.coord i) (b j) = if i = j then 1 else 0 := by
    intro i j
    rw [b.ortho i j, Pi.single_apply]
  simp_rw [h_ortho]
  simp only [ite_smul, one_smul, zero_smul]
  simp_rw [Finset.sum_ite_eq']
  simp only [smul_ite, smul_zero]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_inter, and_comm]

end SchauderBasis'

/-! ### Unconditional Schauder bases -/

namespace UnconditionalSchauderBasis

variable (b : UnconditionalSchauderBasis 𝕜 X)

/-- Projections are uniformly bounded for unconditional bases (Banach-Steinhaus). -/
theorem proj'_uniform_bound [CompleteSpace X] : ∃ C : ℝ, ∀ A : Finset ℕ, ‖b.proj' A‖ ≤ C := by
  apply banach_steinhaus
  intro x
  -- The basis expansion gives HasSum, hence Summable for the unconditional filter
  have hsum : Summable (fun i ↦ b.coord i x • b i) := b.expansion x |>.summable
  -- By the vanishing norm characterization, tails are small
  obtain ⟨A₀, hA₀⟩ := summable_iff_vanishing_norm.mp hsum 1 one_pos
  -- Bound on finite sums over subsets of A₀
  have hne : (A₀.powerset.image fun B ↦ ‖b.proj' B x‖).Nonempty := by
    simp only [Finset.image_nonempty, Finset.powerset_nonempty]
  let M := (A₀.powerset.image fun B ↦ ‖b.proj' B x‖).sup' hne _root_.id
  use M + 1
  intro A
  -- Split A = (A ∩ A₀) ∪ (A \ A₀)
  have hdecomp : b.proj' A x = b.proj' (A ∩ A₀) x + b.proj' (A \ A₀) x := by
    simp only [SchauderBasis'.proj'_apply]
    have hdisj : Disjoint (A ∩ A₀) (A \ A₀) := by
      rw [Finset.disjoint_left]
      intro i hi
      simp only [Finset.mem_inter] at hi
      simp only [Finset.mem_sdiff, hi.2, not_true_eq_false, and_false, not_false_eq_true]
    rw [← Finset.sum_union hdisj]
    congr 1
    ext i
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  rw [hdecomp]
  -- The tail (A \ A₀) is small since it's disjoint from A₀
  have htail : ‖b.proj' (A \ A₀) x‖ < 1 := by
    rw [SchauderBasis'.proj'_apply]
    exact hA₀ (A \ A₀) (Finset.sdiff_disjoint)
  -- The head (A ∩ A₀) is bounded by M
  have hhead : ‖b.proj' (A ∩ A₀) x‖ ≤ M := by
    apply Finset.le_sup' (f := _root_.id)
    simp only [Finset.mem_image, Finset.mem_powerset]
    exact ⟨A ∩ A₀, Finset.inter_subset_right, rfl⟩
  calc ‖b.proj' (A ∩ A₀) x + b.proj' (A \ A₀) x‖
      ≤ ‖b.proj' (A ∩ A₀) x‖ + ‖b.proj' (A \ A₀) x‖ := norm_add_le _ _
    _ ≤ M + 1 := by linarith

/-- The basis constant for unconditional bases (supremum over all finite sets). -/
noncomputable def basisConstant' : ℝ≥0∞ := ⨆ A : Finset ℕ, ‖b.proj' A‖₊

/-- The basis constant is finite if there exists a uniform bound on projection norms. -/
theorem basisConstant'_lt_top_of_bound {C : ℝ} (hC : ∀ A : Finset ℕ, ‖b.proj' A‖ ≤ C) :
    b.basisConstant' < ⊤ := by
  rw [basisConstant', ENNReal.iSup_coe_lt_top, bddAbove_iff_exists_ge (0 : NNReal)]
  have hCpos : 0 ≤ C := by simpa [SchauderBasis'.proj'_empty] using hC ∅
  use C.toNNReal
  constructor
  · exact zero_le _
  · rintro _ ⟨A, rfl⟩
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal C hCpos, coe_nnnorm]
    exact hC A

/-- The basis constant is finite in a complete space for unconditional bases. -/
theorem basisConstant'_lt_top [CompleteSpace X] : b.basisConstant' < ⊤ := by
  obtain ⟨C, hC⟩ := b.proj'_uniform_bound
  exact b.basisConstant'_lt_top_of_bound hC

/-- The norm of any projection is bounded by the basis constant. -/
theorem norm_proj'_le_basisConstant' (A : Finset ℕ) : ‖b.proj' A‖₊ ≤ b.basisConstant' := by
  rw [basisConstant']
  exact le_iSup (fun A ↦ (‖b.proj' A‖₊ : ℝ≥0∞)) A

end UnconditionalSchauderBasis

/-! ### ℕ-indexed Schauder bases with conditional convergence -/

namespace SchauderBasis

variable (b : SchauderBasis 𝕜 X)

/-- The n-th canonical projection P_n = proj' (Finset.range n), given by:
    P_n x = ∑_{i < n} f_i(x) e_i -/
def proj (n : ℕ) : X →L[𝕜] X := b.proj' (Finset.range n)

/-- The canonical projection at 0 is the zero map. -/
@[simp]
theorem proj_zero : b.proj 0 = 0 := by simp only [proj, Finset.range_zero, b.proj'_empty]

/-- The action of the canonical projection on a vector x. -/
@[simp]
theorem proj_apply (n : ℕ) (x : X) : b.proj n x = ∑ i ∈ Finset.range n, b.coord i x • b i := by
  simp only [proj, b.proj'_apply]

/-- The action of the canonical projection on a basis element e i. -/
theorem proj_basis_element (n i : ℕ) : b.proj n (b i) = if i < n then b i else 0 := by
  simp only [proj, b.proj'_basis_element, Finset.mem_range]

/-- The range of the canonical projection is the span of the first n basis elements. -/
theorem range_proj (n : ℕ) : LinearMap.range (b.proj n).toLinearMap =
    Submodule.span 𝕜 (Set.range (fun i : Fin n => b i)) := by
  rw [proj, b.range_proj']
  congr 1
  ext x
  simp only [Set.mem_image, Finset.mem_coe, Finset.mem_range, Set.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact ⟨⟨i, hi⟩, rfl⟩
  · rintro ⟨i, rfl⟩; exact ⟨i, i.is_lt, rfl⟩

/-- The dimension of the range of the canonical projection `P n` is `n`. -/
theorem dim_range_proj (n : ℕ) :
    Module.finrank 𝕜 (LinearMap.range (b.proj n).toLinearMap) = n := by
  rw [range_proj, finrank_span_eq_card]
  · exact Fintype.card_fin n
  · exact b.linearIndependent.comp (fun (i : Fin n) => (i : ℕ)) Fin.val_injective

/-- The canonical projections converge pointwise to the identity map. -/
theorem proj_tendsto_id (x : X) : Tendsto (fun n ↦ b.proj n x) atTop (𝓝 x) := by
  have := b.proj'_tendsto_id x
  rw [SummationFilter.conditional_filter_eq_map_range] at this
  exact this

/-- Composition of canonical projections: `proj n (proj m x) = proj (min n m) x`. -/
theorem proj_comp (n m : ℕ) (x : X) : b.proj n (b.proj m x) = b.proj (min n m) x := by
  simp only [proj, b.proj'_comp, Finset.range_inter_range]

/-- The canonical projections are uniformly bounded (Banach-Steinhaus). -/
theorem proj_uniform_bound [CompleteSpace X] : ∃ C : ℝ, ∀ n : ℕ, ‖b.proj n‖ ≤ C := by
  apply banach_steinhaus
  intro x
  let f: ℕ → X := fun n => b.proj n x
  have : ∃ M : ℝ, ∀ x ∈ Set.range f, ‖x‖ ≤ M :=
      isBounded_iff_forall_norm_le.mp (Metric.isBounded_range_of_tendsto f (proj_tendsto_id b x ))
  rcases this with ⟨M, hM⟩
  rw [Set.forall_mem_range] at hM
  use M

/-- The basis constant is the supremum of the norms of the canonical projections. -/
def basisConstant : ℝ≥0∞ := ⨆ n, ‖b.proj n‖₊

/-- The basis constant is finite if there exists a bound on the norms of the projections. -/
theorem basisConstant_lt_top_uniform_bound {C : ℝ} (hC : ∀ n : ℕ, ‖b.proj n‖ ≤ C) :
    b.basisConstant < ⊤ := by
  rw [basisConstant, ENNReal.iSup_coe_lt_top, bddAbove_iff_exists_ge (0 : NNReal)]
  have hCpos : 0 ≤ C := by simpa [proj_zero] using hC 0
  use C.toNNReal
  constructor
  · exact zero_le _
  · rintro _ ⟨n, rfl⟩
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal C hCpos, coe_nnnorm]
    exact hC n

/-- The basis constant is finite in the complete space case. -/
theorem basisConstant_lt_top_for_complete [CompleteSpace X] : b.basisConstant < ⊤ := by
  obtain ⟨C, hC⟩ := b.proj_uniform_bound
  exact b.basisConstant_lt_top_uniform_bound hC

/-- The norm of any projection is bounded by the basis constant. -/
theorem norm_proj_le_basisConstant (n : ℕ) : ‖b.proj n‖₊ ≤ b.basisConstant := by
  rw [basisConstant]
  exact le_iSup (fun i ↦ (‖b.proj i‖₊ : ℝ≥0∞)) n

/-- The difference operator P_{n+1} - P_n. -/
def succ_sub (P : ℕ → X →L[𝕜] X) (n : ℕ) : X →L[𝕜] X := P (n + 1) - P n

/-- The sum of succ_sub operators up to n equals P n. -/
@[simp]
lemma succ_sub_sum (P : ℕ → X →L[𝕜] X) (h0 : P 0 = 0) (n : ℕ) :
∑ i ∈ Finset.range n, succ_sub P i = P n := by
  induction n with
  | zero => simp [h0]
  | succ n ih => rw [Finset.sum_range_succ, ih, succ_sub]; abel

/-- The operators `succ_sub P i` satisfy a biorthogonality relation. -/
lemma succ_sub_ortho {P : ℕ → X →L[𝕜] X} (hcomp : ∀ n m, ∀ x : X, P n (P m x) = P (min n m) x)
    (i j : ℕ) (x : X) :
    (succ_sub P i) (succ_sub P j x) = (Pi.single j (succ_sub P j x) : ℕ → X) i := by
  simp only [Pi.single_apply, succ_sub, ContinuousLinearMap.sub_apply, map_sub, hcomp,
    Nat.add_min_add_right]
  split_ifs with h
  · rw [h, min_self, min_eq_right (Nat.le_succ j), Nat.min_eq_left (Nat.le_succ j)]
    abel
  · rcases Nat.lt_or_gt_of_ne h with h' | h'
    · rw [min_eq_left_of_lt h', min_eq_left (Nat.succ_le_of_lt h'),
        min_eq_left_of_lt (Nat.lt_succ_of_lt h')]
      abel
    · rw [min_eq_right_of_lt h', min_eq_right (Nat.succ_le_of_lt h'),
        min_eq_right_of_lt (Nat.lt_succ_of_lt h')]
      abel

/-- The rank of `succ_sub P n` is `1`. -/
lemma succ_sub_rank_one {P : ℕ → X →L[𝕜] X}
    (h0 : P 0 = 0)
    (hrank : ∀ n, Module.finrank 𝕜 (LinearMap.range (P n).toLinearMap) = n)
    (hcomp : ∀ n m, ∀ x : X, P n (P m x) = P (min n m) x) (n : ℕ) :
    Module.finrank 𝕜 (LinearMap.range (succ_sub P n).toLinearMap) = 1 := by
  let Q := succ_sub P
  let U := LinearMap.range (Q n).toLinearMap
  let V := LinearMap.range (P n).toLinearMap
  have h_range_Pn_succ : LinearMap.range (P (n + 1)).toLinearMap = U ⊔ V := by
    apply le_antisymm
    · rintro x ⟨y, rfl⟩; rw [ContinuousLinearMap.coe_coe, ← sub_add_cancel (P (n + 1) y) (P n y)]
      exact Submodule.add_mem_sup (LinearMap.mem_range_self _ _) (LinearMap.mem_range_self _ _)
    · rw [sup_le_iff]
      have hV (y : X) : P n y ∈ LinearMap.range (P (n + 1)).toLinearMap := by
        use P n y
        rw [ContinuousLinearMap.coe_coe, hcomp (n + 1) n y, min_eq_right (Nat.le_succ n)]
      constructor
      · rintro x ⟨y, rfl⟩
        apply Submodule.sub_mem _ (LinearMap.mem_range_self _ _)
        dsimp only [ContinuousLinearMap.coe_coe]
        exact hV y
      · rintro x ⟨y, rfl⟩
        exact hV y
  have h_disjoint : U ⊓ V = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro x ⟨⟨y, rfl⟩, ⟨z, hz⟩⟩
    dsimp only [ContinuousLinearMap.coe_coe] at *
    have : Q n (P n z) = 0 := by
      simp_rw [Q, SchauderBasis.succ_sub, ContinuousLinearMap.sub_apply, hcomp,
        min_eq_right (Nat.le_succ n), min_self, sub_self]
    rw [← hz, ← this, hz, succ_sub_ortho hcomp, Pi.single_apply, if_pos rfl]
  have h_fin_Pn (n : ℕ) : FiniteDimensional 𝕜 (LinearMap.range (P n).toLinearMap) := by
    by_cases hn : n = 0
    · rw [hn]
      apply FiniteDimensional.of_rank_eq_zero
      apply Submodule.rank_eq_zero.mpr
      exact LinearMap.range_eq_bot.mpr (by simp only [h0, ContinuousLinearMap.coe_zero])
    apply FiniteDimensional.of_finrank_pos
    rw [hrank n]
    exact Nat.pos_of_ne_zero hn
  have : FiniteDimensional 𝕜 U := by
    have : U ≤ LinearMap.range (P (n+1)).toLinearMap := by
      simp only [U, Q, SchauderBasis.succ_sub]
      intro x ⟨y, hy⟩
      rw [← hy]
      apply Submodule.sub_mem _ (LinearMap.mem_range_self _ _)
      use P n y
      dsimp only [ContinuousLinearMap.coe_coe]
      rw [hcomp (n+1) n y, min_eq_right (Nat.le_succ n)]
    exact Submodule.finiteDimensional_of_le this
  have : FiniteDimensional 𝕜 V := by simp only [V]; exact h_fin_Pn n
  have := Submodule.finrank_sup_add_finrank_inf_eq U V
  rw [h_disjoint, finrank_bot, add_zero, ← h_range_Pn_succ, hrank, hrank, Nat.add_comm] at this
  exact Nat.add_right_cancel this.symm

variable (𝕜 X : Type*) [NontriviallyNormedField 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
structure ProjectionData where
  /-- The sequence of finite-rank projections. -/
  P : ℕ → X →L[𝕜] X
  /-- The sequence of candidate basis vectors. -/
  e : ℕ → X
  /-- The projections start at 0. -/
  proj_zero : P 0 = 0
  /-- The n-th projection has rank n. -/
  finrank_range : ∀ n, Module.finrank 𝕜 (LinearMap.range (P n).toLinearMap) = n
  /-- The projections commute and are nested (P_n P_m = P_{min n m}). -/
  hcomp : ∀ n m, ∀ x : X, P n (P m x) = P (min n m) x
  /-- The projections converge strongly to the identity. -/
  hlim : ∀ x, Tendsto (fun n ↦ P n x) atTop (𝓝 x)
  /-- The vector e_n lies in the range of the difference operator Q_n = P_{n+1} - P_n. -/
  he_in_range : ∀ n, e n ∈ LinearMap.range (succ_sub P n).toLinearMap
  /-- The vector e_n is non-zero. -/
  he_ne : ∀ n, e n ≠ 0

variable {𝕜 X}

namespace ProjectionData

/-- Specification: There exists a coefficient functional scaling `e n` to match `Q P n x`. -/
lemma exists_coeff (D : ProjectionData 𝕜 X) (n : ℕ) (x : X) :
    ∃ c : 𝕜, c • D.e n = (succ_sub D.P n) x := by
  let Q_n := (succ_sub D.P n).toLinearMap
  have h_rank : Module.finrank 𝕜 (LinearMap.range Q_n) = 1 :=
    succ_sub_rank_one D.proj_zero D.finrank_range D.hcomp n
  haveI : FiniteDimensional 𝕜 (LinearMap.range Q_n) :=
    FiniteDimensional.of_finrank_eq_succ (succ_sub_rank_one D.proj_zero D.finrank_range D.hcomp n)
  have h_span : LinearMap.range Q_n = Submodule.span 𝕜 {D.e n} := by
    symm
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact D.he_in_range n
    · rw [succ_sub_rank_one D.proj_zero D.finrank_range D.hcomp n,
        finrank_span_singleton (D.he_ne n)]
  have h_mem : Q_n x ∈ Submodule.span 𝕜 {D.e n} := by
    rw [← h_span]
    exact LinearMap.mem_range_self Q_n x
  exact Submodule.mem_span_singleton.mp h_mem

/-- Auxiliary Def: The coefficient functional value. -/
def basis_coeff (D : ProjectionData 𝕜 X) (n : ℕ) (x : X) : 𝕜 :=
  -- We pass the explicit arguments to the lemma
  Classical.choose (exists_coeff D n x)

/-- Specification: The coefficient satisfies the equation. -/
lemma basis_coeff_spec (D : ProjectionData 𝕜 X)
    (n : ℕ) (x : X) :
    basis_coeff D n x • D.e n = (succ_sub D.P n) x :=
  Classical.choose_spec (exists_coeff D n x)


/-- Main Definition: Constructs the Schauder basis from the projections. -/
def basis (D : ProjectionData 𝕜 X) : SchauderBasis 𝕜 X :=
  -- 1. Use our helper for the raw coefficient function
  let f_fun := basis_coeff D
  -- 2. Establish the key property locally for convenience
  have hQf : ∀ n x, (succ_sub D.P n) x = f_fun n x • D.e n := fun n x ↦
    (basis_coeff_spec D n x).symm
  -- 3. Construct the continuous linear functionals
  let f (n : ℕ) : StrongDual 𝕜 X := LinearMap.mkContinuous (IsLinearMap.mk' (f_fun n) (by
    constructor
    · intro x y; apply smul_left_injective 𝕜 (D.he_ne n); dsimp only [smul_eq_mul]
      rw [← hQf, map_add, add_smul, hQf, hQf]
    · intro c x; apply smul_left_injective 𝕜 (D.he_ne n); dsimp only [smul_eq_mul]
      rw [← hQf, map_smul, mul_smul, hQf]
    )) (‖succ_sub D.P n‖ / ‖D.e n‖) (by
      intro x; rw [div_mul_eq_mul_div, le_div_iff₀ (norm_pos_iff.mpr (D.he_ne n))]
      calc ‖f_fun n x‖ * ‖D.e n‖ = ‖f_fun n x • D.e n‖ := (norm_smul _ _).symm
        _ = ‖(succ_sub D.P n) x‖ := by rw [hQf]
        _ ≤ ‖succ_sub D.P n‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _)
  -- 4. Prove Biorthogonality
  have ortho : ∀ i j, f i (D.e j) = (Pi.single j (1 : 𝕜) : ℕ → 𝕜) i := by
    intro i j; apply smul_left_injective 𝕜 (D.he_ne i); dsimp only [smul_eq_mul]
    simp only [mkContinuous_apply, IsLinearMap.mk'_apply, Pi.single_apply, ite_smul, one_smul,
      zero_smul, f]
    have : (succ_sub D.P i) (D.e j) = (Pi.single j (D.e j) : ℕ → X) i := by
      obtain ⟨x, hx⟩ := D.he_in_range j
      rw [ContinuousLinearMap.coe_coe] at hx
      rw [← hx, succ_sub_ortho D.hcomp i j x]
    rw [← hQf, this, Pi.single_apply]
    split_ifs with hij
    · subst hij; simp only
    · simp only
  -- 5. Prove Basis Expansion
  have lim (x : X) : HasSum (fun i ↦ (f i) x • D.e i) x (SummationFilter.conditional ℕ) := by
    rw [HasSum, SummationFilter.conditional_filter_eq_map_range]
    apply Tendsto.congr _ (D.hlim x)
    intro n; simp_rw [f]; dsimp only [mkContinuous_apply, IsLinearMap.mk'_apply]
    simp_rw [← hQf, succ_sub]
    simp only [← succ_sub_sum D.P D.proj_zero n, ContinuousLinearMap.coe_sum', Finset.sum_apply]
    congr
  -- 6. Bundle it all up
  SchauderBasis'.mk D.e f ortho lim

/-- The projections of the constructed basis correspond to the input data P. -/
@[simp]
theorem basis_proj (D : ProjectionData 𝕜 X) : D.basis.proj = D.P := by
  ext n _
  rw [SchauderBasis.proj_apply, ← succ_sub_sum D.P D.proj_zero n]
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  dsimp [basis, mkContinuous_apply, IsLinearMap.mk'_apply]
  rw [D.basis_coeff_spec]

/-- The sequence of the constructed basis corresponds to the input data e. -/
@[simp]
theorem basis_coe (D : ProjectionData 𝕜 X) : ⇑D.basis = D.e :=
  rfl

end ProjectionData
end SchauderBasis
