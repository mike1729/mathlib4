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
# Schauder Bases and Generalized Bases

This file defines the theory of bases in Banach spaces, unifying the classical
sequential notion with modern generalized bases.

## Overview

A **basis** in a normed space allows every vector to be expanded as a
(potentially infinite) linear combination of basis vectors. Historically, this
was defined strictly for sequences $(x_n)_{n \in \mathbb{N}}$ with convergence
of partial sums (the "classical Schauder basis").

However, modern functional analysis requires bases indexed by arbitrary sets
$\beta$ (e.g., for non-separable spaces or Hilbert spaces), where convergence
is defined via nets over finite subsets (unconditional convergence).

This file provides a unified structure `GeneralSchauderBasis` that captures both:
* **Classical Schauder Bases:** Indexed by `ℕ`, using `SummationFilter.conditional`
  to enforce sequential convergence of partial sums.
* **Unconditional/Extended Bases:** Indexed by arbitrary types `β`, using
  `SummationFilter.unconditional` to enforce convergence of the net of all finite subsets.

## Main Definitions

* `GeneralSchauderBasis β 𝕜 X L`: A structure representing a generalized Schauder basis for a
  normed space `X` over a field `𝕜`, indexed by a type `β` with a `SummationFilter L`.
* `SchauderBasis 𝕜 X`: The classical Schauder basis, an abbreviation for
  `GeneralSchauderBasis ℕ 𝕜 X (SummationFilter.conditional ℕ)`.
* `UnconditionalSchauderBasis β 𝕜 X`: An unconditional Schauder basis, an abbreviation for
  `GeneralSchauderBasis β 𝕜 X (SummationFilter.unconditional β)`.
* `GeneralSchauderBasis.proj b A`: The projection onto a finite set `A` of basis vectors,
  defined as $P_A(x) = \sum_{i \in A} f_i(x)e_i$.
* `SchauderBasis.proj b n`: The $n$-th canonical projection $P_n: X \to X$,
  defined as $P_n(x) = \sum_{i < n} f_i(x)e_i$ (equals `proj (Finset.range n)`).
* `UnconditionalSchauderBasis.enormProjBound`: The supremum of projection norms (`ℝ≥0∞`).
* `UnconditionalSchauderBasis.normProjBound`: The supremum of projection norms (`ℝ≥0`,
  requires `CompleteSpace`).

## Main Results

* `GeneralSchauderBasis.linearIndependent`: A Schauder basis is linearly independent.
* `GeneralSchauderBasis.tendsto_proj`: The projections `proj A` converge to identity
  along the summation filter.
* `GeneralSchauderBasis.range_proj`: The range of `proj A` is the span of the basis
  elements in `A`.
* `GeneralSchauderBasis.proj_comp`: Composition of projections satisfies
  `proj A (proj B x) = proj (A ∩ B) x`.
* `SchauderBasis.proj_uniform_bound`: In a Banach space, the canonical projections
  are uniformly bounded (Banach-Steinhaus Theorem).
* `UnconditionalSchauderBasis.proj_uniform_bound`: For unconditional bases, projections
  onto *all* finite sets are uniformly bounded.
* `ProjectionData.basis`: Constructs a Schauder basis from projection data.

## References

* Albiac, F., & Kalton, N. J. (2016). *Topics in Banach Space Theory*.
* Singer, I. (1970). *Bases in Banach Spaces*.
-/

@[expose] public section

noncomputable section

open Filter Topology LinearMap Set ENNReal NNReal

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

open scoped Classical in
/--
A generalized Schauder basis indexed by `β` with summation along filter `L`.

The key fields are:
- `basis`: The basis vectors $(e_i)_{i \in \beta}$
- `coord`: The coordinate functionals $(f_i)_{i \in \beta}$ in the dual space
- `ortho`: Biorthogonality condition $f_i(e_j) = \delta_{ij}$
- `expansion`: Every $x$ equals $\sum_i f_i(x) e_i$, converging along `L`

See `SchauderBasis` for the classical ℕ-indexed case with conditional convergence,
and `UnconditionalSchauderBasis` for the unconditional case.
-/
structure GeneralSchauderBasis (β : Type*) (𝕜 : Type*)
  (X : Type*) [NontriviallyNormedField 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  (L : SummationFilter β) where
  /-- The basis vectors. -/
  basis : β → X
  /-- Coordinate functionals. -/
  coord : β → StrongDual 𝕜 X
  /-- Biorthogonality. -/
  ortho (i j : β) : coord i (basis j) = (Pi.single j (1 : 𝕜) : β → 𝕜) i
  /-- The sum converges to `x` along the provided `SummationFilter L`. -/
  expansion (x : X) : HasSum (fun i ↦ (coord i) x • basis i) x L

variable {β : Type*}
variable {L : SummationFilter β}

/-- A classical Schauder basis indexed by ℕ with conditional convergence. -/
abbrev SchauderBasis (𝕜 : Type*) (X : Type*) [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] :=
  GeneralSchauderBasis ℕ 𝕜 X (SummationFilter.conditional ℕ)

/--
An unconditional Schauder basis indexed by `β`.

In the literature, this is known as:
* An **Extended Basis** (Marti, 1969): Defined via convergence of the net of finite partial sums.
* An **Unconditional Basis** (Singer, 1981): On an arbitrary set, convergence is necessarily
  unconditional.

This structure generalizes the classical Schauder basis by replacing sequential
convergence with summability over the directed set of finite subsets.
-/
abbrev UnconditionalSchauderBasis (β : Type*)
    (𝕜 : Type*) (X : Type*) [NontriviallyNormedField 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X] :=
  GeneralSchauderBasis β 𝕜 X (SummationFilter.unconditional β)

/-- Coercion from a `GeneralSchauderBasis` to the underlying basis function. -/
instance : CoeFun (GeneralSchauderBasis β 𝕜 X L) (fun _ ↦ β → X) where
  coe b := b.basis

namespace GeneralSchauderBasis

variable (b : GeneralSchauderBasis β 𝕜 X L)

open scoped Classical in
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
def proj (A : Finset β) : X →L[𝕜] X := ∑ i ∈ A, (b.coord i).smulRight (b i)

/-- The canonical projection on the empty set is the zero map. -/
@[simp]
theorem proj_empty : b.proj ∅ = 0 := by simp [proj]

/-- The action of the projection on a vector x. -/
@[simp]
theorem proj_apply (A : Finset β) (x : X) : b.proj A x = ∑ i ∈ A, b.coord i x • b i := by
  simp only [proj, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply]

open scoped Classical in
/-- The action of the projection on a basis element e i. -/
theorem proj_apply_basis (A : Finset β) (i : β) : b.proj A (b i) = if i ∈ A then b i else 0 := by
  rw [proj_apply]
  by_cases hiA : i ∈ A
  · rw [Finset.sum_eq_single_of_mem i hiA]
    · simp only [b.ortho, Pi.single_apply, ↓reduceIte, one_smul, if_pos hiA]
    · intro j _ hji; rw [b.ortho j i, Pi.single_apply, if_neg hji, zero_smul]
  rw [if_neg hiA, Finset.sum_eq_zero]
  intro j hj
  rw [b.ortho j i, Pi.single_apply, if_neg, zero_smul]
  exact fun h => hiA (h ▸ hj)

/-- Projections converge to identity along the summation filter. -/
theorem tendsto_proj (x : X) : Tendsto (fun A ↦ b.proj A x) L.filter (𝓝 x) := by
  simp only [proj_apply]
  exact b.expansion x

/-- The range of the projection is the span of the basis elements in A. -/
theorem range_proj (A : Finset β) :
    LinearMap.range (b.proj A).toLinearMap = Submodule.span 𝕜 (b '' A) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    rw [ContinuousLinearMap.coe_coe, proj_apply]
    apply Submodule.sum_mem
    intros i hi
    apply Submodule.smul_mem
    apply Submodule.subset_span
    exact ⟨i, hi, rfl⟩
  · rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    use b i
    rw [ContinuousLinearMap.coe_coe, proj_apply_basis, if_pos (Finset.mem_coe.mp hi)]

open Classical in
/-- Composition of projections: `proj A (proj B x) = proj (A ∩ B) x`. -/
theorem proj_comp (A B : Finset β) (x : X) : b.proj A (b.proj B x) = b.proj (A ∩ B) x := by
  simp only [proj_apply, map_sum, map_smul]
  simp_rw [b.ortho, Pi.single_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
    smul_ite, smul_zero, Finset.sum_ite, Finset.sum_const_zero, add_zero]
  congr 1; ext i
  simp only [Finset.mem_filter, Finset.mem_inter, and_comm]

/-- The dimension of the range of the projection `proj A` equals the cardinality of `A`. -/
theorem finrank_range_proj (A : Finset β) :
    Module.finrank 𝕜 (LinearMap.range (b.proj A).toLinearMap) = A.card := by
  rw [range_proj, Set.image_eq_range, finrank_span_eq_card]
  · exact Fintype.card_coe A
  · exact b.linearIndependent.comp (fun i : A => i.val) Subtype.val_injective

end GeneralSchauderBasis

/-! ### ℕ-indexed Schauder bases with conditional convergence -/

namespace SchauderBasis

variable (b : SchauderBasis 𝕜 X)

/-- The n-th canonical projection P_n = proj (Finset.range n), given by:
    P_n x = ∑_{i < n} f_i(x) e_i -/
def proj (n : ℕ) : X →L[𝕜] X := GeneralSchauderBasis.proj b (Finset.range n)

/-- The canonical projection at 0 is the zero map. -/
@[simp]
theorem proj_zero : b.proj 0 = 0 := by
  simp only [proj, Finset.range_zero, GeneralSchauderBasis.proj_empty]

/-- The action of the canonical projection on a vector x. -/
@[simp]
theorem proj_apply (n : ℕ) (x : X) : b.proj n x = ∑ i ∈ Finset.range n, b.coord i x • b i := by
  simp only [proj, GeneralSchauderBasis.proj_apply]

/-- The action of the canonical projection on a basis element e i. -/
theorem proj_basis_element (n i : ℕ) : b.proj n (b i) = if i < n then b i else 0 := by
  simp only [proj, GeneralSchauderBasis.proj_apply_basis, Finset.mem_range]

/-- The projection `P_m` applied to a finite basis sum `∑_{i<n} a_i • e_i` with `m ≤ n`
    equals the truncated sum `∑_{i<m} a_i • e_i`. -/
theorem proj_sum_range (m n : ℕ) (a : ℕ → 𝕜) (hmn : m ≤ n) :
    b.proj m (∑ i ∈ Finset.range n, a i • b i) =
    ∑ i ∈ Finset.range m, a i • b i := by
  have : (Finset.range n).filter (fun j => j < m) = Finset.range m := by
    ext i; simp only [Finset.mem_filter, Finset.mem_range]; omega
  simp_rw [map_sum, map_smul, proj_basis_element, smul_ite,
    Finset.sum_ite, smul_zero, Finset.sum_const_zero, add_zero, this]

/-- The range of the canonical projection is the span of the first n basis elements. -/
theorem range_proj (n : ℕ) :
    LinearMap.range (b.proj n).toLinearMap = Submodule.span 𝕜 (b '' ↑(Finset.range n)) := by
  rw [proj, GeneralSchauderBasis.range_proj]

/-- The dimension of the range of the canonical projection `P n` is `n`. -/
theorem finrank_range_proj (n : ℕ) :
    Module.finrank 𝕜 (LinearMap.range (b.proj n).toLinearMap) = n := by
  rw [proj, GeneralSchauderBasis.finrank_range_proj, Finset.card_range]

/-- The canonical projections converge pointwise to the identity map. -/
theorem tendsto_proj (x : X) : Tendsto (fun n ↦ b.proj n x) atTop (𝓝 x) := by
  have := GeneralSchauderBasis.tendsto_proj b x
  rw [SummationFilter.conditional_filter_eq_map_range] at this
  exact this

/-- Composition of canonical projections: `proj n (proj m x) = proj (min n m) x`. -/
theorem proj_comp (n m : ℕ) (x : X) : b.proj n (b.proj m x) = b.proj (min n m) x := by
  simp only [proj, GeneralSchauderBasis.proj_comp]
  congr 2
  ext i
  simp only [Finset.mem_inter, Finset.mem_range]
  omega

/-- The canonical projections are uniformly bounded (Banach-Steinhaus). -/
theorem proj_uniform_bound [CompleteSpace X] : ∃ C : ℝ, ∀ n : ℕ, ‖b.proj n‖ ≤ C := by
  apply banach_steinhaus
  intro x
  let f : ℕ → X := fun n => b.proj n x
  have : ∃ M : ℝ, ∀ x ∈ Set.range f, ‖x‖ ≤ M :=
      isBounded_iff_forall_norm_le.mp (Metric.isBounded_range_of_tendsto f (tendsto_proj b x))
  rcases this with ⟨M, hM⟩
  rw [Set.forall_mem_range] at hM
  use M

/-- The basis constant for Schauder bases (supremum over canonical projections) as enorm. -/
noncomputable def enormProjBound : ℝ≥0∞ := ⨆ n, ‖b.proj n‖₊

/-- The norm of any projection is bounded by the basis constant (general case). -/
theorem norm_proj_le_enormProjBound (n : ℕ) : ‖b.proj n‖₊ ≤ b.enormProjBound := by
  rw [enormProjBound]
  exact le_iSup (fun i ↦ (‖b.proj i‖₊ : ℝ≥0∞)) n

/-- The basis constant for Schauder bases (supremum over canonical projections) as nnnorm.
    Requires completeness to guarantee the supremum is finite. -/
noncomputable def normProjBound : ℝ≥0 := ⨆ n, ‖b.proj n‖₊

/-- The projection norms are bounded above in a complete space (Banach-Steinhaus). -/
theorem normProjBound_bddAbove [CompleteSpace X] :
    BddAbove (Set.range (fun n : ℕ => ‖b.proj n‖₊)) := by
  obtain ⟨C, hC⟩ := b.proj_uniform_bound
  have hCpos : 0 ≤ C := by simpa [proj_zero] using hC 0
  refine ⟨C.toNNReal, ?_⟩
  rintro _ ⟨n, rfl⟩
  rw [← NNReal.coe_le_coe, Real.coe_toNNReal C hCpos, coe_nnnorm]
  exact hC n

/-- The norm of any projection is bounded by the basis constant. -/
theorem norm_proj_le_normProjBound [CompleteSpace X] (n : ℕ) :
    ‖b.proj n‖₊ ≤ b.normProjBound :=
  le_ciSup (normProjBound_bddAbove b) n

/-- If the projection norms are uniformly bounded by `C`, then `enormProjBound < ⊤`. -/
theorem enormProjBound_lt_top_of_bound {C : ℝ}
    (h : ∀ n, ‖b.proj n‖ ≤ C) : b.enormProjBound < ⊤ := by
  have hC : 0 ≤ C := by simpa [proj_zero] using h 0
  apply lt_of_le_of_lt _ ENNReal.ofReal_lt_top
  show (⨆ n, ‖b.proj n‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal C
  apply iSup_le
  intro n
  rw [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_le_ofReal_iff hC]
  simp only [coe_nnnorm]
  exact h n

/-!
### Construction of Schauder basis

We explain how to construct a Schauder basis from a sequence `P n` of projections
satisfying `P n ∘ P m = P (min n m)`, `P n → id` pointwise, and each
`P (n+1) - P n` has rank one. The idea is to define the basis vectors as
`e n = (P (n+1) - P n) x` for some `x` such that this is non-zero, and then
show that these vectors form a Schauder basis. -/

/-- The difference operator `P_{n+1} - P_n`. -/
def succSub (P : ℕ → X →L[𝕜] X) (n : ℕ) : X →L[𝕜] X := P (n + 1) - P n

/-- The sum of `succSub` operators up to `n` equals `P n`. -/
@[simp]
lemma succSub_sum (P : ℕ → X →L[𝕜] X) (h0 : P 0 = 0) (n : ℕ) :
    ∑ i ∈ Finset.range n, succSub P i = P n := by
  induction n with
  | zero => simp [h0]
  | succ n ih => rw [Finset.sum_range_succ, ih, succSub]; abel

/-- The operators `succSub P i` satisfy a biorthogonality relation. -/
lemma succSub_ortho {P : ℕ → X →L[𝕜] X} (hcomp : ∀ n m, ∀ x : X, P n (P m x) = P (min n m) x)
    (i j : ℕ) (x : X) :
    (succSub P i) (succSub P j x) = (Pi.single j (succSub P j x) : ℕ → X) i := by
  simp only [Pi.single_apply, succSub, ContinuousLinearMap.sub_apply, map_sub, hcomp,
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

/-- The rank of `succSub P n` is `1`. -/
lemma succSub_rank_one {P : ℕ → X →L[𝕜] X}
    (h0 : P 0 = 0)
    (hrank : ∀ n, Module.finrank 𝕜 (LinearMap.range (P n).toLinearMap) = n)
    (hcomp : ∀ n m, ∀ x : X, P n (P m x) = P (min n m) x) (n : ℕ) :
    Module.finrank 𝕜 (LinearMap.range (succSub P n).toLinearMap) = 1 := by
  let U := LinearMap.range (succSub P n).toLinearMap
  let V := LinearMap.range (P n).toLinearMap
  have hV (y : X) : P n y ∈ LinearMap.range (P (n + 1)).toLinearMap :=
    ⟨P n y, by rw [ContinuousLinearMap.coe_coe, hcomp, min_eq_right (Nat.le_succ n)]⟩
  have hUV : U ≤ LinearMap.range (P (n + 1)).toLinearMap := by
    rintro _ ⟨y, rfl⟩
    exact Submodule.sub_mem _ (LinearMap.mem_range_self _ _) (hV y)
  have hrange : LinearMap.range (P (n + 1)).toLinearMap = U ⊔ V := by
    apply le_antisymm
    · rintro x ⟨y, rfl⟩; rw [ContinuousLinearMap.coe_coe, ← sub_add_cancel (P (n + 1) y) (P n y)]
      exact Submodule.add_mem_sup (LinearMap.mem_range_self _ _) (LinearMap.mem_range_self _ _)
    · refine sup_le hUV ?_; rintro _ ⟨y, rfl⟩; exact hV y
  have hdisj : U ⊓ V = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro x ⟨⟨y, rfl⟩, ⟨z, hz⟩⟩
    dsimp only [ContinuousLinearMap.coe_coe] at *
    have : succSub P n (P n z) = 0 := by
      simp only [succSub, ContinuousLinearMap.sub_apply, hcomp, min_eq_right (Nat.le_succ n),
        min_self, sub_self]
    rw [← hz, ← this, hz, succSub_ortho hcomp, Pi.single_apply, if_pos rfl]
  have hfinPn (m : ℕ) : FiniteDimensional 𝕜 (LinearMap.range (P m).toLinearMap) := by
    rcases eq_or_ne m 0 with rfl | hm
    · apply FiniteDimensional.of_rank_eq_zero
      exact Submodule.rank_eq_zero.mpr (LinearMap.range_eq_bot.mpr (by simp [h0]))
    · exact .of_finrank_pos (by rw [hrank]; exact Nat.pos_of_ne_zero hm)
  haveI : FiniteDimensional 𝕜 U := Submodule.finiteDimensional_of_le hUV
  haveI : FiniteDimensional 𝕜 V := hfinPn n
  have := Submodule.finrank_sup_add_finrank_inf_eq U V
  rw [hdisj, finrank_bot, add_zero, ← hrange, hrank, hrank, Nat.add_comm] at this
  exact Nat.add_right_cancel this.symm

variable (𝕜 X) in
/-- Data for constructing a Schauder basis from a sequence of finite-rank projections. -/
structure ProjectionData where
  /-- The sequence of finite-rank projections. -/
  P : ℕ → X →L[𝕜] X
  /-- The sequence of candidate basis vectors. -/
  e : ℕ → X
  /-- The projections start at 0. -/
  projZero : P 0 = 0
  /-- The n-th projection has rank n. -/
  finrankRange (n : ℕ) : Module.finrank 𝕜 (LinearMap.range (P n).toLinearMap) = n
  /-- The projections commute and are nested (P_n P_m = P_{min n m}). -/
  hcomp (n m : ℕ) (x : X) : P n (P m x) = P (min n m) x
  /-- The projections converge strongly to the identity. -/
  hlim (x : X) : Tendsto (fun n ↦ P n x) atTop (𝓝 x)
  /-- The vector e_n lies in the range of the difference operator `succSub P n = P (n+1) - P n`. -/
  heInRange (n : ℕ) : e n ∈ LinearMap.range (succSub P n).toLinearMap
  /-- The vector e_n is non-zero. -/
  heNe (n : ℕ) : e n ≠ 0

namespace ProjectionData

/-- There exists a coefficient scaling `e n` to match `(succSub D.P n) x`. -/
lemma exists_coeff (D : ProjectionData 𝕜 X) (n : ℕ) (x : X) :
    ∃ c : 𝕜, c • D.e n = (succSub D.P n) x := by
  let succSubN := (succSub D.P n).toLinearMap
  have hrank : Module.finrank 𝕜 (LinearMap.range succSubN) = 1 :=
    succSub_rank_one D.projZero D.finrankRange D.hcomp n
  haveI : FiniteDimensional 𝕜 (LinearMap.range succSubN) :=
    FiniteDimensional.of_finrank_eq_succ (succSub_rank_one D.projZero D.finrankRange D.hcomp n)
  have hspan : LinearMap.range succSubN = Submodule.span 𝕜 {D.e n} := by
    symm
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact D.heInRange n
    · rw [succSub_rank_one D.projZero D.finrankRange D.hcomp n,
        finrank_span_singleton (D.heNe n)]
  have hmem : succSubN x ∈ Submodule.span 𝕜 {D.e n} := by
    rw [← hspan]
    exact LinearMap.mem_range_self succSubN x
  exact Submodule.mem_span_singleton.mp hmem

/-- The coefficient functional value for the basis construction. -/
def basisCoeff (D : ProjectionData 𝕜 X) (n : ℕ) (x : X) : 𝕜 :=
  Classical.choose (exists_coeff D n x)

/-- The coefficient satisfies `basisCoeff D n x • D.e n = (succSub D.P n) x`. -/
lemma basisCoeff_spec (D : ProjectionData 𝕜 X) (n : ℕ) (x : X) :
    basisCoeff D n x • D.e n = (succSub D.P n) x :=
  Classical.choose_spec (exists_coeff D n x)

/-- Constructs a Schauder basis from projection data. -/
def basis (D : ProjectionData 𝕜 X) : SchauderBasis 𝕜 X :=
  let coeff := basisCoeff D
  have hcoeff : ∀ n x, (succSub D.P n) x = coeff n x • D.e n := fun n x ↦
    (basisCoeff_spec D n x).symm
  { basis := D.e
    coord := fun n ↦ LinearMap.mkContinuous
      (IsLinearMap.mk' (coeff n) ⟨
        fun x y => by
          apply smul_left_injective 𝕜 (D.heNe n); dsimp only [smul_eq_mul]
          rw [← hcoeff, map_add, add_smul, hcoeff, hcoeff],
        fun c x => by
          apply smul_left_injective 𝕜 (D.heNe n); dsimp only [smul_eq_mul]
          rw [← hcoeff, map_smul, mul_smul, hcoeff]⟩)
      (‖succSub D.P n‖ / ‖D.e n‖)
      (fun x => by
        rw [div_mul_eq_mul_div, le_div_iff₀ (norm_pos_iff.mpr (D.heNe n))]
        calc ‖coeff n x‖ * ‖D.e n‖ = ‖coeff n x • D.e n‖ := (norm_smul _ _).symm
          _ = ‖(succSub D.P n) x‖ := by rw [hcoeff]
          _ ≤ ‖succSub D.P n‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _)
    ortho := fun i j => by
      apply smul_left_injective 𝕜 (D.heNe i); dsimp only [smul_eq_mul]
      simp only [mkContinuous_apply, IsLinearMap.mk'_apply, Pi.single_apply, ite_smul, one_smul,
        zero_smul]
      have : (succSub D.P i) (D.e j) = (Pi.single j (D.e j) : ℕ → X) i := by
        obtain ⟨x, hx⟩ := D.heInRange j
        rw [ContinuousLinearMap.coe_coe] at hx
        rw [← hx, succSub_ortho D.hcomp i j x]
      rw [← hcoeff, this, Pi.single_apply]
      split_ifs with hij <;> simp [hij]
    expansion := fun x => by
      rw [HasSum, SummationFilter.conditional_filter_eq_map_range]
      apply Tendsto.congr _ (D.hlim x)
      intro n; dsimp only [mkContinuous_apply, IsLinearMap.mk'_apply]
      simp_rw [← hcoeff, succSub]
      simp only [← succSub_sum D.P D.projZero n, ContinuousLinearMap.coe_sum', Finset.sum_apply]
      congr }

/-- The projections of the constructed basis correspond to the input data P. -/
@[simp]
theorem basis_proj (D : ProjectionData 𝕜 X) : D.basis.proj = D.P := by
  ext n _
  rw [SchauderBasis.proj_apply, ← succSub_sum D.P D.projZero n]
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  dsimp [basis, mkContinuous_apply, IsLinearMap.mk'_apply]
  rw [D.basisCoeff_spec]

/-- The sequence of the constructed basis corresponds to the input data e. -/
@[simp]
theorem basis_coe (D : ProjectionData 𝕜 X) : ⇑D.basis = D.e :=
  rfl

end ProjectionData
end SchauderBasis

/-! ### Unconditional Schauder bases -/

namespace UnconditionalSchauderBasis

variable (b : UnconditionalSchauderBasis ℕ 𝕜 X)

def toSchauderBasis : SchauderBasis 𝕜 X := {
  basis := b.basis
  coord := b.coord
  ortho := b.ortho
  expansion := fun x => (b.expansion x).mono_left SummationFilter.le_atTop
}

variable (b : UnconditionalSchauderBasis β 𝕜 X)

/-- The basis constant for unconditional bases (supremum over all finite sets) as enorm. -/
noncomputable def enormProjBound : ℝ≥0∞ := ⨆ A : Finset β, ‖b.proj A‖ₑ

/-- The norm of any projection is bounded by the basis constant (general case). -/
theorem norm_proj_le_enormProjBound (A : Finset β) : ‖b.proj A‖ₑ ≤ b.enormProjBound := by
  rw [enormProjBound]
  exact le_iSup (fun A ↦ ‖b.proj A‖ₑ) A

open scoped Classical in
/-- Projections are uniformly bounded for unconditional bases (Banach-Steinhaus). -/
theorem proj_uniform_bound [CompleteSpace X] : ∃ C : ℝ, ∀ A : Finset β, ‖b.proj A‖ ≤ C := by
  apply banach_steinhaus
  intro x
  have hsum : Summable (fun i ↦ b.coord i x • b i) := b.expansion x |>.summable
  obtain ⟨A₀, hA₀⟩ := summable_iff_vanishing_norm.mp hsum 1 one_pos
  have hne : (A₀.powerset.image fun B ↦ ‖b.proj B x‖).Nonempty := by
    simp only [Finset.image_nonempty, Finset.powerset_nonempty]
  let M := (A₀.powerset.image fun B ↦ ‖b.proj B x‖).sup' hne id
  use M + 1
  intro A
  -- Split A = (A ∩ A₀) ∪ (A \ A₀)
  have hdecomp : b.proj A x = b.proj (A ∩ A₀) x + b.proj (A \ A₀) x := by
    simp only [GeneralSchauderBasis.proj_apply]
    have hdisj : Disjoint (A ∩ A₀) (A \ A₀) := by
      rw [Finset.disjoint_left]; intro i hi
      simp only [Finset.mem_inter] at hi
      simp only [Finset.mem_sdiff, hi.2, not_true_eq_false, and_false, not_false_eq_true]
    rw [← Finset.sum_union hdisj]
    congr 1; ext i; simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]; tauto
  rw [hdecomp]
  -- The tail (A \ A₀) is small since it's disjoint from A₀
  have htail : ‖b.proj (A \ A₀) x‖ < 1 := by
    rw [GeneralSchauderBasis.proj_apply]
    exact hA₀ (A \ A₀) (Finset.sdiff_disjoint)
  -- The head (A ∩ A₀) is bounded by M
  have hhead : ‖b.proj (A ∩ A₀) x‖ ≤ M := by
    apply Finset.le_sup' (f := _root_.id)
    simp only [Finset.mem_image, Finset.mem_powerset]
    exact ⟨A ∩ A₀, Finset.inter_subset_right, rfl⟩
  calc ‖b.proj (A ∩ A₀) x + b.proj (A \ A₀) x‖
      ≤ ‖b.proj (A ∩ A₀) x‖ + ‖b.proj (A \ A₀) x‖ := norm_add_le _ _
    _ ≤ M + 1 := by linarith

/-- The basis constant for unconditional bases (supremum over all finite sets) as nnnorm.
    Requires completeness to guarantee the supremum is finite. -/
noncomputable def normProjBound : ℝ≥0 := ⨆ A : Finset β, ‖b.proj A‖₊

/-- The projection norms are bounded above in a complete space (Banach-Steinhaus). -/
theorem normProjBound_bddAbove [CompleteSpace X] :
    BddAbove (Set.range (fun A : Finset β => ‖b.proj A‖₊)) := by
  obtain ⟨C, hC⟩ := b.proj_uniform_bound
  have hCpos : 0 ≤ C := by simpa [GeneralSchauderBasis.proj_empty] using hC ∅
  refine ⟨C.toNNReal, ?_⟩
  rintro _ ⟨A, rfl⟩
  rw [← NNReal.coe_le_coe, Real.coe_toNNReal C hCpos, coe_nnnorm]
  exact hC A

/-- The norm of any projection is bounded by the basis constant. -/
theorem norm_proj_le_normProjBound [CompleteSpace X] (A : Finset β) :
    ‖b.proj A‖₊ ≤ b.normProjBound :=
  le_ciSup (normProjBound_bddAbove b) A

variable (b : UnconditionalSchauderBasis ℕ 𝕜 X)

/-- The Schauder basis constant of `toSchauderBasis` is bounded by the unconditional constant. -/
theorem toSchauderBasis_enormProjBound_le :
    b.toSchauderBasis.enormProjBound ≤ b.enormProjBound := by
  simp only [SchauderBasis.enormProjBound, enormProjBound, SchauderBasis.proj, toSchauderBasis]
  apply iSup_le fun n => ?_
  exact le_iSup (fun A => ‖GeneralSchauderBasis.proj b A‖ₑ) (Finset.range n)

end UnconditionalSchauderBasis
