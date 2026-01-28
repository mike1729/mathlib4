/-
Copyright (c) 2025 Michał Świętek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michał Świętek
-/
module

public import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Schauder bases in normed spaces

This file defines Schauder bases in a normed space and develops their basic theory.

## Main definitions

* `SchauderBasis 𝕜 X e`: A structure representing a Schauder basis for a normed space `X`
  over a field `𝕜`, where `e : ℕ → X` is the sequence of basis vectors.
  It includes:
  - `coord`: The sequence of coordinate functionals (elements of the dual space).
  - `ortho`: The biorthogonality condition $f_i(e_j) = \delta_{ij}$.
  - `basis_expansion`: The requirement that for every $x \in X$, the series
    $\sum_{n=0}^\infty f_n(x)e_n$ converges to $x$.

* `SchauderBasis.proj b n`: The $n$-th canonical projection $P_n: X \to X$ associated
  with the basis `b`, defined as $P_n(x) = \sum_{i < n} f_i(x)e_i$.

* `SchauderBasis.basisConstant`: The supremum of the norms of the canonical projections
  (often called the "basis constant").

## Main results

* `SchauderBasis.linearIndependent`: A Schauder basis is linearly independent.
* `SchauderBasis.proj_tendsto_id`: The canonical projections $P_n$ converge pointwise
  to the identity operator.
* `SchauderBasis.proj_uniform_bound`: In a Banach space, the canonical projections
  are uniformly bounded (a consequence of the Banach-Steinhaus Theorem).
* `SchauderBasis.basis_of_canonical_projections`: A criterion to construct a Schauder
  basis from a sequence of projections satisfying certain rank, composition, and
  convergence properties.

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

/-- A Schauder basis is a sequence (e n) of vectors in X such that there exists a sequence of
    continuous linear functionals (f n) (the coordinate functionals) satisfying:
    1) f i (e j) = δ_{ij}
    2) for every x : X, the series ∑_{n=0}^∞ f n (x) e n converges to x.

    In other words, every vector in X can be uniquely represented as a convergent series of basis
    vectors, with coefficients given by the coordinate functionals. -/
structure SchauderBasis (𝕜 : Type*) {X : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] (e : ℕ → X) where
  /-- Coordinate functionals -/
  coord : ℕ → StrongDual 𝕜 X
  /-- Biorthogonality -/
  ortho : ∀ i j, coord i (e j) = (Pi.single j (1 : 𝕜) : ℕ → 𝕜) i
  /-- Convergence of partial sums -/
  basis_expansion : ∀ x : X, HasSum (fun i ↦ (coord i) x • e i) x (SummationFilter.conditional ℕ)

namespace SchauderBasis

variable {e : ℕ → X} (b : SchauderBasis 𝕜 e)

/-- The basis vectors are linearly independent. -/
theorem linearIndependent (h : SchauderBasis 𝕜 e) : LinearIndependent 𝕜 e := by
  rw [linearIndependent_iff]
  intro l hl
  ext i
  have hsum : ∑ i ∈ l.support, l i • e i = 0 := hl
  -- Apply the i-th coordinate functional to the linear combination
  have happ : h.coord i (∑ j ∈ l.support, l j • e j) = 0 := by rw [hsum, map_zero]
  rw [map_sum] at happ
  simp_rw [ContinuousLinearMap.map_smul] at happ
  rw [Finset.sum_eq_single i, h.ortho i i] at happ
  · simpa using happ
  · intro j _ hji; rw [h.ortho i j, Pi.single_apply, if_neg hji.symm, smul_eq_mul, mul_zero]
  · intro hi; simp only [Finsupp.notMem_support_iff.mp hi, smul_eq_mul, zero_mul]

/-- A canonical projection P_n associated to a Schauder basis given by coordinate functionals f_i:
    P_n x = ∑_{i < n} f_i(x) e_i -/
def proj (n : ℕ) : X →L[𝕜] X := ∑ i ∈ Finset.range n, (b.coord i).smulRight (e i)

/-- The canonical projection at 0 is the zero map. -/
@[simp]
theorem proj_zero : b.proj 0 = 0 := by
  simp only [proj, Finset.range_zero, Finset.sum_empty]

/-- The action of the canonical projection on a vector x. -/
@[simp]
theorem proj_apply (n : ℕ) (x : X) : b.proj n x = ∑ i ∈ Finset.range n, b.coord i x • e i := by
  simp only [proj, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply]

/-- The action of the canonical projection on a basis element e i. -/
theorem proj_basis_element (n i : ℕ) : b.proj n (e i) = if i < n then e i else 0 := by
  rw [proj_apply]
  by_cases hin : i < n
  · rw [Finset.sum_eq_single_of_mem i (Finset.mem_range.mpr hin)]
    · simp only [b.ortho, Pi.single_apply, ↓reduceIte, one_smul, if_pos hin]
    · intro j _ hji; rw [b.ortho j i, Pi.single_apply, if_neg hji, zero_smul]
  rw [if_neg hin, Finset.sum_eq_zero]
  intro j hj
  push_neg at hin
  rw [b.ortho j i, Pi.single_apply, if_neg , zero_smul]
  exact (Finset.mem_range.mp hj).trans_le hin |>.ne

/-- The range of the canonical projection is the span of the first n basis elements. -/
theorem range_proj (n : ℕ) : LinearMap.range (b.proj n).toLinearMap =
    Submodule.span 𝕜 (Set.range (fun i : Fin n => e i)) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    rw [ContinuousLinearMap.coe_coe, proj_apply b]
    apply Submodule.sum_mem
    intros i hi
    apply Submodule.smul_mem
    apply Submodule.subset_span
    exact ⟨⟨i, Finset.mem_range.mp hi⟩, rfl⟩
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    use e i
    rw [ContinuousLinearMap.coe_coe, proj_basis_element , if_pos i.is_lt]

/-- The dimension of the range of the canonical projection `P n` is `n`. -/
theorem dim_range_proj (n : ℕ) :
    Module.finrank 𝕜 (LinearMap.range (b.proj n).toLinearMap) = n := by
  rw [range_proj, finrank_span_eq_card]
  · exact Fintype.card_fin n
  · exact b.linearIndependent.comp (fun (i : Fin n) => (i : ℕ)) Fin.val_injective

/-- The canonical projections converge pointwise to the identity map. -/
theorem proj_tendsto_id (x : X) : Tendsto (fun n ↦ b.proj n x) atTop (𝓝 x) := by
  simp only [proj_apply]
  have := b.basis_expansion x
  rw [HasSum, SummationFilter.conditional_filter_eq_map_range] at this
  exact this

/-- Composition of canonical projections: `proj n (proj m x) = proj (min n m) x`. -/
theorem proj_comp (n m : ℕ) (x : X) : b.proj n (b.proj m x) = b.proj (min n m) x := by
  simp only [proj_apply, map_sum, map_smul]
  have h_ortho : ∀ i j, (b.coord i) (e j) = if i = j then 1 else 0 := by
    intro i j
    rw [b.ortho i j, Pi.single_apply]
  simp_rw [h_ortho]
  simp only [ite_smul, one_smul, zero_smul]
  simp_rw [Finset.sum_ite_eq', Finset.mem_range]
  simp only [smul_ite, smul_zero]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range, and_comm]
  exact Nat.lt_min.symm

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
def basisConstant : ℝ≥0∞ := ⨆ n, (‖b.proj n‖₊ : ℝ≥0∞)

-- /-- The basis constant is finite. -/
theorem basisConstant_lt_top_for_complete [CompleteSpace X] : b.basisConstant < ⊤ := by
  rw [basisConstant, ENNReal.iSup_coe_lt_top, bddAbove_iff_exists_ge (0 : NNReal)]
  obtain ⟨C, hC⟩ := b.proj_uniform_bound
  have hCpos : 0 ≤ C := by simpa [proj_zero] using hC 0
  use C.toNNReal
  constructor
  · exact zero_le _
  · rintro _ ⟨n, rfl⟩
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal C hCpos, coe_nnnorm]
    exact hC n

/-- The norm of any projection is bounded by the basis constant (as a real number). -/
theorem norm_proj_le_basisConstant (n : ℕ) : (‖b.proj n‖₊ : ℝ≥0∞) ≤ b.basisConstant := by
  rw [basisConstant]
  exact le_iSup (fun i ↦ (‖b.proj i‖₊ : ℝ≥0∞)) n

/-- `Q_n = P_{n+1} - P_n`. -/
def Q (P : ℕ → X →L[𝕜] X) (n : ℕ) : X →L[𝕜] X := P (n + 1) - P n

/-- The sum of Q i over i < n equals P n. -/
@[simp]
lemma Q_sum (P : ℕ → X →L[𝕜] X) (h0 : P 0 = 0) (n : ℕ) : ∑ i ∈ Finset.range n, Q P i = P n := by
  induction n with
  | zero => simp [h0]
  | succ n ih => rw [Finset.sum_range_succ, ih, Q]; abel

/-- The operators `Q i` are orthogonal projections. -/
lemma Q_ortho {P : ℕ → X →L[𝕜] X} (hcomp : ∀ n m, ∀ x : X, P n (P m x) = P (min n m) x)
    (i j : ℕ) (x : X) : (Q P i) (Q P j x) = (Pi.single j (Q P j x) : ℕ → X) i := by
  simp only [Pi.single_apply, Q, ContinuousLinearMap.sub_apply, map_sub, hcomp,
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

/-- The rank of `Q n` is `1`. -/
lemma Q_rank_one {P : ℕ → X →L[𝕜] X}
    (h0 : P 0 = 0)
    (hrank : ∀ n, Module.finrank 𝕜 (LinearMap.range (P n).toLinearMap) = n)
    (hcomp : ∀ n m, ∀ x : X, P n (P m x) = P (min n m) x) (n : ℕ) :
    Module.finrank 𝕜 (LinearMap.range (Q P n).toLinearMap) = 1 := by
  let Q := Q P
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
      simp_rw [Q, SchauderBasis.Q, ContinuousLinearMap.sub_apply, hcomp,
        min_eq_right (Nat.le_succ n), min_self, sub_self]
    rw [← hz, ← this, hz, Q_ortho hcomp, Pi.single_apply, if_pos rfl]
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
      simp only [U, Q, SchauderBasis.Q]
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

/-- Constructs a Schauder basis from a sequence of projections. -/
def basis_of_canonical_projections {P : ℕ → X →L[𝕜] X} {e : ℕ → X} (h0 : P 0 = 0)
    (hdim : ∀ n, Module.finrank 𝕜 (LinearMap.range (P n).toLinearMap) = n)
    (hcomp : ∀ n m, ∀ x : X, P n (P m x) = P (min n m) x)
    (hlim : ∀ x, Tendsto (fun n ↦ P n x) atTop (𝓝 x))
    (he_in_range : ∀ n, e n ∈ LinearMap.range (Q P n).toLinearMap) (he_ne : ∀ n, e n ≠ 0) :
    SchauderBasis 𝕜 e :=
  let Q := Q P
  have hrankQ := Q_rank_one h0 hdim hcomp
  have h_range_eq_span (n : ℕ) : LinearMap.range (Q n).toLinearMap = Submodule.span 𝕜 {e n} := by
    symm
    have : FiniteDimensional 𝕜 ↥(LinearMap.range (Q n).toLinearMap) := by
      apply FiniteDimensional.of_finrank_pos
      rw [hrankQ n]
      exact Nat.succ_pos 0
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact he_in_range n
    · rw [hrankQ n, finrank_span_singleton (he_ne n)]
  let f_fun : ℕ → X → 𝕜 := fun n x =>
    Classical.choose (Submodule.mem_span_singleton.mp (by
      rw [← h_range_eq_span]
      exact LinearMap.mem_range_self (Q n).toLinearMap x))
  have hQf (n : ℕ) (x : X) : Q n x = f_fun n x • e n :=
    (Classical.choose_spec (Submodule.mem_span_singleton.mp (by
      rw [← h_range_eq_span]
      exact LinearMap.mem_range_self (Q n).toLinearMap x))).symm
  let f (n : ℕ) : StrongDual 𝕜 X := LinearMap.mkContinuous (IsLinearMap.mk' (f_fun n) (by
    constructor
    · intro x y; apply smul_left_injective 𝕜 (he_ne n); dsimp only [smul_eq_mul];
      rw [← hQf, map_add, add_smul, hQf, hQf]
    · intro c x; apply smul_left_injective 𝕜 (he_ne n);dsimp  only [smul_eq_mul];
      rw [← hQf, map_smul, mul_smul, hQf]
    )) (‖Q n‖ / ‖e n‖) (by
      intro x; rw [div_mul_eq_mul_div, le_div_iff₀ (norm_pos_iff.mpr (he_ne n))]
      calc ‖f_fun n x‖ * ‖e n‖ = ‖f_fun n x • e n‖ := (norm_smul _ _).symm
        _ = ‖Q n x‖ := by rw [hQf]
        _ ≤ ‖Q n‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _)
  have ortho : ∀ i j, f i (e j) = (Pi.single j (1 : 𝕜) : ℕ → 𝕜) i := by
    intro i j
    apply smul_left_injective 𝕜 (he_ne i)
    dsimp only [smul_eq_mul]
    simp only [mkContinuous_apply, IsLinearMap.mk'_apply, Pi.single_apply, ite_smul, one_smul,
      zero_smul, f]
    have : Q i (e j) = (Pi.single j (e j) : ℕ → X) i := by
      obtain ⟨x, hx⟩ := he_in_range j
      rw [ContinuousLinearMap.coe_coe] at hx
      rw [← hx, Q_ortho hcomp i j x]
    rw [← hQf, this, Pi.single_apply]
    split_ifs with hij
    · subst hij; simp only
    · simp only
  have lim (x : X) : HasSum (fun i ↦ (f i) x • e i) x (SummationFilter.conditional ℕ) := by
    rw [HasSum, SummationFilter.conditional_filter_eq_map_range]
    apply Tendsto.congr _ (hlim x)
    intro n
    simp_rw [f]
    dsimp only [mkContinuous_apply, IsLinearMap.mk'_apply]
    simp_rw [← hQf, Q]
    simp only [← Q_sum P h0 n, ContinuousLinearMap.coe_sum', Finset.sum_apply]
  SchauderBasis.mk f ortho lim





/-- If `b` is a Schauder basis for a submodule `Y` with uniformly bounded projections,
    it extends to a Schauder basis for the closure of `Y`. -/
def SchauderBasis_of_closure [CompleteSpace 𝕜] [CompleteSpace X] {Y : Submodule 𝕜 X} {e : ℕ → Y}
    (b : SchauderBasis 𝕜 e) (h_bound : ∃ C, ∀ n, ‖b.proj n‖ ≤ C) :
    SchauderBasis 𝕜 (fun n ↦ (⟨e n, Y.le_topologicalClosure (e n).2⟩ :
      Y.topologicalClosure)) := by
  -- Let Z be the closure of Y. It is a Banach space.
  let Z := Y.topologicalClosure
  haveI : CompleteSpace Z := Submodule.topologicalClosure.completeSpace Y
  -- The embedding of Y into Z (inclusion is norm-preserving since both have subspace norm).
  let inc : Y →L[𝕜] Z := (Submodule.inclusion Y.le_topologicalClosure).mkContinuous 1 (fun y => by
    simp only [one_mul, Submodule.coe_norm, Submodule.coe_inclusion, le_refl])

  -- inc is an isometry (both norms are inherited from X)
  have h_isometry : Isometry inc := fun y₁ y₂ => by
    simp only [inc, edist_dist, dist_eq_norm]
    congr 1

  -- inc has dense range (Y is dense in its topological closure)
  have h_dense : DenseRange inc := by
    rw [DenseRange, dense_iff_closure_eq]
    apply Set.eq_univ_of_forall
    intro z
    rw [mem_closure_iff_nhds]
    intro U hU
    -- U is a neighborhood of z in Z, find y : Y with inc y ∈ U
    rw [mem_nhds_iff] at hU
    obtain ⟨V, hVU, hVopen, hzV⟩ := hU
    -- V is open in Z, so V = W ∩ Z for some open W in X
    rw [isOpen_induced_iff] at hVopen
    obtain ⟨W, hWopen, rfl⟩ := hVopen
    -- z ∈ W and z ∈ closure Y (since z ∈ Z)
    have hz_closure : (z : X) ∈ closure (Y : Set X) := z.2
    rw [mem_closure_iff_nhds] at hz_closure
    have hW_nhd : W ∈ 𝓝 (z : X) := hWopen.mem_nhds hzV
    obtain ⟨x, hxW, hxY⟩ := hz_closure W hW_nhd
    exact ⟨inc ⟨x, hxY⟩, hVU hxW, ⟨x, hxY⟩, rfl⟩

  -- inc is uniform inducing (since it's an isometry)
  have h_unif : IsUniformInducing inc := h_isometry.isUniformInducing

  -- 1. Define the sequence of projections P' on Z by extending P ∘ inc.
  -- We view b.proj n as a map Y → Z and extend it to Z → Z.
  let P' : ℕ → Z →L[𝕜] Z := fun n ↦ (inc ∘L b.proj n).extend inc

  -- 2. Define the basis vectors in Z.
  let e' : ℕ → Z := fun n ↦ ⟨e n, Y.le_topologicalClosure (e n).2⟩

  -- Helper: P' agrees with b.proj on Y
  have h_agree (n : ℕ) (y : Y) : P' n (inc y) = inc (b.proj n y) := by
    simp only [P']
    rw [ContinuousLinearMap.extend_eq (e := inc) (inc ∘L b.proj n) h_dense h_unif y]
    rfl

  -- Helper: P' n is uniformly bounded
  -- The norm of the extension equals the norm of the original map since inc is an isometry.
  -- inc has norm 1 (isometry), so ‖P' n‖ = ‖inc ∘ proj n‖ ≤ ‖inc‖ * ‖proj n‖ = ‖proj n‖ ≤ C
  have h_uniform : ∃ C, ∀ n, ‖P' n‖ ≤ C := by
    obtain ⟨C, hC⟩ := h_bound
    refine ⟨C, fun n => ?_⟩
    simp only [P']
    -- Use: ‖f.extend e‖ ≤ N * ‖f‖ when ‖x‖ ≤ N * ‖e x‖
    -- For isometry, ‖y‖ = ‖inc y‖, so N = 1
    have h_norm_eq : ∀ y, ‖inc y‖ = ‖y‖ :=
      AddMonoidHomClass.isometry_iff_norm inc |>.mp h_isometry
    have h_bound_inc : ∀ y, ‖y‖ ≤ (1 : NNReal) * ‖inc y‖ := fun y => by
      simp only [NNReal.coe_one, one_mul, h_norm_eq, le_refl]
    calc ‖(inc ∘L b.proj n).extend inc‖
        ≤ 1 * ‖inc ∘L b.proj n‖ := ContinuousLinearMap.opNorm_extend_le _ h_dense h_bound_inc
      _ = ‖inc ∘L b.proj n‖ := one_mul _
      _ ≤ ‖inc‖ * ‖b.proj n‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * ‖b.proj n‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          exact ContinuousLinearMap.opNorm_le_of_lipschitz h_isometry.lipschitz
      _ = ‖b.proj n‖ := one_mul _
      _ ≤ C := hC n

  exact basis_of_canonical_projections (P := P') (e := e')
    (by -- h0: P' 0 = 0
        simp only [P']
        -- b.proj 0 = 0, so inc ∘L b.proj 0 = 0, and extend of 0 is 0
        have h_proj0 : b.proj 0 = 0 := by ext x; simp [proj_apply, Finset.range_zero]
        simp only [h_proj0, ContinuousLinearMap.comp_zero,
          ContinuousLinearMap.extend_zero h_dense h_unif])
    (by -- hdim: dim(range(P' n)) = n
        intro n
        -- The range of P' n equals the span of {e' 0, ..., e' (n-1)}
        have h_range_eq : LinearMap.range (P' n).toLinearMap =
            Submodule.span 𝕜 (Set.range (fun i : Fin n => e' i)) := by
          apply le_antisymm
          · -- Range P' n ⊆ span {e' i | i < n}
            intro z hz
            obtain ⟨w, rfl⟩ := hz
            -- The span is finite-dimensional, hence closed
            let S := Submodule.span 𝕜 (Set.range (fun i : Fin n => e' i))
            haveI : FiniteDimensional 𝕜 S := FiniteDimensional.span_of_finite 𝕜 (Set.finite_range _)
            have hS_closed : IsClosed (S : Set Z) := Submodule.closed_of_finiteDimensional S
            -- Use density: if property holds on inc(Y) and is closed, it holds on Z
            have h_P'_in_S : ∀ z : Z, (P' n) z ∈ S := fun z =>
              h_dense.induction_on (p := fun z => (P' n) z ∈ S) z
                (hS_closed.preimage (P' n).continuous)
                (fun y => by
                  simp only [SetLike.mem_coe, S]
                  rw [h_agree, b.proj_apply]
                  simp_rw [map_sum, map_smul]
                  apply Submodule.sum_mem
                  intro i hi
                  have hi' : i < n := Finset.mem_range.mp hi
                  have h_e'_mem : e' i ∈ Set.range (fun j : Fin n => e' j) :=
                    ⟨⟨i, hi'⟩, rfl⟩
                  exact Submodule.smul_mem _ _ (Submodule.subset_span h_e'_mem))
            exact h_P'_in_S w
          · -- span {e' i | i < n} ⊆ range(P' n)
            rw [Submodule.span_le]
            rintro _ ⟨i, rfl⟩
            refine ⟨e' i, ?_⟩
            -- P' n (e' i) = e' i for i < n, using h_agree and proj_basis_element
            -- Key: e' k = inc (e k) by definition
            show (P' n) (e' i) = e' i
            calc (P' n) (e' i) = (P' n) (inc (e i)) := rfl
              _ = inc (b.proj n (e i)) := h_agree n (e i)
              _ = inc (e i) := by rw [b.proj_basis_element, if_pos i.is_lt]
              _ = e' i := rfl
        rw [h_range_eq, finrank_span_eq_card]
        · exact Fintype.card_fin n
        · -- Linear independence of e' restricted to Fin n
          -- e' is injective image of e under the injective map inc
          have h_inc_inj : Function.Injective inc := h_isometry.injective
          have h_ind : LinearIndependent 𝕜 e' :=
            b.linearIndependent.map' (Submodule.inclusion Y.le_topologicalClosure) (by
              simp only [Submodule.ker_inclusion])
          exact h_ind.comp (fun (i : Fin n) => (i : ℕ)) Fin.val_injective)
    (by -- hcomp: P' n (P' m z) = P' (min n m) z
        intro n m z
        -- Use density: prove for inc y, then extend by continuity
        apply h_dense.induction_on (p := fun z => (P' n) ((P' m) z) = (P' (min n m)) z) z
        · -- The set {z | P' n (P' m z) = P' (min n m) z} is closed
          exact isClosed_eq ((P' n).continuous.comp (P' m).continuous) (P' (min n m)).continuous
        · -- For y : Y, P' n (P' m (inc y)) = P' (min n m) (inc y)
          intro y
          calc (P' n) ((P' m) (inc y))
              = (P' n) (inc (b.proj m y)) := by rw [h_agree]
            _ = inc (b.proj n (b.proj m y)) := by rw [h_agree]
            _ = inc (b.proj (min n m) y) := by rw [b.proj_comp]
            _ = (P' (min n m)) (inc y) := by rw [← h_agree])
    (by -- hlim: P' n z → z
        intro z
        -- First, show convergence on inc(Y): P' n (inc y) → inc y
        have h_tendsto_on_Y : ∀ y : Y, Tendsto (fun n => (P' n) (inc y)) atTop (𝓝 (inc y)) := by
          intro y
          have h1 : ∀ n, (P' n) (inc y) = inc (b.proj n y) := fun n => h_agree n y
          simp_rw [h1]
          exact inc.continuous.continuousAt.tendsto.comp (b.proj_tendsto_id y)
        -- Use uniform bounds and density to extend to Z
        rw [Metric.tendsto_atTop]
        intro ε hε
        obtain ⟨C, hC⟩ := h_uniform
        -- We need C' + 1 > 0 for the division. C could be negative, so use max.
        set C' := max C 0 with hC'_def
        have hC'_nonneg : C' ≥ 0 := le_max_right C 0
        have hC'1_pos : C' + 1 > 0 := by linarith
        have hC'2_pos : C' + 2 > 0 := by linarith
        have hC'_bound : ∀ n, ‖P' n‖ ≤ C' := fun n => (hC n).trans (le_max_left C 0)
        -- Choose δ = ε / (2 * (C' + 2)) so that (C' + 1) * δ < ε/2
        set δ := ε / (2 * (C' + 2)) with hδ_def
        have hδ_pos : δ > 0 := div_pos hε (by linarith)
        -- Find y : Y with z close to inc y
        have hz_closure : z ∈ closure (Set.range inc) := by
          rw [h_dense.closure_eq]; exact Set.mem_univ z
        rw [Metric.mem_closure_iff] at hz_closure
        obtain ⟨_, ⟨y, rfl⟩, hw⟩ := hz_closure δ hδ_pos
        -- Find N such that P' n (inc y) is close to inc y for n ≥ N
        have h_tendsto_y := h_tendsto_on_Y y
        rw [Metric.tendsto_atTop] at h_tendsto_y
        obtain ⟨N, hN⟩ := h_tendsto_y (ε / 2) (half_pos hε)
        use N
        intro n hn
        have h_dist_z_y : dist z (inc y) < δ := hw
        have h_dist_Pn : dist ((P' n) (inc y)) (inc y) < ε / 2 := hN n hn
        have h_norm_Pn : ‖(P' n) (z - inc y)‖ ≤ C' * dist z (inc y) := by
          calc ‖(P' n) (z - inc y)‖ ≤ ‖P' n‖ * ‖z - inc y‖ := (P' n).le_opNorm _
            _ ≤ C' * ‖z - inc y‖ := mul_le_mul_of_nonneg_right (hC'_bound n) (norm_nonneg _)
            _ = C' * dist z (inc y) := by rw [dist_eq_norm]
        -- Key: (C' + 1) * δ < ε/2 since δ = ε / (2 * (C' + 2)) and C' + 1 < C' + 2
        have h_key : (C' + 1) * δ < ε / 2 := by
          rw [hδ_def]
          have h1 : (C' + 1) / (C' + 2) < 1 := by rw [div_lt_one hC'2_pos]; linarith
          have h2 : (C' + 1) * (ε / (2 * (C' + 2))) = ε / 2 * ((C' + 1) / (C' + 2)) := by
            rw [mul_div_assoc, mul_comm (C' + 1), ← mul_div_assoc, mul_comm 2, mul_assoc]
            congr 1
            rw [div_mul_eq_mul_div, mul_comm (C' + 1)]
          rw [h2]
          calc ε / 2 * ((C' + 1) / (C' + 2))
              < ε / 2 * 1 := mul_lt_mul_of_pos_left h1 (half_pos hε)
            _ = ε / 2 := mul_one _
        -- Need: (C' + 1) * dist z (inc y) < (C' + 1) * δ
        have h_dist_lt : (C' + 1) * dist z (inc y) < (C' + 1) * δ := by
          exact mul_lt_mul_of_pos_left h_dist_z_y hC'1_pos
        calc dist ((P' n) z) z
            ≤ dist ((P' n) z) ((P' n) (inc y)) + dist ((P' n) (inc y)) (inc y) +
                dist (inc y) z := dist_triangle4 _ _ _ _
          _ = ‖(P' n) (z - inc y)‖ + dist ((P' n) (inc y)) (inc y) + dist z (inc y) := by
              simp only [dist_eq_norm, map_sub, norm_sub_rev]
          _ ≤ C' * dist z (inc y) + dist ((P' n) (inc y)) (inc y) + dist z (inc y) := by
              linarith [h_norm_Pn]
          _ = (C' + 1) * dist z (inc y) + dist ((P' n) (inc y)) (inc y) := by ring
          _ < (C' + 1) * δ + ε / 2 := by linarith [h_dist_lt]
          _ < ε / 2 + ε / 2 := by linarith
          _ = ε := add_halves ε)
    (by intro n; sorry)  -- he_in_range: e' n ∈ range (Q P' n)
    (by intro n
        simp only [e', ne_eq, Submodule.mk_eq_zero]
        exact Subtype.coe_ne_coe.mpr (b.linearIndependent.ne_zero n))  -- he_ne: e' n ≠ 0








end SchauderBasis
