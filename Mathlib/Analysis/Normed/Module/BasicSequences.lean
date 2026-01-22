/-
Copyright (c) 2026 Michał Świętek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michał Świętek
-/
module

public import Mathlib.Analysis.Normed.Module.Bases
public import Mathlib.Analysis.Normed.Module.WeakDual

/-!
# Basic Sequences in Banach Spaces
-/

noncomputable section

open Submodule Set WeakDual

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/--
A sequence `e` is a **Basic Sequence** if it forms a Schauder Basis for its closed linear span.
-/
def IsBasicSequence (𝕜 : Type*) {X : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] (e : ℕ → X) : Prop :=
  let Y := (span 𝕜 (range e)).topologicalClosure
  let e_Y : ℕ → Y := fun n ↦ ⟨e n,
    Submodule.le_topologicalClosure _ (subset_span (mem_range_self n))⟩
  Nonempty (SchauderBasis 𝕜 e_Y)

namespace BasicSequences

-- variable (𝕜 : Type*) {X : Type*} [NontriviallyNormedField 𝕜]
--     [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable {e : ℕ → X}

/-- Every Schauder Basis of the whole space `X` is a basic sequence. -/
theorem isBasicSequence_self (b : SchauderBasis 𝕜 e) : IsBasicSequence 𝕜 e := by
  -- rw [IsBasicSequence]
  -- let Y := (span 𝕜 (range e)).topologicalClosure
  -- have h_dense : Y = ⊤ := by
  --   rw [eq_top_iff']
  --   intro x
  --   -- Proof sketch: The basis expansion converges, so x is in the closure of the span.
  --   exact mem_closure_of_tendsto (b.basis_expansion x)
  --     (eventually_of_forall (fun n ↦ sum_mem (fun i _ ↦ smul_mem _ _ (subset_span (mem_range_self i)))))
  -- -- We construct the basis for Y by restricting b.
  -- -- (Technical construction omitted for brevity, asserting existence).
  -- use ?_
  sorry -- Standard coercion of basis to the top submodule.

/-- The **Basis Constant** of a basic sequence. -/
noncomputable def basicSequenceConstant (he : IsBasicSequence 𝕜 e) : ℝ :=
  (Classical.choice he).basisConstant



/-- A sequence satisfies the **Grünblum Condition** if the norms of the projections
onto the span of its first `n` elements are uniformly bounded. -/
def SatisfiesGrunblumCondition (𝕜 : Type*) {X : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] (e : ℕ → X) : Prop :=
  ∃ K, 1 ≤ K ∧ ∀ (n m : ℕ) (a : ℕ → 𝕜), m ≤ n →
    ‖∑ i ∈ Finset.range m, a i • e i‖ ≤ K * ‖∑ i ∈ Finset.range n, a i • e i‖

/-- A basic sequence implies the Grünblum inequality holds for its basis constant. -/
theorem grunblum_of_basic (he : IsBasicSequence 𝕜 e) : SatisfiesGrunblumCondition 𝕜 e := by
    sorry

/--
**The Grünblum Criterion**:
If a sequence satisfies the Grünblum condition (bounded projections on the span),
and the elements are non-zero, then it is a Basic Sequence.
-/
theorem isBasicSequence_of_grunblum [CompleteSpace X]
    (h_grunblum : SatisfiesGrunblumCondition 𝕜 e)
    (h_nz : ∀ n, e n ≠ 0) : IsBasicSequence  𝕜 e := by
  sorry


/-- Small perturbations of finite-dimensional subspaces
    by elements from the weak*-closure (but not norm-closure) of a set S. -/
lemma perturbation_finite_dimensional {S : Set (StrongDual 𝕜 X)}
    (h_weak_star : (0 : StrongDual 𝕜 X) ∈ closure (StrongDual.toWeakDual '' S))
    (h_norm : (0 : StrongDual 𝕜 X) ∉ closure S)
    (E : Subspace 𝕜 (StrongDual 𝕜 X))
    [FiniteDimensional 𝕜 E]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ x ∈ S, ∀ (e : E) (c : 𝕜), ‖(e : StrongDual 𝕜 X) + c • x‖ ≥ (1 - ε) * ‖e‖ := by
  sorry

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
