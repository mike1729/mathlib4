/-
Copyright (c) 2026 Michał Świętek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michał Świętek
-/
module

public import Mathlib.Analysis.Normed.Module.SchauderBasis.BasicSequence
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.Neighborhoods

/-!
# Selection Principle for Basic Sequences

The **selection principle** extracts basic sequences from sets that are weak*-dense near the
origin but norm-separated from it. This gap between the weak and norm topologies is the
mechanism behind many structural results in Banach space theory.

The key technical ingredient is a perturbation lemma: given a finite-dimensional subspace and a
weak*-dense set, one can find an element of the set that is almost orthogonal to the subspace.
Iterating this produces a sequence satisfying the Grünblum condition, hence a basic sequence.

As a corollary, every infinite-dimensional Banach space contains a basic sequence with basis
constant arbitrarily close to 1 (the Bessaga–Pełczyński theorem).

## Main Results

* `perturbation_finite_dimensional`: Given a weak*-dense set and a finite-dimensional subspace,
  there exists a perturbation element almost orthogonal to the subspace.
* `basic_sequence_selection_dual`: The dual selection principle — extracts a basic sequence
  from a set that is weak*-dense near 0 but norm-separated from 0.
* `weak_closure_sphere_contains_zero`: In an infinite-dimensional space, 0 is in the weak*
  closure of the unit sphere's image in the bidual.
* `exists_basicSequence`: Every infinite-dimensional Banach space contains a basic sequence
  with basis constant arbitrarily close to 1.

## References

* [F. Albiac, N.J. Kalton, *Topics in Banach Space Theory*][albiac2016]
-/

@[expose] public section

noncomputable section

open Submodule Set WeakDual Metric Filter Topology

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

namespace BasicSequence

/-- Given a weak*-dense set `S` norm-separated from 0 and a finite-dimensional subspace `E`,
    there exists `x ∈ S` that is almost orthogonal to `E`: for all `e ∈ E` and scalars `c`,
    `‖e + c • x‖ ≥ (1 - ε) * ‖e‖`. -/
lemma perturbation_finite_dimensional {S : Set (StrongDual 𝕜 X)}
    (h_weak_star : (0 : WeakDual 𝕜 X) ∈ closure (StrongDual.toWeakDual '' S))
    (h_norm : (0 : StrongDual 𝕜 X) ∉ closure S)
    (E : Subspace 𝕜 (StrongDual 𝕜 X))
    (hefind : FiniteDimensional 𝕜 E)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ x ∈ S, ∀ (e : E) (c : 𝕜), ‖(e : StrongDual 𝕜 X) + c • x‖ ≥ (1 - ε) * ‖e‖ := by
  -- 0. S is nonempty (0 is in the closure of its image)
  have hS_nonempty : S.Nonempty := by
    by_contra h; rw [Set.not_nonempty_iff_eq_empty] at h; simp [h] at h_weak_star
  -- Handle trivial ε case: if ε ≥ 1, any x ∈ S works since (1-ε) ≤ 0
  rcases le_or_gt 1 ε with hε1 | hε1
  · obtain ⟨x, hxS⟩ := hS_nonempty
    exact ⟨x, hxS, fun e c => le_trans
      (mul_nonpos_of_nonpos_of_nonneg (by linarith) (norm_nonneg _)) (norm_nonneg _)⟩
  -- 1. Setup constants based on distance to S
  let δ := Metric.infDist (0 : StrongDual 𝕜 X) S
  have hδ : 0 < δ := (Metric.infDist_pos_iff_notMem_closure hS_nonempty).mp h_norm
  let M := 2 / δ
  let γ := ε * δ / 4
  have h_norm_S : ∀ x ∈ S, δ ≤ ‖x‖ := fun x hx =>
    (Metric.infDist_le_dist_of_mem hx).trans_eq (dist_zero_left x)
  -- 2. Use compactness of the sphere in E to find a finite "test set" F ⊂ X
  let sphere := Metric.sphere (0 : E) 1
  -- Define the open sets covering the sphere, indexed by the unit ball of vectors X.
  let U (v : {v : X // ‖v‖ ≤ 1}) : Set E :=
    {e | 1 - ε / 2 < ‖(e : StrongDual 𝕜 X) v‖}
  have h_cover : sphere ⊆ ⋃ v, U v := by
    intro e he
    rw [mem_sphere_zero_iff_norm] at he
    -- We have ‖e‖ = 1 and ε > 0, so 1 - ε/2 < ‖e‖
    have h_lt : 1 - ε / 2 < ‖(e : StrongDual 𝕜 X)‖ := by
      rw [norm_coe, he]
      linarith
    -- Find a vector v with ||v|| ≤ 1 that "witnesses" the norm of e
    obtain ⟨v, hv, hv_val⟩ :=
      ContinuousLinearMap.exists_lt_apply_of_lt_opNorm (e : StrongDual 𝕜 X) h_lt
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
  have hW0 : (0 : WeakDual 𝕜 X) ∈ W := fun _ _ => by
    rw [ContinuousLinearMap.zero_apply, norm_zero]; exact hγ
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
        _ ≥ 1 - ε                               := by dsimp [M]; field_simp [hδ.ne']; nlinarith
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
  -- Reconstruct for original e and c: factor out ‖e‖
  have h_norm_ne : (e_norm : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr he_ne)
  have hfactor : (e : StrongDual 𝕜 X) + c • x =
      (e_norm : 𝕜) • ((e' : StrongDual 𝕜 X) + ((e_norm⁻¹ : 𝕜) * c) • x) := by
    simp only [e', smul_add, Submodule.coe_smul, smul_smul,
      mul_inv_cancel₀ h_norm_ne, one_smul, ← mul_assoc, one_mul]
  rw [ge_iff_le, hfactor, norm_smul, RCLike.norm_ofReal, abs_norm, mul_comm (1 - ε)]
  gcongr; rw [← RCLike.ofReal_inv]; exact estimate.le

theorem basic_sequence_selection_dual {S : Set (StrongDual 𝕜 X)}
    (h_weak_star : (0 : WeakDual 𝕜 X) ∈ closure (StrongDual.toWeakDual '' S))
    (h_norm : (0 : StrongDual 𝕜 X) ∉ closure S)
    {ε : ℝ} (hε : ε > 0) :
    ∃ (b : BasicSequence 𝕜 (StrongDual 𝕜 X)),
      (∀ n, b n ∈ S) ∧
      b.basicSequenceConstant ≤ 1 + ε := by
  -- Use ε/2 in the construction so that the Grünblum constant is 1 + ε/2 < 1 + ε
  -- 1. Setup control sequence `δ` using a telescoping product `u`.
  let u (n : ℕ) := 1 + ε * (1 - (1/2) ^ n)
  let δ (n : ℕ) := 1 - u n / u (n + 1)
  have hu : ∀ n, 1 ≤ u n ∧ u n < 1 + ε := fun n ↦ by
    have hp : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hp' : 0 < (1 / 2 : ℝ) ^ n := pow_pos (by norm_num) n
    constructor <;> { dsimp [u]; nlinarith }
  have hδ_pos : ∀ n, 0 < δ n := fun n ↦ by
    have hp : 0 < (1 / 2 : ℝ) ^ n := pow_pos (by norm_num) n
    dsimp [δ, u]; rw [sub_pos, div_lt_one (by nlinarith [(hu (n + 1)).1])]
    nlinarith [show (1 / 2 : ℝ) ^ (n + 1) = 1 / 2 * (1 / 2) ^ n from by ring]
  have hu_pos : ∀ k, 0 < u k := fun k => lt_of_lt_of_le (by linarith) (hu k).1
  -- 2. Construct the sequence `f` via strong recursion.
  let f : ℕ → StrongDual 𝕜 X := fun n => Nat.strongRecOn n (fun k prev ↦
    let E := Submodule.span 𝕜 (Set.range (fun i : Fin k ↦ prev i i.isLt))
    Classical.choose (perturbation_finite_dimensional h_weak_star h_norm E
      (FiniteDimensional.span_of_finite 𝕜 (Set.finite_range _)) (hδ_pos k)))
  -- 3. Extract properties of `f`.
  have hf_spec (n : ℕ) :
      f n ∈ S ∧ ∀ (e : Submodule.span 𝕜 (Set.range (fun i : Fin n ↦ f i))) (c : 𝕜),
        (1 - δ n) * ‖e‖ ≤ ‖(e : StrongDual 𝕜 X) + c • f n‖ := by
    let P := perturbation_finite_dimensional h_weak_star h_norm
      (Submodule.span 𝕜 (Set.range (fun i : Fin n ↦ f i)))
      (FiniteDimensional.span_of_finite 𝕜 (Set.finite_range _)) (hδ_pos n)
    have hfn : f n = Classical.choose P := by unfold f; rw [Nat.strongRecOn_eq]
    rw [hfn]; exact Classical.choose_spec P
  -- 4. Prove the Grünblum condition via telescoping product.
  -- Keep the explicit bound with K = 1 + ε for later use
  have h_grunblum_bound : ∀ n m (a : ℕ → 𝕜), m ≤ n →
      ‖∑ i ∈ Finset.range m, a i • f i‖ ≤ (1 + ε) * ‖∑ i ∈ Finset.range n, a i • f i‖ := by
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
        simp only [δ, sub_sub_cancel]; exact div_pos (hu_pos k) (hu_pos (k+1))
      rw [le_inv_mul_iff₀ h1δ]
      calc (1 - δ k) * ‖S k‖ ≤ ‖S k + a k • f k‖ := h
        _ = ‖S (k + 1)‖ := by simp only [S, Finset.sum_range_succ]
    -- The key bound: ‖S m‖ ≤ (1 + ε) * ‖S n‖ via telescoping product
    -- Each step gives ‖S k‖ ≤ (1 - δ k)⁻¹ * ‖S (k+1)‖
    -- Product of (1 - δ k)⁻¹ from m to n-1 equals u n / u m ≤ (1 + ε)
    -- Key identity: (1 - δ k)⁻¹ = u (k+1) / u k
    have h_inv : ∀ k, (1 - δ k)⁻¹ = u (k + 1) / u k := fun k => by
      simp only [δ, sub_sub_cancel]; rw [inv_div]
    -- Chain the inequalities via induction
    have h_chain : ‖S m‖ ≤ (u n / u m) * ‖S n‖ := by
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
      induction d with
      | zero => simp [(hu_pos m).ne']
      | succ d ih =>
        calc ‖S m‖
          _ ≤ (u (m + d) / u m) * ‖S (m + d)‖ :=
              ih (Nat.le_add_right m d) (fun k hk => h_step k (Nat.lt_add_right 1 hk))
          _ ≤ (u (m + d) / u m) * ((1 - δ (m + d))⁻¹ * ‖S (m + d + 1)‖) := by
              gcongr
              · exact div_nonneg (hu_pos _).le (hu_pos _).le
              · exact h_step (m + d) (by omega)
          _ = (u (m + (d + 1)) / u m) * ‖S (m + (d + 1))‖ := by
              rw [h_inv, show m + d + 1 = m + (d + 1) from by ring]
              field_simp [(hu_pos _).ne']
    -- Finally bound u n / u m ≤ (1 + ε)
    calc ‖S m‖ ≤ (u n / u m) * ‖S n‖ := h_chain
      _ ≤ (1 + ε) * ‖S n‖ := by
          gcongr; exact (div_le_self (hu_pos n).le (hu m).1).trans (hu n).2.le
  -- 5. Final assembly.
  have h_nz n : f n ≠ 0 := by
    intro hfn
    apply h_norm
    rw [← hfn]
    exact subset_closure (hf_spec n).1
  obtain ⟨b, hb, hbound⟩ := isBasicSequence_of_Grunblum_with_bound h_grunblum_bound h_nz
  refine ⟨b, ?_, hbound⟩
  intro n
  rw [show b n = f n from congrFun hb n]
  exact (hf_spec n).1

/-- In an infinite-dimensional normed space, `0` is in the weak* closure of the image of the
    unit sphere under the canonical embedding into the bidual. -/
lemma weak_closure_sphere_contains_zero (hinf : ¬ FiniteDimensional 𝕜 X) :
    (0 : WeakDual 𝕜 (StrongDual 𝕜 X)) ∈ closure (
      StrongDual.toWeakDual '' (NormedSpace.inclusionInDoubleDual 𝕜 X '' Metric.sphere 0 1)) := by
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
  have h0V : (fun f => (0 : WeakDual 𝕜 (StrongDual 𝕜 X)) f) ∈ V := by
    rw [← hV_eq] at hU_zero; exact hU_zero
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
      let φ := LinearMap.pi (fun (f : F) => (f : StrongDual 𝕜 X).toLinearMap)
      apply Module.Finite.of_injective φ
      intro x y hxy
      simp only [funext_iff] at hxy
      have hmem : x - y ∈ K := by
        simp only [K, Submodule.mem_iInf, LinearMap.mem_ker, map_sub, sub_eq_zero]
        exact fun f hf => hxy ⟨f, hf⟩
      rw [h_bot, Submodule.mem_bot] at hmem
      exact sub_eq_zero.mp hmem
    exact hinf this
  -- Pick nonzero v ∈ K and normalize to unit sphere
  obtain ⟨v, hvK, hv_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hK_nontrivial
  let x := (‖v‖⁻¹ : 𝕜) • v
  have hx_norm : ‖x‖ = 1 := norm_smul_inv_norm hv_ne
  have hx_K : x ∈ K := K.smul_mem _ hvK
  -- x satisfies f(x) = 0 for all f ∈ F
  have h_vanish : ∀ f ∈ F, (f : StrongDual 𝕜 X) x = 0 := fun f hf =>
    LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp hx_K f) hf)
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
    simp only [topDualPairing_apply, StrongDual.coe_toWeakDual, J, NormedSpace.dual_def]
    rw [h_vanish f hf]
    -- 0 ∈ t f because the zero functional evaluates to 0 there
    exact (ht_cond f hf).2
  exact ⟨StrongDual.toWeakDual (J x), hJx_U, hJx_S⟩

/-- Every infinite-dimensional Banach space contains a basic sequence with basis constant
    arbitrarily close to 1 (the Bessaga–Pełczyński theorem, [albiac2016, Corollary 1.5.3]). -/
theorem exists_basicSequence [CompleteSpace X] (hinf : ¬ FiniteDimensional 𝕜 X) {ε : ℝ}
    (hε : 0 < ε) : ∃ (b : BasicSequence 𝕜 X), b.basicSequenceConstant ≤ 1 + ε := by
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
  -- 4. Pull back the sequence to X using the pullback lemma
  obtain ⟨b, _, hb_bound⟩ := b_bidual.pullback J
    (NormedSpace.inclusionInDoubleDualLi (𝕜 := 𝕜) (E := X)).norm_map hb_mem
  exact ⟨b, hb_bound.trans hb_const⟩

end BasicSequence
