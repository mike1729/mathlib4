/-
Copyright (c) 2026 Michał Świętek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michał Świętek
-/
module

public import Mathlib.Analysis.Normed.Module.SchauderBasis.Selection
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.Topology.UniformSpace.UniformEmbedding


/-!
# Perturbation and Closure Results for Basic Sequences

This file contains results about perturbations of basic sequences, the relationship
between basic sequences and weak closure, and the construction of Schauder bases
from basic sequences via closure.

## Main Results

* `perturb_basic_sequence`: A perturbation of a basic sequence by a fixed vector
  (under suitable functional conditions) is still a basic sequence.
* `no_basic_sequence_implies_zero_not_in_weak_closure`: If a bounded set contains no basic
  sequence, then 0 is not in its weak closure.
* `SchauderBasis_of_closure`: Constructs a Schauder basis for the topological closure
  from a Schauder basis on a subspace.
-/

@[expose] public section

noncomputable section

open Submodule Set WeakDual Metric Filter Topology

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

namespace BasicSequence

lemma perturb_basic_sequence [CompleteSpace X] (b : BasicSequence 𝕜 X)
    (h_bound : b.basis.enormProjBound < ⊤)
    (u : X) (g : StrongDual 𝕜 X)
    (hf : ∀ n, g (b n) = 1) (hu : g u = -1)
    (hunin : u ∉ closure (Submodule.span 𝕜 (Set.range b) : Set X)) :
    IsBasicSequence 𝕜 (fun n ↦ b n + u) := by
  have hh : ∃ h : StrongDual 𝕜 X, h u = -1 ∧ ∀ n, h (b n) = 0 := by
    let M := (Submodule.span 𝕜 (Set.range b.toFun)).topologicalClosure
    have hM_closed : IsClosed (M : Set X) := Submodule.isClosed_topologicalClosure _
    have hM_eq : (M : Set X) = closure (Submodule.span 𝕜 (Set.range b.toFun) : Set X) :=
      Submodule.topologicalClosure_coe _
    have hunin' : u ∉ (M : Set X) := hM_eq ▸ hunin
    obtain ⟨f, hf_u, hf_vanish⟩ :=
      exists_functional_neg_one_and_vanishes_on_closed_submodule M hM_closed u hunin'
    refine ⟨f, hf_u, fun n => hf_vanish (b n) ?_⟩
    exact (Submodule.span 𝕜 _).le_topologicalClosure (Submodule.subset_span (Set.mem_range_self n))
  obtain ⟨h, hh_u, hg_b⟩ := hh
  let f := g - h
  have hu0 : f u = 0 := by simp only [f, ContinuousLinearMap.sub_apply, hu, hh_u, sub_self]
  have hf' : ∀ n, f (b n) = 1 := fun n => by
    simp only [f, ContinuousLinearMap.sub_apply, hf n, hg_b n, sub_zero]

  let y := fun n ↦ b n + u
  -- 1. Elements are non-zero because f(y n) = 1
  have h_nz : ∀ n, y n ≠ 0 := fun n h_zero ↦ by
    have h_val : f (y n) = 1 := by simp [y, f.map_add, hf', hu0]
    rw [h_zero, f.map_zero] at h_val
    exact zero_ne_one h_val
    -- fun h => by simpa [y, hf, hu0, h] using f.map_zero

  -- 2. Grünblum Condition
  have hK := basicSequence_satisfiesGrunblum b
  let K := b.basicSequenceConstant
  -- Define the distortion constant C
  let C := 1 + ‖f‖ * ‖u‖
  have hC : 0 ≤ C := add_nonneg zero_le_one (mul_nonneg (norm_nonneg f) (norm_nonneg u))
  have hC_ge_one : 1 ≤ C := le_add_of_nonneg_right (mul_nonneg (norm_nonneg f) (norm_nonneg u))

  refine isBasicSequence_of_grunblum (K := K * C ^ 2) h_nz
    fun n m a hnm ↦ ?_
  let Y k := ∑ i ∈ Finset.range k, a i • y i
  let E k := ∑ i ∈ Finset.range k, a i • b i
  have h_rel (k) : Y k = E k + f (Y k) • u := by
    simp only [Y, E, y, smul_add, Finset.sum_add_distrib, ← Finset.sum_smul]
    congr 1
    simp only [map_add, map_sum, map_smul, hf', hu0, smul_eq_mul, mul_one, mul_zero, add_zero]
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
  calc ‖Y m‖
    _ ≤ C * ‖E m‖ := h_Y_E m
    _ ≤ C * (K * ‖E n‖) := by gcongr; exact hK n m a hnm
    _ = C * K * ‖E n‖ := by ring
    _ ≤ C * K * (C * ‖Y n‖) := by
        apply mul_le_mul_of_nonneg_left (h_E_Y n)
        exact mul_nonneg hC (zero_le_one.trans (grunblum_const_ge_1 hK h_nz 0))

    _ = (K * C ^ 2) * ‖Y n‖ := by ring

/-- If a bounded set S in a Banach space X does not contain a basic sequence,
    then 0 is not in the weak closure of S.

    This is a consequence of the basic sequence selection principle: if 0 is in the
    weak* closure of J(S) but not in its norm closure, then J(S) contains a basic sequence,
    which can be pulled back to a basic sequence in S. -/
theorem no_basic_sequence_implies_zero_not_in_weak_closure [CompleteSpace X]
    {S : Set X} (_hS_ne : S.Nonempty) (h_norm : (0 : X) ∉ closure S)
    (h_no_basic : ∀ (e : ℕ → X), (∀ n, e n ∈ S) → ¬ IsBasicSequence 𝕜 e) :
    (0 : X) ∉ closure (toWeakSpace 𝕜 X '' S) := by
  -- We prove the contrapositive: if 0 is in the weak closure, we can find a basic sequence.
  contrapose! h_no_basic

  -- 1. Setup the Bidual embedding J : X → X**
  let J := NormedSpace.inclusionInDoubleDual 𝕜 X
  let S' := J '' S

  -- 2. Translate the weak closure hypothesis to the bidual's weak* topology.
  -- The weak topology on X and the weak* topology on X** are both induced by X*.
  -- A basic weak* neighborhood of 0 in X** is determined by finitely many f ∈ X*.
  -- The preimage under J of such a neighborhood equals the corresponding weak neighborhood
  -- of 0 in X.
  have h_weak_star : (0 : WeakDual 𝕜 (StrongDual 𝕜 X)) ∈ closure (StrongDual.toWeakDual '' S') := by
    rw [_root_.mem_closure_iff]
    intro U hU_open hU_zero
    -- U is open in weak* topology, which is induced from StrongDual 𝕜 X → 𝕜
    rw [isOpen_induced_iff] at hU_open
    obtain ⟨V, hV_open, hV_eq⟩ := hU_open
    have h0V : (fun f => (0 : WeakDual 𝕜 (StrongDual 𝕜 X)) f) ∈ V := by
      rw [← hV_eq] at hU_zero; exact hU_zero
    -- V is open in product topology, so contains a basic open set
    rw [isOpen_pi_iff] at hV_open
    obtain ⟨F, t, ht_cond, hFt_sub⟩ := hV_open _ h0V
    -- F is finite set of functionals in X*, t gives open neighborhoods in 𝕜
    -- Construct corresponding weak neighborhood W of 0 in X
    -- In WeakSpace 𝕜 X, evaluation at f ∈ X* is continuous (WeakBilin.eval_continuous)
    let W : Set (WeakSpace 𝕜 X) := ⋂ f ∈ F, {w : WeakSpace 𝕜 X | f ((toWeakSpace 𝕜 X).symm w) ∈ t f}
    have hW_open : IsOpen W := by
      apply isOpen_biInter_finset
      intro f _
      -- The evaluation map w ↦ f(w) is continuous in the weak topology
      have hf_cont : Continuous (fun w : WeakSpace 𝕜 X => f ((toWeakSpace 𝕜 X).symm w)) :=
        WeakBilin.eval_continuous (topDualPairing 𝕜 X).flip f
      exact (ht_cond f ‹f ∈ F›).1.preimage hf_cont
    have hW_zero : toWeakSpace 𝕜 X 0 ∈ W := by
      simp only [W, mem_iInter, mem_setOf, map_zero]
      intro f hf
      exact (ht_cond f hf).2
    -- Since 0 ∈ weak closure of S, W ∩ (toWeakSpace '' S) is nonempty
    have h_inter : (W ∩ (toWeakSpace 𝕜 X '' S)).Nonempty := by
      have h_cl := @_root_.mem_closure_iff (WeakSpace 𝕜 X) _
        (toWeakSpace 𝕜 X 0) (toWeakSpace 𝕜 X '' S)
      exact h_cl.mp h_no_basic W hW_open hW_zero
    obtain ⟨w, hwW, x, hxS, hwx⟩ := h_inter
    -- x ∈ S satisfies: f(x) ∈ t f for all f ∈ F
    have hx_in_t : ∀ f ∈ F, f x ∈ t f := fun f hf => by
      have := hwW
      simp only [W, mem_iInter] at this
      specialize this f hf
      simp only [mem_setOf, hwx.symm, LinearEquiv.symm_apply_apply] at this
      exact this
    -- Therefore J(x) ∈ U
    have hJx_U : StrongDual.toWeakDual (J x) ∈ U := by
      rw [← hV_eq]
      apply hFt_sub
      intro f hf
      change topDualPairing 𝕜 (StrongDual 𝕜 X) (StrongDual.toWeakDual (J x)) f ∈ t f
      simp only [topDualPairing_apply, StrongDual.coe_toWeakDual, J, NormedSpace.dual_def]
      exact hx_in_t f hf
    -- And J(x) ∈ toWeakDual '' S'
    have hJx_S' : StrongDual.toWeakDual (J x) ∈ StrongDual.toWeakDual '' S' :=
      ⟨J x, ⟨x, hxS, rfl⟩, rfl⟩
    exact ⟨StrongDual.toWeakDual (J x), hJx_U, hJx_S'⟩

  -- 3. Show 0 is not in the norm closure of S' in the bidual.
  -- Since J is an isometry, it preserves distances to the origin.
  have h_norm_S' : (0 : StrongDual 𝕜 (StrongDual 𝕜 X)) ∉ closure S' := by
    rw [Metric.mem_closure_iff]
    push_neg
    -- 0 ∉ closure S means there exists δ > 0 such that S ∩ ball(0, δ) = ∅
    rw [Metric.mem_closure_iff] at h_norm
    push_neg at h_norm
    obtain ⟨δ, hδ_pos, hδ_S⟩ := h_norm
    use δ, hδ_pos
    rintro _ ⟨x, hxS, rfl⟩
    -- J is an isometry: dist(J x, 0) = dist(x, 0)
    have hJ_iso : ‖J x‖ = ‖x‖ := (NormedSpace.inclusionInDoubleDualLi (𝕜 := 𝕜) (E := X)).norm_map x
    rw [dist_zero_left, hJ_iso, ← dist_zero_left]
    exact hδ_S x hxS

  -- 4. Apply the Selection Principle for Dual Spaces with ε = 1.
  obtain ⟨b_bidual, hb_mem, -, hb_bound⟩ :=
    basic_sequence_selection_dual h_weak_star h_norm_S' zero_lt_one

  -- 5. Pull the sequence back to X.
  -- Since b_bidual n ∈ S' = J '' S, there exists x_n ∈ S such that J x_n = b_bidual n.
  choose e he_S he_eq using hb_mem

  -- 6. Show e is a basic sequence in S using the Grünblum condition.
  use e, he_S

  -- e has nonzero elements (since b_bidual is basic and J is injective)
  have h_nz : ∀ n, e n ≠ 0 := fun n h_zero => by
    -- b_bidual.basis is linearly independent, so its elements are nonzero
    have hb_indep := b_bidual.basis.linearIndependent
    have hb_nz := hb_indep.ne_zero n
    -- b_bidual.basis_eq says: b_bidual.basis n = codRestrict b_bidual.toFun ... n
    -- So (b_bidual.basis n : X**) = b_bidual n
    have h_eq : (b_bidual.basis n : StrongDual 𝕜 (StrongDual 𝕜 X)) = b_bidual n := by
      have := congrFun b_bidual.basis_eq n
      exact congrArg Subtype.val this
    -- If e n = 0, then J(e n) = 0 = b_bidual n, but b_bidual n ≠ 0
    rw [← he_eq n, h_zero, map_zero] at h_eq
    -- h_eq : (b_bidual.basis n : X**) = 0, so b_bidual.basis n = 0 as subtype element
    exact hb_nz (Subtype.ext h_eq)

  -- The Grünblum constant for b_bidual
  let K := b_bidual.basicSequenceConstant

  -- Transfer Grünblum condition from b_bidual to e using J being an isometry
  have hK_bound_e : ∀ (n m : ℕ) (a : ℕ → 𝕜), m ≤ n →
      ‖∑ i ∈ Finset.range m, a i • e i‖ ≤ K * ‖∑ i ∈ Finset.range n, a i • e i‖ := by
    intro n m a hmn
    have h_J_sum (k : ℕ) : J (∑ i ∈ Finset.range k, a i • e i) =
        ∑ i ∈ Finset.range k, a i • b_bidual i := by
      simp only [map_sum, map_smul, he_eq]
    have hJ_norm : ∀ y : X, ‖J y‖ = ‖y‖ :=
      (NormedSpace.inclusionInDoubleDualLi (𝕜 := 𝕜) (E := X)).norm_map
    calc ‖∑ i ∈ Finset.range m, a i • e i‖
      _ = ‖J (∑ i ∈ Finset.range m, a i • e i)‖ := (hJ_norm _).symm
      _ = ‖∑ i ∈ Finset.range m, a i • b_bidual i‖ := by rw [h_J_sum]
      _ ≤ K * ‖∑ i ∈ Finset.range n, a i • b_bidual i‖ :=
          basicSequence_satisfiesGrunblum b_bidual n m a hmn
      _ = K * ‖J (∑ i ∈ Finset.range n, a i • e i)‖ := by rw [h_J_sum]
      _ = K * ‖∑ i ∈ Finset.range n, a i • e i‖ := by rw [hJ_norm]

  -- Apply Grünblum criterion
  exact isBasicSequence_of_grunblum h_nz hK_bound_e


def SchauderBasis_of_closure [CompleteSpace X] {Y : Submodule 𝕜 X}
    (b : SchauderBasis 𝕜 Y) (h_bound : b.enormProjBound < ⊤) :
    SchauderBasis 𝕜 Y.topologicalClosure := by
  -- 1. Identify the closure Z and the inclusion map ι
  let Z := Y.topologicalClosure
  haveI : CompleteSpace Z := isClosed_closure.completeSpace_coe
  let ι : Y →L[𝕜] Z := (Submodule.inclusion Y.le_topologicalClosure).mkContinuous 1 (fun y => by
    simp only [one_mul, Submodule.coe_norm, Submodule.coe_inclusion, le_refl])
  have h_isometry : Isometry ι := fun y₁ y₂ => by
    simp only [ι, edist_dist, dist_eq_norm]
    congr 1
  -- 2. Verify that ι is a dense uniform embedding
  have h_dense : DenseRange ι := by
    have h_range : Set.range ι = {z : Z | (z : X) ∈ Y} := Set.ext fun z => ⟨
      fun ⟨y, hy⟩ => hy ▸ y.2,
      fun hz => ⟨⟨z, hz⟩, rfl⟩⟩
    rw [DenseRange, h_range, Subtype.dense_iff]
    intro x hxZ
    have hsub : (Y : Set X) ⊆ Subtype.val '' {z : Z | (z : X) ∈ Y} := fun y hy =>
      ⟨⟨y, subset_closure hy⟩, hy, rfl⟩
    exact closure_mono hsub hxZ
  have h_unif : IsUniformInducing ι := h_isometry.isUniformInducing
  -- 3. Extract the uniform bound C for the projections
  let C := b.enormProjBound.toReal
  have hC : 0 ≤ C := ENNReal.toReal_nonneg
  -- 4. Extend the projections P_n from Y to Z
  let P (n : ℕ) : Z →L[𝕜] Z := (ι.comp (b.proj n)).extend ι
  -- Helper: P' agrees with b.proj on Y
  have h_agree (n : ℕ) (y : Y) : P n (ι y) = ι (b.proj n y) := by
    simp only [P]
    rw [ContinuousLinearMap.extend_eq (e := ι) (ι ∘L b.proj n) h_dense h_unif y]
    rfl
  have h_uniform : ∀ n, ‖P n‖ ≤ C := by
    intro n
    simp only [P]
    have h_norm : ∀ x, ‖x‖ = ‖ι x‖ := fun x ↦ h_isometry.norm_map_of_map_zero (map_zero _) x
    refine (ContinuousLinearMap.opNorm_extend_le (ι.comp (b.proj n)) (N := 1) h_dense ?_).trans ?_
    · intro x; simp only [h_norm]
      simp only [AddSubgroupClass.coe_norm, NNReal.coe_one, one_mul]
      exact le_refl _
    rw [NNReal.coe_one, one_mul]
    calc
      ‖ι.comp (b.proj n)‖ ≤ ‖ι‖ * ‖b.proj n‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * ‖b.proj n‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        refine ι.opNorm_le_bound zero_le_one (fun x ↦ ?_)
        simp only [h_isometry.norm_map_of_map_zero (map_zero _), one_mul, le_refl]
      _ = ‖b.proj n‖ := by rw [one_mul]
      _ ≤ C := by
        dsimp only [C]
        apply (ENNReal.ofReal_le_iff_le_toReal h_bound.ne).mp
        simp only [ofReal_norm]
        exact b.norm_proj_le_enormProjBound n
  -- 5. Define the basis sequence in Z (inclusion of original basis)
  let e (n : ℕ) : Z := ι (b n)
  -- 6. Verify properties required for CanonicalProjectionProperties
  have h0 : P 0 = 0 := by
    simp only [P]
    have h_proj0 : b.proj 0 = 0 := b.proj_zero
    simp only [h_proj0, ContinuousLinearMap.comp_zero,
      ContinuousLinearMap.extend_zero h_dense h_unif]
  have hdim : ∀ n, Module.finrank 𝕜 (LinearMap.range (P n).toLinearMap) = n := by
    intro n
    -- The range of P n equals the span of {e 0, ..., e (n-1)}
    have h_range_eq : LinearMap.range (P n).toLinearMap =
        Submodule.span 𝕜 (Set.range (fun i : Fin n => e i)) := by
      apply le_antisymm
      · -- Range P n ⊆ span {e i | i < n}
        intro z hz
        obtain ⟨w, rfl⟩ := hz
        -- The span is finite-dimensional, hence closed
        let S := Submodule.span 𝕜 (Set.range (fun i : Fin n => e i))
        haveI : FiniteDimensional 𝕜 S := FiniteDimensional.span_of_finite 𝕜 (Set.finite_range _)
        have hS_closed : IsClosed (S : Set Z) := Submodule.closed_of_finiteDimensional S
        -- Use density: if property holds on ι(Y) and is closed, it holds on Z
        have h_P_in_S : ∀ z : Z, (P n) z ∈ S := fun z =>
          h_dense.induction_on (p := fun z => (P n) z ∈ S) z
            (hS_closed.preimage (P n).continuous)
            (fun y => by
              simp only [S]
              rw [h_agree, b.proj_apply]
              simp_rw [map_sum, map_smul]
              apply Submodule.sum_mem
              intro i hi
              have hi' : i < n := Finset.mem_range.mp hi
              have h_e_mem : e i ∈ Set.range (fun j : Fin n => e j) :=
                ⟨⟨i, hi'⟩, rfl⟩
              exact Submodule.smul_mem _ _ (Submodule.subset_span h_e_mem))
        exact h_P_in_S w
      · -- span {e i | i < n} ⊆ range(P n)
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        refine ⟨e i, ?_⟩
        -- P n (e i) = e i for i < n, using h_agree and proj_basis_element
        change (P n) (e i) = e i
        calc (P n) (e i) = (P n) (ι (b i)) := rfl
          _ = ι (b.proj n (b i)) := h_agree n (b i)
          _ = ι (b i) := by rw [b.proj_basis_element, if_pos i.is_lt]
          _ = e i := rfl
    rw [h_range_eq, finrank_span_eq_card]
    · exact Fintype.card_fin n
    · -- Linear independence of e restricted to Fin n
      have h_ι_inj : Function.Injective ι := h_isometry.injective
      have h_ind : LinearIndependent 𝕜 e :=
        b.linearIndependent.map' (Submodule.inclusion Y.le_topologicalClosure) (by
          simp only [Submodule.ker_inclusion])
      exact h_ind.comp (fun (i : Fin n) => (i : ℕ)) Fin.val_injective
  have hcomp : ∀ n m, ∀ x, P n (P m x) = P (min n m) x := by
    intro n m z
    -- Use density: prove for ι y, then extend by continuity
    apply h_dense.induction_on (p := fun z => (P n) ((P m) z) = (P (min n m)) z) z
    · -- The set {z | P n (P m z) = P (min n m) z} is closed
      exact isClosed_eq ((P n).continuous.comp (P m).continuous) (P (min n m)).continuous
    · -- For y : Y, P n (P m (ι y)) = P (min n m) (ι y)
      intro y
      calc (P n) ((P m) (ι y))
          = (P n) (ι (b.proj m y)) := by rw [h_agree]
        _ = ι (b.proj n (b.proj m y)) := by rw [h_agree]
        _ = ι (b.proj (min n m) y) := by rw [b.proj_comp]
        _ = (P (min n m)) (ι y) := by rw [← h_agree]
  have hlim : ∀ x, Filter.Tendsto (fun n ↦ P n x) Filter.atTop (𝓝 x) := by
    intro z
    -- Convergence on ι(Y): P n (ι y) → ι y
    have h_tendsto_on_Y : ∀ y : Y, Tendsto (fun n => (P n) (ι y)) atTop (𝓝 (ι y)) := fun y => by
      simp_rw [h_agree]; exact ι.continuous.continuousAt.tendsto.comp (b.tendsto_proj y)
    -- Extend to Z using density and uniform bounds
    rw [Metric.tendsto_atTop]; intro ε hε
    set C' := max C 0; have hC'1 : C' + 1 > 0 := by linarith [le_max_right C 0]
    have hC'_bound : ∀ n, ‖P n‖ ≤ C' := fun n => (h_uniform n).trans (le_max_left C 0)
    set δ := ε / (2 * (C' + 2)); have hδ_pos : δ > 0 := div_pos hε (by linarith)
    obtain ⟨_, ⟨y, rfl⟩, h_close⟩ := Metric.mem_closure_iff.mp
      (h_dense.closure_eq ▸ Set.mem_univ z) δ hδ_pos
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (h_tendsto_on_Y y) (ε / 2) (half_pos hε)
    refine ⟨N, fun n hn => ?_⟩
    have h1 : dist ((P n) z) ((P n) (ι y)) ≤ C' * dist z (ι y) := by
      simp only [dist_eq_norm, ← map_sub]
      exact ((P n).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hC'_bound n) (norm_nonneg _))
    have h2 : (C' + 1) * δ < ε / 2 := by
      have : C' + 2 > 0 := by linarith
      calc (C' + 1) * δ = (C' + 1) * ε / (2 * (C' + 2)) := by ring
        _ < (C' + 2) * ε / (2 * (C' + 2)) := by gcongr; linarith
        _ = ε / 2 := by field_simp
    calc dist ((P n) z) z
        ≤ dist ((P n) z) ((P n) (ι y)) + dist ((P n) (ι y)) (ι y) + dist (ι y) z :=
          dist_triangle4 _ _ _ _
      _ ≤ C' * dist z (ι y) + dist ((P n) (ι y)) (ι y) + dist z (ι y) := by
          rw [dist_comm (ι y)]; linarith [h1]
      _ = (C' + 1) * dist z (ι y) + dist ((P n) (ι y)) (ι y) := by ring
      _ < (C' + 1) * δ + ε / 2 := by linarith [mul_lt_mul_of_pos_left h_close hC'1, hN n hn]
      _ < ε := by linarith [h2]
  have he_range : ∀ n, e n ∈ LinearMap.range (SchauderBasis.succSub P n).toLinearMap := by
    intro n
    -- Show e n = Q n (e n), i.e., e n is in the range of Q n
    use e n
    simp only [SchauderBasis.succSub, ContinuousLinearMap.coe_sub, ContinuousLinearMap.coe_coe,
      LinearMap.sub_apply]
    -- Need to show P(n+1)(e n) - P n(e n) = e n
    have h1 : (P (n + 1)) (e n) = e n := by
      calc (P (n + 1)) (e n) = (P (n + 1)) (ι (b n)) := rfl
        _ = ι (b.proj (n + 1) (b n)) := h_agree (n + 1) (b n)
        _ = ι (b n) := by rw [b.proj_basis_element, if_pos (Nat.lt_succ_self n)]
        _ = e n := rfl
    have h2 : (P n) (e n) = 0 := by
      calc (P n) (e n) = (P n) (ι (b n)) := rfl
        _ = ι (b.proj n (b n)) := h_agree n (b n)
        _ = ι 0 := by rw [b.proj_basis_element, if_neg (Nat.lt_irrefl n)]
        _ = 0 := map_zero _
    rw [h1, h2, sub_zero]
  have he_ne : ∀ n, e n ≠ 0 := by
    intro n
    simp only [e, ne_eq]
    intro h
    have h_inj : Function.Injective ι := h_isometry.injective
    rw [← map_zero ι] at h
    have := h_inj h
    exact b.linearIndependent.ne_zero n this
  -- 7. Construct the basis using the projections
  exact (SchauderBasis.ProjectionData.mk P e h0 hdim hcomp hlim he_range he_ne).basis

/-- The closure basis vectors are the inclusion of the original basis vectors. -/
@[simp]
theorem SchauderBasis_of_closure_apply [CompleteSpace X] {Y : Submodule 𝕜 X}
    (b : SchauderBasis 𝕜 Y) (h_bound : b.enormProjBound < ⊤) (n : ℕ) :
    (SchauderBasis_of_closure b h_bound) n = ⟨b n, Y.le_topologicalClosure (b n).2⟩ :=
  rfl

/-- Functional equality version (as requested). -/
theorem SchauderBasis_of_closure_coe [CompleteSpace X] {Y : Submodule 𝕜 X}
    (b : SchauderBasis 𝕜 Y) (h_bound : b.enormProjBound < ⊤) :
    ⇑(SchauderBasis_of_closure b h_bound) = fun n ↦ ⟨b n, Y.le_topologicalClosure (b n).2⟩ :=
  funext fun n => SchauderBasis_of_closure_apply b h_bound n

end BasicSequence
