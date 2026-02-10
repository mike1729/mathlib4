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

* `perturbBasicSequence`: A perturbation of a basic sequence by a fixed vector
  (under suitable functional conditions) is still a basic sequence.
* `not_mem_weakClosure_of_no_basicSequence`: If a bounded set contains no basic
  sequence, then 0 is not in its weak closure.
* `schauderBasisOfClosure`: Constructs a Schauder basis for the topological closure
  from a Schauder basis on a subspace.
-/

@[expose] public section

noncomputable section

open Submodule Set WeakDual Metric Filter Topology

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- The inclusion of a normed space into its double dual is an embedding
    from the weak topology to the weak-star topology. -/
theorem NormedSpace.inclusionInDoubleDual_isEmbedding_weak
    (𝕜 : Type*) [RCLike 𝕜] (X : Type*) [NormedAddCommGroup X] [NormedSpace 𝕜 X] :
    IsEmbedding (fun x : WeakSpace 𝕜 X =>
      StrongDual.toWeakDual (NormedSpace.inclusionInDoubleDual 𝕜 X x)) := by
  let J := NormedSpace.inclusionInDoubleDual 𝕜 X
  let ι := fun x : WeakSpace 𝕜 X => StrongDual.toWeakDual (J x)
  -- Both topologies are induced by the same family of maps: x ↦ (fun f => f x)
  -- WeakSpace 𝕜 X: induced by topDualPairing.flip; WeakDual 𝕜 X**: induced by eval
  -- Composition: (ι x)(f) = (J x)(f) = f(x), so evalWeakDual ∘ ι = evalWeakSpace
  let evalWeakSpace : WeakSpace 𝕜 X → (StrongDual 𝕜 X → 𝕜) := fun x f => f x
  let evalWeakDual : WeakDual 𝕜 (StrongDual 𝕜 X) → (StrongDual 𝕜 X → 𝕜) := fun φ f => φ f
  have h_commute : evalWeakDual ∘ ι = evalWeakSpace := by ext x f; rfl
  -- Injectivity: J is injective (isometry) and toWeakDual is injective
  have h_inj : Function.Injective ι := by
    intro x y hxy
    simp only [ι] at hxy
    have h1 : J x = J y := StrongDual.toWeakDual.injective hxy
    exact (NormedSpace.inclusionInDoubleDualLi (𝕜 := 𝕜) (E := X)).injective h1
  -- Inducing: both topologies are induced from Pi, and evalWeakDual ∘ ι = evalWeakSpace
  have h_ind : IsInducing ι := by
    constructor; symm
    calc TopologicalSpace.induced ι (TopologicalSpace.induced evalWeakDual Pi.topologicalSpace)
        = TopologicalSpace.induced (evalWeakDual ∘ ι) Pi.topologicalSpace := induced_compose
      _ = TopologicalSpace.induced evalWeakSpace Pi.topologicalSpace := by rw [h_commute]
  exact ⟨h_ind, h_inj⟩

namespace BasicSequence

/- -/
lemma perturbBasicSequence [CompleteSpace X] (b : BasicSequence 𝕜 X)
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
theorem not_mem_weakClosure_of_no_basicSequence [CompleteSpace X]
    {S : Set X} (_hS_ne : S.Nonempty) (h_norm : (0 : X) ∉ closure S)
    (h_no_basic : ∀ (e : ℕ → X), (∀ n, e n ∈ S) → ¬ IsBasicSequence 𝕜 e) :
    (0 : X) ∉ closure (toWeakSpace 𝕜 X '' S) := by
  -- We prove the contrapositive: if 0 is in the weak closure, we can find a basic sequence.
  contrapose! h_no_basic
  -- 1. Setup the Bidual embedding J : X → X**
  let J := NormedSpace.inclusionInDoubleDual 𝕜 X
  let S' := J '' S
  -- 2. Translate the weak closure hypothesis to the bidual's weak* topology.
  -- The embedding φ : WeakSpace X → WeakDual X** satisfies closure s = φ⁻¹' closure (φ '' s).
  have h_weak_star : (0 : WeakDual 𝕜 (StrongDual 𝕜 X)) ∈ closure (StrongDual.toWeakDual '' S') := by
    let φ := fun x : WeakSpace 𝕜 X => StrongDual.toWeakDual (J x)
    have hemb := NormedSpace.inclusionInDoubleDual_isEmbedding_weak 𝕜 X
    have h_eq : StrongDual.toWeakDual '' S' = φ '' (toWeakSpace 𝕜 X '' S) := by
      simp only [S', Set.image_image]; rfl
    rw [h_eq]; rw [hemb.closure_eq_preimage_closure_image] at h_no_basic
    have h0 : φ (toWeakSpace 𝕜 X 0) = 0 := by simp [φ, map_zero]
    exact h0 ▸ (Set.mem_preimage.mp h_no_basic)
  -- 3. Show 0 is not in the norm closure of S' in the bidual.
  -- Since J is an isometry from a complete space, it is a closed embedding.
  have h_norm_S' : (0 : StrongDual 𝕜 (StrongDual 𝕜 X)) ∉ closure S' := by
    have hce := (NormedSpace.inclusionInDoubleDualLi (𝕜 := 𝕜) (E := X)).isometry.isClosedEmbedding
    rw [show S' = (NormedSpace.inclusionInDoubleDualLi (𝕜 := 𝕜) (E := X)) '' S from rfl,
      hce.closure_image_eq]
    exact fun ⟨x, hx, hJx⟩ => h_norm (hce.injective (hJx.trans (map_zero _).symm) ▸ hx)
  -- 4. Apply the Selection Principle for Dual Spaces with ε = 1.
  obtain ⟨b_bidual, hb_mem, -⟩ :=
    basic_sequence_selection_dual h_weak_star h_norm_S' zero_lt_one
  -- 5. Pull the basic sequence back to X using the pullback lemma.
  have hb_basic : IsBasicSequence 𝕜 ⇑b_bidual := ⟨b_bidual, rfl⟩
  exact hb_basic.pullback J
    (NormedSpace.inclusionInDoubleDualLi (𝕜 := 𝕜) (E := X)).norm_map hb_mem



def schauderBasisOfClosure [CompleteSpace X] {Y : Submodule 𝕜 X}
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
  -- 5. Define the basis sequence in Z (inclusion of original basis)
  let e (n : ℕ) : Z := ι (b n)
  have h_ι_norm : ‖ι‖ ≤ 1 :=
    ι.opNorm_le_bound zero_le_one (fun x ↦ by
      simp only [h_isometry.norm_map_of_map_zero (map_zero _), one_mul, le_refl])
  have h_uniform : ∀ n, ‖P n‖ ≤ C := by
    intro n
    simp only [P]
    have h_norm : ∀ x, ‖x‖ = ‖ι x‖ := fun x ↦ h_isometry.norm_map_of_map_zero (map_zero _) x
    refine (ContinuousLinearMap.opNorm_extend_le (ι.comp (b.proj n)) (N := 1) h_dense
      (fun x ↦ by simp [h_norm])).trans ?_
    rw [NNReal.coe_one, one_mul]
    calc ‖ι.comp (b.proj n)‖
        ≤ ‖ι‖ * ‖b.proj n‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * ‖b.proj n‖ := by gcongr
      _ = ‖b.proj n‖ := one_mul _
      _ ≤ C := by
        dsimp only [C]
        exact (ENNReal.ofReal_le_iff_le_toReal h_bound.ne).mp
          (by simp only [ofReal_norm]; exact b.norm_proj_le_enormProjBound n)
  -- 6. Convergence: P n x → x for all x ∈ Z
  have hlim : ∀ x, Filter.Tendsto (fun n ↦ P n x) Filter.atTop (𝓝 x) := by
    intro z
    have h_tendsto_on_Y : ∀ y : Y, Tendsto (fun n => (P n) (ι y)) atTop (𝓝 (ι y)) := fun y => by
      simp_rw [h_agree]; exact ι.continuous.continuousAt.tendsto.comp (b.tendsto_proj y)
    rw [Metric.tendsto_atTop]; intro ε hε
    have hC1 : C + 1 > 0 := by linarith
    set δ := ε / (2 * (C + 2)); have hδ_pos : δ > 0 := div_pos hε (by linarith)
    obtain ⟨_, ⟨y, rfl⟩, h_close⟩ := Metric.mem_closure_iff.mp
      (h_dense.closure_eq ▸ Set.mem_univ z) δ hδ_pos
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (h_tendsto_on_Y y) (ε / 2) (half_pos hε)
    refine ⟨N, fun n hn => ?_⟩
    have h1 : dist ((P n) z) ((P n) (ι y)) ≤ C * dist z (ι y) := by
      simp only [dist_eq_norm, ← map_sub]
      exact ((P n).le_opNorm _).trans (mul_le_mul_of_nonneg_right (h_uniform n) (norm_nonneg _))
    have h2 : (C + 1) * δ < ε / 2 := by
      calc (C + 1) * δ = (C + 1) * ε / (2 * (C + 2)) := by ring
        _ < (C + 2) * ε / (2 * (C + 2)) := by gcongr; linarith
        _ = ε / 2 := by field_simp
    calc dist ((P n) z) z
        ≤ dist ((P n) z) ((P n) (ι y)) + dist ((P n) (ι y)) (ι y) + dist (ι y) z :=
          dist_triangle4 _ _ _ _
      _ ≤ C * dist z (ι y) + dist ((P n) (ι y)) (ι y) + dist z (ι y) := by
          rw [dist_comm (ι y)]; linarith [h1]
      _ = (C + 1) * dist z (ι y) + dist ((P n) (ι y)) (ι y) := by ring
      _ < (C + 1) * δ + ε / 2 := by linarith [mul_lt_mul_of_pos_left h_close hC1, hN n hn]
      _ < ε := by linarith [h2]
  -- 7. Extend each coordinate functional from Y to Z
  let coord_ext (n : ℕ) : StrongDual 𝕜 Z := (b.coord n).extend ι
  have h_coord_agree (n : ℕ) (y : Y) : coord_ext n (ι y) = b.coord n y :=
    ContinuousLinearMap.extend_eq (b.coord n) h_dense h_unif y
  -- 8. Partial sums of the extended coords equal the projection operators
  have h_partial_eq_P (n : ℕ) (z : Z) :
      ∑ i ∈ Finset.range n, coord_ext i z • e i = P n z :=
    congr_fun (DenseRange.equalizer h_dense
      (continuous_finset_sum _ fun i _ => ((coord_ext i).continuous.smul continuous_const))
      (P n).continuous
      (funext fun y => by
        simp only [Function.comp_apply, e]
        rw [h_agree]
        simp_rw [b.proj_apply, map_sum, map_smul, h_coord_agree])) z
  -- 9. Construct the SchauderBasis directly
  exact {
    basis := e
    coord := coord_ext
    ortho := fun i j => by
      change coord_ext i (e j) = _
      simp only [e]; rw [h_coord_agree]; exact b.ortho i j
    expansion := fun z => by
      rw [HasSum, SummationFilter.conditional_filter_eq_map_range, Filter.tendsto_map'_iff]
      exact (hlim z).congr (fun n => (h_partial_eq_P n z).symm)
  }

/-- The closure basis vectors are the inclusion of the original basis vectors. -/
@[simp]
theorem schauderBasisOfClosure_apply [CompleteSpace X] {Y : Submodule 𝕜 X}
    (b : SchauderBasis 𝕜 Y) (h_bound : b.enormProjBound < ⊤) (n : ℕ) :
    (schauderBasisOfClosure b h_bound) n = ⟨b n, Y.le_topologicalClosure (b n).2⟩ :=
  rfl

/-- Functional equality version (as requested). -/
theorem schauderBasisOfClosure_coe [CompleteSpace X] {Y : Submodule 𝕜 X}
    (b : SchauderBasis 𝕜 Y) (h_bound : b.enormProjBound < ⊤) :
    ⇑(schauderBasisOfClosure b h_bound) = fun n ↦ ⟨b n, Y.le_topologicalClosure (b n).2⟩ :=
  funext fun n => schauderBasisOfClosure_apply b h_bound n

end BasicSequence
