/-
Copyright (c) 2026 Michał Świętek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michał Świętek
-/
module

public import Mathlib.Analysis.Normed.Module.SchauderBasis.Selection
public import Mathlib.Analysis.Normed.Module.SchauderBasis.CountablyCompact
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.LocallyConvex.WeakSpace
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
  have h_nz : ∀ n, y n ≠ 0 := fun n h_zero ↦ by
    have : f (y n) = 1 := by simp [y, f.map_add, hf', hu0]
    rw [h_zero, f.map_zero] at this; exact zero_ne_one this
  have hK := basicSequence_satisfiesGrunblum b
  let K := b.basicSequenceConstant
  let C := 1 + ‖f‖ * ‖u‖
  have hC : 0 ≤ C := add_nonneg zero_le_one (mul_nonneg (norm_nonneg f) (norm_nonneg u))
  refine isBasicSequence_of_Grunblum (K := K * C ^ 2) h_nz fun n m a hnm ↦ ?_
  let Y k := ∑ i ∈ Finset.range k, a i • y i
  let E k := ∑ i ∈ Finset.range k, a i • b i
  have h_rel (k) : Y k = E k + f (Y k) • u := by
    simp only [Y, E, y, smul_add, Finset.sum_add_distrib, ← Finset.sum_smul]; congr 1
    simp only [map_add, map_sum, map_smul, hf', hu0, smul_eq_mul, mul_one, mul_zero, add_zero]
  have h_pert (v : X) : ‖v‖ + ‖f v • u‖ ≤ C * ‖v‖ := by
    calc ‖v‖ + ‖f v • u‖ = ‖v‖ + ‖f v‖ * ‖u‖ := by rw [norm_smul]
      _ ≤ ‖v‖ + ‖f‖ * ‖v‖ * ‖u‖ := by gcongr; exact f.le_opNorm v
      _ = C * ‖v‖ := by ring
  have h_E_Y (k) : ‖E k‖ ≤ C * ‖Y k‖ := by
    rw [(sub_eq_of_eq_add (h_rel k)).symm]
    exact (norm_sub_le _ _).trans (h_pert (Y k))
  have h_Y_E (k) : ‖Y k‖ ≤ C * ‖E k‖ := by
    have : f (Y k) = f (E k) := by rw [h_rel k, map_add, map_smul, hu0, smul_zero, add_zero]
    rw [h_rel k, this]; exact (norm_add_le _ _).trans (h_pert (E k))
  calc ‖Y m‖
    _ ≤ C * ‖E m‖ := h_Y_E m
    _ ≤ C * (K * ‖E n‖) := by gcongr; exact hK n m a hnm
    _ ≤ C * (K * (C * ‖Y n‖)) := by
        apply mul_le_mul_of_nonneg_left _ hC
        exact mul_le_mul_of_nonneg_left (h_E_Y n)
          (zero_le_one.trans b.basicSequenceConstant_ge_one)
    _ = (K * C ^ 2) * ‖Y n‖ := by ring

-- TODO contrapose the statement
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
    have hce : IsClosedEmbedding (NormedSpace.inclusionInDoubleDualLi (𝕜 := 𝕜) (E := X)) := by
      let li := NormedSpace.inclusionInDoubleDualLi (𝕜 := 𝕜) (E := X)
      have : @Isometry X (StrongDual 𝕜 (StrongDual 𝕜 X))
          EMetricSpace.toPseudoEMetricSpace EMetricSpace.toPseudoEMetricSpace li :=
        fun x y => li.isometry.edist_eq x y
      exact this.isClosedEmbedding
    rw [show S' = (NormedSpace.inclusionInDoubleDualLi (𝕜 := 𝕜) (E := X)) '' S from rfl,
      hce.closure_image_eq]
    have hJ0 : (NormedSpace.inclusionInDoubleDualLi (𝕜 := 𝕜) (E := X)) 0 = 0 :=
      map_zero (NormedSpace.inclusionInDoubleDualLi (𝕜 := 𝕜) (E := X)).toContinuousLinearMap
    exact fun ⟨x, hx, hJx⟩ =>
      h_norm (hce.injective (hJx.trans hJ0.symm) ▸ hx)
  -- 4. Apply the Selection Principle for Dual Spaces with ε = 1.
  obtain ⟨b_bidual, hb_mem, -⟩ :=
    basic_sequence_selection_dual h_weak_star h_norm_S' zero_lt_one
  -- 5. Pull the basic sequence back to X using the pullback lemma.
  have hb_basic : IsBasicSequence 𝕜 ⇑b_bidual := ⟨b_bidual, rfl⟩
  exact hb_basic.pullback J
    (NormedSpace.inclusionInDoubleDualLi (𝕜 := 𝕜) (E := X)).norm_map hb_mem

/-- Contrapositive of `not_mem_weakClosure_of_no_basicSequence`: if `0` is in the weak closure
of `S` but not in the norm closure, then `S` contains a basic sequence. -/
theorem exists_basicSequence_of_weakClosure_not_normClosure [CompleteSpace X]
    {S : Set X} (hS_ne : S.Nonempty) (h_norm : (0 : X) ∉ closure S)
    (h_weak : (0 : X) ∈ closure (toWeakSpace 𝕜 X '' S)) :
    ∃ e : ℕ → X, (∀ n, e n ∈ S) ∧ IsBasicSequence 𝕜 e := by
  by_contra h_no; push_neg at h_no
  exact (not_mem_weakClosure_of_no_basicSequence hS_ne h_norm h_no) h_weak

def schauderBasisOfClosure [CompleteSpace X] {Y : Submodule 𝕜 X}
    (b : SchauderBasis 𝕜 Y) (h_bound : b.enormProjBound < ⊤) :
    SchauderBasis 𝕜 Y.topologicalClosure := by
  let Z := Y.topologicalClosure
  haveI : CompleteSpace Z := isClosed_closure.completeSpace_coe
  let ι : Y →L[𝕜] Z := (Submodule.inclusion Y.le_topologicalClosure).mkContinuous 1 (fun y => by
    simp only [one_mul, Submodule.coe_norm, Submodule.coe_inclusion, le_refl])
  have h_isometry : Isometry ι :=
    AddMonoidHomClass.isometry_of_norm ι fun _ => rfl
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
  let C := b.enormProjBound.toReal
  have hC : 0 ≤ C := ENNReal.toReal_nonneg
  let P (n : ℕ) : Z →L[𝕜] Z := (ι.comp (b.proj n)).extend ι
  have h_agree (n : ℕ) (y : Y) : P n (ι y) = ι (b.proj n y) := by
    simp only [P]; exact ContinuousLinearMap.extend_eq _ h_dense h_unif y
  let e (n : ℕ) : Z := ι (b n)
  have h_ι_norm : ‖ι‖ ≤ 1 :=
    ι.opNorm_le_bound zero_le_one fun x ↦ by
      simp [h_isometry.norm_map_of_map_zero (map_zero _)]
  have h_uniform : ∀ n, ‖P n‖ ≤ C := fun n => by
    simp only [P]
    refine (ContinuousLinearMap.opNorm_extend_le (ι.comp (b.proj n)) (N := 1) h_dense
      (fun x ↦ by simp [h_isometry.norm_map_of_map_zero (map_zero _)])).trans ?_
    rw [NNReal.coe_one, one_mul]
    calc ‖ι.comp (b.proj n)‖
        ≤ ‖b.proj n‖ := (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_of_le_one_left (norm_nonneg _) h_ι_norm)
      _ ≤ C := by
          dsimp only [C]
          exact (ENNReal.ofReal_le_iff_le_toReal h_bound.ne).mp
            (by simp only [ofReal_norm]; exact b.norm_proj_le_enormProjBound n)
  have hlim : ∀ x, Filter.Tendsto (fun n ↦ P n x) Filter.atTop (𝓝 x) := fun z => by
    have h_tendsto_on_Y : ∀ y : Y, Tendsto (fun n => (P n) (ι y)) atTop (𝓝 (ι y)) := fun y => by
      simp_rw [h_agree]; exact ι.continuous.continuousAt.tendsto.comp (b.tendsto_proj y)
    rw [Metric.tendsto_atTop]; intro ε hε
    have hC1_pos : C + 1 > 0 := by linarith
    obtain ⟨_, ⟨y, rfl⟩, h_close⟩ := Metric.mem_closure_iff.mp
      (h_dense.closure_eq ▸ Set.mem_univ z) (ε / (2 * (C + 1))) (div_pos hε (by linarith))
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (h_tendsto_on_Y y) (ε / 2) (half_pos hε)
    refine ⟨N, fun n hn => ?_⟩
    have h1 : dist ((P n) z) ((P n) (ι y)) ≤ C * dist z (ι y) := by
      simp only [dist_eq_norm, ← map_sub]
      exact ((P n).le_opNorm _).trans (mul_le_mul_of_nonneg_right (h_uniform n) (norm_nonneg _))
    calc dist ((P n) z) z
        ≤ dist ((P n) z) ((P n) (ι y)) + dist ((P n) (ι y)) (ι y) + dist (ι y) z :=
          dist_triangle4 ..
      _ ≤ (C + 1) * dist z (ι y) + dist ((P n) (ι y)) (ι y) := by
          rw [dist_comm (ι y)]; linarith [h1]
      _ < (C + 1) * (ε / (2 * (C + 1))) + ε / 2 :=
          add_lt_add (mul_lt_mul_of_pos_left h_close hC1_pos) (hN n hn)
      _ = ε := by field_simp; ring
  let coord_ext (n : ℕ) : StrongDual 𝕜 Z := (b.coord n).extend ι
  have h_coord_agree (n : ℕ) (y : Y) : coord_ext n (ι y) = b.coord n y :=
    ContinuousLinearMap.extend_eq (b.coord n) h_dense h_unif y
  have h_partial_eq_P (n : ℕ) (z : Z) :
      ∑ i ∈ Finset.range n, coord_ext i z • e i = P n z :=
    congr_fun (DenseRange.equalizer h_dense
      (continuous_finset_sum _ fun i _ => ((coord_ext i).continuous.smul continuous_const))
      (P n).continuous
      (funext fun y => by
        simp only [Function.comp_apply, e]
        rw [h_agree]
        simp_rw [b.proj_apply, map_sum, map_smul, h_coord_agree])) z
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

variable (bs : BasicSequence 𝕜 X)

theorem cluster_point_of_basicSequence [CompleteSpace X] (x : X)
    (hx : MapClusterPt (X := WeakSpace 𝕜 X) x atTop bs) : x = 0 := by
  -- Setup: Y = span, Z = closure of span
  set Y := Submodule.span 𝕜 (Set.range bs.toFun) with hY_def
  set Z := Y.topologicalClosure with hZ_def
  -- Step 1: Show x ∈ Z
  -- Every bs n is in Z
  have h_range_Z : ∀ n, bs.toFun n ∈ (Z : Set X) :=
    fun n => Y.le_topologicalClosure (Submodule.subset_span (Set.mem_range_self n))
  -- x is in the weak closure of Z, and Z is weakly closed by Mazur
  haveI : NormedSpace ℝ X := NormedSpace.restrictScalars ℝ 𝕜 X
  have h_convex_Z : Convex ℝ (Z : Set X) :=
    (Submodule.convex (Y.restrictScalars ℝ)).closure
  have h_norm_closed : closure (Z : Set X) = (Z : Set X) :=
    IsClosed.closure_eq (Submodule.isClosed_topologicalClosure Y)
  -- Mazur: toWeakSpace '' closure Z = closure (toWeakSpace '' Z)
  have h_mazur := h_convex_Z.toWeakSpace_closure (𝕜 := 𝕜)
  rw [h_norm_closed] at h_mazur
  -- So toWeakSpace '' Z is weakly closed
  have h_wcl_eq : closure (toWeakSpace 𝕜 X '' (Z : Set X)) = toWeakSpace 𝕜 X '' (Z : Set X) :=
    h_mazur.symm
  -- x ∈ weak closure of Z
  have h_in_wcl : (toWeakSpace 𝕜 X x) ∈ closure (toWeakSpace 𝕜 X '' (Z : Set X)) := by
    apply clusterPt_iff_forall_mem_closure.mp hx.clusterPt
    rw [Filter.mem_map]
    exact Filter.Eventually.of_forall fun n => Set.mem_image_of_mem _ (h_range_Z n)
  rw [h_wcl_eq] at h_in_wcl
  obtain ⟨z, hz, hzx⟩ := h_in_wcl
  have h_mem_Z : x ∈ (Z : Set X) := by
    have : z = x := (toWeakSpace 𝕜 X).injective hzx
    rwa [this] at hz
  -- Step 2: Construct closure basis
  set b_cl := schauderBasisOfClosure bs.basis bs.basisConstant_lt_top
  -- Step 3: Show all coordinates vanish
  suffices h_coord : ∀ n, b_cl.coord n ⟨x, h_mem_Z⟩ = 0 by
    -- Step 4: Conclude x = 0 from expansion uniqueness
    have h_exp := b_cl.expansion ⟨x, h_mem_Z⟩
    have h_zero_exp : HasSum (fun _ : ℕ => (0 : ↥Z)) 0 (SummationFilter.conditional ℕ) := by
      convert hasSum_zero using 1
    have h_eq : HasSum (fun i => b_cl.coord i ⟨x, h_mem_Z⟩ • b_cl i) 0
        (SummationFilter.conditional ℕ) := by
      convert h_zero_exp using 1; ext n; simp [h_coord n]
    have h_x_eq_0 : (⟨x, h_mem_Z⟩ : ↥Z) = 0 := h_exp.unique h_eq
    exact congr_arg Subtype.val h_x_eq_0
  -- Prove each coordinate vanishes
  intro n
  -- Extend b_cl.coord n : Z →L[𝕜] 𝕜 to g : X →L[𝕜] 𝕜 via Hahn-Banach
  obtain ⟨g, hg_ext, -⟩ := exists_extension_norm_eq Z (b_cl.coord n)
  -- g(bs m) = b_cl.coord n (b_cl m) = δ_{nm}
  have h_g_bs : ∀ m, g (bs.toFun m) = (Pi.single m (1 : 𝕜) : ℕ → 𝕜) n := by
    intro m
    change g ↑(⟨bs.toFun m, h_range_Z m⟩ : ↥Z) = _; rw [hg_ext]
    -- Show ⟨bs m, _⟩ = b_cl m via schauderBasisOfClosure_apply
    have h_basis : (⟨bs.toFun m, h_range_Z m⟩ : ↥Z) = b_cl m :=
      Subtype.ext (by
        change bs.toFun m = ↑(schauderBasisOfClosure bs.basis bs.basisConstant_lt_top m)
        rw [schauderBasisOfClosure_apply]; exact (bs.basis_eq m).symm)
    rw [h_basis]
    convert b_cl.ortho n m
  -- g ∘ bs is eventually 0 (for m > n, Pi.single m 1 n = 0)
  have h_eventually_zero : ∀ᶠ m in Filter.atTop, g (bs.toFun m) = 0 := by
    filter_upwards [Filter.eventually_ge_atTop (n + 1)] with m hm
    rw [h_g_bs m, Pi.single_apply, if_neg (by omega)]
  -- g ∘ bs converges to 0
  have h_tendsto : Filter.Tendsto (g ∘ bs.toFun) Filter.atTop (𝓝 0) :=
    Filter.Tendsto.congr' (Filter.Eventually.mono h_eventually_zero
      (fun m hm => hm.symm)) tendsto_const_nhds
  -- g is weakly continuous (evaluation by a functional is continuous in weak topology)
  have h_g_weak_cont : Continuous (fun y : WeakSpace 𝕜 X => g y) :=
    WeakBilin.eval_continuous (topDualPairing 𝕜 X).flip g
  -- g x is a cluster point of g ∘ bs (avoid topology mismatch by using frequently)
  have h_cluster_g : MapClusterPt (g x) Filter.atTop (g ∘ bs.toFun) := by
    rw [mapClusterPt_iff_frequently]
    intro s hs
    exact mapClusterPt_iff_frequently.mp hx _ (h_g_weak_cont.continuousAt hs)
  -- In a T2 space, cluster point of convergent net equals limit
  have h_gx_eq_0 : g x = 0 :=
    t2_iff_nhds.mp inferInstance (h_cluster_g.clusterPt.mono h_tendsto)
  -- Transfer: b_cl.coord n ⟨x, h_mem_Z⟩ = g ↑⟨x, h_mem_Z⟩ = g x = 0
  rw [← hg_ext ⟨x, h_mem_Z⟩]
  exact h_gx_eq_0

/-- If `e` is a basic sequence and `y` is a weak cluster point of the sequence
`fun n => toWeakSpace 𝕜 X (e n + x₀)`, then `y = toWeakSpace 𝕜 X x₀`. -/
theorem weakClusterPt_of_basicSequence_add [CompleteSpace X]
    {e : ℕ → X} (he : IsBasicSequence 𝕜 e) (x₀ : X)
    {y : WeakSpace 𝕜 X}
    (hy : MapClusterPt y atTop (fun n => toWeakSpace 𝕜 X (e n + x₀))) :
    y = toWeakSpace 𝕜 X x₀ := by
  suffices h : y - toWeakSpace 𝕜 X x₀ = 0 by rwa [sub_eq_zero] at h
  have h_sub : MapClusterPt (y - toWeakSpace 𝕜 X x₀) atTop
      (fun n => toWeakSpace 𝕜 X (e n)) := by
    have h_eq : (fun n => toWeakSpace 𝕜 X (e n)) =
        (fun n => toWeakSpace 𝕜 X (e n + x₀) - toWeakSpace 𝕜 X x₀) := by
      ext n; simp [map_add]
    rw [h_eq]
    exact hy.tendsto_comp (continuous_id.sub continuous_const).continuousAt.tendsto
  let b := he.toBasicSequence
  have h_cluster_b : MapClusterPt (X := WeakSpace 𝕜 X) (y - toWeakSpace 𝕜 X x₀) atTop b := by
    convert h_sub using 1
    exact IsBasicSequence.coe_toBasicSequence he
  exact cluster_point_of_basicSequence b _ h_cluster_b

theorem unique_clusterPt_limit
  (A : Set (WeakSpace 𝕜 X))
  (hA : IsCountablyCompact A)
  (w : X)
  (x : ℕ → WeakSpace 𝕜 X)
  (h_seq : ∀ n, x n ∈ A)
  (h_unique : ∀ y : WeakSpace 𝕜 X,
    MapClusterPt y atTop x → y = w) :
  Tendsto x atTop (𝓝 w) := by
  by_contra h_not
  obtain ⟨U, hU_mem, hU_freq⟩ := Filter.not_tendsto_iff_exists_frequently_notMem.mp h_not
  obtain ⟨φ, hφ_strict, hφ_outside⟩ := Filter.extraction_of_frequently_atTop hU_freq
  have h_sub : ∀ n, (x ∘ φ) n ∈ A := fun n => h_seq (φ n)
  obtain ⟨y, -, hy_cluster⟩ := hA (x ∘ φ) h_sub
  have hy_original : MapClusterPt y atTop x :=
    hy_cluster.of_comp hφ_strict.tendsto_atTop
  have hy_eq : y = w := h_unique y hy_original
  subst hy_eq
  exact (hy_cluster.frequently hU_mem) (Filter.Eventually.of_forall hφ_outside)

end BasicSequence
