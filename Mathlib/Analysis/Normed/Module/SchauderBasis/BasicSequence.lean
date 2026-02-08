/-
Copyright (c) 2026 Michał Świętek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michał Świętek
-/
module

public import Mathlib.Analysis.Normed.Module.SchauderBasis.Basic
public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.Analysis.LocallyConvex.Separation


/-!
# Basic Sequences in Banach Spaces

This file defines the basic sequence structures and foundational lemmas.

## Main Definitions

* `GeneralBasicSequence`: A bundled sequence that forms a generalized Schauder basis for its span.
* `BasicSequence`: A bundled ℕ-indexed sequence that forms a Schauder basis for its closed span.
* `IsBasicSequence`: Predicate for a sequence being a basic sequence.
* `IsGeneralBasicSequence`: Predicate for a general basic sequence.

## Main Results

* `functional_vanishes_on_set_of_bound`: A functional with a lower bound on a scaling-closed set
  containing 0 must vanish on that set.
* `exists_functional_neg_one_and_vanishes_on_closed_submodule`: Hahn-Banach separation for
  a point outside a closed submodule.
-/

@[expose] public section

noncomputable section

open Submodule Set WeakDual Metric Filter Topology

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- A `GeneralBasicSequence` is a bundled sequence indexed by `β` that forms a
    generalized Schauder basis for its algebraic span. No boundedness field is included;
    boundedness is tracked separately via `enormProjBound`. -/
structure GeneralBasicSequence (β : Type*) (𝕜 : Type*) (X : Type*)
    [NontriviallyNormedField 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (L : SummationFilter β) where
  toFun : β → X
  basis : GeneralSchauderBasis β 𝕜 (Submodule.span 𝕜 (Set.range toFun)) L
  basis_eq : ⇑basis = Set.codRestrict toFun (Submodule.span 𝕜 (Set.range toFun))
      (fun i ↦ Submodule.subset_span (Set.mem_range_self i))

instance {β : Type*} {L : SummationFilter β} :
    CoeFun (GeneralBasicSequence β 𝕜 X L) (fun _ ↦ β → X) where
  coe b := b.toFun

/-- A `BasicSequence` is a sequence indexed by `ℕ` that forms a Schauder basis
    for its closed span. No boundedness field; track via `enormProjBound`. -/
structure BasicSequence (𝕜 : Type*) (X : Type*) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] where
  toFun : ℕ → X
  basis : SchauderBasis 𝕜 (Submodule.span 𝕜 (Set.range toFun))
  basis_eq : ⇑basis = Set.codRestrict toFun (Submodule.span 𝕜 (Set.range toFun))
      (fun i ↦ Submodule.subset_span (Set.mem_range_self i))

instance : CoeFun (BasicSequence 𝕜 X) (fun _ ↦ ℕ → X) where
  coe b := b.toFun

/-- A sequence `e` is a basic sequence if there exists a `BasicSequence` structure
    whose underlying sequence is equal to `e` and whose projection bound is finite. -/
def IsBasicSequence (𝕜 : Type*) {X : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] (e : ℕ → X) : Prop :=
  ∃ b : BasicSequence 𝕜 X, ⇑b = e ∧ b.basis.enormProjBound < ⊤

/-- A sequence `e : β → X` is a general basic sequence if there exists a
    `GeneralBasicSequence` structure whose underlying sequence equals `e`
    and whose projection bound is finite. -/
def IsGeneralBasicSequence (β : Type*) (𝕜 : Type*) {X : Type*}
    [NontriviallyNormedField 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (L : SummationFilter β) (e : β → X) : Prop :=
  ∃ b : GeneralBasicSequence β 𝕜 X L,
    b.toFun = e ∧ (⨆ A : Finset β, ‖b.basis.proj A‖ₑ) < ⊤

namespace BasicSequences

/-- A continuous linear functional with a lower bound on a set closed under 𝕜-scaling and containing 0
    must vanish on that set. If u < re(g y) for all y ∈ S, 0 ∈ S, and c • y ∈ S for all c : 𝕜, y ∈ S,
    then g = 0 on S. -/
lemma functional_vanishes_on_set_of_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {S : Set E} (h0 : (0 : E) ∈ S) (hS_smul : ∀ (c : 𝕜) (y : E), y ∈ S → c • y ∈ S)
    (g : E →L[𝕜] 𝕜) (u : ℝ) (hg_bound : ∀ y ∈ S, u < RCLike.re (g y)) :
    ∀ y ∈ S, g y = 0 := by
  intro y hy
  by_contra h_ne
  let gy : 𝕜 := g y
  have hnorm_pos : 0 < ‖gy‖ := norm_pos_iff.mpr h_ne
  have hnorm_ne : ‖gy‖ ≠ 0 := ne_of_gt hnorm_pos
  -- u < 0 since 0 ∈ S
  have hu_neg : u < 0 := by simpa using hg_bound 0 h0
  -- Choose c such that c * gy is a negative real number
  let c : 𝕜 := -star gy / ‖gy‖
  have hcy_mem : c • y ∈ S := hS_smul c y hy
  have h_gc : g (c • y) = c * gy := by simp [gy, smul_eq_mul]
  have h_re : RCLike.re (c * gy) = -‖gy‖ := by
    simp only [c, neg_div, neg_mul, div_mul_eq_mul_div]
    simp only [map_neg, neg_inj]
    have h_conj : star gy * gy = (‖gy‖ : 𝕜)^2 := by
      rw [RCLike.star_def, RCLike.conj_mul, sq]
    rw [h_conj, sq]
    have h_simpl : (‖gy‖ : 𝕜) * ‖gy‖ / (‖gy‖ : 𝕜) = ‖gy‖ := by field_simp
    rw [h_simpl, RCLike.ofReal_re]
  -- Scale further to make re(g(t • c • y)) < u
  let t : ℝ := (|u| + 1) / ‖gy‖ + 1
  have ht_pos : 0 < t := by positivity
  have htcy_mem : (t : 𝕜) • (c • y) ∈ S := hS_smul (t : 𝕜) (c • y) hcy_mem
  have h_gtc : g ((t : 𝕜) • (c • y)) = (t : 𝕜) * (c * gy) := by
    simp only [map_smul, smul_eq_mul, h_gc]
  have h_re_t : RCLike.re ((t : 𝕜) * (c * gy)) = t * (-‖gy‖) := by
    rw [RCLike.re_ofReal_mul, h_re]
  have h_bound' := hg_bound ((t : 𝕜) • (c • y)) htcy_mem
  rw [h_gtc, h_re_t] at h_bound'
  have h_neg : t * (-‖gy‖) < u := by
    have h1 : ((|u| + 1) / ‖gy‖ + 1) * ‖gy‖ = |u| + 1 + ‖gy‖ := by field_simp
    calc t * (-‖gy‖) = -(((|u| + 1) / ‖gy‖ + 1) * ‖gy‖) := by ring
      _ = -(|u| + 1 + ‖gy‖) := by rw [h1]
      _ < -(|u| + 1) := by linarith
      _ ≤ u - 1 := by linarith [neg_abs_le u]
      _ < u := by linarith
  linarith

/-- Given a point outside a closed submodule over 𝕜, there exists a continuous linear functional
    that equals -1 on the point and vanishes on the submodule. This follows from geometric
    Hahn-Banach separation applied to normed spaces. -/
lemma exists_functional_neg_one_and_vanishes_on_closed_submodule
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (M : Submodule 𝕜 E) (hM_closed : IsClosed (M : Set E))
    (u : E) (hu : u ∉ M) :
    ∃ f : E →L[𝕜] 𝕜, f u = -1 ∧ ∀ m ∈ (M : Set E), f m = 0 := by
  -- Set up real scalar structure
  haveI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  -- M is convex (it's a submodule)
  have hM_convex : Convex ℝ (M : Set E) := by
    intro x hx y hy a c ha hc hac
    have hax : (a : 𝕜) • x ∈ M := M.smul_mem _ hx
    have hcy : (c : 𝕜) • y ∈ M := M.smul_mem _ hy
    have h_add := M.add_mem hax hcy
    convert h_add using 1
    simp only [RCLike.real_smul_eq_coe_smul (K := 𝕜)]
  -- LocallyConvexSpace instance for Hahn-Banach
  haveI : LocallyConvexSpace ℝ E := by
    refine LocallyConvexSpace.ofBasisZero ℝ E
      (fun r => Metric.closedBall 0 r) (fun r => 0 < r) ?_ ?_
    · exact @Metric.nhds_basis_closedBall E _ 0
    · intro r _; exact @convex_closedBall E _ _ 0 r
  -- Apply Hahn-Banach separation
  obtain ⟨g, s, hg_u, hg_M⟩ := @RCLike.geometric_hahn_banach_point_closed 𝕜 E _ _ _
    (M : Set E) u _ _ _ _ _ _ hM_convex hM_closed hu
  -- s < 0 since 0 ∈ M
  have h0_in_M : (0 : E) ∈ M := M.zero_mem
  have hs_neg : s < 0 := by simpa using hg_M 0 h0_in_M
  -- g vanishes on M
  have hg_vanish : ∀ m ∈ (M : Set E), g m = 0 :=
    functional_vanishes_on_set_of_bound h0_in_M (fun c y hy => M.smul_mem c hy) g s hg_M
  -- g u ≠ 0 (since re(g u) < s < 0)
  have hg_u_ne : g u ≠ 0 := by
    intro h; simp [h] at hg_u; linarith
  -- Scale g to get f with f u = -1
  use (-(g u)⁻¹) • g
  constructor
  · simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, neg_mul, inv_mul_cancel₀ hg_u_ne]
  · intro m hm
    simp only [ContinuousLinearMap.smul_apply, hg_vanish m hm, smul_zero]

end BasicSequences
