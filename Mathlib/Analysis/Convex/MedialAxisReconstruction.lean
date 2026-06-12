/-
Copyright (c) 2026 Michal Swietek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Swietek
-/
import Mathlib.Analysis.Convex.MedialAxisInflation
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Reconstruction of a set complement from the medial axis

This file works towards Białożyt's characterisation of reconstructible sets (Theorem 6 of the
reference): for a nonempty closed `X` in a finite-dimensional real inner product space, `Xᶜ` is
reconstructible from the medial axis if and only if
`Xᶜ ⊆ closedConvexHull ℝ X ∪ ⋃ L defective supporting hyperplane, L⁺`,
where a supporting hyperplane `L` of the closed convex hull is *defective* if
`X ∩ L ≠ closedConvexHull ℝ X ∩ L`, and `L⁺` is the open half-space bounded by `L` on the side
opposite to `X`.

In this file:

* `IsSupportingHyperplane s v c`: the hyperplane `{x | ⟪v, x⟫_ℝ = c}` supports `s`;
* `Convex.medialAxis_eq_empty`: a convex set has empty medial axis (so nothing outside a closed
  convex set is reconstructible);
* `Metric.IsReconstructiblePt.exists_isSupportingHyperplane` and
  `Metric.Reconstructible.compl_subset`: the *forward* implication of the characterisation —
  a reconstructible point outside the closed convex hull lies strictly beyond some defective
  supporting hyperplane.

The proof of the forward implication is by an explicit construction: given a medial ball
`ball a (infDist a X) ∋ p` with two nearest points `q ≠ q'`, the midpoint `q''` of `q, q'` lies
in the open ball (strict convexity) and in the hull, hence outside `X`; walking from `p` towards
`q''` one finds the first point `ā` of the hull, and the metric projection `z` of a segment
point `b` close to `ā` onto the hull provides the supporting hyperplane: `z ∉ X` witnesses the
defect, and `p` lies strictly on the far side.

## References

* [A. Białożyt, *Sets reconstructible with medial axis*]
-/

open Set Metric
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {X : Set E}

/-- The hyperplane `{x | ⟪v, x⟫_ℝ = c}` (with normal vector `v ≠ 0`) is a supporting hyperplane
of `s`: it meets `s`, and `s` lies in the closed half-space `{x | ⟪v, x⟫_ℝ ≤ c}`. -/
def IsSupportingHyperplane (s : Set E) (v : E) (c : ℝ) : Prop :=
  v ≠ 0 ∧ (s ∩ {x | ⟪v, x⟫ = c}).Nonempty ∧ ∀ x ∈ s, ⟪v, x⟫ ≤ c

/-- A convex set has empty medial axis: nearest points in a convex set are unique. -/
theorem Convex.medialAxis_eq_empty (hX : Convex ℝ X) : medialAxis X = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  rintro a ⟨q, ⟨hqX, hqd⟩, q', ⟨hq'X, hq'd⟩, hqq'⟩
  have hbridge : ∀ x ∈ X, dist a x = infDist a X → ‖a - x‖ = ⨅ w : X, ‖a - w‖ := by
    intro x _ hxd
    rw [← dist_eq_norm, hxd, infDist_eq_iInf]
    exact iInf_congr fun w => dist_eq_norm a w
  have h1 := (norm_eq_iInf_iff_real_inner_le_zero hX hqX).1 (hbridge q hqX hqd) q' hq'X
  have h2 := (norm_eq_iInf_iff_real_inner_le_zero hX hq'X).1 (hbridge q' hq'X hq'd) q hqX
  have expand : ⟪a - q, q' - q⟫ + ⟪a - q', q - q'⟫ = ‖q - q'‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right]
    ring
  have hq0 : ‖q - q'‖ = 0 := by nlinarith [norm_nonneg (q - q')]
  exact hqq' (sub_eq_zero.1 (norm_eq_zero.1 hq0))

/-- **Proposition 2 of Białożyt**: every point of the convex hull of `X` outside `X` is
reconstructible. The proof runs the inflation dichotomy from a nearest point of `p`: the
half-space branch is impossible because the half-space behind the tangent hyperplane is convex
and would contain `p` itself. -/
theorem Metric.isReconstructiblePt_of_mem_convexHull [FiniteDimensional ℝ E] (hX : IsClosed X)
    {p : E} (hp : p ∈ convexHull ℝ X) (hpX : p ∉ X) : IsReconstructiblePt X p := by
  have hne : X.Nonempty := by
    rcases X.eq_empty_or_nonempty with rfl | h
    · simp at hp
    · exact h
  obtain ⟨x₀, hx₀⟩ := nearestPoints_nonempty hX hne p
  rcases inflation_dichotomy_nearestPoints hpX hx₀ with h | ⟨c, hc, hpc, -⟩
  · exfalso
    have hlin : IsLinearMap ℝ fun y : E => ⟪p - x₀, y⟫ :=
      ⟨fun y z => inner_add_right _ _ _, fun c y => real_inner_smul_right _ _ _⟩
    have hXK : X ⊆ {y : E | ⟪p - x₀, y⟫ ≤ ⟪p - x₀, x₀⟫} := fun y hy => by
      have hy' := h y hy
      rw [inner_sub_right] at hy'
      simpa using sub_nonpos.1 hy'
    have hp2 := convexHull_min hXK (convex_halfSpace_le hlin _) hp
    have hp3 : ⟪p - x₀, p - x₀⟫ ≤ 0 := by
      rw [inner_sub_right]
      simp only [mem_setOf_eq] at hp2
      linarith
    have hp4 : p = x₀ := sub_eq_zero.1 (real_inner_self_nonpos.1 hp3)
    exact hpX (by rw [hp4]; exact hx₀.1)
  · exact (isReconstructiblePt_iff_exists_centralSet hX).2 ⟨c, hc, mem_ball.1 hpc⟩

variable [CompleteSpace E]

/-- **Forward implication of the reconstruction theorem** (Białożyt, Theorem 6, "⟹"), pointwise
form: a reconstructible point `p` outside the closed convex hull of `X` lies strictly beyond a
*defective* supporting hyperplane of the hull, i.e. a supporting hyperplane `L` with
`X ∩ L ≠ closedConvexHull ℝ X ∩ L`. -/
theorem Metric.IsReconstructiblePt.exists_isSupportingHyperplane (hX : IsClosed X) {p : E}
    (hp : IsReconstructiblePt X p) (hpc : p ∉ closedConvexHull ℝ X) :
    ∃ v c, IsSupportingHyperplane (closedConvexHull ℝ X) v c ∧
      X ∩ {x | ⟪v, x⟫ = c} ≠ closedConvexHull ℝ X ∩ {x | ⟪v, x⟫ = c} ∧ c < ⟪v, p⟫ := by
  obtain ⟨a, ha, hpa⟩ := hp
  obtain ⟨q, hq, q', hq', hqq'⟩ := ha
  have hCconv : Convex ℝ (closedConvexHull ℝ X) := convex_closedConvexHull
  have hCclosed : IsClosed (closedConvexHull ℝ X) := isClosed_closedConvexHull
  have hXC : X ⊆ closedConvexHull ℝ X := subset_closedConvexHull
  -- the midpoint `q''` of the two nearest points lies in the open medial ball and in the hull
  set q'' : E := (2⁻¹ : ℝ) • q + (2⁻¹ : ℝ) • q' with hq''def
  have hq''ball : q'' ∈ ball a (infDist a X) :=
    combo_mem_ball_of_ne (by rw [mem_closedBall, dist_comm]; exact hq.2.le)
      (by rw [mem_closedBall, dist_comm]; exact hq'.2.le) hqq' (by norm_num) (by norm_num)
      (by norm_num)
  have hq''C : q'' ∈ closedConvexHull ℝ X :=
    hCconv (hXC hq.1) (hXC hq'.1) (by norm_num) (by norm_num) (by norm_num)
  -- the segment from `p` to `q''` stays in the open medial ball, hence avoids `X`
  set f : ℝ → E := fun s => p + s • (q'' - p) with hfdef
  have hfball : ∀ s ∈ Icc (0 : ℝ) 1, f s ∈ ball a (infDist a X) := by
    intro s hs
    have hfs : f s = (1 - s) • p + s • q'' := by simp only [hfdef]; module
    rw [hfs]
    exact convex_ball a (infDist a X) (mem_ball.2 hpa) hq''ball (by linarith [hs.2]) hs.1
      (by ring)
  -- the first parameter at which the segment meets the hull
  set S : Set ℝ := {s | s ∈ Icc (0 : ℝ) 1 ∧ f s ∈ closedConvexHull ℝ X} with hSdef
  have hfcont : Continuous f := continuous_const.add (continuous_id.smul continuous_const)
  have hS1 : (1 : ℝ) ∈ S := by
    refine ⟨⟨zero_le_one, le_refl 1⟩, ?_⟩
    have : f 1 = q'' := by simp [hfdef]
    rwa [this]
  have hSclosed : IsClosed S := isClosed_Icc.inter (hCclosed.preimage hfcont)
  have hSbdd : BddBelow S := ⟨0, fun s hs => hs.1.1⟩
  have hs₀S : sInf S ∈ S := hSclosed.csInf_mem ⟨1, hS1⟩ hSbdd
  set s₀ := sInf S with hs₀def
  have hs₀pos : 0 < s₀ := by
    rcases hs₀S.1.1.eq_or_lt with h | h
    · exact absurd (by simpa [hfdef, ← h] using hs₀S.2) hpc
    · exact h
  have habarX : f s₀ ∉ X := ball_infDist_subset_compl (hfball s₀ hs₀S.1)
  -- a δ-neighbourhood of `f s₀` avoiding the closed set `X`
  obtain ⟨δ, hδ0, hδ⟩ : ∃ δ > 0, ball (f s₀) δ ⊆ Xᶜ :=
    Metric.isOpen_iff.1 hX.isOpen_compl (f s₀) habarX
  -- a segment point `b` slightly before `f s₀`; it is outside the hull and δ/2-close to `f s₀`
  set η := min (s₀ / 2) (δ / (2 * (‖q'' - p‖ + 1))) with hηdef
  have hη0 : 0 < η := lt_min (by linarith) (by positivity)
  have hηs : η ≤ s₀ / 2 := min_le_left _ _
  have hηδ : η ≤ δ / (2 * (‖q'' - p‖ + 1)) := min_le_right _ _
  set s₁ := s₀ - η with hs₁def
  have hs₁0 : 0 ≤ s₁ := by simp only [hs₁def]; linarith
  have hs₁lt : s₁ < s₀ := by simp only [hs₁def]; linarith
  have hs₁1 : s₁ ≤ 1 := by simp only [hs₁def]; linarith [hs₀S.1.2]
  have hbC : f s₁ ∉ closedConvexHull ℝ X := fun hbC =>
    absurd (csInf_le hSbdd ⟨⟨hs₁0, hs₁1⟩, hbC⟩) (not_le.2 hs₁lt)
  have hdist_b : ‖f s₁ - f s₀‖ < δ / 2 := by
    have hdiff : f s₁ - f s₀ = (-η) • (q'' - p) := by
      simp only [hfdef, hs₁def]; module
    rw [hdiff, norm_smul, norm_neg, Real.norm_of_nonneg hη0.le]
    calc η * ‖q'' - p‖ ≤ δ / (2 * (‖q'' - p‖ + 1)) * ‖q'' - p‖ :=
          mul_le_mul_of_nonneg_right hηδ (norm_nonneg _)
      _ < δ / 2 := by
          rw [div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
          nlinarith [norm_nonneg (q'' - p), hδ0]
  -- the metric projection `z` of `b := f s₁` onto the hull
  obtain ⟨z, hzC, hzmin⟩ := exists_norm_eq_iInf_of_complete_convex ⟨q, hXC hq.1⟩
    hCclosed.isComplete hCconv (f s₁)
  have hchar := (norm_eq_iInf_iff_real_inner_le_zero hCconv hzC).1 hzmin
  have hbz_le : ‖f s₁ - z‖ ≤ ‖f s₁ - f s₀‖ := by
    rw [hzmin]
    exact ciInf_le ⟨0, by rintro x ⟨w, rfl⟩; exact norm_nonneg _⟩
      (⟨f s₀, hs₀S.2⟩ : closedConvexHull ℝ X)
  -- `z` is δ-close to `f s₀`, hence outside `X`: the defect witness
  have hzX : z ∉ X := by
    intro hzX
    refine hδ ?_ hzX
    rw [mem_ball]
    calc dist z (f s₀) ≤ dist z (f s₁) + dist (f s₁) (f s₀) := dist_triangle _ _ _
      _ = ‖f s₁ - z‖ + ‖f s₁ - f s₀‖ := by rw [dist_comm z (f s₁), dist_eq_norm, dist_eq_norm]
      _ < δ := by linarith [hbz_le, hdist_b]
  have hbz : f s₁ ≠ z := fun h => hbC (h ▸ hzC)
  have hg0 : 0 < ‖f s₁ - z‖ := norm_pos_iff.2 (sub_ne_zero.2 hbz)
  -- the supporting hyperplane with normal `b - z` through `z`
  refine ⟨f s₁ - z, ⟪f s₁ - z, z⟫, ⟨sub_ne_zero.2 hbz, ⟨z, hzC, rfl⟩, fun x hx => ?_⟩, ?_, ?_⟩
  · have hx' := hchar x hx
    rw [inner_sub_right] at hx'
    linarith
  · intro heq
    have hzmem : z ∈ closedConvexHull ℝ X ∩ {x | ⟪f s₁ - z, x⟫ = ⟪f s₁ - z, z⟫} := ⟨hzC, rfl⟩
    rw [← heq] at hzmem
    exact hzX hzmem.1
  · -- `p` lies strictly beyond the hyperplane
    have habz := hchar (f s₀) hs₀S.2
    have hab_decomp : f s₀ - z = η • (q'' - p) + (f s₁ - z) := by
      simp only [hfdef, hs₁def]; module
    rw [hab_decomp, inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
      at habz
    have hwneg : ⟪f s₁ - z, q'' - p⟫ ≤ 0 := by
      by_contra hpos
      nlinarith [mul_pos hη0 (not_le.1 hpos), pow_pos hg0 2]
    have hpb : 0 ≤ ⟪f s₁ - z, p - f s₁⟫ := by
      have hpb_eq : p - f s₁ = (-s₁) • (q'' - p) := by simp only [hfdef]; module
      rw [hpb_eq, real_inner_smul_right]
      nlinarith [mul_nonneg hs₁0 (neg_nonneg.2 hwneg)]
    have hpz : 0 < ⟪f s₁ - z, p - z⟫ := by
      have hdecomp : p - z = (p - f s₁) + (f s₁ - z) := by abel
      rw [hdecomp, inner_add_right, real_inner_self_eq_norm_sq]
      nlinarith [pow_pos hg0 2]
    have hfinal : ⟪f s₁ - z, p⟫ - ⟪f s₁ - z, z⟫ = ⟪f s₁ - z, p - z⟫ :=
      (inner_sub_right _ _ _).symm
    linarith

/-- **Forward implication of the reconstruction theorem** (Białożyt, Theorem 6, "⟹"): if `Xᶜ` is
reconstructible, then it is contained in the union of the closed convex hull of `X` and the open
half-spaces strictly beyond defective supporting hyperplanes of the hull. -/
theorem Metric.Reconstructible.compl_subset (hX : IsClosed X) (h : Reconstructible X) :
    Xᶜ ⊆ closedConvexHull ℝ X ∪
      {p | ∃ v c, IsSupportingHyperplane (closedConvexHull ℝ X) v c ∧
        X ∩ {x | ⟪v, x⟫ = c} ≠ closedConvexHull ℝ X ∩ {x | ⟪v, x⟫ = c} ∧ c < ⟪v, p⟫} := by
  intro p hp
  by_cases hpc : p ∈ closedConvexHull ℝ X
  · exact Or.inl hpc
  · exact Or.inr ((h p hp).exists_isSupportingHyperplane hX hpc)
