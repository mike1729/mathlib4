/-
Copyright (c) 2026 Michal Swietek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Swietek
-/
import Mathlib.Analysis.Convex.MedialAxis
import Mathlib.Analysis.InnerProductSpace.Convex

/-!
# Ball inflation along a ray and the inflation dichotomy

This file develops the *inflation* technique underlying Białożyt's characterisation of sets
reconstructible from the medial axis: growing a one-parameter family of open balls
`ball (x₀ + t • v) t` tangent to a fixed point `x₀` of a set `X`, in a fixed unit direction
`v`, for as long as they avoid `X`.

The basic tool is the membership criterion `Metric.mem_ball_add_smul_iff`:
`p ∈ ball (x + ρ • v) ρ ↔ ‖p - x‖ ^ 2 < 2 * ρ * ⟪v, p - x⟫_ℝ`, from which monotonicity of the
tangent family and the identification of its unions (`Metric.iUnion_ball_add_smul`,
`Metric.iUnion_ball_add_smul_eq_halfspace`) are immediate.

The main result is the dichotomy `Metric.inflation_dichotomy`: if some tangent ball avoids `X`,
then either *all* tangent balls in the direction `v` avoid `X` — and then `X` lies in the closed
half-space `{y | ⟪v, y - x₀⟫_ℝ ≤ 0}` — or the family has a largest member, which is a *maximal*
ball in `Xᶜ`, so its centre belongs to the central set `Metric.centralSet X` and is tangent to
`X` at `x₀`.

The specialisation `Metric.inflation_dichotomy_nearestPoints` starts the inflation from a
nearest point `x₀` of `p ∉ X` in the direction of `p`; in the second branch the maximal ball
contains `p`.

## References

* [A. Białożyt, *Sets reconstructible with medial axis*]
-/

open Set
open scoped RealInnerProductSpace

namespace Metric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {X : Set E}
  {v x x₀ p : E} {ρ s t T : ℝ}

/-- Membership in a ball tangent at `x` to the hyperplane with unit normal `v`: the quantitative
criterion through which all inflation arguments factor. -/
theorem mem_ball_add_smul_iff (hv : ‖v‖ = 1) (hρ : 0 < ρ) :
    p ∈ ball (x + ρ • v) ρ ↔ ‖p - x‖ ^ 2 < 2 * ρ * ⟪v, p - x⟫ := by
  rw [mem_ball, dist_eq_norm, show p - (x + ρ • v) = p - x - ρ • v from by abel]
  have hsq : ‖p - x - ρ • v‖ ^ 2 = ‖p - x‖ ^ 2 - 2 * ρ * ⟪v, p - x⟫ + ρ ^ 2 := by
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, hv, mul_one,
      Real.norm_of_nonneg hρ.le, real_inner_comm]
    ring
  constructor
  · intro h
    have h2 : ‖p - x - ρ • v‖ ^ 2 < ρ ^ 2 := by nlinarith [norm_nonneg (p - x - ρ • v)]
    rw [hsq] at h2
    linarith
  · intro h
    have h2 : ‖p - x - ρ • v‖ ^ 2 < ρ ^ 2 := by rw [hsq]; linarith
    nlinarith [norm_nonneg (p - x - ρ • v)]

/-- Points of a tangent ball lie strictly on the `v`-side of the tangent hyperplane. -/
theorem inner_pos_of_mem_ball_add_smul (hv : ‖v‖ = 1) (ht : 0 < t)
    (hp : p ∈ ball (x + t • v) t) : 0 < ⟪v, p - x⟫ := by
  rw [mem_ball_add_smul_iff hv ht] at hp
  by_contra hI
  have h1 : 2 * t * ⟪v, p - x⟫ ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) (not_lt.1 hI)
  nlinarith [sq_nonneg ‖p - x‖]

/-- The tangent family is monotone in the radius. -/
theorem ball_add_smul_subset_ball_add_smul (hv : ‖v‖ = 1) (hs : 0 < s) (hst : s ≤ t) :
    ball (x + s • v) s ⊆ ball (x + t • v) t := by
  intro p hp
  have ht : 0 < t := hs.trans_le hst
  have hpos : 0 < ⟪v, p - x⟫ := inner_pos_of_mem_ball_add_smul hv hs hp
  rw [mem_ball_add_smul_iff hv hs] at hp
  rw [mem_ball_add_smul_iff hv ht]
  nlinarith [mul_nonneg (sub_nonneg.2 hst) hpos.le]

/-- The union of the tangent balls of radius less than `T` is the tangent ball of radius `T`. -/
theorem iUnion_ball_add_smul (hv : ‖v‖ = 1) (hT : 0 < T) :
    ⋃ t ∈ Ioo (0 : ℝ) T, ball (x + t • v) t = ball (x + T • v) T := by
  refine Subset.antisymm
    (iUnion₂_subset fun t ht => ball_add_smul_subset_ball_add_smul hv ht.1 ht.2.le) fun p hp => ?_
  have hpos : 0 < ⟪v, p - x⟫ := inner_pos_of_mem_ball_add_smul hv hT hp
  rw [mem_ball_add_smul_iff hv hT] at hp
  have h2I : (0 : ℝ) < 2 * ⟪v, p - x⟫ := by linarith
  set L := ‖p - x‖ ^ 2 / (2 * ⟪v, p - x⟫) with hLdef
  have hL0 : 0 ≤ L := div_nonneg (sq_nonneg _) h2I.le
  have hLT : L < T := by
    rw [hLdef, div_lt_iff₀ h2I]
    calc ‖p - x‖ ^ 2 < 2 * T * ⟪v, p - x⟫ := hp
      _ = T * (2 * ⟪v, p - x⟫) := by ring
  have ht0 : 0 < (L + T) / 2 := by linarith
  refine mem_iUnion₂.2 ⟨(L + T) / 2, ⟨ht0, by linarith⟩, ?_⟩
  rw [mem_ball_add_smul_iff hv ht0,
    show 2 * ((L + T) / 2) * ⟪v, p - x⟫ = (L + T) / 2 * (2 * ⟪v, p - x⟫) from by ring,
    ← div_lt_iff₀ h2I]
  linarith

/-- The union of all the tangent balls in the direction `v` is the open half-space on the
`v`-side of the tangent hyperplane. -/
theorem iUnion_ball_add_smul_eq_halfspace (hv : ‖v‖ = 1) :
    ⋃ t ∈ Ioi (0 : ℝ), ball (x + t • v) t = {y | 0 < ⟪v, y - x⟫} := by
  ext p
  simp only [mem_iUnion, mem_Ioi, mem_setOf_eq, exists_prop]
  constructor
  · rintro ⟨t, ht0, hp⟩
    exact inner_pos_of_mem_ball_add_smul hv ht0 hp
  · intro hpos
    have h2I : (0 : ℝ) < 2 * ⟪v, p - x⟫ := by linarith
    set L := ‖p - x‖ ^ 2 / (2 * ⟪v, p - x⟫) with hLdef
    have hL0 : 0 ≤ L := div_nonneg (sq_nonneg _) h2I.le
    refine ⟨L + 1, by linarith, ?_⟩
    rw [mem_ball_add_smul_iff hv (by linarith),
      show 2 * (L + 1) * ⟪v, p - x⟫ = (L + 1) * (2 * ⟪v, p - x⟫) from by ring,
      ← div_lt_iff₀ h2I]
    linarith

/-- **The inflation dichotomy.** If the tangent ball of radius `t₀ > 0` at `x₀ ∈ X` in the unit
direction `v` avoids `X`, then either `X` lies in the closed half-space
`{y | ⟪v, y - x₀⟫_ℝ ≤ 0}`, or the tangent family has a largest member: a ball of radius
`T ≥ t₀` which is maximal among open balls in `Xᶜ`, with centre `x₀ + T • v` in the central set
and tangency point `x₀`. -/
theorem inflation_dichotomy (hv : ‖v‖ = 1) (hx₀ : x₀ ∈ X) {t₀ : ℝ} (ht₀ : 0 < t₀)
    (hdisj : ball (x₀ + t₀ • v) t₀ ⊆ Xᶜ) :
    (∀ y ∈ X, ⟪v, y - x₀⟫ ≤ 0) ∨
      ∃ T, t₀ ≤ T ∧ infDist (x₀ + T • v) X = T ∧ x₀ + T • v ∈ centralSet X ∧
        x₀ ∈ nearestPoints X (x₀ + T • v) := by
  classical
  haveI : Nontrivial E := nontrivial_of_ne v 0 fun h => by simp [h] at hv
  set A := {t : ℝ | 0 < t ∧ ball (x₀ + t • v) t ⊆ Xᶜ} with hAdef
  have hAne : t₀ ∈ A := ⟨ht₀, hdisj⟩
  by_cases hbdd : BddAbove A
  · -- bounded case: the supremum gives a maximal ball
    right
    set T := sSup A with hTdef
    have ht₀T : t₀ ≤ T := le_csSup hbdd hAne
    have hT0 : 0 < T := ht₀.trans_le ht₀T
    have hTdisj : ball (x₀ + T • v) T ⊆ Xᶜ := by
      rw [← iUnion_ball_add_smul hv hT0]
      refine iUnion₂_subset fun t ht => ?_
      obtain ⟨t', ht'A, htt'⟩ := exists_lt_of_lt_csSup ⟨t₀, hAne⟩ ht.2
      exact (ball_add_smul_subset_ball_add_smul hv ht.1 htt'.le).trans ht'A.2
    have hd2 : dist (x₀ + T • v) x₀ = T := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, hv, mul_one,
        Real.norm_of_nonneg hT0.le]
    have hdeq : infDist (x₀ + T • v) X = T :=
      le_antisymm ((infDist_le_dist_of_mem hx₀).trans_eq hd2)
        ((ball_subset_compl_iff ⟨x₀, hx₀⟩).1 hTdisj)
    have hnear : x₀ ∈ nearestPoints X (x₀ + T • v) := ⟨hx₀, hd2.trans hdeq.symm⟩
    have hmax : IsMaximalBallIn (x₀ + T • v) T Xᶜ := by
      refine ⟨hT0, hTdisj, ?_⟩
      rintro c' r' hr' hsub' hball'
      have hd4 : dist (x₀ + T • v) c' + T ≤ r' := (ball_subset_ball_iff hT0).1 hball'
      have hd3 : r' ≤ dist x₀ c' :=
        not_lt.1 fun h => hsub' (mem_ball.2 h) hx₀
      have htri := dist_triangle x₀ (x₀ + T • v) c'
      have hd2' : dist x₀ (x₀ + T • v) = T := by rw [dist_comm]; exact hd2
      have h6 : dist x₀ (x₀ + T • v) + dist (x₀ + T • v) c' = dist x₀ c' := by linarith
      have hd5 : dist x₀ c' = r' := by linarith
      have hw : Wbtw ℝ x₀ (x₀ + T • v) c' := dist_add_dist_eq_iff.1 h6
      obtain ⟨u', w', hu', hw', huw', hcomb⟩ := mem_segment_iff_wbtw.2 hw
      have hkey : w' • (c' - x₀) = T • v := by
        have hu'1 : u' = 1 - w' := by linarith
        calc w' • (c' - x₀) = u' • x₀ + w' • c' - x₀ := by rw [hu'1]; module
          _ = T • v := by rw [hcomb]; abel
      have hnormc : ‖c' - x₀‖ = r' := by
        rw [← dist_eq_norm, dist_comm]; exact hd5
      have hn : w' * r' = T := by
        have := congrArg norm hkey
        rwa [norm_smul, norm_smul, hv, mul_one, hnormc, Real.norm_of_nonneg hw',
          Real.norm_of_nonneg hT0.le] at this
      have hw'0 : w' ≠ 0 := fun h => hT0.ne' (by rw [← hn, h, zero_mul])
      have hc' : c' = x₀ + r' • v := by
        have h1 : c' - x₀ = (w'⁻¹ * T) • v := by
          rw [← smul_smul, ← hkey, inv_smul_smul₀ hw'0]
        have h2 : w'⁻¹ * T = r' := by
          rw [inv_mul_eq_div, div_eq_iff hw'0]
          linear_combination -hn
        rw [h2] at h1
        rw [← h1]; abel
      have hr'T : r' ≤ T := by
        by_contra hgt
        exact hgt (le_csSup hbdd ⟨hr', by rw [← hc']; exact hsub'⟩)
      have hdn : (0 : ℝ) ≤ dist (x₀ + T • v) c' := dist_nonneg
      have hr'eq : r' = T := le_antisymm hr'T (by linarith)
      refine ⟨?_, hr'eq⟩
      rw [hc', hr'eq]
    exact ⟨T, ht₀T, hdeq, (mem_centralSet_iff ⟨x₀, hx₀⟩).2 ⟨T, hmax⟩, hnear⟩
  · -- unbounded case: the half-space is swept out
    left
    intro y hy
    by_contra hpos
    have h2I : (0 : ℝ) < 2 * ⟪v, y - x₀⟫ := by
      have := not_le.1 hpos
      linarith
    obtain ⟨t, htA, htL⟩ :=
      not_bddAbove_iff.1 hbdd (‖y - x₀‖ ^ 2 / (2 * ⟪v, y - x₀⟫))
    refine htA.2 ?_ hy
    rw [mem_ball_add_smul_iff hv htA.1,
      show 2 * t * ⟪v, y - x₀⟫ = t * (2 * ⟪v, y - x₀⟫) from by ring, ← div_lt_iff₀ h2I]
    exact htL

/-- Specialisation of the inflation dichotomy to the ray from a nearest point `x₀` of `p`
through `p`: either `X` lies in the closed half-space behind the tangent hyperplane at `x₀`, or
some maximal ball tangent to `X` at `x₀` contains `p`. -/
theorem inflation_dichotomy_nearestPoints (hp : p ∉ X) (hx₀ : x₀ ∈ nearestPoints X p) :
    (∀ y ∈ X, ⟪p - x₀, y - x₀⟫ ≤ 0) ∨
      ∃ c ∈ centralSet X, p ∈ ball c (infDist c X) ∧ x₀ ∈ nearestPoints X c := by
  obtain ⟨hx₀X, hx₀d⟩ := hx₀
  have hpx : p ≠ x₀ := fun h => hp (h ▸ hx₀X)
  have hd0 : 0 < ‖p - x₀‖ := norm_pos_iff.2 (sub_ne_zero.2 hpx)
  set v := ‖p - x₀‖⁻¹ • (p - x₀) with hvdef
  have hv : ‖v‖ = 1 := by
    rw [hvdef, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hd0.ne']
  have hpx₀ : x₀ + ‖p - x₀‖ • v = p := by
    rw [hvdef, smul_smul, mul_inv_cancel₀ hd0.ne', one_smul]
    abel
  have hdisj : ball (x₀ + ‖p - x₀‖ • v) ‖p - x₀‖ ⊆ Xᶜ := by
    rw [hpx₀, ← dist_eq_norm, hx₀d]
    exact ball_infDist_subset_compl
  rcases inflation_dichotomy hv hx₀X hd0 hdisj with h | ⟨T, hT, hdeq, hcs, hnear⟩
  · left
    intro y hy
    have := h y hy
    have hrw : ⟪p - x₀, y - x₀⟫ = ‖p - x₀‖ * ⟪v, y - x₀⟫ := by
      rw [hvdef, real_inner_smul_left]
      field_simp
    rw [hrw]
    exact mul_nonpos_of_nonneg_of_nonpos hd0.le this
  · right
    refine ⟨x₀ + T • v, hcs, ?_, hnear⟩
    rw [hdeq, mem_ball_add_smul_iff hv (hd0.trans_le hT)]
    have hvp : ⟪v, p - x₀⟫ = ‖p - x₀‖ := by
      rw [hvdef, real_inner_smul_left, real_inner_self_eq_norm_sq]
      field_simp
    rw [hvp]
    nlinarith

/-!
### Assumed classical result (to be proved in a later stage)

The inclusion `centralSet X ⊆ closure (medialAxis X)` is the Motzkin–Fremlin theorem (Motzkin;
Fremlin, *Skeletons and central sets*, Prop. 2B): every centre of a maximal ball in `Xᶜ` is a
limit of points with at least two nearest points in `X`. It is the single classical input of
this development that is currently assumed; an elementary, Brouwer-free proof via an Euler
polygon inflation is planned (see the project notes). Everything downstream is proved in full,
and `#print axioms` transparently reports the dependency through `sorryAx`.
-/

variable [FiniteDimensional ℝ E]

/-- **Motzkin–Fremlin theorem** (assumed for now): the central set is contained in the closure
of the medial axis. -/
theorem centralSet_subset_closure_medialAxis (hX : IsClosed X) :
    centralSet X ⊆ closure (medialAxis X) := sorry

/-- **Lemma 1 of Białożyt**: a point is reconstructible from the medial axis if and only if it
lies in a ball `ball c (infDist c X)` centred at a point `c` of the central set. -/
theorem isReconstructiblePt_iff_exists_centralSet (hX : IsClosed X) {p : E} :
    IsReconstructiblePt X p ↔ ∃ c ∈ centralSet X, dist p c < infDist c X := by
  constructor
  · rintro ⟨a, ha, hd⟩
    exact ⟨a, medialAxis_subset_centralSet hX ha, hd⟩
  · rintro ⟨c, hc, hd⟩
    have hcc : c ∈ closure (medialAxis X) := centralSet_subset_closure_medialAxis hX hc
    set ε := (infDist c X - dist p c) / 3 with hεdef
    have hε0 : 0 < ε := by simp only [hεdef]; linarith
    obtain ⟨a, haM, hca⟩ := Metric.mem_closure_iff.1 hcc ε hε0
    refine ⟨a, haM, ?_⟩
    have h1 : dist p a ≤ dist p c + dist c a := dist_triangle p c a
    have h2 : infDist c X ≤ infDist a X + dist c a := infDist_le_infDist_add_dist
    linarith

end Metric
