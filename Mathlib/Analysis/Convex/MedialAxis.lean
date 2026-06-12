/-
Copyright (c) 2026 Michal Swietek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Swietek
-/
import Mathlib.Analysis.Convex.StrictConvexBetween
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# The medial axis and the central set of a closed set

For a set `X` in a (pseudo)metric space we define:

* `Metric.nearestPoints X a`: the set `m(a)` of points of `X` nearest to `a`;
* `Metric.medialAxis X`: the *medial axis* `M_X`, the set of points with at least two nearest
  points in `X`;
* `Metric.IsMaximalBallIn c r U`: the open ball `ball c r` is an inclusion-maximal open ball
  contained in `U`;
* `Metric.centralSet X`: the *central set* `C_X`, the set of centres of maximal open balls
  contained in the complement of `X`;
* `Metric.IsReconstructiblePt X p`: `p` belongs to a ball `ball a (infDist a X)` centred at a
  point `a` of the medial axis;
* `Metric.Reconstructible X`: every point of `Xᶜ` is reconstructible.

The main result of this development is Białożyt's characterisation of reconstructible sets: for
a nonempty closed `X` in a finite-dimensional real inner product space, `Xᶜ` is reconstructible
if and only if it is contained in the union of the closed convex hull of `X` and the open
half-spaces bounded by *defective* supporting hyperplanes of that hull (supporting hyperplanes
`L` with `X ∩ L ≠ closedConvexHull ℝ X ∩ L`).

In this file we prove the basic API, including the inclusion `medialAxis X ⊆ centralSet X` in
strictly convex spaces.

## References

* [A. Białożyt, *Sets reconstructible with medial axis*]
* [D. Fremlin, *Skeletons and central sets*]
-/

open Set

namespace Metric

section PseudoMetric

variable {α : Type*} [PseudoMetricSpace α] {X : Set α} {a : α}

/-- The set of points of `X` nearest to `a`, denoted `m(a)` in the medial axis literature.
It is empty when the infimum distance is not attained (e.g. when `X = ∅`). -/
def nearestPoints (X : Set α) (a : α) : Set α :=
  {x ∈ X | dist a x = infDist a X}

theorem mem_nearestPoints {x : α} :
    x ∈ nearestPoints X a ↔ x ∈ X ∧ dist a x = infDist a X := Iff.rfl

theorem nearestPoints_subset : nearestPoints X a ⊆ X := fun _ hx => hx.1

theorem nearestPoints_subset_sphere : nearestPoints X a ⊆ sphere a (infDist a X) :=
  fun x hx => by simpa [dist_comm] using hx.2

theorem isClosed_nearestPoints (hX : IsClosed X) (a : α) : IsClosed (nearestPoints X a) :=
  hX.inter <| isClosed_eq (continuous_const.dist continuous_id) continuous_const

theorem nearestPoints_nonempty [ProperSpace α] (hX : IsClosed X) (hne : X.Nonempty) (a : α) :
    (nearestPoints X a).Nonempty := by
  obtain ⟨y, hy, hd⟩ := hX.exists_infDist_eq_dist hne a
  exact ⟨y, hy, hd.symm⟩

theorem isCompact_nearestPoints [ProperSpace α] (hX : IsClosed X) (a : α) :
    IsCompact (nearestPoints X a) :=
  (isCompact_sphere a (infDist a X)).of_isClosed_subset (isClosed_nearestPoints hX a)
    nearestPoints_subset_sphere

/-- The graph of the nearest-point multifunction is closed. -/
theorem isClosed_setOf_mem_nearestPoints (hX : IsClosed X) :
    IsClosed {p : α × α | p.2 ∈ nearestPoints X p.1} :=
  (hX.preimage continuous_snd).inter <|
    isClosed_eq continuous_dist ((continuous_infDist_pt X).comp continuous_fst)

/-- The medial axis of `X`: the set of points having at least two nearest points in `X`. -/
def medialAxis (X : Set α) : Set α := {a | (nearestPoints X a).Nontrivial}

theorem mem_medialAxis : a ∈ medialAxis X ↔ (nearestPoints X a).Nontrivial := Iff.rfl

theorem nonempty_of_mem_medialAxis (ha : a ∈ medialAxis X) : X.Nonempty :=
  let ⟨x, hx, _⟩ := ha
  ⟨x, hx.1⟩

/-- `ball c r` is an inclusion-maximal open ball among the open balls of positive radius
contained in `U`. -/
def IsMaximalBallIn (c : α) (r : ℝ) (U : Set α) : Prop :=
  0 < r ∧ ball c r ⊆ U ∧
    ∀ ⦃c' : α⦄ ⦃r' : ℝ⦄, 0 < r' → ball c' r' ⊆ U → ball c r ⊆ ball c' r' → c' = c ∧ r' = r

/-- The central set of `X`: the set of centres of maximal open balls contained in `Xᶜ`.
A maximal ball centred at `c` necessarily has radius `infDist c X`
(see `Metric.mem_centralSet_iff`). -/
def centralSet (X : Set α) : Set α := {c | IsMaximalBallIn c (infDist c X) Xᶜ}

theorem ball_subset_compl_iff (hne : X.Nonempty) {c : α} {r : ℝ} :
    ball c r ⊆ Xᶜ ↔ r ≤ infDist c X := by
  rw [le_infDist hne]
  refine ⟨fun h y hy => ?_, fun h y hy hyX => ?_⟩
  · by_contra hlt
    exact h (mem_ball'.2 (not_le.1 hlt)) hy
  · exact absurd (h hyX) (not_le.2 (mem_ball'.1 hy))

theorem IsMaximalBallIn.radius_eq (hne : X.Nonempty) {c : α} {r : ℝ}
    (h : IsMaximalBallIn c r Xᶜ) : r = infDist c X := by
  have hr : r ≤ infDist c X := (ball_subset_compl_iff hne).1 h.2.1
  exact (h.2.2 (h.1.trans_le hr) ball_infDist_subset_compl (ball_subset_ball hr)).2.symm

theorem mem_centralSet_iff (hne : X.Nonempty) {c : α} :
    c ∈ centralSet X ↔ ∃ r, IsMaximalBallIn c r Xᶜ :=
  ⟨fun h => ⟨_, h⟩, fun ⟨_, hr⟩ =>
    show IsMaximalBallIn c (infDist c X) Xᶜ from hr.radius_eq hne ▸ hr⟩

theorem infDist_pos_of_mem_centralSet {c : α} (hc : c ∈ centralSet X) : 0 < infDist c X :=
  hc.1

theorem notMem_of_mem_centralSet {c : α} (hc : c ∈ centralSet X) : c ∉ X := fun hcX =>
  absurd hc.1 (by simp [infDist_zero_of_mem hcX])

/-- `p` is a reconstructible point of `Xᶜ`: it lies in an open ball of maximal radius centred
at a point of the medial axis. -/
def IsReconstructiblePt (X : Set α) (p : α) : Prop :=
  ∃ a ∈ medialAxis X, dist p a < infDist a X

/-- `Xᶜ` is reconstructible from the medial axis of `X` if every point outside `X` lies in a
ball `ball a (infDist a X)` with `a` in the medial axis. -/
def Reconstructible (X : Set α) : Prop :=
  ∀ p ∉ X, IsReconstructiblePt X p

theorem isReconstructiblePt_iff_mem_iUnion {p : α} :
    IsReconstructiblePt X p ↔ p ∈ ⋃ a ∈ medialAxis X, ball a (infDist a X) := by
  simp [IsReconstructiblePt, mem_ball]

theorem reconstructible_iff_compl_subset :
    Reconstructible X ↔ Xᶜ ⊆ ⋃ a ∈ medialAxis X, ball a (infDist a X) :=
  ⟨fun h p hp => isReconstructiblePt_iff_mem_iUnion.1 (h p hp),
    fun h p hp => (isReconstructiblePt_iff_mem_iUnion (p := p)).2 (h hp)⟩

theorem IsReconstructiblePt.notMem {p : α} (h : IsReconstructiblePt X p) : p ∉ X := by
  obtain ⟨a, -, hd⟩ := h
  exact fun hp => absurd hd (not_lt.2 (by simpa [dist_comm] using infDist_le_dist_of_mem hp))

end PseudoMetric

section MetricSp

variable {α : Type*} [MetricSpace α] {X : Set α} {a : α}

theorem nearestPoints_of_mem (h : a ∈ X) : nearestPoints X a = {a} := by
  ext x
  simp only [mem_nearestPoints, infDist_zero_of_mem h, mem_singleton_iff]
  exact ⟨fun hx => (dist_eq_zero.1 hx.2).symm, fun hx => by rw [hx]; exact ⟨h, dist_self a⟩⟩

theorem notMem_of_mem_medialAxis (ha : a ∈ medialAxis X) : a ∉ X := fun h => by
  obtain ⟨x, hx, y, hy, hxy⟩ := ha
  rw [nearestPoints_of_mem h, mem_singleton_iff] at hx hy
  exact hxy (hx.trans hy.symm)

theorem disjoint_medialAxis (X : Set α) : Disjoint (medialAxis X) X :=
  disjoint_left.2 fun _ ha => notMem_of_mem_medialAxis ha

theorem infDist_pos_of_mem_medialAxis (hX : IsClosed X) (ha : a ∈ medialAxis X) :
    0 < infDist a X :=
  (infDist_pos_iff_notMem_closure (nonempty_of_mem_medialAxis ha)).1 fun hmem =>
    notMem_of_mem_medialAxis ha (hX.closure_eq ▸ hmem)

end MetricSp

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {X : Set E}

/-- In a nontrivial real normed space, inclusion of open balls is characterised by the distance
of the centres: `ball c r ⊆ ball c' r' ↔ dist c c' + r ≤ r'` (for `0 < r`). -/
theorem ball_subset_ball_iff [Nontrivial E] {c c' : E} {r r' : ℝ} (hr : 0 < r) :
    ball c r ⊆ ball c' r' ↔ dist c c' + r ≤ r' := by
  refine ⟨fun h => ?_, fun h => ball_subset_ball' (by linarith)⟩
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  set δ := min ε r with hδdef
  have hδ0 : 0 < δ := lt_min hε hr
  have hδr : δ ≤ r := min_le_right _ _
  have hδε : δ ≤ ε := min_le_left _ _
  have hrδ : (0 : ℝ) ≤ r - δ := by linarith
  -- a unit vector `u` aligned with `c - c'` (or arbitrary if `c = c'`)
  obtain ⟨u, hu1, hu2⟩ :
      ∃ u : E, ‖u‖ = 1 ∧ ‖c - c' + (r - δ) • u‖ = ‖c - c'‖ + (r - δ) := by
    rcases eq_or_ne c c' with rfl | hcc
    · obtain ⟨v, hv⟩ := exists_ne (0 : E)
      have hv0 : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv
      refine ⟨‖v‖⁻¹ • v, ?_, ?_⟩
      · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hv0]
      · simp only [sub_self, zero_add, norm_zero]
        rw [norm_smul, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hv0, mul_one,
          Real.norm_of_nonneg hrδ]
    · have hcc0 : ‖c - c'‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 hcc)
      refine ⟨‖c - c'‖⁻¹ • (c - c'), ?_, ?_⟩
      · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hcc0]
      · have hkey : c - c' + (r - δ) • ‖c - c'‖⁻¹ • (c - c') =
            (1 + (r - δ) * ‖c - c'‖⁻¹) • (c - c') := by module
        have hnn : (0 : ℝ) ≤ 1 + (r - δ) * ‖c - c'‖⁻¹ :=
          add_nonneg zero_le_one (mul_nonneg hrδ (inv_nonneg.2 (norm_nonneg _)))
        rw [hkey, norm_smul, Real.norm_of_nonneg hnn, add_mul, one_mul, mul_assoc,
          inv_mul_cancel₀ hcc0, mul_one]
  have hz : c + (r - δ) • u ∈ ball c r := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, hu1, mul_one,
      Real.norm_of_nonneg hrδ]
    linarith
  have hlt := mem_ball.1 (h hz)
  rw [dist_eq_norm, add_sub_right_comm, hu2] at hlt
  rw [dist_eq_norm]
  linarith

variable [StrictConvexSpace ℝ E]

/-- In a strictly convex real normed space, every point of the medial axis is the centre of a
maximal ball: `M_X ⊆ C_X`. -/
theorem medialAxis_subset_centralSet (hX : IsClosed X) : medialAxis X ⊆ centralSet X := by
  intro a ha
  obtain ⟨q, hq, q', hq', hqq'⟩ := ha
  have hamem : a ∈ medialAxis X := ⟨q, hq, q', hq', hqq'⟩
  have hne : X.Nonempty := ⟨q, hq.1⟩
  have hR : 0 < infDist a X := infDist_pos_of_mem_medialAxis hX hamem
  haveI : Nontrivial E := ⟨⟨q, q', hqq'⟩⟩
  refine ⟨hR, ball_infDist_subset_compl, ?_⟩
  rintro c' r' hr' hsub hball
  have hdc : dist a c' + infDist a X ≤ r' := (ball_subset_ball_iff hR).1 hball
  -- every nearest point `x` of `a` satisfies `c' - x = (r' / infDist a X) • (a - x)`
  have key : ∀ x ∈ nearestPoints X a, c' - x = (r' / infDist a X) • (a - x) := by
    rintro x ⟨hxX, hxd⟩
    have h1 : r' ≤ dist x c' := by
      by_contra hlt
      exact hsub (mem_ball.2 (not_le.1 hlt)) hxX
    have h2 : dist x a = infDist a X := by rw [dist_comm]; exact hxd
    have h4 : dist x a + dist a c' = dist x c' :=
      le_antisymm (by linarith) (dist_triangle x a c')
    have h5 : dist x c' = r' := le_antisymm (by linarith [dist_triangle x a c']) h1
    have hw : Wbtw ℝ x a c' := dist_add_dist_eq_iff.1 h4
    obtain ⟨u, v, hu, hv, huv, hcomb⟩ := mem_segment_iff_wbtw.2 hw
    have hu1 : u = 1 - v := by linarith
    have hax : a - x = v • (c' - x) := by
      calc a - x = u • x + v • c' - x := by rw [hcomb]
        _ = v • (c' - x) := by rw [hu1, smul_sub]; module
    have hnorm : infDist a X = v * r' := by
      have hn : dist a x = v * dist c' x := by
        rw [dist_eq_norm, dist_eq_norm, hax, norm_smul, Real.norm_of_nonneg hv]
      rwa [hxd, dist_comm c' x, h5] at hn
    have hv0 : v ≠ 0 := by
      rintro rfl
      rw [zero_mul] at hnorm
      exact hR.ne' hnorm
    have hinv : c' - x = v⁻¹ • (a - x) := by rw [hax, inv_smul_smul₀ hv0]
    have hvval : v⁻¹ = r' / infDist a X := by
      rw [hnorm]
      field_simp
    rw [hinv, hvval]
  have e1 := key q hq
  have e2 := key q' hq'
  have hsub2 : q' - q = (r' / infDist a X) • (q' - q) := by
    have h : (c' - q) - (c' - q') = (r' / infDist a X) • (a - q - (a - q')) := by
      rw [e1, e2, ← smul_sub]
    calc q' - q = (c' - q) - (c' - q') := by abel
      _ = (r' / infDist a X) • (a - q - (a - q')) := h
      _ = (r' / infDist a X) • (q' - q) := by rw [show a - q - (a - q') = q' - q by abel]
  have hfac : (1 - r' / infDist a X) • (q' - q) = 0 := by
    rw [sub_smul, one_smul, ← hsub2, sub_self]
  rcases smul_eq_zero.1 hfac with h | h
  · have hrR : r' = infDist a X := by
      have hd1 : r' / infDist a X = 1 := by linarith
      rwa [div_eq_one_iff_eq hR.ne'] at hd1
    have hda : dist a c' ≤ 0 := by linarith
    exact ⟨(dist_le_zero.1 hda).symm, hrR⟩
  · exact absurd (sub_eq_zero.1 h) hqq'.symm

end Normed

end Metric
