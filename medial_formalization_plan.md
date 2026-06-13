# Formalization plan: "Sets Reconstructible with Medial Axis" (A. Białożyt), Theorem 6

Source: `medial_v2.pdf` (corrected version). Branch: `medial-axis` (no commits beyond master yet).

## 1. Context

The paper characterizes which closed sets X ⊆ ℝⁿ have a complement reconstructible from the
medial axis. Main result:

> **Theorem 6.** Let X ⊆ ℝⁿ be closed, and let 𝓛 be the family of supporting hyperplanes L of
> cl(conv X) with X ∩ L ≠ cl(conv X) ∩ L ("defective" hyperplanes). Then Xᶜ is reconstructible
> if and only if Xᶜ ⊆ cl(conv X) ∪ ⋃_{L∈𝓛} L⁺.

(The paper says "a family"; for the ⟹ direction 𝓛 must be *the* family of all such hyperplanes —
we formalize it that way.)

Proof chain in the paper: Lemma 1 (central set C_X can replace medial axis M_X) → Prop 2
(points of conv X are reconstructible) → Prop 3 (L⁺ for supporting L with X∩L non-convex) →
Prop 4 (L⁺ for defective L) → Cor 5 (cl(conv X)) → Theorem 6.

## 2. Scope and generality

- **Phase 1 (this plan's focus — the paper itself):** definitions (nearest points, medial axis,
  central set, reconstructible point, supporting hyperplane), Lemma 1, Prop 2, the **unified
  Prop 3/4** (see §4 item 2), Cor 5, Theorem 6. Exactly **one** classical background theorem the
  paper only *cites* (Fremlin, see §4) is **stated in final form but stubbed with `sorry`** and
  treated as an assumption. (Motzkin turned out not to be needed at all — §4 item 2.)
- **Phase 2 (deferred):** prove the Fremlin stub (elementary route worked out in §4.1; no
  Brouwer needed); optionally add Motzkin as a corollary (§4.2).
- **Companion document:** `medial_formalization_notes.tex/pdf` (repo root) contains the complete
  human-readable proofs of everything below, written for the paper's author; it is the canonical
  reference for the arguments during implementation.
- **Out of scope (possible follow-ups):** §4 of paper (Prop 7 stability — needs Kuratowski set
  convergence, absent from mathlib and a project of its own), §5 (λ-medial axis, Prop 8,
  Conjecture 9), Riemannian generalization (the `cot1.md`/`cot2.md` notes).
- **Stub mechanism:** plain `theorem … := sorry` (not literal `axiom` commands) — keeps the
  signatures final so nothing downstream changes when proofs land in Phase 2, and `lean_verify` /
  `#print axioms` transparently reports `sorryAx` on everything that depends on them.
- **Generality:** definitions in general (pseudo)metric spaces (this is *needed*, not just nice —
  Prop 3 applies Motzkin's theorem *inside a hyperplane*, so the defs must transfer along
  isometries). Theorems in
  `variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]`,
  with `open scoped RealInnerProductSpace`. ℝⁿ = `EuclideanSpace ℝ (Fin n)` is an instance.

## 3. Mathlib inventory (verified by exploration)

**Available and load-bearing:**
- `Metric.infDist` API (`Mathlib/Topology/MetricSpace/HausdorffDistance.lean`):
  `IsClosed.exists_infDist_eq_dist` (needs `ProperSpace`), `lipschitz_infDist_pt`,
  `disjoint_ball_infDist` / `ball_infDist_subset_compl`, `IsClosed.mem_iff_infDist_zero`,
  `infDist_le_dist_of_mem`. `FiniteDimensional.proper_real` gives properness.
- Convexity: `convexHull_min`, `closedConvexHull` with `closedConvexHull_eq_closure_convexHull`
  (`Mathlib/Analysis/Convex/Topology.lean`), Carathéodory (`convexHull_eq_union`) — though we
  mostly won't need it (see §5, Prop 2 simplification).
- Separation (`Mathlib/Analysis/LocallyConvex/Separation.lean`): all `geometric_hahn_banach_*`
  variants; `iInter_halfSpaces_eq`.
- Hilbert projection onto convex sets (`Mathlib/Analysis/InnerProductSpace/Projection/Minimal.lean`):
  `exists_norm_eq_iInf_of_complete_convex`, `norm_eq_iInf_iff_real_inner_le_zero` — this is the key
  tool for the ⟹ direction of Theorem 6.
- Strict convexity: `sameRay_iff_norm_add`, `dist_add_dist_eq_iff`, `combo_mem_ball_of_ne`,
  `inner_eq_norm_mul_iff_real`; `convex_ball`; Riesz `InnerProductSpace.toDual`.
- Compactness: `IsCompact.tendsto_subseq` (Bolzano–Weierstrass), `IsCompact.exists_infDist_eq_dist`.

**Absent (we must build):** nearest-point set for non-convex sets, medial axis, central set,
reconstructibility, supporting-hyperplane predicate, Chebyshev/Motzkin theorems, foot-map
semicontinuity, ball-inclusion iff (`ball c r ⊆ ball c' r' ↔ dist c c' ≤ r' - r` — only the easy
direction exists), recession-cone material (not needed as a def — inlined), **Brouwer FPT**
(absent — and *not needed*, see §4), Danskin-type derivative of `infDist` (we use a one-line
quadratic substitute).

## 4. Audit results: gaps in the paper and how we close them

This is the most important section; it was produced by working the proofs in detail.

1. **Lemma 1 hides Fremlin's theorem.** "c ∈ C_X can be approximated by points of M_X" *is*
   C_X ⊆ cl(M_X) (Fremlin 1997, cited as [19]/[15]), a genuine theorem on the critical path of
   *everything* (Prop 2 produces central-set points; maximal balls can touch X at a single point).
   Classical proofs use Brouwer/degree theory — absent from mathlib. **Phase 1: stub with
   `sorry`.** For Phase 2, an elementary route is worked out (no Brouwer, no Peano, no
   Arzelà–Ascoli):
   - If a neighborhood B(c, ε) of a maximal-ball center misses M_X, the foot map is single-valued
     there, hence continuous (closed graph + compact values), hence uniformly continuous on
     B̄(c, ε/2).
   - Quadratic "Danskin substitute" (pure algebra): if x_a is a foot of a, v = (a−x_a)/d(a), and
     y is any foot of a + h·v, then d(a+hv)² ≥ (d(a)+h)² − h‖x_a − y‖²/d(a)·(1+o(1)). The loss is
     controlled by foot oscillation ‖x_a − y‖, which is uniformly small by the previous item.
   - Euler polygon of total length ℓ = ε/2 with steps → 0: endpoints w_δ satisfy ‖w_δ − c‖ ≤ ℓ
     and d(w_δ) ≥ d(c) + ℓ(1−δ). A cluster point w (Bolzano–Weierstrass) has ‖w−c‖ ≤ ℓ,
     d(w) ≥ d(c) + ℓ, so `ball w (d w)` strictly contains `ball c (d c)` — contradicting
     maximality. ∎
2. **Props 3 and 4 merge, and Motzkin drops out entirely** (discovered while writing the author
   notes — see `medial_formalization_notes.pdf` §5 for the full proof). The hypothesis of Prop 3
   implies that of Prop 4 (non-convex X∩L ⇒ X∩L ⊊ conv(X∩L) ⊆ clconv∩L = defect), and the
   Prop-4-style ladder run from a *defect witness* w ∈ (clconv∩L)\X proves the unified statement
   without ever using two nearest points of X∩L: the infinite-radius branch is killed by
   "half-space is closed convex ⊇ clconv ∋ w ⇒ x_t = w ∉ X, contradiction". Consequences:
   **no Motzkin stub, no affine-slice transfer, one ladder proof instead of two.** Motzkin
   ("closed Chebyshev ⇒ convex") remains an optional Phase-2 corollary of Fremlin + dichotomy:
   if M_S = ∅ then C_S = ∅, so the dichotomy at p ∈ conv S \ S yields a half-space through the
   foot, contradicting p ∈ conv S via `convexHull_min`. No Brouwer needed.
3. **Prop 2's sup-condition is mis-stated** in the paper (`B(p_t, d(p_t)) ∩ X = ∅` is vacuously
   true). Correct reading: balls tangent at x_p, i.e. `B(x_p + t•v, t) ∩ X = ∅`. Also Carathéodory
   + the simplex computation is unnecessary: the half-space is convex, so `convexHull_min` does it
   in one line.
4. **The "swallowing" steps of Props 3/4 are loose** ("any sequence c_n ∈ C_X with ‖c_n‖ → ∞,
   c_n/‖c_n‖ → η eventually captures p" — false for arbitrary such sequences). Fix: the
   quantitative criterion `p ∈ ball (x + ρ•v) ρ ↔ 2ρ⟪v, p−x⟫ > ‖p−x‖²` (v unit), carrying the
   tangent point x_t and direction v_t through the construction. Verified to close both proofs:
   - Prop 3: anchor x_t near foot a via: a is the *unique* foot of tη+a (one-line computation using
     X ⊆ {⟪η,·⟫ ≤ 0}, ⟪η,a⟫ = 0), then closed-graph usc gives feet of tη + (λa+(1−λ)b) within ε
     of a for λ near 1. Then r_t ≥ t → ∞, ⟪v_t, p − x_t⟫ → ⟪η, p⟫ > 0, ‖p − x_t‖ bounded ⇒
     criterion holds for large t.
   - Prop 3, infinite-radius branch: X ⊆ {⟪w_t − x_t, · − x_t⟫ ≤ 0} evaluated at a and b gives
     x_t = λa+(1−λ)b; but strict ball convexity makes proper combinations of two *equidistant*
     feet strictly closer to q than R = d_{X∩L}(q), so the combination is *not* in X∩L, while
     x_t ∈ X and x_t ∈ L — contradiction. (This is why the paper's "λ₁a + λ₂b ≠ x_t" holds.)
   - Prop 4: the coordinate computation becomes one line, coordinate-free:
     ‖x_t − w‖² = d(w_t)² − t² + 2t⟪η, x_t⟫ ≤ 2tδ* + d(w)² where δ* = −⟪η, x*⟫ ≥ 0 for any foot
     x* of w. So ‖x_t − w‖ = O(√t) while t⟪η, p − w⟫ grows linearly ⇒ criterion holds for large t.
   - Prop 4, infinite branch (simpler than paper): X ⊆ half-space ⇒ cl(conv X) ⊆ half-space
     (`convexHull_min` + closure) ∋ w ⇒ ‖w − x_t‖² ≤ 0 ⇒ x_t = w ∉ X, contradiction. No
     approximating sequences a_ν, b_ν needed.
5. **Cor 5 is not a corollary of Prop 4's statement** (paper: "raise a sequence of balls as in the
   proof"). With the swallow criterion it is in fact a *one-shot* argument, no limits: for
   p ∈ cl(conv X) \ conv X, p ∉ X, take a supporting hyperplane at p (p is a frontier point;
   interior-empty case reduces to the affine hull, see §5 F); p itself is the defect witness; run
   the dichotomy once from a foot x_t of w_t = tη + p (any fixed t > 0): the infinite branch gives
   x_t = p ∉ X (contradiction), the finite branch gives a maximal ball whose criterion at p reads
   2r_t⟪v_t, p−x_t⟫ ≥ 2(r_t/d(w_t))‖p−x_t‖² ≥ 2‖p−x_t‖² > ‖p−x_t‖². ∎
6. **Theorem 6 (⟹) proof sketch in the paper has a real gap** (a separating hyperplane through the
   first contact point ā need not exist — grazing/tangency; also ā can coincide with q ∈ X).
   **Complete elementary replacement found** (also avoids any interior-nonemptiness assumption):
   - p reconstructible, p ∉ cl(conv X) =: C. Take a ∈ M_X with p ∈ B(a, d(a)) and two distinct
     feet q ≠ q'; let q'' := midpoint q q' ∈ C ∩ B(a, d(a)) (strict ball convexity), so q'' ∉ X.
   - The segment [p, q''] lies in the open ball; let ā be its first point in C (from p). Then
     ā ∉ X (it's in the open ball ⊆ Xᶜ) and [p, ā) ∩ C = ∅.
   - For b ∈ [p, ā) near ā, let z_b := proj_C(b) (Hilbert projection; exists/unique, mathlib).
     ‖z_b − ā‖ ≤ ‖z_b − b‖ + ‖b − ā‖ ≤ 2‖b − ā‖ → 0, and X is closed with ā ∉ X, so z_b ∉ X for
     b close enough: **defect witness**. Let v_b := (b − z_b)/‖b − z_b‖, c_b := ⟪v_b, z_b⟫; the
     projection characterization `norm_eq_iInf_iff_real_inner_le_zero` makes (v_b, c_b) a
     supporting hyperplane of C.
   - p ∈ L⁺: with u := direction from ā to p, ⟪v_b, u⟫ = ⟪v_b, b − ā⟫/‖b−ā‖ ≥ ‖b − z_b‖/‖b−ā‖ > 0
     (using ⟪v_b, ā − z_b⟫ ≤ 0), hence ⟪v_b, p − z_b⟫ = ‖p−b‖⟪v_b, u⟫ + ‖b − z_b‖ > 0. ∎

## 5. Design: definitions and proof architecture

### Definitions (metric-general where possible)

```lean
namespace Metric
variable {α : Type*} [PseudoMetricSpace α] (X : Set α)

/-- The set `m(a)` of points of `X` nearest to `a`. -/
def nearestPoints (a : α) : Set α := {x ∈ X | dist a x = infDist a X}

/-- The medial axis: points with at least two nearest points in `X`. -/
def medialAxis : Set α := {a | (nearestPoints X a).Nontrivial}

/-- `p` is reconstructible if it lies in a medial ball. -/
def IsReconstructiblePt (p : α) : Prop := ∃ a ∈ medialAxis X, dist p a < infDist a X

def Reconstructible : Prop := ∀ p ∉ X, IsReconstructiblePt X p
```

```lean
-- Normed-space level (needs ball-inclusion geometry):
/-- `ball c r` is a maximal open ball inside `U`. -/
def IsMaximalBallIn (c : E) (r : ℝ) (U : Set E) : Prop :=
  0 < r ∧ ball c r ⊆ U ∧
    ∀ ⦃c' r'⦄, 0 < r' → ball c' r' ⊆ U → ball c r ⊆ ball c' r' → c' = c ∧ r' = r

def centralSet (X : Set E) : Set E := {c | IsMaximalBallIn c (infDist c X) Xᶜ}
-- lemma: c ∈ centralSet X ↔ ∃ r, IsMaximalBallIn c r Xᶜ  (radius is forced to be infDist)
```

```lean
-- Inner-product level (hyperplanes via normal vectors; convert HB functionals via toDual):
def IsSupportingHyperplane (s : Set E) (v : E) (c : ℝ) : Prop :=
  v ≠ 0 ∧ (s ∩ {x | ⟪v, x⟫ = c}).Nonempty ∧ ∀ x ∈ s, ⟪v, x⟫ ≤ c
-- L⁺ := {x | c < ⟪v, x⟫};  defect := X ∩ {⟪v,·⟫ = c} ≠ closedConvexHull ℝ X ∩ {⟪v,·⟫ = c}
```

Target statement:

```lean
theorem Metric.reconstructible_iff (hX : IsClosed X) (hne : X.Nonempty) :
    Reconstructible X ↔ Xᶜ ⊆ closedConvexHull ℝ X ∪
      ⋃ (v : E) (c : ℝ)
        (_ : IsSupportingHyperplane (closedConvexHull ℝ X) v c)
        (_ : X ∩ {x | ⟪v, x⟫ = c} ≠ closedConvexHull ℝ X ∩ {x | ⟪v, x⟫ = c}),
        {x | c < ⟪v, x⟫}
```

### Lemma stack (dependency order)

- **A. Basic API** (~mostly metric-general): `nearestPoints` nonempty/compact for closed nonempty X
  in proper spaces; closed graph of (a, x) ↦ x ∈ nearestPoints; `medialAxis X ∩ X = ∅`
  (m(a) = {a} for a ∈ X); behavior under isometries (`medialAxis_image` etc. — needed for the
  in-hyperplane Motzkin, F below); `Convex.medialAxis_eq_empty` (smoke test, via mathlib's convex
  projection uniqueness).
- **B. Ball geometry helpers** (normed/IPS):
  `ball_subset_ball_iff` (0 < r → (ball c r ⊆ ball c' r' ↔ dist c c' ≤ r' − r));
  **swallow criterion** `mem_ball_ray_iff : p ∈ ball (x + ρ•v) ρ ↔ 2ρ⟪v, p−x⟫ > ‖p−x‖²` (‖v‖=1);
  tangent family monotone: t ≤ t' → ball (x+t•v) t ⊆ ball (x+t'•v) t'; union over t < T equals
  ball (x+T•v) T; union over all t equals the open half-space {y | ⟪v, y−x⟫ > 0}. (All immediate
  from the criterion — keeps everything algebraic.)
- **C. medialAxis ⊆ centralSet**: two equidistant feet pin a maximal ball (strict convexity /
  `dist_add_dist_eq_iff` collinearity argument).
- **D. Inflation dichotomy** (the engine): X closed nonempty, x₀ ∈ X, v unit with
  ball(x₀+t₀•v, t₀) ∩ X = ∅ for some t₀ > 0. Let T := sup of such t. Either T = ∞ and
  X ∩ {y | ⟪v, y−x₀⟫ > 0} = ∅, or T < ∞ and x₀ + T•v ∈ centralSet X with d(x₀+T•v) = T,
  x₀ ∈ nearestPoints X (x₀+T•v) (maximality via B + strict convexity). Specialization: for p ∉ X
  with foot x_p and v = (p−x_p)/d(p), the ball at any T ≥ d(p) contains p (criterion: 2T > d(p)).
- **E. Fremlin (STUB in Phase 1)** `centralSet_subset_closure_medialAxis := sorry` — Phase 2
  route in §4.1. Hardest single lemma of Phase 2.
- **Lemma 1** `isReconstructiblePt_iff_exists_centralSet`: → via C; ← via E + 1-Lipschitz infDist.
- **F. Frontier supporting hyperplane, empty-interior case** (small): if
  `interior (closedConvexHull ℝ X) = ∅` then the hull spans a proper affine subspace
  (`Convex.interior_nonempty_iff_affineSpan_eq_top`-style), and any unit v orthogonal to its
  direction gives a supporting hyperplane through any p ∈ hull. Needed only by Cor 5.
- **Prop 2** `isReconstructiblePt_of_mem_convexHull`: D + Lemma 1 + `convexHull_min` (§4.3).
- **Unified Prop 3/4** `isReconstructiblePt_of_inner_lt` (hypotheses: X ⊆ {⟪η,·⟫ ≤ c}, defect
  witness w ∈ closedConvexHull ∩ {⟪η,·⟫ = c}, w ∉ X, conclusion for all p with c < ⟪η,p⟫):
  the w-ladder with the O(√t) transverse bound and the explicit swallow chain — full proof in
  notes §5. Paper's Prop 3 is a special case (one-line corollary if wanted). Bulk of the
  analytic work, but a single construction.
- **Cor 5** `isReconstructiblePt_of_mem_closure_convexHull`: one-shot ladder (§4.5) + supporting
  hyperplane at a frontier point (interior-nonempty case via
  `geometric_hahn_banach_of_nonempty_interior_point`; empty-interior case via F, where the
  X = hull subcase is vacuous since then hull \ X = ∅).
- **Theorem 6**: ⟸ = Cor 5 + Prop 4 (note cl(conv X) ∩ L convex ⇒ defective L has X∩L ≠ that,
  feeding Prop 4). ⟹ = the new proof in §4.6 (Hilbert projection; no Props needed).

## 6. Files and naming

Flat files in the existing directory `Mathlib/Analysis/Convex/` (no new directories):

1. `Mathlib/Analysis/Convex/MedialAxis.lean` — definitions + A + C (defs section is
   metric-general; can be split out to `Mathlib/Topology/MetricSpace/` at PR time if reviewers
   prefer).
2. `Mathlib/Analysis/Convex/MedialAxisInflation.lean` — B, D, the Fremlin stub in a
   clearly-marked "Assumed classical result (Phase 2)" section, Lemma 1.
3. `Mathlib/Analysis/Convex/MedialAxisReconstruction.lean` — supporting hyperplanes, F,
   Prop 2, unified Prop 3/4, Cor 5, Theorem 6.

Register imports with `lake exe mk_all` (CI checks this). Namespace `Metric` for the metric defs;
follow `Mathlib/Analysis/Convex/` conventions otherwise.

## 7. Milestones

**Phase 1 — the paper (only Fremlin assumed via a `sorry` stub):**

| # | Deliverable | Contents | Est. size | Risk |
|---|---|---|---|---|
| M1 | **DONE** (commit c07e0054) | defs, A, C, smoke tests — `MedialAxis.lean` | 400–700 lines | low |
| M2 | **DONE** (commit c07e0054) | §4.6 proof — `MedialAxisReconstruction.lean`; sorry-free, std axioms | 300–500 | low (proof fully worked) |
| M3 | **DONE** (516659fb) | B, D — `MedialAxisInflation.lean` | 400–600 | low-med |
| M4 | **DONE** (799758e5) | Fremlin stated (`sorry`), Lemma 1, Prop 2 | 150–300 | low |
| M5 | **DONE** (ebfb4565) | engine `isReconstructiblePt_of_inner_le`; *no limits needed* — exact cross-term cancellation, explicit t | 400–800 | was med-high, landed easily |
| M6 | **DONE** (7f1380fb) | F + Cor 5 (engine at t = 1, w = p) + `Metric.reconstructible_iff` | 300–500 | low-med |

**Phase 1 complete (2026-06-12).** Single `sorry` in the codebase: the Fremlin stub. All main
theorems check with standard axioms + `sorryAx` through that stub only; Theorem 6 ⟹ and
`exists_unit_forall_inner_le` are unconditionally sorry-free.

**Phase 2 — discharge the stub:**

| # | Deliverable | Contents | Est. size | Risk |
|---|---|---|---|---|
| M7 | Fremlin proved | §4.1 polygon route (notes Appendix A) | 400–700 | **med-high** (uniformity bookkeeping) |
| M8 | Motzkin corollary (optional) | §4.2, cheap once M7 lands | 100–200 | low |

Total ≈ 3–5k lines. M2 is deliberately early: it is a complete, self-contained, `sorry`-free win
that validates the definitions. Within each milestone: state everything with `sorry` first, get
statements type-correct, then fill (lean4 skill workflow; `lean_goal`/`lean_multi_attempt` for
iteration; checkpoint commits per milestone).

## 8. Risks / decision log

- **Unified Prop 3/4 (M5)** is the Phase-1 critical path: estimates are fully verified on paper
  (notes §5, every inequality displayed) but it is a long inner-product computation; expect
  grind, not surprises.
- **Fremlin (M7, Phase 2)** is the riskiest correctness-critical lemma overall; the polygon route
  (notes Appendix A) is elementary but has real bookkeeping (uniform foot modulus on a compact
  ball). Deferring it is safe: its *statement* is classical and certainly true, and nothing
  downstream changes when the proof lands.
- While the stub is open, every result depending on it (Lemma 1 ←, Prop 2, unified Prop 3/4,
  Cor 5, Theorem 6 ⟸) reports `sorryAx`; only M2's ⟹ direction is unconditionally `sorry`-free
  in Phase 1. Keep the stub in a clearly-marked section so the debt is visible.
- Degenerate cases to keep in hypotheses from the start: `X.Nonempty`, possibly `Nontrivial E`
  for ball-inclusion lemmas; 0-dimensional E.
- Paper's Def 4 normalizes "X on the ≤ side"; we bake the sign into `IsSupportingHyperplane`
  (both orientations of a geometric hyperplane appear as different (v, c) pairs — harmless, and
  the X ⊆ L case correctly yields both half-spaces, matching e.g. X = {(0,±1)} where both sides
  of the vertical line are reconstructible).
- If PR-ing to mathlib: defs/A are independently PR-able; Fremlin and Motzkin are independently
  interesting (Chebyshev ⇒ convex is a known formalization target) and make good standalone PRs.

## 9. Verification

- Per milestone: `lake build` of the touched files (or `lean_build` MCP); at milestone close,
  zero `sorry`s **except the single named stub** (Fremlin) during Phase 1; `lean_verify` on the
  main theorems (expect exactly `sorryAx` via that stub and nothing else).
- Smoke-test examples in a scratch section (not committed to Mathlib files):
  `Convex.medialAxis_eq_empty` consistency (disc example: nothing reconstructible);
  two-point set X = {q₁, q₂}: medialAxis = bisector hyperplane, Theorem 6 RHS = everything except
  the two rays of the line through q₁q₂ beyond the points — sanity-checkable instance.
- `lake exe mk_all --check` for import registration; run mathlib linters (`#lint` locally / CI).

## 10. Open follow-ups (not in this plan)

- Prop 7 (stability under Kuratowski convergence) — requires building Kuratowski liminf/limsup of
  sets first (nothing in mathlib).
- λ-medial axis (Def 5, Prop 8, Conjecture 9).
- Riemannian version (cot1/cot2 notes; Busemann functions exist in mathlib? unchecked — separate
  investigation).
