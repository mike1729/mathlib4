"""Numerical check of the capture theorem (medial_axis_complete.tex, Thm 3.1)
on S^2 with X a non-circular convex curve (continuum contact set, sliding feet).

Checks, along the discrete capture flow x' = -u(x) (step away from nearest point):
  (1) rate-one identity: d_X(Phi_t) - d_X(p) ~ t while the trajectory avoids
      the two-geodesic axis (including through focal points, where the foot
      slides continuously -- the delicate regime);
  (2) capture margin: at the first approach to a genuine two-foot tie,
      d_X(a) - d(p,a) >= d_X(p) - tol.
"""
import numpy as np

rng = np.random.default_rng(7)

def sphd(x, y):
    return np.arccos(np.clip(np.dot(x, y), -1.0, 1.0))

def normalize(v):
    return v / np.linalg.norm(v)

def step_away(x, foot, h):
    """Unit-speed step from x along the great circle away from `foot`."""
    t = normalize(np.cross(np.cross(x, foot), x))   # tangent at x toward foot
    d = -t                                          # away from foot
    return normalize(np.cos(h) * x + np.sin(h) * d)

# X: convex non-circular closed curve on S^2 (perturbed latitude circle),
# colatitude beta(phi) = 0.9 + 0.25*cos(2 phi)  -> genuinely varying curvature,
# nonempty focal set (evolute) inside.
M = 4000
phis = np.linspace(0, 2 * np.pi, M, endpoint=False)
beta = 0.9 + 0.25 * np.cos(2 * phis)
X = np.stack([np.sin(beta) * np.cos(phis),
              np.sin(beta) * np.sin(phis),
              np.cos(beta)], axis=1)

def dX_and_feet(x, tie_tol):
    d = np.arccos(np.clip(X @ x, -1.0, 1.0))
    i0 = np.argmin(d)
    dmin = d[i0]
    near = np.where(d <= dmin + tie_tol)[0]
    return dmin, i0, near

def angular_spread(idx):
    """Max pairwise angular gap (in parameter phi) of a set of contact indices."""
    ph = np.sort(phis[idx])
    gaps = np.diff(np.concatenate([ph, [ph[0] + 2 * np.pi]]))
    return 2 * np.pi - gaps.max()   # extent of the arc covered

h = 2e-4          # step size
tie_tol = 5e-4    # distance tie tolerance (>> curve discretisation ~ 2pi/M)
spread_tol = 0.2  # feet count as *distinct* if parameter spread exceeds this

fails = 0
trials = 60
worst_rate = 1.0
worst_margin_gap = 0.0
for tr in range(trials):
    # start near the curve, inside (toward the pole), so the flow crosses the
    # focal set before reaching the medial axis for many directions
    ph0 = rng.uniform(0, 2 * np.pi)
    b0 = 0.9 + 0.25 * np.cos(2 * ph0)
    inward = rng.uniform(0.05, 0.35)
    bstart = b0 - inward
    p = np.array([np.sin(bstart) * np.cos(ph0),
                  np.sin(bstart) * np.sin(ph0),
                  np.cos(bstart)])
    d0, i0, near0 = dX_and_feet(p, tie_tol)
    if d0 < 5 * h or angular_spread(near0) > spread_tol:
        continue  # started on/too close to X or already on the axis

    x = p.copy()
    t = 0.0
    captured = False
    for k in range(200000):
        dmin, i0, near = dX_and_feet(x, tie_tol)
        if angular_spread(near) > spread_tol:
            captured = True
            break
        x = step_away(x, X[i0], h)
        t += h
    if not captured:
        continue

    dcap, _, _ = dX_and_feet(x, tie_tol)
    rate = (dcap - d0) / t if t > 0 else 1.0
    margin = dcap - sphd(p, x)
    worst_rate = min(worst_rate, rate)
    gap = d0 - margin
    worst_margin_gap = max(worst_margin_gap, gap)
    ok = abs(rate - 1.0) < 5e-3 and margin >= d0 - 5e-3
    if not ok:
        fails += 1
        print(f"trial {tr}: rate={rate:.5f} margin={margin:.5f} dX(p)={d0:.5f}")

print(f"trials with capture: checked; failures: {fails}")
print(f"worst dX growth rate along flow (should be ~1): {worst_rate:.5f}")
print(f"worst (dX(p) - margin) at capture (should be <= ~0): {worst_margin_gap:.2e}")
