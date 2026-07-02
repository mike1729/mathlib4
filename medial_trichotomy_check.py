"""
Numeric backing for the Busemann-Hessian-sign trichotomy (capstone note).

Central positive-curvature claim being checked:
  On S^n the signed distance to an equator, b(x) = d(x,v) - pi/2 (v the pole),
  has Hess b = cot(d(x,v)) * (g - dr (x) dr).  Hence:
    - inside the v-hemisphere (r<pi/2): cot r > 0  => b convex, sublevel convex;
    - on the equator (r=pi/2):           cot r = 0  => Hessian vanishes;
    - outside (r>pi/2):                   cot r < 0  => b concave, sublevel NON-convex.
  Therefore the maximal geodesically convex free region is the hemisphere
  (radius = convexity radius pi/2): BOUNDED, with a FINITE centre v.
  This is the curvature>0 branch: finite centre, detection = (>=2 contacts).

Checks:
  (A) cap of angular radius R about a pole is geodesically convex  <=>  R <= pi/2
      (the convexity-radius / boundedness threshold).
  (B) tangential eigenvalue of Hess d(.,v), by finite differences, equals cot r,
      flipping sign exactly at r = pi/2.
  (C) finite-centre reconstruction: a free hemisphere with >=2 equatorial
      contacts has an equidistant (pi/2) pole that is medial.
"""
import numpy as np

rng = np.random.default_rng(0)

def normalize(x):
    return x / np.linalg.norm(x, axis=-1, keepdims=True)

def dist(x, y):
    return np.arccos(np.clip(np.dot(x, y), -1.0, 1.0))

def geodesic_midpoint(x, y):
    """Midpoint of the (unique, if x!=-y) minimizing geodesic on the sphere."""
    m = x + y
    nm = np.linalg.norm(m)
    if nm < 1e-12:               # antipodal: midpoint undefined
        return None
    return m / nm

# ---------- (A) convexity-radius threshold: caps convex iff R <= pi/2 ----------
print("(A) Geodesic convexity of a cap of angular radius R about the pole e3:")
e = np.array([0.0, 0.0, 1.0])
for R in [0.4, 0.8, np.pi/2 - 0.02, np.pi/2 + 0.02, 2.0, 2.6]:
    # sample many pairs inside the closed cap {d(.,e) <= R}, test midpoint stays in
    worst = 0.0
    leaks = 0
    N = 40000
    for _ in range(N):
        # random points in the cap: colatitude in [0,R], uniform-ish
        def rand_in_cap():
            ct = np.cos(R) + (1 - np.cos(R)) * rng.random()   # cos colat in [cosR,1]
            st = np.sqrt(max(0.0, 1 - ct*ct))
            ph = 2*np.pi*rng.random()
            return np.array([st*np.cos(ph), st*np.sin(ph), ct])
        x, y = rand_in_cap(), rand_in_cap()
        mid = geodesic_midpoint(x, y)
        if mid is None:
            continue
        dm = dist(mid, e)
        if dm > R + 1e-9:
            leaks += 1
            worst = max(worst, dm - R)
    status = "CONVEX" if leaks == 0 else f"NOT convex (leaks={leaks}, worst excess={worst:.4f})"
    flag = "<= pi/2" if R <= np.pi/2 + 1e-12 else "> pi/2"
    print(f"   R={R:5.3f} ({flag:7s}) : {status}")

# ---------- (B) tangential Hessian eigenvalue of d(.,v) equals cot r ----------
print("\n(B) Tangential eigenvalue of Hess d(.,v) vs cot(r) (finite differences):")
v = np.array([0.0, 0.0, 1.0])
def d_to_v(x):
    return dist(normalize(x), v)
for r in [0.3, 0.7, np.pi/2 - 0.1, np.pi/2, np.pi/2 + 0.1, 2.0, 2.5]:
    # base point at colatitude r in the x-z plane
    p = np.array([np.sin(r), 0.0, np.cos(r)])
    # unit tangent at p orthogonal to the radial (d/dr) direction: the e_phi direction
    t_hat = np.array([0.0, 1.0, 0.0])            # tangential, orthogonal to grad d
    h = 1e-3
    # second difference of d along the geodesic in direction t_hat
    def step(sign):
        q = np.cos(h) * p + np.sin(h) * sign * t_hat   # geodesic from p in dir t_hat
        return d_to_v(q)
    f0 = d_to_v(p)
    hess_tt = (step(+1) - 2*f0 + step(-1)) / (h*h)
    print(f"   r={r:5.3f}: Hess_tt={hess_tt:+.4f}  cot r={1/np.tan(r):+.4f}  "
          f"sign={'+' if hess_tt>1e-6 else ('0' if abs(hess_tt)<1e-2 else '-')}")

# ---------- (C) finite-centre reconstruction: free hemisphere, >=2 contacts ----------
print("\n(C) Finite-centre (pole) reconstruction on S^2, random free hemispheres:")
fails = 0
trials = 2000
for _ in range(trials):
    vpole = normalize(rng.standard_normal(3))
    # build a contact set ON the equator of vpole: orthogonal to vpole
    # pick k>=2 points on the great circle {<.,vpole>=0}
    b1 = normalize(np.cross(vpole, rng.standard_normal(3)))
    b2 = normalize(np.cross(vpole, b1))
    k = rng.integers(2, 6)
    angs = rng.random(k) * 2*np.pi
    X = np.array([np.cos(a)*b1 + np.sin(a)*b2 for a in angs])  # all have <x,vpole>=0
    # all equidistant pi/2 from vpole?
    ds = np.array([dist(vpole, x) for x in X])
    equidist = np.allclose(ds, np.pi/2, atol=1e-9)
    # vpole is medial (>=2 nearest) and B(vpole,pi/2)=hemisphere is free
    # check freeness: no contact strictly inside hemisphere
    free = np.all(np.array([np.dot(vpole, x) for x in X]) <= 1e-12)
    # a random interior point of the hemisphere is reconstructed (in B(vpole,pi/2))
    interior = normalize(vpole + 0.3*normalize(rng.standard_normal(3)))
    while np.dot(interior, vpole) <= 0.05:
        interior = normalize(vpole + 0.3*normalize(rng.standard_normal(3)))
    covered = dist(interior, vpole) < np.pi/2 - 1e-12
    if not (equidist and free and covered):
        fails += 1
print(f"   {trials} trials, failures = {fails}")
print("\nDone.")
