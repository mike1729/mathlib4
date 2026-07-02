"""
Does TWO-POINT total reconstruction survive off constant curvature?

Test: X = {x0, x1} (maximally sparse) on a positively curved surface of
revolution (prolate ellipsoid, sec>0 everywhere).  With |X|=2 the two-point
medial axis M_X is exactly the bisector {a: d(a,x0)=d(a,x1)}, and
  q in R_X  <=>  exists bisector a with d(a,q) < r(a)=d(a,x0).
We compute the GLOBAL reconstructed set R_X and its complement (shielded set),
validating the whole pipeline on the ROUND SPHERE first (where the theorem
guarantees R_X = M\X, i.e. shielded set empty).

Geodesic distance: Dijkstra on a dense surface point cloud with edges to all
neighbours within a Euclidean radius (Lanthier-style; Euclidean ~ geodesic for
nearby points on a smooth surface).  Validated against arccos on the sphere.
"""
import numpy as np
from scipy.sparse import csr_matrix
from scipy.sparse.csgraph import dijkstra

def fibonacci_sphere(N):
    i = np.arange(N) + 0.5
    phi = np.arccos(1 - 2*i/N)            # colatitude
    gold = np.pi*(1+5**0.5)
    theta = gold*i
    x = np.sin(phi)*np.cos(theta); y = np.sin(phi)*np.sin(theta); z = np.cos(phi)
    return np.stack([x,y,z], 1)

def build(N, c):
    """Point cloud on ellipsoid x^2+y^2+(z/c)^2=1 (c=1 -> round sphere)."""
    S = fibonacci_sphere(N)
    P = S.copy(); P[:,2] *= c
    return P

def geodesic_graph(P, radius_mult=3.0):
    from scipy.spatial import cKDTree
    tree = cKDTree(P)
    # mean nearest-neighbour spacing
    d1,_ = tree.query(P, k=2); h = d1[:,1].mean()
    R = radius_mult*h
    pairs = tree.query_pairs(R, output_type='ndarray')
    w = np.linalg.norm(P[pairs[:,0]]-P[pairs[:,1]], axis=1)
    n = len(P)
    rows = np.concatenate([pairs[:,0], pairs[:,1]])
    cols = np.concatenate([pairs[:,1], pairs[:,0]])
    ww   = np.concatenate([w, w])
    G = csr_matrix((ww,(rows,cols)), shape=(n,n))
    return G, h

def nearest(P, pt):
    return int(np.argmin(np.linalg.norm(P-pt,axis=1)))

def run(name, c, N=7000, radius_mult=3.0):
    print(f"\n================ {name}  (c={c}, N={N}) ================")
    P = build(N, c)
    G, h = geodesic_graph(P, radius_mult)
    # validation on the SPHERE only (ground truth = arccos)
    if abs(c-1.0) < 1e-9:
        src = nearest(P, np.array([1.0,0,0]))
        Dnum = dijkstra(G, indices=src, directed=False)
        Dtrue = np.arccos(np.clip(P@P[src], -1, 1))
        finite = np.isfinite(Dnum) & (Dtrue>0.2) & (Dtrue<2.9)
        relerr = np.abs(Dnum[finite]-Dtrue[finite])/Dtrue[finite]
        print(f"  geodesic validation: mean rel err {relerr.mean()*100:.2f}%, "
              f"95th pct {np.percentile(relerr,95)*100:.2f}%, max {relerr.max()*100:.2f}%")

    # X = two points: x0 on the waist (equator), x1 at the top tip
    i0 = nearest(P, np.array([1.0, 0.0, 0.0]))     # waist
    i1 = nearest(P, np.array([0.0, 0.0, c]))        # top tip
    D = dijkstra(G, indices=[i0, i1], directed=False)
    D0, D1 = D[0], D[1]
    finite = np.isfinite(D0) & np.isfinite(D1)
    scale = np.nanmax(D0[finite])

    # bisector nodes: |D0-D1| small (two-point medial axis, |X|=2)
    eps = 1.5*h
    bis = np.where(finite & (np.abs(D0-D1) < eps))[0]
    bis = bis[(bis!=i0)&(bis!=i1)]
    r = 0.5*(D0[bis]+D1[bis])                        # reach r(a)=d(a,X)
    print(f"  scale(diam from waist) {scale:.3f}, mesh h {h:.4f}, "
          f"#bisector nodes {len(bis)}")

    # global reconstructed set: cover q if some bisector a has d(a,q) < r(a)
    Dbis = dijkstra(G, indices=list(bis), directed=False)   # (nb x N)
    # conservative margins relative to mesh error
    val = 0.02*scale                                  # ~2% numeric tolerance
    # covered (strict, conservative AGAINST coverage): need clearly inside
    covered = (Dbis < (r[:,None] - val)).any(axis=0)
    # uncovered even generously (ball allowed bigger): clearly shielded
    cov_gen = (Dbis < (r[:,None] + val)).any(axis=0)
    onX = np.zeros(len(P), bool); onX[i0]=onX[i1]=True
    valid = finite & ~onX

    shielded_strict = valid & ~cov_gen               # shielded even allowing +2% balls
    shielded_loose  = valid & ~covered               # not covered at -2%
    frac_recon = covered[valid].mean()
    print(f"  reconstructed fraction (conservative): {frac_recon*100:.1f}%")
    print(f"  SHIELDED nodes (strict, uncovered even w/ +2% balls): {shielded_strict.sum()}")
    print(f"  shielded nodes (loose, -2%): {shielded_loose.sum()}")

    if shielded_strict.sum() > 0:
        idx = np.where(shielded_strict)[0]
        # report a representative shielded point + its margin
        # margin(q) = min_a [d(a,q) - r(a)]  (>0 means shielded)
        margins = (Dbis[:, idx] - r[:,None]).min(axis=0)
        jbest = idx[np.argmax(margins)]            # most robustly shielded
        q = P[jbest]
        # describe location
        zfrac = q[2]/c
        d0q, d1q = D0[jbest], D1[jbest]
        print(f"  e.g. shielded q=({q[0]:+.2f},{q[1]:+.2f},{q[2]:+.2f}) z/c={zfrac:+.2f}; "
              f"d(q,x0)={d0q:.3f} d(q,x1)={d1q:.3f}; "
              f"min margin over bisector = {margins.max():.3f} "
              f"(= {margins.max()/scale*100:.1f}% of scale)")
        # how big is the shielded region?
        print(f"  shielded fraction of surface: {shielded_strict.mean()*100:.1f}%")
    else:
        print("  -> NO shielded points: two-point reconstruction is TOTAL here.")
    return shielded_strict.sum()

# Validate on the round sphere, then test the prolate ellipsoid.
s_sphere = run("ROUND SPHERE  S^2  (constant curvature, theorem: total)", c=1.0)
s_prol1  = run("PROLATE ELLIPSOID  c=2.0  (sec>0, variable)", c=2.0)
s_prol2  = run("PROLATE ELLIPSOID  c=3.0  (sec>0, more variable)", c=3.0)

print("\n================ VERDICT ================")
print(f"round sphere shielded: {s_sphere}   (expect ~0: validates method + theorem)")
print(f"prolate c=2.0 shielded: {s_prol1}")
print(f"prolate c=3.0 shielded: {s_prol2}")
