I'm reviewing the extensive mathematical work from my previous thinking to understand what's been established so far about generalizing Theorem 6 to Riemannian manifolds. Let me verify the key claims and organize this into a coherent writeup that builds on what's already been developed. Now I'm defining the key objects on a Riemannian manifold: the medial axis consists of points with at least two distinct minimizing geodesics to XX
X (not just two feet, since on manifolds geodesics can branch), and reconstructibility means a point lies in some ball centered at a medial axis point with radius equal to its distance to XX
X.
For rays emanating to infinity, I'm introducing the Busemann function and using it to define free horoballs—the maximal open regions disjoint from XX
X that are bounded by horospheres. The horoball hull X^\widehat{X}
X is then the complement of all such disjoint horoballs, equivalently characterized as the set where the Busemann function stays above its infimum for every ray.
In Euclidean space, this recovers the convex hull since horoballs correspond exactly to open half-spaces—the Busemann function for a ray in direction η\eta
η gives a linear functional, so its sublevel sets are half-spaces with normal η\eta
η. On compact manifolds without rays to infinity, the construction trivializes to the whole space.
Now I'm thinking about defective horoballs: when the boundary horosphere contains a trapped point outside XX
X, the horoball fails to be maximal. This connects to the Euclidean picture where a supporting hyperplane of conv⁡X\operatorname{conv}X
convX is defective if it doesn't contain the full intersection of XX
X with that hyperplane—I need to check whether the paper's definition aligns with this geometric condition. conv}X \cap L$ always, the defect condition means there's a point in the horosphere that touches the convex hull but lies outside the original set XX
X. In horoball geometry, the boundary horosphere plays the role of the supporting hyperplane LL
L, and the trapped condition is that it intersects X^∖X\widehat{X} \setminus X
X∖X. The Euclidean analogue would use the closed convex hull instead, giving a slightly different formulation than what the paper states, though the paper itself is imprecise about closure.
There's a discrepancy worth noting: Theorem 6 uses the open convex hull while Corollary 5 reconstructs the closed one. Now I'm laying out the two main results from the scratch work. The first is a curvature-free sufficiency theorem stating that every point outside XX
X but in its hull is reconstructible, with the proof relying on the distance function and the medial axis structure. p is the point at distance δ along the geodesic. I'm defining r as the supremum of all distances t where the ball around γ(t) with radius t doesn't intersect X, and checking that this set forms an interval using the triangle inequality — for any smaller t, the distance from points in X to γ(t) is at least t by the metric properties along the geodesic.
For t < r, I'm verifying that γ restricted to [0,t] is a minimizing geodesic from γ(t) to X: the freeness condition ensures d(γ(t), X) ≥ t, and since d(γ(t), x_p) ≤ t, we get equality, confirming that the path is indeed minimizing.
Now for the case where r = ∞: γ becomes a ray with each segment minimizing, and the union of all balls B(γ(t), t) forms an open horoball around the Busemann function b_γ that's disjoint from X and contains p. I'm checking that this union equals {b_γ < 0} by examining how the Busemann function behaves on points in these balls. So the contradiction follows: cγ=inf⁡Xbγ≥0c_\gamma = \inf_X b_\gamma \ge 0
cγ​=infX​bγ​≥0 but bγ(p)<0b_\gamma(p) < 0
bγ​(p)<0, meaning pp
p can't be in the closure. Now for the finite radius case, I'm setting a=γ(r)a = \gamma(r)
a=γ(r) and verifying that d(a)=rd(a) = r
d(a)=r by continuity, with B(a,r)B(a,r)
B(a,r) disjoint from XX
X. The key remaining question is whether this ball is actually free, which requires checking the distance condition for points inside it. So the key insight is that aa
a marks where the geodesic stops being minimizing to XX
X—this is the cut point. The crucial theorem here is that the cut locus of a closed set in a complete manifold sits inside the closure of points admitting multiple minimizing geodesics, a result going back to Wolter's work in the 1980s and related to viscosity solutions theory. More precisely, for distance functions from closed subsets, the cut locus equals the closure of the non-uniqueness set where minimizing geodesics aren't unique. vable at points with multiple minimizing geodesics from the closed set, so the cut locus is the closure of points where the distance function fails to be differentiable — this is Albano's result that I should cite as the key external reference for the closed set case. that's Albano's theorem for closed sets — the cut locus is the closure of the singular set. Now I'm checking a subtlety: whether the endpoint where a geodesic stops minimizing to XX
X actually lies in the cut locus as Albano defines it. By definition, a cut point is exactly where the geodesic ceases to minimize distance to XX
X, so yes. The theorem states Cut(X)⊂Σ‾\mathrm{Cut}(X) \subset \overline{\Sigma}
Cut(X)⊂Σ where Σ\Sigma
Σ is the singular set, and I'm verifying this holds since points strictly inside the ball satisfy d(p,a)<rd(p, a) < r
d(p,a)<r.
Since both distance functions are continuous, nearby singular points a′a'
a′ will also satisfy d(p,a′)<d(a′)d(p, a') < d(a')
d(p,a′)<d(a′), making pp
p reconstructible. This argument also implicitly reproves Lemma 1 about the relationship between CXC_X
CX​ and MXM_X
MX​ in the manifold setting, and yields the corollary that on a compact manifold, every nonempty closed set has a fully reconstructible complement — no rays means the infinite radius case is impossible, recovering the paper's remark from section 5.2.
Actually, let me double-check Theorem A more carefully. I showed that for any point pp
p outside XX
X, either pp
p is reconstructible or it lies in an open free horoball where the boundary horosphere passes through the foot point. Taking the contrapositive gives the full statement of Theorem A.
Now for Theorem B in the Hadamard setting: if γ\gamma
γ is a ray with finite critical value cγc_\gamma
cγ​ and the maximal free horoball is defective (meaning there's a point on its boundary that lies in the compactification but not in XX
X), then every point in that horoball must be reconstructible. The proof strategy here is actually simpler than what appears in the paper's Euclidean version — I'll normalize the Busemann function by subtracting cγc_\gamma
cγ​ to center things properly.
With this normalization, the horosphere becomes the level set {b=0}\{b = 0\}
{b=0}, the horoball is {b<0}\{b < 0\}
{b<0}, and the manifold sits in the half-space {b≥0}\{b \geq 0\}
{b≥0}. The defective point ww
w satisfies b(w)=0b(w) = 0
b(w)=0 and lies in the ideal boundary but not in XX
X. The key move is to consider the asymptotic ray from ww
w toward the ideal point ξ=γ(∞)\xi = \gamma(\infty)
ξ=γ(∞) — in a Hadamard space this ray is unique — and use the fact that Busemann functions of asymptotic rays differ by constants, which gives us the rate at which the Busemann function decreases along this ray.
Now I'm establishing bounds on the distance from points along the ray to the set XX
X. The lower bound follows from the 1-Lipschitz property of bb
b and the fact that b≥0b \geq 0
b≥0 on XX
X, while the upper bound comes from constructing a path through ww
w. The crucial observation is that the distance is strictly greater than the parameter value along the ray for all positive times.
To prove this strictness, I assume the distance equals tt
t at some point and derive a contradiction. If there's a closest point xtx_t
xt​ on XX
X to wtw_t
wt​, then the Lipschitz bound on bb
b combined with b(wt)=−tb(w_t) = -t
b(wt​)=−t forces b(xt)=0b(x_t) = 0
b(xt​)=0, meaning xtx_t
xt​ lies on the boundary. The minimizing segment connecting them must then align with the asymptotic ray itself, which leads to a contradiction when we trace this geometry further. point and direction, so xtx_t
xt​ and ww
w must lie on the same geodesic. Since bb
b decreases strictly along σxt\sigma_{x_t}
σxt​​ at unit rate, the level-0 point is unique on that geodesic, giving xt=wx_t = w
xt​=w—but w∉Xw \notin X
w∈/X, a contradiction. Therefore d(wt)>td(w_t) > t
d(wt​)>t. Now I need to verify that the backward extensions of σxt\sigma_{x_t}
σxt​​ and σw\sigma_w
σw​ actually coincide; both rays pass through wtw_t
wt​, but I should confirm they're pointing in the same direction before and after that point.
Since both rays are asymptotic to ξ\xi
ξ and the asymptotic ray from any point in a Hadamard manifold is unique, their forward velocities at wtw_t
wt​ must agree. A geodesic is fully determined by a point and velocity, so the two rays extend backward as the same unparametrized geodesic. At parameter −t-t
−t from wtw_t
wt​ along this geodesic sits both xtx_t
xt​ and ww
w, but a single parameter value gives a unique point, so xt=wx_t = w
xt​=w—confirming the contradiction.
Now for the inflation step: I'm taking each wtw_t
wt​ where d(wt)>td(w_t) > t
d(wt​)>t and considering the ball B(wt,d(wt))B(w_t, d(w_t))
B(wt​,d(wt​)), which is free and contains points from H\mathcal{H}
H. I'll pick a foot xt∗x_t^*
xt∗​ in the metric projection m(wt)m(w_t)
m(wt​) and construct a unit-speed minimizing geodesic γt\gamma_t
γt​ starting from xt∗x_t^*
xt∗​ through wtw_t
wt​.
Then I'm finding the cut time rtr_t
rt​ as the supremum of distances ss
s where the ball B(γt(s),s)B(\gamma_t(s), s)
B(γt​(s),s) doesn't intersect XX
X, which is at least d(wt)d(w_t)
d(wt​). When rtr_t
rt​ is finite, the cut point ct=γt(rt)c_t = \gamma_t(r_t)
ct​=γt​(rt​) satisfies a nesting property: the ball around wtw_t
wt​ fits inside the ball around ctc_t
ct​ because the distance from any point in B(wt,d(wt))B(w_t, d(w_t))
B(wt​,d(wt​)) to ctc_t
ct​ is bounded by rt=d(ct)r_t = d(c_t)
rt​=d(ct​).
For the case where rt=∞r_t = \infty
rt​=∞, the geodesic γt\gamma_t
γt​ extends as a ray, and I need to verify that the horoball centered at infinity along this ray contains ww
w by checking whether bγt(w)<0b_{\gamma_t}(w) < 0
bγt​​(w)<0.  Using the triangle inequality and the fact that d(wt)>td(w_t) > t
d(wt​)>t, I can show this inequality holds, which means ww
w lies in an open free horoball and therefore cannot be in the boundary—a contradiction. So the infinite case is ruled out and case 1 must always apply. Now for the swallowing step: I need to show that every point in H\mathcal{H}
H eventually lies in some ball B(wt,d(wt))B(w_t, d(w_t))
B(wt​,d(wt​)) as tt
t grows large, which requires controlling the distance from points to wtw_t
wt​ relative to the depth function. The Busemann function of the asymptotic ray equals the original one when normalized at ww
w, so for points in the horoball, the Busemann value is negative, which means the distance to wtw_t
wt​ stays bounded below tt
t for large tt
t. Now I'm second-guessing whether asymptotic rays in CAT(0) spaces actually have Busemann functions differing by constants—I should verify this against the standard references.
Looking at the Euclidean sanity check: two rays parallel to the xx
x-axis at different heights give Busemann functions that differ by a constant, and rays from different starting points also differ by a constant. This confirms the property holds.
In the hyperbolic plane, horocycles centered at the same ideal point are level sets of each other's Busemann functions. More generally in CAT(0) spaces, the distance between two asymptotic rays is a convex, bounded function of the parameter, which forces it to be nonincreasing. The key result from BH II.8.20 states that for asymptotic rays in CAT(0), their Busemann functions differ by a constant, though I'm working through what that constant equals exactly.
This is a standard fact in CAT(0) geometry: the horofunction boundary coincides with the visual boundary, meaning every horofunction is Busemann and the map from the visual boundary to horofunctions modulo constants is a bijection. I'll cite BH II.8.13–8.24 for this.
The conclusion follows: the horoball is contained in the union of balls around the points wtw_t
wt​, which lies in the reconstructible set. This completes Theorem B: in a Hadamard space, a maximal free horoball is entirely reconstructible.
Now for Theorem C, I'm stating the sufficiency direction: in a Hadamard space with closed set XX
X, every point in the complement of XX
X plus all maximal free defective horoballs is reconstructible. The necessity direction requires more care — the scratch work revealed gaps in both the manifold case and in the paper's own Euclidean proof, particularly around how segments can tangentially enter the region.
I'm working through a partial necessity result: if pp
p is reconstructible but not in the visual boundary, then pp
p lies in a ball around some point aa
a in the medial axis, and picking a foot qq
q on the medial axis with the right distance property, the geodesic from pp
p to qq
q must have a first entry point into the visual boundary.
Now I'm trying to pin down what happens along the segment before that entry point—each point sits in some open free horoball, so I'm considering a sequence of points approaching the boundary with their corresponding horoballs, hoping to extract a limiting ideal point from the visual boundary's compactness.
Since the visual boundary of a Hadamard manifold is homeomorphic to Sn−1S^{n-1}
Sn−1 with the cone topology, I can extract a convergent subsequence of these ideal points. The key is that normalized Busemann functions converge locally uniformly in this setting, which follows from the homeomorphism between visual and horofunction boundaries. So I need to track the normalized Busemann functions carefully—subtracting the value at a basepoint to handle the normalization constants properly—and verify that the inequality still holds under this normalization. So ww
w lies on the maximal horosphere of ξ∗\xi_*
ξ∗​, but I need to verify whether ww
w is actually outside XX
X. Since ww
w sits on the segment from pp
p (in the open ball) to qq
q (on the boundary sphere), and balls in Hadamard spaces are convex, the open portion [p,q)[p, q)
[p,q) stays strictly inside the open ball, which is disjoint from XX
X. The question is whether ww
w coincides with the boundary point qq
q or enters X^\widehat X
X before reaching it.
If w≠qw \neq q
w=q, then ww
w lies in the open ball and thus outside XX
X, making Hξ∗\mathcal H_{\xi_*}
Hξ∗​​ defective with ww
w as a trapped witness—which would mean everything in Hξ∗\mathcal H_{\xi_*}
Hξ∗​​ is reconstructible by Theorem B, but I haven't established whether pp
p itself belongs to Hξ∗\mathcal H_{\xi_*}
Hξ∗​​, and that's the critical gap. If instead w=qw = q
w=q, then qq
q is the first entry point into X^\widehat X
X and we have bξ∗(q)=cξ∗b_{\xi_*}(q) = c_{\xi_*}
bξ∗​​(q)=cξ∗​​ with q∈Xq \in X
q∈X, which looks non-defective and doesn't immediately yield a contradiction.
The strong pointwise necessity—that every reconstructible point outside X^\widehat X
X lies in some defective maximal free horoball—remains unresolved even in the Hadamard setting. Looking back at the Euclidean proof in the paper, I'm noticing what might be a gap at the tangential entry case too, so I need to carefully trace through their necessity argument in Theorem 6 to see exactly how they handle it and whether the gap is real or fixable. They start with a reconstructible point pp
p outside the convex hull of XX
X, pick qq
q on a ray from aa
a, and use the segment between pp
p and qq
q to establish that part of it stays inside the ball around aa
a.
The key step is showing that for any supporting hyperplane LL
L of conv⁡X\operatorname{conv}X
convX containing the boundary point α\alpha
α, we have α\alpha
α in the relative interior of conv⁡X∩L\operatorname{conv}X \cap L
convX∩L but not in X∩LX \cap L
X∩L. The argument uses the fact that α\alpha
α lies in the free ball so it's not in XX
X, and it's on the boundary of the convex hull—but here's where I see the sloppiness: they're working with conv⁡‾X\overline{\operatorname{conv}}X
convX (the closure) while their defect condition is stated for conv⁡X\operatorname{conv}X
convX itself. It's a minor notational issue but worth flagging. Then they consider a separating hyperplane between pp
p and conv⁡X\operatorname{conv}X
convX to push the argument further. So when I translate L0L_0
L0​ toward the hull until it becomes supporting, the contact point doesn't have to be α\alpha
α, and the hyperplane might touch XX
X at an interior point rather than on the boundary—which means it could be useless for separating pp
p from the hull. The question is whether there's a different hyperplane that actually passes through α\alpha
α and does the job.
Since α\alpha
α lies on the boundary of the closed convex hull (it's the first intersection point of the ray from pp
p), supporting hyperplanes at α\alpha
α definitely exist. But here's the catch: at a tangential entry point, the segment from pp
p to α\alpha
α might actually lie inside the supporting hyperplane itself, like a line grazing a circle at a single point—so pp
p wouldn't be strictly separated. the supporting hyperplane at the entry point would contain the entire segment direction, keeping it tangent to the hull. But for a strictly convex smooth body, a tangent line can only touch at that single point—it can't enter the interior—so the interval [α,β[[\alpha, \beta[
[α,β[ must be empty. Actually, I think the issue is that a tangent line to a strictly convex hull at some point α\alpha
α can still intersect the hull boundary elsewhere — like at qq
q — and the open segment between them might only touch the hull at its endpoints, making the intersection with the closed hull a half-open interval [α,β[[\alpha, \beta[
[α,β[ where β\beta
β is excluded because the segment itself is open at that end. me try to construct a concrete counterexample: a reconstructible point pp
p that lies outside both the hull's closure and all the defective regions L+L^+
L+. If I can build such an example, then Theorem 6 as stated has a genuine gap; if not, the statement might be salvageable.
Actually, I should step back — diving into a counterexample hunt could consume a lot of time. The real issue is that the necessity direction breaks down at these collinear/tangential edge cases, and I suspect the fix is to perturb qq
q slightly within m(a)m(a)
m(a) or use dimension reduction: since the configuration forces everything into the supporting hyperplane LL
L, I can recurse on L≅Rn−1L \cong \mathbb{R}^{n-1}
L≅Rn−1 with the restricted hull and point set. Induction on dimension looks like the right approach here. I'll document this as a fixable gap with a concrete suggested remedy rather than treating it as a fatal flaw.
On the sufficiency side, there's a subtler issue: Proposition 3 claims that direction-convergence alone guarantees ball-swallowing, but that's not quite right — I can sketch a counterexample with cn=(n,n0.9,…)c_n = (n, n^{0.9}, \ldots)
cn​=(n,n0.9,…) where the directions converge but the balls don't grow fast enough. The proof actually survives because of the ϵ\epsilon
ϵ-pinning of feet via upper semicontinuity of mm
m. However, Proposition 4's final step ("by the same argument") has a real quantitative gap when points sit at small height h≤δh \le \delta
h≤δ above LL
L — this is patchable by choosing the trapped point ww
w with sufficiently small δ\delta
δ, which is possible when X∩L≠∅X \cap L \neq \emptyset
X∩L=∅.
Now I'm checking whether the hypothesis in Proposition 4 actually forces X∩L≠∅X \cap L \neq \emptyset
X∩L=∅ automatically. If X∩L=∅X \cap L = \emptyset
X∩L=∅ but conv⁡X∩L≠∅\operatorname{conv}X \cap L \neq \emptyset
convX∩L=∅, that's geometrically possible — imagine LL
L as a supporting hyperplane of the convex hull that touches it but misses XX
X entirely, like when XX
X consists of two points and LL
L is a line containing the segment between them but positioned so it doesn't intersect either point.
But here's the key: if conv⁡X∩L\operatorname{conv}X \cap L
convX∩L is a nonempty compact convex set, its extreme points are also extreme points of the hull, and by Milman's theorem those extreme points must lie in XX
X. So whenever the intersection is compact and nonempty, it contains points from XX
X.
Now I'm wondering whether points in the hull-face that lie outside XX
X can get arbitrarily close to X∩LX \cap L
X∩L. If w′w'
w′ approaches some x0∈X∩Lx_0 \in X \cap L
x0​∈X∩L, then the distance from w′w'
w′ to its projection onto LL
L shrinks to zero, which is what we'd want. But the issue is whether the set (hull⁡∩L)∖X(\operatorname{hull} \cap L) \setminus X
(hull∩L)∖X actually accumulates at X∩LX \cap L
X∩L, or if the defect set could be isolated elsewhere. So if any foot lies on L itself, then δ = 0, which would make the paper's bounds trivial. But that seems to suggest the defect measure breaks down when the supporting hyperplane actually contains points from the convex hull that aren't in X — I need to think through whether this is a genuine issue with the construction or if there's something about how the feet are defined that prevents this. Now I'm checking whether the defect set (hull∩L)\X is relatively open and whether it contains points arbitrarily close to X∩L. Since hull∩L is convex and X∩L is closed, I can trace a segment from a defect point to a point in X∩L and identify the boundary where the defect region meets X∩L — this gives me control over choosing w with small δ for each target point p at height h. So the gap in Proposition 4 is fixable when the intersection is nonempty by selecting a witness with small enough defect through a face-segment argument, but the noncompact case needs separate handling. What's encouraging is that my Hadamard Theorem B proof avoids this issue entirely—the strictness lemma and swallowing mechanism work uniformly across all heights. That's actually a real advantage: when I specialize Theorem B back to Euclidean space, I get a cleaner, shorter proof of Propositions 3–4 without these gaps.
Let me verify that the Euclidean specialization of Theorem B actually recovers both propositions. The Hadamard condition holds, and a defective maximal free horoball corresponds to a supporting hyperplane where the closure of the convex hull intersects the hyperplane but contains points outside XX
X. For Proposition 4, if X∩LX \cap L
X∩L is not convex relative to the full intersection, then there's a point in the convex hull of that intersection that lies outside XX
X, which makes the horoball defective. For Proposition 3, when X∩LX \cap L
X∩L is nonconvex...
Actually, I realize the closure version of the convex hull is the right formulation here. Using the closed hull potentially gives more witnesses for defective hyperplanes, which strengthens the sufficiency direction. And looking at their proof of Theorem 6, they actually produce witnesses in the closed hull anyway, so the closure version is the correct statement and resolves that subtle issue.
Now let me verify the Strictness Lemma holds in the Euclidean case to confirm it patches the paper properly. I'm checking the setup where ww
w is a supporting point in the hyperplane L={x1=0}L = \{x_1 = 0\}
L={x1​=0}, XX
X lies in the half-space {x1≤0}\{x_1 \le 0\}
{x1​≤0}, and ww
w is in the closed convex hull but not in XX
X itself. Moving ww
w in the direction e1e_1
e1​ by distance tt
t should give distance strictly greater than tt
t from XX
X, and I'm verifying this by looking at the foot of the perpendicular and checking the constraint from the bb
b-function.
The key insight is that equality in the distance bound forces xtx_t
xt​ to lie on the hyperplane and align with ww
w, which contradicts w∉Xw \notin X
w∈/X. The same argument works in the Hadamard case using co-ray uniqueness. For the swallow condition, I'm confirming that the distance inequality d(p,wt)2<t2d(p, w_t)^2 < t^2
d(p,wt​)2<t2 holds whenever tt
t exceeds the threshold (T2+h2)/(2h)(T^2 + h^2)/(2h)
(T2+h2)/(2h), which works for all positive heights.
Now I need to verify the Euclidean upgrade: if the cut point rtr_t
rt​ is infinite, then the union of balls along the geodesic γt\gamma_t
γt​ forms the open half-space HtH_t
Ht​ defined by {⟨x−xt∗,vt⟩>0}\{⟨x - x_t^*, v_t⟩ > 0\}
{⟨x−xt∗​,vt​⟩>0}, which is free. I'm checking whether ww
w lies in this half-space by bounding the Busemann function at ww
w and comparing it to the inner product involving wtw_t
wt​.
The calculation shows that ∣⟨w−wt,vt⟩∣≤t|⟨w - w_t, v_t⟩| \le t
∣⟨w−wt​,vt​⟩∣≤t, which gives me bH(w)≤t−d(wt)<0b_H(w) \le t - d(w_t) < 0
bH​(w)≤t−d(wt​)<0, confirming that w∈Htw \in H_t
w∈Ht​. Since HtH_t
Ht​ is a free open half-space, there exists a free horoball containing ww
w, which contradicts the assumption that ww
w belongs to the closed convex hull of XX
X. For the cut point case in the Euclidean setting, the inflation endpoint is the center of a maximal ball, so CX⊂MX‾C_X \subset \overline{M_X}
CX​⊂MX​​. This Euclidean repair is self-contained and rigorous, spanning about a page, and it's actually stronger than the original approach since it also handles the noncompact-face case where X∩L=∅X \cap L = \emptyset
X∩L=∅.
Now I need to check whether this argument is airtight when the contact face is at infinity—if the supremum isn't attained, could the hull still intersect LL
L? The key is that if LL
L supports the closed hull with contact, then hull‾∩L≠∅\overline{\text{hull}} \cap L \neq \emptyset
hull∩L=∅ by definition. If the contact face is nonempty but X∩L=∅X \cap L = \emptyset
X∩L=∅, then any point in the contact face is trapped and not in XX
X, making the set defective and applying Theorem B. This covers the case from Proposition 4.
For the response itself, I should lay out the full setup: the medial axis on complete Riemannian manifolds via multiple minimizing geodesics (with the sphere as a cautionary example for why naive foot-counting fails), reconstructible points, rays and Busemann functions, horoballs, the maximal free horoball Hγ\mathcal{H}_\gamma
Hγ​, the horoball hull X^\widehat{X}
X, and defective horoballs. I'll note that X^=conv⁡‾X\widehat{X} = \overline{\operatorname{conv}} X
X=convX in Euclidean space and that on compact manifolds X^=M\widehat{X} = M
X=M since there are no rays.
A key point is that X^\widehat{X}
X is generally not the geodesic convex hull—the hyperbolic plane gives a two-point example where the horoconvex hull is strictly larger (banana-shaped), and on positively curved spheres the geodesic hull explodes, so the horoball hull is the right invariant object. Then I'll invoke the lemma on cut loci of closed sets being contained in the closure of the multi-geodesic set (from Wolter and Albano, using semiconcavity of distance), followed by the full curvature-free proof of Theorem A, with a corollary showing that compactness implies everything is reconstructible, recovering the paper's earlier remark as a special case.
For Theorem B under Hadamard curvature, I need the Strictness Lemma establishing co-ray rigidity, then upgrade to cut points via Busemann monotonicity and the CAT(0) fact about asymptotic rays having constant difference. Theorem C combines sufficiency and states the conjectural iff condition, along with a partial necessity result: the limit horosphere through the entry point is maximal and the entry point is a trapped witness when entry differs from the foot, though the precise gap remains—I haven't established that p∈Hξ∗p \in \mathcal{H}_{\xi_*}
p∈Hξ∗​​ or handled the w=qw=q
w=q case.
Now examining where each hypothesis fails: uniqueness of asymptotic rays breaks with conjugate points or positive curvature; the Busemann constant-difference property is a CAT(0) fact that fails generally on manifolds where the horoboundary differs from the visual boundary; convexity of balls and segments matters for the necessity direction entry-point argument; and compactness of the visual boundary plus upper semicontinuity of cξc_\xi
cξ​ are needed for the limit horosphere. Notably, Theorem A requires none of these. Simple-connectivity also plays a role—the cylinder example with S1×RS^1 \times \mathbb{R}
S1×R shows how a closed geodesic circle can make the maximal set empty.
For the cylinder, I'm checking whether points (θ,y)(θ, y)
(θ,y) with y≠0y ≠ 0
y=0 have unique feet and geodesics: the vertical geodesic to (θ,0)(θ, 0)
(θ,0) has distance ∣y∣|y|
∣y∣, and any other path to the circle is longer, so MXM_X
MX​ is indeed empty and nothing reconstructs. The asymptotic rays are just the vertical ones, with Busemann function bup(θ,y)=−yb_{up}(θ,y) = -y
bup​(θ,y)=−y, and the infimum on XX
X is zero, making the free horoballs {y>0}\{y > 0\}
{y>0} which are XX
X-free.
For the paraboloid with vertex as XX
X: the vertex is a pole so MX=∅M_X = ∅
MX​=∅ and reconstructible is empty; the rays are upward meridians, and every non-vertex point lies in a free horoball of its own meridian ray, with the Busemann function along that ray through the point determining the horoball structure. So the free horoball around qq
q correctly avoids the vertex since the Busemann function is zero there, not negative. Now I'm noting some key weaknesses in the original paper that are worth highlighting: the epsilon-pinning in Proposition 3 is actually critical—the naive approach of letting directions go to infinity doesn't work without it, and there's a counterexample showing this; there are also gaps in Proposition 4's treatment of small heights, a necessity argument missing from Theorem 6 about tangential entry, and confusion between convex and closed-convex sets, but the horoball approach ends up patching all of these issues.
For the writeup itself, I should frame this as how the generalization exercise feeds corrections back into the Euclidean case—that's exactly what he'll appreciate. I'll skip the medial axis and stability sections since they're outside the scope here. Given the depth and length of this mathematical content, I should write it in chat with proper LaTeX formatting rather than as a separate file, keeping it readable and allowing for iteration. I should verify the key technical points carefully and be explicit about what's actually proved versus what remains open. The necessity direction in particular needs to be flagged as unresolved. Let me double-check the Busemann function construction: the difference d(y,γ(t))−td(y,\gamma(t)) - t
d(y,γ(t))−t is indeed nonincreasing by the triangle inequality and bounded below, so the limit exists and gives a 1-Lipschitz function on any complete manifold.
For Theorem A with r=∞r=\infty
r=∞, I need to confirm γ\gamma
γ is a ray. The key is showing each segment γ∣[0,t]\gamma|_{[0,t]}
γ∣[0,t]​ minimizes distance between its endpoints. I've established that d(γ(t),X)=td(\gamma(t), X) = t
d(γ(t),X)=t and d(γ(t),xp)≤td(\gamma(t), x_p) \le t
d(γ(t),xp​)≤t, which forces equality, so the segment from γ(0)=xp\gamma(0) = x_p
γ(0)=xp​ to γ(t)\gamma(t)
γ(t) is indeed minimizing—that gives us the ray property. No curvature assumptions are needed for this part.
For the finite radius case, the cut point c=γ(r)c = \gamma(r)
c=γ(r) satisfies d(c)=rd(c) = r
d(c)=r by continuity. To verify rr
r is the cut time along the normal geodesic from foot xpx_p
xp​: when t>rt > r
t>r, the ball B(γ(t),t)B(\gamma(t), t)
B(γ(t),t) intersects XX
X, so there's a shorter path to XX
X than following γ\gamma
γ for length tt
t, meaning the geodesic segment doesn't realize the distance function. But for t<rt < r
t<r, it does minimize. This characterizes rr
r as the cut time.
Albano's theorem tells us the cut locus sits in the closure of the singular set of d(⋅,X)d(\cdot, X)
d(⋅,X)—the multi-geodesic points. I should verify whether cut points can be focal/conjugate-type points with unique minimizing geodesics: the circle's center is a cut point with infinitely many minimizers, while the parabola's evolute cusp has a unique foot and unique geodesic, yet the cut point lies in the closure of the medial axis rather than in its interior.
So the key statement is that Cut(X)⊂MX‾\mathrm{Cut}(X) \subset \overline{M_X}
Cut(X)⊂MX​​ where MXM_X
MX​ is the nondifferentiability set of the distance function. This is known for Euclidean closed sets via Fremlin, and Albano's 2015 paper proves it for closed subsets of Riemannian manifolds, showing the cut locus equals the closure of points where distance fails to be differentiable.
Now I need to work through the strictness of Theorem B using a concatenation argument — suppose I have a point wtw_t
wt​ at distance tt
t from the origin with foot xtx_t
xt​, and a minimizing geodesic segment connecting them.  Since xtx_t
xt​ lies in XX
X, we have b(xt)≥0b(x_t) \ge 0
b(xt​)≥0, but the Lipschitz constraint on bb
b combined with b(wt)=−tb(w_t) = -t
b(wt​)=−t forces b(xt)=0b(x_t) = 0
b(xt​)=0. This means bb
b decreases by exactly tt
t along a length-tt
t segment, so bb
b must drop linearly along the entire geodesic. I'm constructing a path by concatenating the ray τ\tau
τ from xtx_t
xt​ to wtw_t
wt​ (where bb
b decreases from 00
0 to −t-t
−t) with the co-ray from wtw_t
wt​ (where bb
b continues dropping at unit rate), creating a unit-speed geodesic ray PP
P with b(P(s))=−sb(P(s)) = -s
b(P(s))=−s throughout. To verify it's geodesic, I'm checking that the distance between any two points on the path equals the arc length between them, which follows from the Lipschitz bound on bb
b and the path length constraint. , that's xtx_t
xt​ — so both geodesics pass through the same point with the same velocity, which by ODE uniqueness means they're the same geodesic wherever both are defined.
Now for the Busemann functions: since bσwb_{\sigma_w}
bσw​​ and bγb_\gamma
bγ​ are both Busemann functions of rays asymptotic to ξ\xi
ξ, they differ by a constant in CAT(0) spaces, and that constant is pinned down by evaluating at ww
w where both vanish. So I can reconstruct pp
p as being in some ball around a point in MXM_X
MX​ near ctc_t
ct​. Now I need to verify the constant-difference property for Busemann functions—I'm pretty confident this is in Bridson-Haefliger around II.8.20, where they establish that asymptotic rays in CAT(0) spaces have Busemann functions differing by a constant, and there's also a direct proof using the convexity of the distance function between the two rays. So for the geodesic [p,q][p,q]
[p,q] where pp
p is in the open ball and qq
q is on the boundary sphere, I need to verify that the interior points stay strictly inside the ball. In Hadamard spaces, distance functions are strictly convex along geodesics not passing through the center, so the distance from aa
a to points along [p,q)[p,q)
[p,q) must be strictly less than d(a)d(a)
d(a) by convexity, which confirms they lie in the interior.
Now I'm identifying where the geodesic first enters the closed set X^\widehat{X}
X—call this point ww
w at parameter s0s_0
s0​. Since qq
q is already in X^\widehat{X}
X, this minimum exists. If s0=1s_0 = 1
s0​=1 then w=qw = q
w=q and we have a degenerate case with a gap, but otherwise ww
w lies strictly between pp
p and qq
q.
Since points before ww
w aren't in X^\widehat{X}
X, each lies in an open free horoball with an associated ideal point on the boundary sphere. The ideal points form a compact sequence, so I can extract a convergent subsequence. Using the fact that normalized horofunctions converge locally uniformly on Hadamard spaces (the visual boundary identification with the cone topology), the upper semicontinuity of the normalized horofunction gives me control over the limiting behavior.
The limit point ξ∗ξ_*
ξ∗​ determines a horofunction cξ∗c_{ξ_*}
cξ∗​​ that equals bξ∗(w)b_{ξ_*}(w)
bξ∗​​(w) on the maximal horosphere. Since ww
w is trapped outside XX
X, the horosphere Hξ∗\mathcal{H}_{ξ_*}
Hξ∗​​ is defective, which by Theorem B means it's entirely reconstructible—but I still need to verify that pp
p actually lies in Hξ∗\mathcal{H}_{ξ_*}
Hξ∗​​, and the convexity bounds from the sequence are pointing the wrong direction. Let me reconsider whether there's another angle here. jecture: the reconstructible set should equal the complement of XX
X union all the defective horoballs. I've shown the inclusion one direction through Theorems A and B, but the reverse inclusion remains open—even in Euclidean space there's technically a gap in the literature, though Theorem 6 essentially settles it for Rn\mathbb{R}^n
Rn. Now I'm checking whether Theorem 6 actually establishes what I need: it's phrased at the set level, saying XcX^c
Xc is reconstructible iff it's contained in the union, but I should verify the pointwise argument holds. Checking the sphere case: the open unit ball is reconstructible from the center via the medial axis, and points outside the closed ball aren't in the convex hull but are covered by free horoballs (exterior half-spaces) whose union gives back the closed ball, confirming X^=B‾\widehat X = \overline B
X=B.
For compact spaces, there are no rays (finite diameter prevents isometric embeddings of [0,∞)[0,\infty)
[0,∞)), so no free horoballs exist, meaning X^=M\widehat X = M
X=M itself—this aligns with Theorem A that all of XcX^c
Xc is reconstructible.
For complete noncompact spaces, rays always exist (take any point and consider limits of segments toward a divergent sequence), so rayless is equivalent to compact. Now I'm thinking about the medial axis definition more carefully—on Hadamard spaces where geodesics between points are unique, multiple geodesics correspond to multiple feet, so MXM_X
MX​ is exactly the classical feet-based axis; the geodesic-counting refinement only matters beyond Hadamard geometry (like the sphere antipode case). I should also trace where simple-connectedness and curvature actually become essential versus where the formula might hold more broadly—the cylinder and paraboloid checks suggest the formula is fairly robust, though the proof of Theorem B does rely on Hadamard specifically for co-ray uniqueness.
On the cylinder, defective horoballs don't occur so Theorem B becomes vacuous there, which is consistent. The conjecture might plausibly extend to all complete spaces with the same statement, but the two key lemmas are where the obstruction lies. I need to verify the claim in Theorem B that d(wt)≤t+d(w)d(w_t) \le t + d(w)
d(wt​)≤t+d(w)—this is used implicitly for Hopf–Rinow to guarantee bounded feet exist, though I'm working through the exact bound here since ww
w itself isn't in XX
X.
For the "upgrade" nesting, I need d(ct)=rtd(c_t) = r_t
d(ct​)=rt​ and d(wt,ct)=rt−d(wt)d(w_t, c_t) = r_t - d(w_t)
d(wt​,ct​)=rt​−d(wt​), which means parametrizing the geodesic γt\gamma_t
γt​ from the foot xt∗x_t^*
xt∗​ so that ct=γt(rt)c_t = \gamma_t(r_t)
ct​=γt​(rt​) and wt=γt(d(wt))w_t = \gamma_t(d(w_t))
wt​=γt​(d(wt​)) along the minimizing geodesic.
The distance bound d(wt,ct)≤rt−d(wt)d(w_t, c_t) \le r_t - d(w_t)
d(wt​,ct​)≤rt​−d(wt​) holds along the geodesic, and I'm using the triangle inequality to show d(y,ct)≤d(y,wt)+(rt−d(wt))d(y, c_t) \le d(y, w_t) + (r_t - d(w_t))
d(y,ct​)≤d(y,wt​)+(rt​−d(wt​)) for the nesting condition. The key is that d(ct)=rtd(c_t) = r_t
d(ct​)=rt​ follows from the same interval and limit argument as in Theorem A, with freeness propagating down through the parameter via the triangle-inequality argument.
Now I'm checking that the same normalization applies here: balls of radius equal to the parameter, centered along a unit-speed geodesic from a basepoint. The argument only needed d(γ(t),γ(t0))=t0−td(\gamma(t), \gamma(t_0)) = t_0 - t
d(γ(t),γ(t0​))=t0​−t, which holds in both cases. For the freeness at small tt
t, I need to verify that d(γt(s))≥sd(\gamma_t(s)) \ge s
d(γt​(s))≥s near 0, which follows because for s≤d(wt)s \le d(w_t)
s≤d(wt​), the foot of the geodesic gives us the distance bound we need.
Then I'm confirming that rt≥d(wt)>tr_t \ge d(w_t) > t
rt​≥d(wt​)>t, so everything stays consistent. For the final piece, I need ct∈MX‾c_t \in \overline{M_X}
ct​∈MX​​ to correspond to an actual point in MXM_X
MX​, and by openness of the ball B(ct,d(ct))B(c_t, d(c_t))
B(ct​,d(ct​)) plus continuity of the distance function, I can find a nearby point in MXM_X
MX​ that works—this is the paper's Lemma 1 argument applied directly.
Now I'm checking how the Euclidean case specializes: Theorem B applied to Rn\mathbb{R}^n
Rn should re-derive Propositions 3 and 4 in about half a page, handling the h≤δh \le \delta
h≤δ and X∩L=∅X \cap L = \emptyset
X∩L=∅ cases by replacing the foot-drift estimates. I also need to update Theorem 6's statement to use conv⁡‾X\overline{\operatorname{conv}}X
convX, and for the necessity direction I should add the tangential-entry fix—either by induction on dimension within the supporting hyperplane or by perturbing the point q∈m(a)q \in m(a)
q∈m(a).
Let me verify the claimed counterexample to the naive statement: if cn∈CXc_n \in C_X
cn​∈CX​ with ∥cn∥→∞\|c_n\| \to \infty
∥cn​∥→∞, cn/∥cn∥→ηc_n/\|c_n\| \to \eta
cn​/∥cn​∥→η, and p∈L+p \in L^+
p∈L+, does d(cn)≤∥p−cn∥d(c_n) \le \|p - c_n\|
d(cn​)≤∥p−cn​∥ hold infinitely often? The key issue is that the implication "∥cn∥→∞\|c_n\| \to \infty
∥cn​∥→∞ and direction converges ⇒\Rightarrow
⇒ eventually ∥p−cn∥<d(cn)\|p - c_n\| < d(c_n)
∥p−cn​∥<d(cn​) for all p∈L+p \in L^+
p∈L+" is actually false as stated, because d(cn)d(c_n)
d(cn​) doesn't necessarily grow at the same rate as the height of cnc_n
cn​ above the boundary. So d(cn)≥Hnd(c_n) \ge H_n
d(cn​)≥Hn​ since XX
X is contained in the lower half-space. Now for the distance ∥p−cn∥\|p - c_n\|
∥p−cn​∥ where pp
p is at height hh
h with transverse offset PP
P: this decomposes as (Hn−h)2(H_n - h)^2
(Hn​−h)2 plus the squared transverse gap. The constraint ∥p−cn∥<d(cn)\|p - c_n\| < d(c_n)
∥p−cn​∥<d(cn​) is tight because d(cn)d(c_n)
d(cn​) is also bounded above by the distance to nearby points in XX
X at similar transverse positions, giving roughly Hn2+(transverse gap)2\sqrt{H_n^2 + (\text{transverse gap})^2}
Hn2​+(transverse gap)2​.
For the failure case, I need d(cn)2<(Hn−h)2+∥Tn−P∥2d(c_n)^2 < (H_n - h)^2 + \|T_n - P\|^2
d(cn​)2<(Hn​−h)2+∥Tn​−P∥2. With d(cn)≥Hnd(c_n) \ge H_n
d(cn​)≥Hn​, this requires the transverse offset to dominate: ∥Tn−P∥2>2hHn−h2\|T_n - P\|^2 > 2hH_n - h^2
∥Tn​−P∥2>2hHn​−h2. Since Tn∼n0.9T_n \sim n^{0.9}
Tn​∼n0.9 and Hn∼nH_n \sim n
Hn​∼n, we have Tn2=n1.8≫nT_n^2 = n^{1.8} \gg n
Tn2​=n1.8≫n, so this is achievable. And if XX
X reaches up to LL
L directly below cnc_n
cn​ at transverse position TnT_n
Tn​, then d(cn)≈Hnd(c_n) \approx H_n
d(cn​)≈Hn​, making ∥p−cn∥\|p - c_n\|
∥p−cn​∥ strictly larger.
The key insight is that the naive implication fails—their proof's foot-pinning constraint (which bounds TnT_n
Tn​) is what actually saves Proposition 3. For Proposition 4, the feet drift transversally by order 2δt\sqrt{2\delta t}
2δt​, which means the centers' transverse drift scales accordingly.
Now I'm analyzing the swallowing condition more carefully: the center is ct=xt+rtvtc_t = x_t + r_t v_t
ct​=xt​+rt​vt​, and the transverse component of the velocity is bounded by 2δ/t\sqrt{2\delta/t}
2δ/t​, but rtr_t
rt​ grows unboundedly, so the transverse drift rtvt⊥r_t v_t^⊥
rt​vt⊥​ could potentially be huge. However, the swallowing condition ∥p−ct∥<rt\|p - c_t\| < r_t
∥p−ct​∥<rt​ is exactly asking whether pp
p lies inside the ball of radius rtr_t
rt​, which I can analyze via tangency at xtx_t
xt​ using the inner product expansion. x_t⟩ ≥ h − Cδ + o(1), which is positive only when h exceeds Cδ—this aligns with the gap appearing around h ≤ δ. For the inequality to hold, I need the RHS (roughly 2δt) to be bounded by the LHS (2t(h − Cδ)), which requires h > δ + Cδ or so, and that's consistent with what I'm seeing. Let me be careful though: since r_t ≥ t, the LHS is at least 2t(h − Cδ).
So the condition h > (C+1)δ is what's actually needed, and anything at or below that threshold—heights on the order of δ—fails to be established. That confirms the gap.
Now, the user wants me to generalize Theorem 6 to Riemannian manifolds with all the necessary modifications: definitions, statements, proofs, and honest assessment of what's proven versus what remains open. Given his background in Banach spaces and research-level math, I should write this rigorously and tersely without oversimplifying. The output will likely run 1500–2200 words.
For presentation: I'll use minimal headers, keep proofs in prose style with displayed equations where needed, and use itemization sparingly—only when the structure genuinely demands it. A short bulleted list for where Hadamard geometry enters is cleaner than prose. I'll write this as a direct continuation of our discussion, and skip offering to create files unless he asks. I need to verify whether horoconvex hulls and their connection to medial-axis reconstruction are actually novel or already established in the literature — Innami's work on reconstruction and Cheeger–Gromoll convexity at infinity seem relevant, but I can't search to confirm. The honest move is to flag that horoconvexity itself is studied in Hadamard geometry, so the novelty claim hinges on whether the medial-axis connection is genuinely new, which I should state clearly rather than overstate.
For Theorem A, the dichotomy is clean: every point in the complement is either reconstructible or lies in an open free horoball whose horosphere passes through its foot, with the Busemann function level exactly zero at that foot — this recovers Corollary 5 in Euclidean space and gives a nice unified formulation. I should also note that while horoballs are convex (since the Busemann function is convex), their complements are not, which highlights an interesting structural difference between the horoconvex hull and the standard convex hull on Hadamard spaces.
Now I'm realizing that X^\widehat X
X is defined as the intersection of complements of horoballs — complements of convex sets — so X^\widehat X
X itself need not be convex. In Euclidean space this works out because half-space complements are half-spaces, but in hyperbolic geometry like H2\mathbb{H}^2
H2, the picture is more subtle. For two points, X^\widehat X
X becomes the region bounded by horocycle arcs, which bulges outward relative to the geodesic segment connecting them — it's like a lens or banana shape that contains the geodesic but isn't geodesically convex in the usual sense.
The key insight is that X^\widehat X
X strictly contains the geodesic convex hull of the two points, which means the geodesic segment itself isn't reconstruction-saturating. I'm trying to figure out what the actual reconstructible set is for two points in H2\mathbb{H}^2
H2 — it should be related to the perpendicular bisector geodesic and the union of balls centered at points along that bisector.
As I move along the bisector toward infinity in both directions, these balls approach horoballs at the ideal endpoints. The reconstructible set should be the complement of two maximal horoball families, and I'm checking whether the banana's boundary arcs (which consist of horocycle segments) actually touch the horospheres that define the trapped points. So for those two special ideal points where the horosphere contains the entire arc, the trapped points form a non-empty set excluding the endpoints, making them defective — but this means the open horoballs below those two arcs are fully reconstructible. The reconstructible region turns out to be the banana plus those two horoballs minus X, which is equivalent to the complement of all the other maximal free horoballs. Let me verify this against direct computation: points far out near the bisector's ideal endpoint should be reconstructible since the balls centered there grow large enough to contain them.
Now I'm checking whether points beyond the defective horocycle arcs — specifically inside the two defective horoballs — are indeed reconstructible by the theorem, and whether the union of the banana and these two horoballs equals the complement of the non-defective free horoballs. For the two-point case, every other maximal free horoball touches X at exactly one of the two points, since a horosphere through one point that doesn't contain the other also shouldn't intersect the banana's boundary. I need to examine whether a horosphere through one point at a generic ideal point actually intersects the banana minus X.
Since the two points form corners of the banana where the arcs meet, a horosphere through a corner point must avoid the other point, which constrains the ideal points to an arc on the boundary at infinity. The key question is whether such a horocycle through the corner dips into the banana's wedge interior — if it does, those crossing points would be trapped simultaneously in the banana, on the horosphere, and outside X, making them defective and expanding the reconstructible region beyond what the naive picture suggests.
For the writeup, I'll present the two-point example in ℍ² compactly: the reconstructible set is the horocyclic lens formed by the two horocycles through both points, which are defective, so their horoballs are reconstructible — this aligns with direct computation via the bisector. I'll keep it to three sentences and assert only the sufficiency direction without claiming an equivalence for the example.
Now I need to verify the claim that in ℝⁿ, the reconstructible set equals the closed convex hull of X, which should follow from the fact that the reconstructible set is the complement of the union of open horoballs centered at points in X. antly, when the space is compact there are no rays or horoballs, so the closure of X equals the whole space M. Now I need to structure the writeup: first a brief framing of what's been established and what remains open, then lay out the definitions including the medial axis, Busemann functions, and horoballs with the compactness sanity checks, followed by the cut locus density lemma and finally Theorem A with its curvature-free proof and corollaries.
Then Theorem B under the Hadamard assumption, walking through strictness, the upgrade step, and the swallowing argument. Theorem C combines everything with a conjecture about when the formula holds exactly, plus the partial necessity result and where the gap lies. I should clarify where Hadamard enters the argument and what fails without it, then point to evidence from cylinders and paraboloids that the formula might generalize. Finally, I'll connect back to the Euclidean paper by showing how its three key propositions fit into this framework and how Theorem B's Euclidean specialization gives a cleaner complete proof, before noting the caveats around novelty verification.
Now I need to be careful about the medial axis definition and how it relates to the distance function's non-differentiability set via semiconcavity—that's the core identification that makes the lemma work. I'm also setting up the standard definitions for rays and Busemann functions, which will be essential for the later arguments.
For any ray γ on a complete manifold, the Busemann function exists as a monotone limit and is 1-Lipschitz. I define the critical value cγc_γ
cγ​ as the infimum of the Busemann function over X, and when this is finite, the maximal free horoball Hγ\mathcal H_γ
Hγ​ is the set where the Busemann function stays strictly below this critical value. If cγ=−∞c_γ = -∞
cγ​=−∞, there's no free horoball for that ray. The closure X^\widehat X
X is then the complement of all these free horoballs—the set where every Busemann function meets or exceeds its critical value. A maximal free horoball becomes defective when its boundary (where the Busemann function equals the critical value) intersects X^\widehat X
X outside of X itself.
Now I'm looking at a key lemma about the distance function to X: on the complement of X, this function is locally semiconcave and fails to be differentiable precisely at the cut locus of X, which sits inside the closure of the medial axis. This gives me the foundation for the main theorem—that every point in X^\widehat X
X outside X is either reconstructible from X, or it lies in an X-free horoball whose horosphere passes through one of its feet, creating a dichotomy. For compact manifolds, this leads to a corollary.
For Hadamard spaces, I'm proving that when a maximal free horoball is defective, every point in it becomes reconstructible. The argument normalizes the setup, picks a trapped point, and constructs a co-ray; then uses C¹-Busemann gradient-flow uniqueness to establish strictness, shows that normal-geodesic inflation from any foot terminates (which would contradict the point being trapped otherwise), and identifies cut points whose balls contain the trapped point's ball, with these cut points lying in the closure of the medial axis by an earlier lemma. For the necessity direction, I need to establish that the visual boundary is compact, identify horofunctions properly, verify upper semicontinuity of the cost function, and use convexity of balls—this should be stated as a proposition with a proof sketch and flagged gaps. Then examining where each hypothesis actually matters: completeness is essential throughout (Hopf–Rinow for feet, geodesic extension), while the Hadamard condition in Theorem B specifically enables C¹ Busemann functions and unique asymptotes for strictness, plus the constant difference property of asymptotic Busemann functions. I'm questioning whether convexity of horoballs was actually needed anywhere, and noting that strictness relies on C¹ regularity and unit gradient norm—though in general complete manifolds Busemann functions are only Lipschitz, with local semiconcavity in some cases. In Hadamard spaces, the uniqueness follows from the gradient structure of the Busemann function. For the necessity direction, I need ball convexity and boundary identification. Beyond Hadamard, the cylinder and paraboloid examples verify the formula directly, and since Theorem A already handles both cases with empty defect, the full equivalence holds by inspection.
For the findings section, I'll list three numbered results and note that Theorem B restricted to Euclidean space supersedes the earlier propositions. On Proposition 3 specifically, the paper's proof does execute the ε-pinning argument correctly, so the proof itself is sound—the actual issue is only in their final claim about arbitrary sequences with diverging norms, which as stated doesn't hold.
Now I'm checking whether their conclusion becomes true when restricted to their specific pinned sequences. With the foot pinned near the reference point, the transverse component of their sequence is bounded by the pinned foot's distance plus a remainder term involving the velocity's perpendicular part. Since the velocity scales like O(1/t) and the remainder coefficient r_n grows at least as fast as t_n (possibly much faster), the transverse component behaves roughly like r_n/t_n, which I need to evaluate more carefully depending on how r_n compares to t_n.
I'm now testing whether this actually works by checking the specific case where r_n = t_n². Here the transverse component grows like t_n while the height grows like t_n², so their ratio shrinks to zero and the direction converges to the expected limit. For the swallowing condition, I need to compare the distance from a point p to the sequence against the distance from the sequence to its tangency foot, which should be exactly r_n by the maximality construction. Now I'm checking whether the radius can grow faster than t_n² while keeping the ball tangent at the pinned point—examining the geometric constraints of a free ball centered near height r_n with transverse displacement T_n, and how its cross-section with the level set L constrains the possible configurations. So the constraint simplifies to needing T_n² to scale like r_n²/t_n², which aligns with T_n ~ r_n/t_n — this suggests the geometry could allow r_n to grow much faster than t_n² initially, but the paper's construction uses a different parametrization where the center is defined as r_{v_t}(x_t)v_t + x_t.
Here r_{v_t}(x_t) is the directional reaching radius determined by the data and direction rather than freely chosen, and the paper establishes two key convergences: the norm ∥c_t∥ diverges to infinity (proven to be at least (t² − tε)/(t+Δ) → ∞), and the direction converges to η through a two-term decomposition where the second term vanishes because x_t stays bounded while ∥c_t∥ grows, leaving the first term to drive the directional convergence.
Now I'm checking their final claim that for any p in the positive orthant and sequences c_n with diverging norm and direction converging to η, we get d(c_n) > ∥p−c_n∥ for large n — but this conclusion requires an additional transversality condition like the squared transverse component being negligible relative to the height, which translates to ∥c_n∥·(1 − ⟨c_n/∥c_n∥, η⟩²) → 0. c_t/∥c_t∥, η⟩ ≥ 1 − C/t − C/r_t − ⟨x_t,η⟩/(...), and since ⟨x_t,η⟩ ∈ [−ε', 0], I get θ² ≲ 1/t + 1/r, which means T² ~ r²/t + r. But this needs to satisfy T² ≪ 2hr, requiring r ≪ ht — yet r_t ≥ t generically, so r_t ≤ ht/C isn't guaranteed, creating a fundamental tension in the pinned-Prop 3 argument.
When r ~ t, I get T² ≲ 2t, but I need T² < 2ht, which only works if h > 1. The issue is that these are dimensionful quantities normalized by the local feature scale d(q, X_L) = 1, so the condition really says the height must exceed this scale. The r²/t term might vanish if ε-pinning is strong enough, but I need to trace back where that term originated from the θ² ≲ 1/t bound.
Now I'm looking at how Λ_t is bounded. It's constructed as Λ_t = (a − x_t) + (1−λ_t)(b − a) where x_t stays in B(a,ε), giving ∥Λ_t∥ ≤ ε + (1−λ_t)∥b−a∥. The question is whether λ_t → 1 as t → ∞, which would force x_t to stay pinned near a. But the real issue is what happens to m(tη + a)—the nearest point on X to the lifted position—for large t. It's not obvious that this stays close to a; it could jump to a different part of X entirely.
Now I'm wrestling with the transverse component of the velocity direction. The perpendicular part of v_t scales like Λ_t^⊥/t, so the transverse displacement T_t is bounded by ε' plus a term involving r_t∥Λ_t∥/t. For the curvature condition T² ≪ 2hr_t to hold, I need (r_t∥Λ_t∥/t)² ≪ hr_t, which forces r_t∥Λ_t∥² = o(t²). Since ∥Λ_t∥ is bounded by a constant, this means r_t must grow slower than t², and the constraint becomes r_t = o(t²)·h/∥Λ_t∥².
But here's the key issue: ∥b − a∥ is fixed—it's the distance between the two feet of the curve—unless λ_t approaches 1, which would make (1−λ_t)∥b−a∥ vanish. For fixed t they're choosing λ_t, and the pinning keeps x_t near a, so Λ_t = λ_ta + (1−λ_t)b − x_t. If (1−λ_t) → 0, then Λ_t → a − lim x_t with ∥Λ_t∥ ≤ ε + o(1). The upper semicontinuity argument suggests the points x_t converge to a when λ_t → 1, and they're using the pinning to push λ_t toward 1.
So yes, I can arrange λ_t → 1 by choosing each λ_t sufficiently close to 1, say λ_t ≥ 1 − 1/t. This gives ∥Λ_t∥ ≤ ε + o(1), which cascades into T_t ≤ ε' + r_t(ε + o(1))/t and T² ≲ r²ε²/t². For this to be much smaller than 2hr, I need r_tε²/t² ≪ h, which means r_t ≲ ht²/ε² eventually. The problem is r_t is the reaching radius and could grow unboundedly—but they did prove r_{v_t}(x_t) < ∞, so at least it's finite.
Now if r_t is very large, the ball B(c_t, r_t) becomes huge. The key observation is that the point p gets swallowed by the ball exactly when p ∈ B(c_n, r_n), which happens when the tangency condition 2r⟨v, p−x⟩ > ∥p−x∥² holds. Since ∥p − x_n∥ ≤ ∥p − a∥ + ε, this distance is bounded by some R_p. Breaking down the inner product ⟨v_n, p − x_n⟩ into a component along η plus a perturbation, I get at least h minus a term proportional to |v−η|R_p, which is at most h minus something of order C...
The left side grows like 2r_n h → ∞, which dominates the bounded R_p² term — this confirms the swallowing works. The crucial insight is that with pinned feet, the distance ∥p − x_n∥ stays bounded, so the tangency-form inequality is what matters, not the center-distance form. This means Proposition 3 with its ε-pinning is actually correct and complete, even though the literal claim about any sequence with direction→η isn't true in general — their specific constructed sequence satisfies the stronger pinned-feet property.
For Proposition 4 with unpinned feet that drift like √(2δt) → ∞, the distance ∥p − x_t∥² grows like 2δt unbounded, and the tangency condition becomes 2r_t(h − Cδ) > 2δt + O(√t), which holds when r_t ≥ t provided h exceeds a certain threshold depending on δ. Now I'm working through the bounds on the normal vector components — checking that the vertical component grows like t while the transverse component stays bounded by the geometry, so the normalized direction v_t stabilizes as t increases. I'm realizing the transverse term ∥w⊥−x⊥∥² contributes positively, which would make ⟨v_t,p−x_t⟩ ≥ h regardless of δ, but the inner product ⟨w⊥−x⊥, P−x⊥⟩ could be negative and dominate, so I need to carefully bound which term wins. The cross-term analysis confirms the threshold is exactly h > δ, not h > (1+C)δ — the RHS grows like 2δt while the LHS needs 2r_t h to exceed it, which requires h > δ when r_t ~ t. Even if r_t were larger, the proven bound still holds at h > δ, so Proposition 4's argument is tight at this boundary.
Now I'm checking whether the witness re-selection strategy works: when X∩L ≠ ∅, we can shrink δ(w') toward zero via the face-segment argument, but when X∩L = ∅, that route fails and we need the horoball proof instead. The remaining question is whether Proposition 4's hypothesis is even satisfiable in the X∩L = ∅ case — we'd need conv(X∩L) ≠ ∅ while X∩L itself is empty, which means the contact face of the hull is nonempty but contains no points from X.
This raises a deeper issue about extreme points of closed convex hulls: for a closed set X, do the extreme points of cl conv X necessarily lie in X? I'm trying to work through whether a noncompact face is required here, and testing this against potential counterexamples like the hyperbola branch xy = 1 with x > 0, where the closure of the convex hull seems to add boundary behavior that complicates the picture. So the closure of the convex hull equals the set where xy ≥ 1 with x > 0, plus some boundary pieces. For closed convex sets, Straszewicz and Klee tell us the closure of the convex hull of extreme points recovers the original set, which works here since compact faces give us the X-points we need. The key insight is that if the convex hull doesn't touch a line L, then any contact face must contain only extreme rays or be affine—no actual extreme points—like with a graph of an exponential decay function where the hull stays strictly above the x-axis.
Now I'm checking whether the closure of that hull actually touches the x-axis: chords connecting the tails of the bell curve at (−N, e^{−N²}) and (N, e^{−N²}) have height e^{−N²} that shrinks to zero as N grows, so the origin does end up in the closure of the hull. This means the closed hull intersects the x-axis, making it defective under my definition, so Theorem B applies and the lower half-plane should be reconstructible from the medial axis. But wait—the exponential graph itself isn't convex since it's bell-shaped with convex tails and a concave middle, which means points below it can have two closest feet on the curve simultaneously.
The paper's Theorem 6 uses the non-closed convex hull instead, and here the x-axis doesn't actually intersect it since all convex combinations of points on the bell curve have positive y-coordinates. This means the x-axis doesn't qualify as a supporting hyperplane under their Definition 4, which requires the hyperplane to intersect the convex hull of the set. So their theorem would exclude the x-axis from the family of supporting hyperplanes and predict that the lower half-plane is not reconstructible—the opposite conclusion from what my approach suggests.
But wait, let me verify this directly: if I take a point p = (0, −Y) far below the origin, the two symmetric tails of the bell curve should give me two equidistant feet, which would place p inside M_X itself and make it reconstructible. That would contradict their Theorem 6. Let me check whether (0, −Y) is actually equidistant to two points on the curve by minimizing the distance function. The only supporting lines that could work are horizontal lines below the origin or tangent lines to the tail of the exponential, but neither qualifies as non-defective under their definition—horizontal lines don't intersect the convex hull at all, and tangent lines touch at isolated points. This means their Theorem 6 fails to capture this reconstructible point, so the necessity direction of their characterization appears to be false.
Wait, but I should reconsider what they're actually claiming. Theorem 6 is a set-level statement: X^c is reconstructible if and only if X^c is contained in the union of the convex hull and all supporting half-spaces. For my bell curve example, X^c might actually be mostly reconstructible even if individual points near the bump aren't—the set-level condition could hold vacuously even when the pointwise reconstruction fails, since their theorem is phrased in terms of set containment rather than pointwise coverage.
But now I'm seeing a potential issue with their proof. They seem to argue pointwise in the second paragraph ("every reconstructible p not in the convex hull must be..."), which would actually prove a pointwise version—and that's exactly what my counterexample contradicts. Let me verify my example once more: p is reconstructible (it's in M_X and lies in some ball around itself), p is outside the convex hull (below the y-axis), so if their pointwise argument is correct, this shouldn't be possible.
Now I need to check whether p lies in any defective supporting hyperplane. For a supporting hyperplane L of conv X, I need X ∩ L to be a proper subset of conv X ∩ L, with p on the open side. Looking at tangent lines to the graph: a tangent at some point touches the curve at exactly one location, so X ∩ L is just that single tangency point. The question is whether a tangent line—say at a far-right tail point where x₀ is very large—could touch the convex hull at more than just the tangency point, perhaps intersecting near the left tail or the bump region.
For a tangent line at large x₀ on the right tail of e^{−x₀²}, the line has a small negative slope. Evaluating this line at x = −x₀ gives a value strictly above the graph point e^{−x₀²}, which means the line passes above the left tail and enters the interior of the convex hull. This suggests the tangent line does intersect the hull at multiple locations, not just the tangency point. The bitangent line touching both tails at symmetric points is a supporting line, and the segment between those tangency points lies in the convex hull—making it defective. Since the point below the bitangent line is in the open region beneath it, it belongs to their union.
So my "counterexample" actually doesn't contradict Theorem 6; the bell curve is perfectly consistent with it. The gaps I identified aren't counterexamples but rather proof gaps around tangential entry and the relationship between convexity and closure. The strictly convex exponential example also checks out—no bitangents means nothing reconstructible below the curve, which is consistent. I should correct my anxiety about claiming Theorem 6 false; these are genuine proof gaps to address, not refutations.
Now checking whether the closed convex hull of the bell curve intersects the line y=0: the convex hull's lower boundary consists of the tails plus the bitangent, all with y > 0, so the infimum is 0 but never attained. For any fixed x-coordinate, the convex hull at that abscissa has y bounded away from 0, so points (x, 0) don't lie in the closure of the convex hull either. This means the closed version also excludes the horizontal line, so both versions agree—no spurious defective line appears in either formulation.
For the maximal free horoball pointing downward with horosphere at y=0: since the closed convex hull doesn't intersect y=0, Theorem B says nothing about the lower half-plane {y<0}. However, most of {y<0} is still recoverable through the bitangent-defective horoball, which covers everything below the bitangent line, and the region between y=0 and the bitangent near the bump lies inside the convex hull, so Theorem A captures that part too.
Now I'm consolidating everything into a structured write-up with clear headers rather than walking through the scratch narrative—just the distilled mathematics. I'll keep the opening brief and focus on delivering the final result. I need to finalize the paper with the corrected Prop-3 verdict, wrap up the findings section, and close with a novelty caveat and honest assessment of the construction's weaknesses. I'll keep proofs tight with key inequalities displayed, use inline and display math notation, and include the hyperbolic plane two-point example (3 sentences to show how X^\widehat{X}
X differs from the geodesic hull) plus brief coverage of the cylinder and paraboloid cases. Then I'll audit Prop-3 and Prop-4 before closing.
Now I'm working through the "defective" definition more carefully — comparing my condition (a trapped point on the horosphere within X^∖X\widehat{X} \setminus X
X∖X) against the paper's formulation. In Rn\mathbb{R}^n
Rn terms, mine requires (conv⁡‾X∩L)∖X≠∅(\overline{\operatorname{conv}}X \cap L) \setminus X \neq \emptyset
(convX∩L)∖X=∅ while the paper uses X∩L≠conv⁡X∩LX \cap L \neq \operatorname{conv}X \cap L
X∩L=convX∩L. My condition is stronger (the paper's implies mine), but there's a subtle gap: the closure could add points at the boundary where the convex hull only touches via limit points, creating a witness in the closure but not in the convex hull itself — I need to pin down whether this distinction actually matters for the defective classification.
The key question is whether my Theorem B's sufficiency condition is genuinely weaker than the paper's necessity condition, and if so, whether there exists a configuration where my definition marks something as defective but the paper doesn't, yet the reconstruction still works — which would expose an incompleteness in their Theorem 6.
I'm testing this with a concrete example: a discrete set like points (n, 1/n) whose closure includes limit points on the x-axis. The closure of the convex hull would contain that ray, but the convex hull itself wouldn't intersect the supporting line y=0, so the paper's condition wouldn't even apply. My definition would flag this as defective since there's a ray of potential witnesses, but the reconstruction might still be possible.
Now I'm checking whether the region below these points is actually reconstructible. The medial axis between consecutive lattice-like points extends downward unboundedly along bisector lines, and the distance function grows along them. For any point below with two equidistant nearest points, it's clearly in the medial axis. Even for generic points with a unique nearest point, they'd still lie within balls centered at nearby bisector points, so plausibly the entire lower half-plane is reconstructible—which would contradict what the paper claims in Theorem 6.
But wait, looking at the defective lines more carefully: bitangent lines through pairs of points, especially consecutive ones, have negative slope. The regions below each chord union together to cover everything below the lower convex envelope, which is the entire region {y<0}. So the paper's union of defective L⁺ regions does actually cover the lower half-plane through these chord-lines—no contradiction after all. The distinction between closure and convex hull versions is subtle since other defective lines fill in the gaps, but the closure version is more natural and strictly easier to satisfy.
Now I need to write up the clean result without all the verification dead-ends, locking in the final theorem statements with the definitions for the complete Riemannian manifold, the closed nonempty subset X, and the distance function d.
I'm defining the medial axis M_X as the set of points admitting at least two distinct minimizing geodesics to X, which on manifolds captures the non-differentiability set of the distance function via semiconcavity. The reconstructible set R_X consists of all points lying in balls centered at medial axis points with radius equal to their distance to X.
For a ray γ, I'm introducing the horoball function b_γ as the limit of distance to γ(t) minus t, which is monotone and 1-Lipschitz, with c_γ being its infimum over X. When c_γ is finite, this defines the maximal X-free horoball H_γ and its bounding horosphere S_γ.
The horoball hull X̂ is constructed by removing all X-free open horoballs from the ambient space M, equivalently characterized as points where b_γ ≥ c_γ for all rays γ. In Euclidean space this recovers the closed convex hull, while on compact manifolds it equals M itself. A horosphere is defective when it intersects X̂ outside of X.
The distance function d is locally semiconcave on the complement of X, with singular set equal to the medial axis M_X, which contains the cut locus of X—the endpoints of maximal X-minimizing normal geodesics. Theorem A establishes that every point in X̂ \ X is reconstructible, meaning any non-reconstructible point in the complement must lie in an X-free horoball whose horosphere contains one of its feet, with no curvature assumptions needed. For compact M this implies the reconstructible set equals the entire complement of X. Theorem B adds that on Hadamard manifolds, maximal free and defective horoballs are contained in the reconstructible set.
Now for Theorem C: on Hadamard manifolds, the union of points in X̂ \ X together with all defective horoballs is contained in the reconstructible set. I'm conjecturing this is actually an equality, which would give a clean characterization—the reconstructible set equals exactly these components. This suggests a set-level corollary: the complement of X is fully reconstructible if and only if it's covered by X̂ and the defective horoballs, where the sufficiency direction follows from Theorem C but the necessity direction remains at the conjecture level.
For the partial necessity result, I'm showing that any point in the reconstructible set outside X̂ must witness some defective horoball. Given such a point p and a foot a on the manifold, if w is the first point along the geodesic where we re-enter X̂ and w ≠ q, then there exists an ideal point whose maximal free horoball through w is defective—so w lies in the intersection of X̂ with this horoball but outside X itself.
There are still gaps to address: I haven't shown that p actually lies in the horofunction level set for ξ*, and the case where w = q remains unhandled. I should also cite the relevant literature—Albano, Mantegazza–Mennucci, Wolter for the ancestry of this approach, plus Heintze–Im Hof and Bridson–Haefliger for the Busemann function theory, and Innami and Shiohama–Shioya–Tanaka for general background. For the Euclidean case, I need to describe the tangential and collinear entry scenarios more carefully.
Now I'm drafting the response itself. I'll keep the tone direct and honest, starting with a status summary, then laying out the critical weaknesses of my own argument—the unresolved conjecture status, how much I'm relying on Bridson–Haefliger and Heintze–Im Hof, and whether the literature novelty actually holds up. I'll use markdown headers and bold theorem labels with LaTeX math notation.
