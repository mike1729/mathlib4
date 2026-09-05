# Another attempt: nuclear matrix limits and diagonal modules

Date: 2026-09-05.

This continues
[the preceding attempt](/Users/michal/Workspace/mathlib4/grothendieck-remaining-problems-2026-09-05.md).
The general Grothendieck problem for \(\mathcal B(\ell_p)\), \(1<p<\infty\),
\(p\ne2\), is not solved here. The new positive result is a proof of weak
sequential completeness for every finitely generated diagonal submodule
of the nuclear ultraproduct. A second result shows that annihilating any
prescribed separable family of operator tests leaves all of the local
nuclear geometry available.

The proofs below are mathematical arguments, not Lean formalizations.
No claim of novelty in the literature is made.

Follow-up: the
[next attempt](/Users/michal/Workspace/mathlib4/grothendieck-approximation-obstructions-2026-09-05.md)
constructs a weakly null unit sequence in \(D\) whose average distance
from every finitely generated left diagonal module tends to one.
Thus weak Cauchyness does not supply uniform approximation by the
modules studied here. That note also proves WSC for larger block-row
subspaces and tests the corresponding approximation principle.

## 1. Notation and the exact question

Work over either the real or complex field. Set \(p'=p/(p-1)\), fix a free
ultrafilter \(\mathcal U\) on \(\mathbb N\), and write
\[
 F=(N(\ell_p^n))_{\mathcal U},\qquad
 A=(\mathcal B(\ell_p^n))_{\mathcal U},\qquad
 D=\{[u_n]\in F:\lim_{\mathcal U}\|u_n\|_{\rm op}=0\}.
\]
Here \(N(E)\) has its nuclear norm and represents the projective tensor
product \(E\widehat\otimes_\pi E^*\) in these finite-dimensional cases.
Use the bilinear trace pairing
\[
 \langle[T_n],[u_n]\rangle=\lim_{\mathcal U}\operatorname{tr}(T_nu_n).
\]
It embeds \(F\) isometrically into \(A^*\). The space \(D\) is closed,
being the kernel of the contractive map \(F\to A\) induced by the identity
on matrices.

The previous attempt reduced the WSC part of the problem to the following
question. If \(u_k=[u_{k,n}]\in D\) is bounded and
\[
 \lim_{k\to\infty}\langle T,u_k\rangle
 \quad\hbox{exists for every }T\in A,                         \tag{1}
\]
does there exist \(u\in D\) representing all these limits?
The separable exact norming lemma proved in the earlier notes says that
(1) is precisely weak Cauchyness: every functional on a separable subspace
of \(F\) is the restriction of an element of \(A\).

Let
\[
 \mathscr H=(\ell_\infty^n)_{\mathcal U}.
\]
This is a commutative unital \(C^*\)-algebra in the complex case, and is
isometrically a \(C(K)\) algebra; the real version is \(C(K,\mathbb R)\).
It acts contractively on \(F\) by left and right diagonal multiplication.
For \(a=[a_n]\in\mathscr H\), write
\[
 a\cdot[u_n]=[\operatorname{diag}(a_n)u_n],\qquad
 [u_n]\cdot a=[u_n\operatorname{diag}(a_n)].
\]
These are diagonal multipliers *within* each matrix. They differ from the
outer coordinate cuts in the earlier \(\ell_\infty\)-sum arguments.

## 2. A dimension-independent nuclear estimate

### Lemma 1

If \(v\in N(\ell_p^n)\) and scalar vectors \(c_1,\ldots,c_s\) satisfy
\[
 \sum_{i=1}^s|c_i(t)|^p\le1\quad(1\le t\le n),
\]
then
\[
 \left(\sum_{i=1}^s
       \|\operatorname{diag}(c_i)v\|_N^p\right)^{1/p}
 \le\|v\|_N.                                                \tag{2}
\]
For right multiplication, the corresponding estimate has exponent \(p'\).

**Proof.** Take a nuclear decomposition
\(v=\sum_jx_j\otimes f_j\), where \(x_j\in\ell_p^n\) and
\(f_j\in\ell_{p'}^n\). The triangle inequality in \(\ell_p^s\) gives
\[
\begin{aligned}
 \left(\sum_i\|\operatorname{diag}(c_i)v\|_N^p\right)^{1/p}
 &\le
 \sum_j\|f_j\|_{p'}
       \left(\sum_i\|\operatorname{diag}(c_i)x_j\|_p^p\right)^{1/p}\\
 &\le\sum_j\|f_j\|_{p'}\|x_j\|_p.
\end{aligned}
\]
Take the infimum over decompositions. For right multiplication, apply
the same argument to the dual factors \(f_j\) and use exponent \(p'\).
\(\square\)

Consequently, for arbitrary \(a_1,\ldots,a_s\in\ell_\infty^n\), put
\[
 b(t)=\left(\sum_i|a_i(t)|^p\right)^{1/p}.
\]
Taking \(v=\operatorname{diag}(b)u\) and \(c_i(t)=a_i(t)/b(t)\), with
zero where \(b(t)=0\), yields
\[
 \left(\sum_i\|\operatorname{diag}(a_i)u\|_N^p\right)^{1/p}
 \le\|\operatorname{diag}(b)u\|_N.                          \tag{3}
\]
The constants are independent of both \(n\) and \(s\). Passing to the
ultralimit gives, for all \(u\in F\) and \(a_i\in\mathscr H\),
\[
 \boxed{\left(\sum_i\|a_i\cdot u\|^p\right)^{1/p}
 \le\left\|\left(\sum_i|a_i|^p\right)^{1/p}\cdot u\right\|.}   \tag{4}
\]
Again, right multiplication has the same assertion with \(p'\).

## 3. A positive solution for finitely generated diagonal modules

For \(u\in F\), set
\[
 M_L(u)=\overline{\mathscr H\cdot u}.
\]
The norm closure is taken in \(F\).

### Proposition 2

Every \(M_L(u)\) is a \(p\)-concave Banach lattice with constant one,
and is weakly sequentially complete. Every right cyclic module
\(M_R(u)=\overline{u\cdot\mathscr H}\) has the corresponding properties
with exponent \(p'\).

**Proof.** The cyclic-module lattice structure has positive cone
\(\overline{\{a\cdot u:a\ge0\}}\) and positive quasi-interior point \(u\).
This is Proposition 2.4 of Kitover–Orhon, cited below. In this case the
lattice structure is also visible directly: multiplying rows by phases
preserves the nuclear norm, and a coordinatewise inequality
\(|a|\le|b|\) gives \(\|a\cdot u\|\le\|b\cdot u\|\).
Thus the multiplier seminorm is a lattice seminorm, and its quotient
and completion give this lattice.

On its dense multiplier orbit,
\[
 \left(\sum_i|a_i\cdot u|^p\right)^{1/p}
 =\left(\sum_i|a_i|^p\right)^{1/p}\cdot u.
\]
Estimate (4), followed by norm approximation, proves \(p\)-concavity
for arbitrary finite families of vectors in \(M_L(u)\).

In particular, disjoint positive \(z_1,\ldots,z_s\) satisfy
\[
 \left(\sum_i\|z_i\|^p\right)^{1/p}
 \le\left\|\sum_i z_i\right\|.                              \tag{5}
\]
If there were a sublattice lattice isomorphic to \(c_0\), the images of
its unit vectors would be disjoint positive vectors whose norms are
bounded below, but whose partial sums have uniformly bounded norm.
This contradicts (5). The Banach-lattice WSC criterion, stated as
Theorem 2.18 in Kitover–Orhon, now proves WSC. The right-sided argument
uses the right-sided estimate from Lemma 1. \(\square\)

### Theorem 3

For any finite list \(v_1,\ldots,v_r\in F\), both
\[
 M_L(v_1,\ldots,v_r)
   =\overline{\mathscr H\cdot v_1+\cdots+\mathscr H\cdot v_r}
\]
and
\[
 M_R(v_1,\ldots,v_r)
   =\overline{v_1\cdot\mathscr H+\cdots+v_r\cdot\mathscr H}
\]
are weakly sequentially complete.

**Proof.** The first space is a finitely generated Banach \(C(K)\)-module.
Every cyclic subspace of it is \(M_L(w)\) for some \(w\) in that space,
and Proposition 2 applies to every such \(w\). Kitover–Orhon,
Theorem 3.1, therefore gives WSC. The right-sided proof is identical.
\(\square\)

The quantifier “every cyclic subspace” matters here. The argument checks
all vectors \(w\), not just the original generators. No assumption that the
algebra of diagonal projections is already Bade complete is being made;
the cited theorem does not require that as an additional hypothesis.

### Corollary 4: the matrix limit question has a solution in these modules

Suppose \(u_k\) satisfies (1), and that all \(u_k\) belong to one fixed
module \(M_L(v_1,\ldots,v_r)\), where \(v_j\in D\). Then there exists
\(u\in D\) such that
\[
 \langle T,u\rangle=\lim_k\langle T,u_k\rangle
 \quad(T\in A).                                            \tag{6}
\]
The same holds for a fixed right module.

Indeed, multiplication by a bounded diagonal operator preserves \(D\).
Thus the module is a closed subspace of \(D\). Exact separable norming
turns (1) into weak Cauchyness there, and Theorem 3 provides its weak limit.

For example, the hypothesis holds if
\[
 u_k=\left[\sum_{j=1}^r\operatorname{diag}(a_n^{k,j})v_n^j\right],
 \qquad v_j=[v_n^j]\in D,
\]
with bounded multiplier families in \(n\) for each fixed \(k,j\).
It also allows norm limits of these expressions. There is no bound
on the ranks of \(v_n^j\). In particular, it includes modules generated
by diffuse elements such as \([I_n/n]\).

**What this does not prove.** An arbitrary sequence generates a countably
generated diagonal module, and Theorem 3 does not cover that case.
One cannot infer WSC of the closure of an increasing union of WSC
subspaces: the finite-dimensional coordinate spaces of \(c_0\) illustrate
the failure. Equally, with just scalar multiplication as a \(C(K)\)
action, every finitely generated module in \(c_0\) is finite dimensional.
An additional argument controlling the infinitely many generators is
still needed in the present nuclear setting.

## 4. Finite-dimensional nuclear spaces invisible to finitely many tests

### Lemma 5: a flat vector in the kernel of a linear map

Let \(L:\mathbb R^m\to\mathbb R^q\) have rank \(h<m\). There is
\(a\in\ker L\) with
\[
 \sum_{b=1}^m|a_b|=1,\qquad
 \max_b|a_b|\le\frac1{m-h}.
                                                               \tag{7}
\]

**Proof.** Choose an extreme point \(x\) of
\(\ker L\cap[-1,1]^m\). At least \(m-h\) coordinates of \(x\) have
absolute value one. Otherwise a nonzero vector in \(\ker L\) vanishing
on those coordinates gives small perturbations \(x\pm tw\) still in
the cube, contradicting extremality. Consequently
\(\|x\|_1\ge m-h>0\); put \(a=x/\|x\|_1\). \(\square\)

### Proposition 6

Let \(T^1,\ldots,T^r\in\mathcal B(\ell_p^N)\), and let \(d,m\) be positive
integers with \(dm\le N\) and \(m>2rd^2\). There is a linear isometry
\[
 Q:N(\ell_p^d)\longrightarrow N(\ell_p^N)
\]
such that, for every \(u\in N(\ell_p^d)\),
\[
 \operatorname{tr}(T^jQ(u))=0\quad(1\le j\le r),\qquad
 \|Q(u)\|_{\rm op}\le\frac{\|u\|_N}{m-2rd^2}.                \tag{8}
\]

**Proof.** Divide the first \(dm\) coordinates into \(m\) blocks of size
\(d\), and write \(T^j_{bb}\) for the diagonal block compressions.
The equations
\[
 \sum_{b=1}^m a_bT^j_{bb}=0\quad(1\le j\le r)                \tag{9}
\]
impose at most \(2rd^2\) real linear constraints on real weights \(a_b\).
Apply Lemma 5 to their real and imaginary parts (only real parts in
the real case). Define
\[
 Q(u)=\operatorname{diag}(a_1u,\ldots,a_mu)\oplus0.
\]
The block formula for the nuclear norm is
\[
 \|Q(u)\|_N=\sum_b|a_b|\|u\|_N=\|u\|_N.
\]
For completeness, the upper bound follows from separate block nuclear
decompositions. For the lower bound, choose an operator contraction
norming \(u\), and put its signed copies on the diagonal blocks.
The resulting operator is a contraction and its trace pairing with
\(Q(u)\) is \(\sum_b|a_b|\|u\|_N\).
The operator norm is \(\max_b|a_b|\|u\|_{\rm op}\), giving (8).
Finally, (9) gives the asserted zero trace pairings. \(\square\)

## 5. Countably many tests leave the entire WSC obstruction

For a norm-separable subset \(S\subseteq A\), define
\[
 D\cap S^\perp=\{u\in D:\langle T,u\rangle=0\ \text{for all }T\in S\}.
\]

### Theorem 7

Every separable Banach space finitely representable in \(N(\ell_p)\)
embeds linearly and isometrically into \(D\cap S^\perp\).

**Proof.** Choose a dense sequence \(T^j=[T_n^j]\) in \(S\), and bounded
representatives for each \(T^j\). If necessary repeat elements; the empty
case simply has no test constraints.

For the given space \(Y\), choose increasing finite-dimensional
subspaces \(Y_k\) with dense union, \(0<\varepsilon_k<1\) tending to zero,
and linear maps
\[
 J_k:Y_k\longrightarrow N(\ell_p^{d_k}),\qquad
 (1-\varepsilon_k)\|y\|\le\|J_ky\|_N
 \le(1+\varepsilon_k)\|y\|.                                 \tag{10}
\]
Finite representability followed by finite-coordinate compression in
nuclear norm gives these maps. Enlarge \(d_k\) so that they increase
strictly. Put
\[
 N_k=d_k(2kd_k^2+k),\qquad
 k(n)=\max\{k:N_k\le n\},\qquad
 m(n)=\left\lfloor n/d_{k(n)}\right\rfloor.
\]
Ignore the finitely many indices preceding \(N_1\).
Then \(k(n)\to\infty\) and
\[
 m(n)-2k(n)d_{k(n)}^2\ge k(n).
\]
Apply Proposition 6 in coordinate \(n\), to dimension \(d_{k(n)}\),
the first \(k(n)\) tests \(T_n^j\), and \(m(n)\) blocks, producing \(Q_n\).
For \(y\in\bigcup_kY_k\), eventually set
\[
 V_n(y)=Q_n(J_{k(n)}y);
\]
use zero at the finitely many initial indices where it is undefined.
Then
\[
 \|V_n(y)\|_N\longrightarrow\|y\|,\qquad
 \|V_n(y)\|_{\rm op}
 \le\frac{(1+\varepsilon_{k(n)})\|y\|}{k(n)}
 \longrightarrow0.
\]
For each fixed \(j\), \(\operatorname{tr}(T_n^jV_n(y))=0\) eventually.
Thus \(y\mapsto[V_n(y)]\) is an isometry into \(D\cap S^\perp\).
It is linear in the ultraproduct because each fixed linear relation lies
in \(Y_{k(n)}\) eventually. Extend by continuity to \(Y\); closedness of
the target completes the proof. \(\square\)

Combining Theorem 7 with the prior local-reflexivity reduction yields
\[
 \boxed{D\cap S^\perp\text{ is WSC}
 \iff D\text{ is WSC}
 \iff \mathcal B(\ell_p)^*\text{ is WSC}.}                   \tag{11}
\]
For the nontrivial implication, every separable subspace of
\(N(\ell_p)^{**}=\mathcal B(\ell_p)^*\) is finitely representable in
\(N(\ell_p)\), hence embeds in \(D\cap S^\perp\).
WSC passes to closed subspaces and is separably determined.
The reverse implication uses the closed-subspace inclusions from the
previous attempt.

This is stronger than just producing a nonzero vector undetected by
countably many tests. Such tests leave an annihilator containing every
separable space relevant to the WSC question.

## 6. A false diagonal limit, even for the zero sequence

Here is a direct illustration of the limitation of countable test
matching. Given \(T^1,T^2,\ldots\in A\), apply the scalar-block case of
Proposition 6 with \(d=1\), \(m=n\), and \(r=\lfloor n/4\rfloor\).
For small \(n\), allow zero tests. It gives diagonal \(v_n\) such that
\[
 \|v_n\|_N=1,\qquad \|v_n\|_{\rm op}\le 2/n,\qquad
 \operatorname{tr}(T_n^jv_n)=0\quad(j\le\lfloor n/4\rfloor).
\]
Hence \(v=[v_n]\) is a norm-one element of \(D\), annihilating all the
prescribed tests. Define representatives
\[
 u_{k,n}=
 \begin{cases}
 0,&k\le n,\\
 v_n,&k>n.
 \end{cases}
\]
For every fixed \(k\), \(u_k=[u_{k,n}]=0\) in \(F\). The sequence \(u_k\)
therefore has weak limit zero. But selecting \(k(n)=n+1\) gives
\([u_{k(n),n}]=v\ne0\), which agrees with that limit on every prescribed
test. The diagonal operator consisting of the signs of the diagonal
entries of \(v_n\) has norm one and pairs with \(v_n\) to give one, so
another bounded test detects the error.

This is not a counterexample to WSC: the sequence is identically zero.
It proves that matching a countable family of pairings does not by
itself justify an asserted internal limit. A countable family can norm
a specified separable subspace, but cannot identify an unrestricted
candidate in all of \(D\).

## 7. Outcome and references

The attempt establishes the matrix limit assertion under a fixed finite
diagonal-generation hypothesis (Theorem 3 and Corollary 4). It also
strengthens the earlier kernel obstruction to every separable
annihilator (Theorem 7). The remaining step is to control weakly Cauchy
sequences outside these finitely generated modules, or to construct an
actual weakly Cauchy sequence with no weak limit. Neither has been done.
The separate no-\(c_0\)-quotient condition in the Grothendieck problem
also remains unresolved.

The external theorem used for the positive result is:

- A. Kitover and M. Orhon, *Weak sequential completeness in Banach
  \(C(K)\)-modules of finite multiplicity*,
  [arXiv:1408.0040](https://arxiv.org/abs/1408.0040),
  [full paper](https://arxiv.org/pdf/1408.0040).
  Proposition 2.4, Theorem 2.18, and Theorem 3.1 supply, respectively,
  the cyclic lattice structure, the lattice WSC criterion, and the
  passage from all cyclic subspaces to a finitely generated module.

The original problem and reductions are documented in the preceding
local notes, with sources including:

- M. González and T. Kania, *Grothendieck spaces: the landscape and
  perspectives*, [arXiv:2102.03838](https://arxiv.org/abs/2102.03838).
- S. Heinrich, *Ultraproducts in Banach space theory*, J. Reine Angew.
  Math. 313 (1980), 72–104,
  [paper](https://www.digizeitschriften.de/download/pdf/243919689_0313/log9.pdf).
