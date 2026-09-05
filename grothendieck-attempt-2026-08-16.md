# A proof attempt for the Grothendieck property of \(\mathcal B(\ell_p)\)

**Date:** 2026-08-16  
**Range:** \(1<p<\infty\), \(p\ne2\)  
**Outcome:** no complete proof and no counterexample. The problem is still
open. This note records positive single-fiber results, a sharp obstruction to
the proposed cut argument, a rigorous conditional counterexample criterion,
and corrections needed in `grothendieck.md`.

Throughout, \(p'=p/(p-1)\), and scalar fields may be real or complex unless a
construction is explicitly presented first over the reals.

## 1. Exact finite-block reduction

Put
\[
  W_p=\left(\bigoplus_{n\ge1}\mathcal B(\ell_p^n)\right)_{\ell_\infty}.
\]

### Proposition 1

The spaces \(W_p\) and \(\mathcal B(\ell_p)\) are complementably bi-embeddable,
with contractive embeddings and projections. Consequently,
\[
  \mathcal B(\ell_p)\text{ is Grothendieck}
  \quad\Longleftrightarrow\quad
  W_p\text{ is Grothendieck}.
\]

### Proof

Partition \(\mathbb N\) into finite sets \(I_n\), \(|I_n|=n\). The block-diagonal
map
\[
  (T_n)_n\longmapsto \bigoplus_nT_n
\]
is an isometry from \(W_p\) into \(\mathcal B(\ell_p)\). Its range is the image
of the contractive projection
\[
  T\longmapsto\sum_nP_{I_n}TP_{I_n}.
\]
Indeed, for \(x\in\ell_p\),
\[
 \sum_n\|P_{I_n}TP_{I_n}x\|_p^p
 \le \|T\|^p\sum_n\|P_{I_n}x\|_p^p.
\]

Conversely, let \(P_n\) be the projection onto the first \(n\) coordinates and
define
\[
  J(T)=(P_nTP_n)_n\in W_p.
\]
Then \(J\) is an isometry. Fix a free ultrafilter \(\mathcal U\). If
\((A_n)\in W_p\), extend each \(A_n\) by zero to \(\ell_p\), and set
\[
 L((A_n))x=\mathrm{weak}\!\!\lim_{\mathcal U}A_nx.
\]
Reflexivity of \(\ell_p\) makes this well-defined, linear, and contractive. Since
\(P_nTP_nx\to Tx\) for every \(x\), \(LJ=I\). Thus \(JL\) is a contractive
projection of \(W_p\) onto \(J(\mathcal B(\ell_p))\). The Grothendieck property
passes to complemented subspaces, proving the equivalence. \(\square\)

Taking adjoints gives an isometry
\(\mathcal B(\ell_p)\cong\mathcal B(\ell_{p'})\). Hence it is enough in all
geometric arguments to treat \(p>2\); the case \(p<2\) follows by transposition.

## 2. What must be ruled out

A weak-star null sequence in \(W_p^*\) which is not weakly null has, by
Rosenthal's dichotomy, either

1. a subsequence equivalent to the \(\ell_1\) basis; or
2. a weakly Cauchy subsequence which has no weak limit in the relevant singular
   part.

Thus excluding weak-star null \(\ell_1\)-sequences is only the first half of the
problem. The second, or **ghost/WSC half**, cannot be omitted.

## 3. A general single-ultrafilter lemma

Let \((E_n)\) be arbitrary Banach spaces,
\(W=(\bigoplus_nE_n)_{\ell_\infty}\), and let \(\mathcal U\) be a free
ultrafilter on \(\mathbb N\). For bounded families \(f_{i,n}\in E_n^*\), define
\[
  \rho_i(x)=\lim_{\mathcal U}f_{i,n}(x_n),\qquad x=(x_n)\in W.
\]

### Proposition 2

If, for some \(c>0\),
\[
  \left\|\sum_i a_i\rho_i\right\|
  \ge c\sum_i|a_i|
\]
for all finitely supported scalar families \((a_i)\), then \((\rho_i)\) is not
weak-star null. No geometry of the spaces \(E_n\) is required.

### Proof

For each \(m\), the evaluation map
\[
  R_m:W\longrightarrow\ell_\infty^m,qquad
  R_mx=(\rho_1(x),\ldots,\rho_m(x))
\]
has adjoint bounded below by \(c\). By finite-dimensional polarity, choose
\(x^{(m)}\in B_W\) such that
\[
  \operatorname{Re}\rho_i(x^{(m)})\ge c/2\qquad(i\le m).
\]
There is \(A_m\in\mathcal U\) on which all the corresponding coordinate
inequalities hold with \(c/3\) in place of \(c/2\). Replacing \(A_m\) by finite
intersections, choose \(k(n)\to_{\mathcal U}\infty\) with \(n\in A_{k(n)}\), and
put \(x_n=x_n^{(k(n))}\). Then
\[
  \operatorname{Re}\rho_i(x)\ge c/3
\]
for every fixed \(i\), contradicting weak-star nullity. \(\square\)

This says that an \(\ell_1\)-obstruction cannot live inside one canonical
ultrafilter fiber. Section 10 proves the stronger fact that *no* canonical
weak-star null sequence in one fiber can be a counterexample, including
sequences represented by diffuse nuclear tensors.

## 4. Rank-one functionals in one operator ultraproduct

There is a stronger result for rank-one functionals. Let \(d_n\ge1\),
\[
 X=(\ell_p^{d_n})_{\mathcal U},
 \qquad
 A=(\mathcal B(\ell_p^{d_n}))_{\mathcal U}.
\]
The algebra \(A\) acts contractively on \(X\). Uniform superreflexivity gives
\[
  X^*=(\ell_{p'}^{d_n})_{\mathcal U}
\]
canonically, and every finite-rank operator on \(X\) belongs to \(A\).

For \(x_k=[x_{k,n}]\in X\) and \(f_k=[f_{k,n}]\in X^*\), set
\[
  \phi_k([T_n])
   =\lim_{\mathcal U}f_{k,n}(T_nx_{k,n})
   =f_k([T_n]x_k).
\]

### Theorem 3 (single-fiber rank-one theorem)

For \(1<p<\infty\), if \((\phi_k)\subset A^*\) is weak-star null on \(A\),
then it is weakly null in \(A^*\).

Equivalently, after pullback along the quotient
\[
 \left(\bigoplus_n\mathcal B(\ell_p^{d_n})\right)_{\ell_\infty}
 \longrightarrow A,
\]
every weak-star null sequence of canonical rank-one functionals from one fixed
ultrafilter is weakly null.

### Proof for \(p\ge2\)

The ultrapower \(X\) is an abstract \(L^p\)-space and has the metric
approximation property. The map
\[
 \iota:N(X)=X^*\widehat\otimes_\pi X\longrightarrow A^*,
 \qquad
 \langle\iota(f\otimes x),S\rangle=f(Sx),
\]
is isometric. To see the nontrivial inequality, norm a nuclear tensor \(u\) by
some \(T\in\mathcal B(X)\). If \((R_\alpha)\) are finite-rank contractions tending
strongly to the identity, then \(TR_\alpha\) is finite rank, hence belongs to
\(A\), and
\[
  \langle TR_\alpha,u\rangle\longrightarrow\langle T,u\rangle.
\]

After rescaling the factors, assume \((x_k)\) and \((f_k)\) are bounded. Pass to
a subsequence with
\[
  x_k\rightharpoonup x\quad\text{in }X,
  \qquad
  f_k\rightharpoonup f\quad\text{in }X^*.
\]
Testing weak-star nullity on rank-one operators \(y\otimes g\in A\) gives
\[
  f(y)g(x)=0\qquad(y\in X,\ g\in X^*).
\]
Therefore \(f=0\) or \(x=0\).

Suppose that \((f_k\otimes x_k)\) is not weakly null in \(N(X)\). For a further
subsequence there are \(T\in\mathcal B(X)\) and \(\varepsilon>0\) such that
\[
  |f_k(Tx_k)|\ge\varepsilon.
\]
Put \(u_k=x_k-x\) and \(h_k=f_k-f\). The cross terms tend to zero and
\(f(Tx)=0\), so, after another subsequence,
\[
  |h_k(Tu_k)|\ge\varepsilon/2.
\]
In particular, \((u_k)\) is a seminormalized weakly null sequence in the
\(L^p\)-space \(X\).

For \(p>2\), the complemented Kadec--Pełczyński dichotomy gives a subsequence
whose closed span is complemented and whose basis is equivalent to the
\(\ell_2\) or \(\ell_p\) basis. For \(p=2\), use the Hilbert-space version. Thus
there are uniformly bounded finite-rank operators \(P_m\) with
\[
  P_mu_j=u_j\qquad(j\le m).
\]
The finite-rank operators \(S_m=TP_m\) belong to \(A\) and are uniformly
bounded. A diagonal choice of coordinate representatives (equivalently,
countable saturation of the metric ultraproduct) produces \(S\in A\) such that
\[
  Su_j=Tu_j\qquad(j\ge1).
\]
Indeed, for each \(m\) choose a large \(\mathcal U\)-set on which a representative
of \(S_m\) satisfies the first \(m\) equations to within \(1/m\), make these sets
nested, and diagonalize.

Now
\[
\begin{aligned}
 f_k(Sx_k)
 &=h_k(Sx)+f(Sx)+h_k(Su_k)+f(Su_k)\\
 &=h_k(Sx)+f(Sx)+h_k(Tu_k)+f(Tu_k).
\end{aligned}
\]
The first and last terms tend to zero, \(f(Sx)=0\) because \(f=0\) or \(x=0\),
and the middle residual stays away from zero. This contradicts weak-star
nullity on the fixed element \(S\in A\). Hence \(f_k\otimes x_k\to0\) weakly in
\(N(X)\), and therefore \(\phi_k\to0\) weakly in \(A^*\). \(\square\)

For \(1<p<2\), transpose the coordinate matrices and apply the result to
\(p'>2\).

### Limitation

The theorem does not cover arbitrary elements of
\((N(\ell_p^{d_n}))_{\mathcal U}\) by its rank-one argument. Those spaces
contain diffuse nuclear mass which is invisible as an operator on \(X\); see
Section 6. Proposition 4 below nevertheless covers every such internal tensor
by a different, general norming-and-diagonalization argument.

## 5. A sharp counterexample to coordinate-cut disjointification

The row/column capacity estimates in `grothendieck.md` are correct, but they do
not imply that an \(\ell_1\)-family can be separated by coordinate rectangles.

Work first over the reals. Take disjoint row and column blocks
\[
  R_n,C_n\cong G_n=(\mathbb F_2)^n,
  \qquad d_n=|G_n|=2^n,
\]
and a free ultrafilter \(\mathcal U\). For \(i\le n\), let
\[
 x_{i,n}=d_n^{-1/p}\big((-1)^{g_i}\big)_{g\in G_n}\in\ell_p(C_n),
 \qquad
 f_{i,n}=d_n^{-1/p'}\big((-1)^{g_i}\big)_{g\in G_n}\in\ell_{p'}(R_n),
\]
and define
\[
  \sigma_i(T)=\lim_{\mathcal U}f_{i,n}(Tx_{i,n}),
  \qquad T\in\mathcal B(\ell_p).
\]

Then:

1. \(\|\sigma_i\|=1\), and \(\sigma_i\) is singular because
   \((x_{i,n})_n\) is a normalized weakly null block sequence.
2. The functionals are off-diagonal: they vanish on every diagonal operator.
3. \((\sigma_i)\) is isometric to the real \(\ell_1\) basis. For prescribed
   signs \(\varepsilon_1,\ldots,\varepsilon_m\), choose \(a_n\in G_n\) with
   \((-1)^{(a_n)_i}=\varepsilon_i\) for \(i\le m\). Blockwise translation
   \(g\mapsto g+a_n\) is an \(\ell_p\)-isometry and simultaneously gives
   \(\sigma_i(T)=\varepsilon_i\) for \(i\le m\).
4. Nevertheless, for every pair of coordinate sets \(R,C\subseteq\mathbb N\),
   writing \(\mathsf Q_{R,C}(T)=P_RTP_C\),
   \[
   \boxed{
   \|\sigma_i\mathsf Q_{R,C}\|
   =\lim_{\mathcal U}
     \left(\frac{|R\cap R_n|}{d_n}\right)^{1/p'}
     \left(\frac{|C\cap C_n|}{d_n}\right)^{1/p}
   }
   \]
   independently of \(i\).

The formula follows by restricting the two constant-modulus character vectors;
the lower bound is attained by assembling their rank-one normers blockwise.

For complex scalars, replace \((\mathbb F_2)^n\) by
\((\mathbb Z/M_n\mathbb Z)^n\), with \(M_n\to\infty\), and use characters.
Translations approximate every prescribed finite list of phases, exactly in the
ultralimit.

This example is deliberately **not** weak-star null: the block identity from
\(C_n\) to \(R_n\) has \(\sigma_i(T)=1\) for all \(i\). Its significance is that
even exact L-orthogonality does not force pairwise or finite coordinate
separation. A viable proof needs a global dichotomy:

- either produce bi-disjoint humps which can be glued; or
- prove that persistent rotated overlap is coherent enough to assemble one
  common detector, contradicting weak-star nullity.

Uniform convexity plus row/column cut inequalities alone cannot provide the
first branch.

## 6. The nuclear-ultraproduct ghost

The identification
\[
  (N(\ell_p^{d_n}))_{\mathcal U}
  \stackrel{?}{=}N((\ell_p^{d_n})_{\mathcal U})
\]
is false. Let
\[
  u_n=d_n^{-1}I_{d_n}.
\]
Trace duality and the diagonal decomposition give
\[
  \|u_n\|_N=1,
  \qquad
  \|u_n\|_{\mathcal B(\ell_p^{d_n})}=d_n^{-1}.
\]
Thus \([u_n]\) is nonzero in the nuclear ultraproduct but induces the zero
operator on \((\ell_p^{d_n})_{\mathcal U}\). The kernel retains diffuse trace
mass and is precisely what the rank-one theorem does not see.

For \(p=2\), Raynaud's theorem identifies ultraproducts of \(S_1^{d_n}\) with
noncommutative \(L^1\)-spaces; hence they are L-embedded and weakly
sequentially complete. For \(p\ne2\), no proof or counterexample was found for
the following intermediate problem:
\[
  \boxed{
  \text{Is }(N(\ell_p^{d_n}))_{\mathcal U}
  \text{ weakly sequentially complete?}}
\]

Lewis--Bu weak sequential completeness of
\(L^p\widehat\otimes_\pi X\), under the relevant hypotheses, controls the genuine
nuclear space on the Banach ultrapower but not the diffuse kernel above.

Even a positive answer for every \(\mathcal U\) would not by itself finish the
main problem. One would still need a disintegration theorem turning a dominated
part of the global singular dual into an \(L^1\)-space of these fibers. Available
Banach \(C(K)\)-module results of Kitover--Orhon assume finite multiplicity and a
Bade-complete projection algebra; the present growing-block corona has neither
feature.

## 7. A summability target that is too strong

One cannot prove the desired weak compactness by showing that every singular
off-diagonal map \(\mathcal B(\ell_p)\to c_0\) is absolutely \(q\)-summing for
some finite \(q\), even if the map is compact.

Let
\[
 \Delta_1(T)=(T_{n+1,n})_n,
 \qquad
 J_1(b)e_n=b_ne_{n+1}.
\]
Then \(\Delta_1J_1=I_{\ell_\infty}\). Partition \(\mathbb N\) into infinite sets
\((A_j)\), choose free ultrafilters \(\mathcal U_j\) with \(A_j\in\mathcal U_j\),
and put
\[
 f_j(b)=\lim_{\mathcal U_j}b_n,
 \qquad
 a_j=\frac1{\log(j+1)}.
\]
Define
\[
  \Theta(T)=(a_jf_j(\Delta_1T))_j\in c_0.
\]
The map \(\Theta\) is compact because \(a_j\to0\), and it annihilates compact
operators because \(\Delta_1(K)\in c_0\) for \(K\in\mathcal K(\ell_p)\).

Set \(x_j=J_1(\mathbf1_{A_j})\). The sequence \((x_j)\) is isometric to the
\(c_0\) basis, so its weak \(q\)-norm is at most one for every finite \(q\), while
\[
  \Theta x_j=a_je_j.
\]
Since \((a_j)\notin\ell_q\) for any finite \(q\), \(\Theta\) is not absolutely
\(q\)-summing for any such \(q\). This rules out blanket cotype/summing
factorizations, but does not threaten the conjecture because \(\Theta\) is
already compact, hence weakly compact.

## 8. Corrections to `grothendieck.md`

The following points should be corrected before building further arguments on
the original summary.

1. The equality
   \((N(\ell_p^{d_n}))_{\mathcal U}=N((\ell_p^{d_n})_{\mathcal U})\) in the
   discussion of condition (B) is false; Section 6 gives a one-line
   counterexample.
2. “Uniformly convex summands \(\Rightarrow\) Grothendieck” is too strong in the
   non-lattice setting. Theorem A in the summary rules out weak-star null
   \(\ell_1\)-sequences, but the summary itself correctly notes elsewhere that
   the weakly-Cauchy ghost half remains open.
3. The blanket claim that rotated/Hadamard families cannot be \(\ell_1\) is
   false. Section 5 gives an isometric \(\ell_1\)-family of diffuse character
   vectors for every \(1<p<\infty\). What saves the conjecture in that example is
   a common detector, not Hausdorff--Young growth.
4. There is no general implication that the singular L-summand of an
   L-embedded bidual is itself L-embedded or weakly sequentially complete. The
   proposed shortcut through that assertion is unavailable.
5. arXiv:math/0505306, *Operator space Grothendieck inequalities for
   noncommutative \(L_p\)-spaces*, is by Quanhua Xu, not Junge--Parcet.

## 9. The remaining frontier

The most credible next target is not a pure coordinate-cut lemma. It is a
**coherence-or-disjointness theorem** for asymptotic \(\ell_1\)-families in
\(W_p^*\):

> Given a normalized weak-star null asymptotic \(\ell_1\)-sequence of singular
> functionals, either extract bi-disjoint row/column humps of uniformly positive
> mass, or show that its persistent rotated overlap lives in a coherent fiber
> from which one fixed operator can be assembled to norm an infinite
> subsequence.

The disjoint branch contradicts weak-star nullity by gluing block normers. The
coherent single-ultrafilter branch is ruled out by Proposition 2, and its
rank-one weak-convergence version is Theorem 3. Proposition 4 below rules out
all canonical internal tensors in that branch. What is missing is the global
passage from arbitrary finitely additive/control-measure mass to one of these
two branches, together with weak sequential completeness of the nuclear
ultraproduct fibers.

This is a sharper endpoint than the one in `grothendieck.md`, but it is still an
open lemma rather than a proof of the theorem.

## 10. Counterexample audit

The question here is whether the conjecture itself might be false. No actual
counterexample was found, but the search gives an exact negative criterion and
a concrete sufficient finite-dimensional target.

### 10.1 Every internal sequence in one fiber is harmless

Let \((E_n)\) be finite-dimensional Banach spaces and fix a free ultrafilter
\(\mathcal U\). Put
\[
 F=(E_n)_{\mathcal U},
 \qquad
 A=(E_n^*)_{\mathcal U},
\]
with the canonical pairing. In the application,
\[
 E_n=N(\ell_p^{d_n}),
 \qquad
 E_n^*=\mathcal B(\ell_p^{d_n}).
\]

### Proposition 4 (separable exact norming)

For every separable subspace \(Y\subseteq F\), restriction maps the unit ball
of \(A\) onto the unit ball of \(Y^*\). Consequently, if \((u_k)\subset F\)
satisfies
\[
 \langle a,u_k\rangle\longrightarrow0\qquad(a\in A),
\]
then \(u_k\rightharpoonup0\) in \(F\).

### Proof

The space \(A\) is 1-norming for \(F\): coordinate normers give
\[
 \|u\|=\sup_{a\in B_A}|\langle a,u\rangle|.
\]
The bipolar theorem therefore makes the restrictions of \(B_A\) weak-star
dense in \(B_{Y^*}\). Let \((y_j)\) be dense in \(B_Y\) and let
\(\lambda\in B_{Y^*}\). For each \(m\), choose \(a^{(m)}\in B_A\) which agrees
with \(\lambda\) to within \(1/m\) on \(y_1,\ldots,y_m\). Choose coordinate
representatives of pointwise norm at most one. Choose nested
\(B_m\in\mathcal U\), with \(B_m\subseteq\{n:n\ge m\}\), on which the first
\(m\) coordinate pairings have error less than \(2/m\). Set
\(k(n)=\max\{m:n\in B_m\}\) (using an arbitrary default if the set is empty)
and splice by taking the \(n\)-th coordinate of \(a^{(k(n))}\). Since
\(k(n)\to_{\mathcal U}\infty\), this produces one \(a\in B_A\) satisfying
\(\langle a,y_j\rangle=\lambda(y_j)\) for every \(j\), hence
\(a|_Y=\lambda\).

For the consequence, take
\(Y=\overline{\operatorname{span}}\{u_k:k\ge1\}\). Every member of \(Y^*\) is
the restriction of one \(a\in A\), so every functional on \(Y\) tends to zero
on \((u_k)\). \(\square\)

The canonical map
\[
 \iota:F\longrightarrow A^*,
 \qquad
 \iota(u)(a)=\langle a,u\rangle,
\]
is an isometry. Weak convergence in \(F\) also implies weak convergence of the
images in \(A^*\), since each member of \(A^{**}\) restricts to a bounded
functional on \(\iota(F)\). Hence no canonical/internal sequence in a fixed
fiber can be weak-star null without being weakly null. This includes normalized
identities, diagonal tensors, permutations, Fourier tensors, random matrices,
and arbitrary diffuse elements of the nuclear ultraproduct. The diffuse kernel
in Section 6 is real, but an internal sequence in that kernel is not by itself a
counterexample.

### 10.2 The surviving external-limit mechanism

The preceding proposition does **not** say that \(F\) is weakly sequentially
complete. This distinction gives the cleanest counterexample criterion.

### Proposition 5 (WSC failure gives a counterexample)

Let
\[
 F=\bigl(N(\ell_p^{d_n})\bigr)_{\mathcal U}.
\]
If \(F\) is not weakly sequentially complete for some dimensions \(d_n\) and
some free \(\mathcal U\), then \(\mathcal B(\ell_p)\) is not Grothendieck.

### Proof

Set
\[
 A=\bigl(\mathcal B(\ell_p^{d_n})\bigr)_{\mathcal U}.
\]
Choose a bounded weakly Cauchy sequence \((s_k)\subset F\) with no weak limit.
For \(a\in A\), define the external pointwise limit
\[
 \sigma(a)=\lim_k\langle a,s_k\rangle.
\]
Then \(\sigma\in A^*\), and
\[
 \tau_k=\iota(s_k)-\sigma
\]
is weak-star null in \(A^*\). It is not weakly null. Otherwise
\(\iota(s_k)\rightharpoonup\sigma\) in \(A^*\); but the norm-closed linear
subspace \(\iota(F)\) is weakly closed, so \(\sigma=\iota(s)\) for some
\(s\in F\). By Hahn--Banach, the weak topology on \(\iota(F)\) is exactly the
one inherited from \(A^*\), so this forces \(s_k\rightharpoonup s\), a
contradiction.

The quotient from the bounded block sum onto \(A\) pulls \((\tau_k)\) back to a
weak-star null, non-weakly-null sequence; Hahn--Banach gives the same weak
topology on the range of the adjoint embedding. The block-complement argument
of Proposition 1 applies verbatim to arbitrary dimensions \((d_n)\), so this
block sum is complemented in \(\mathcal B(\ell_p)\). Hence
\(\mathcal B(\ell_p)\) is not Grothendieck. \(\square\)

Thus a counterexample may still come from one ultrafilter, but it must use an
external weak-Cauchy limit in \(A^*\), not a sequence of internal tensors alone.

### 10.3 A finite-cotype trigger

Write
\[
 Z_p=N(\ell_p)=\ell_{p'}\widehat\otimes_\pi\ell_p.
\]

### Proposition 6 (conditional disproof)

If \(Z_p\) fails finite cotype, then \(\mathcal B(\ell_p)\) is not
Grothendieck.

### Proof

By the Maurey--Pisier theorem, failure of finite cotype is equivalent to the
existence of uniformly isomorphic copies of \(\ell_\infty^m\) in \(Z_p\). The
coordinate compressions
\[
 C_d:Z_p\longrightarrow N(\ell_p^d)
\]
are contractions and converge pointwise in nuclear norm to the identity. On
each finite-dimensional copy this convergence is uniform on its unit ball.
Consequently, there are dimensions \(d_m\), a constant \(C\), and embeddings
\[
 j_m:\ell_\infty^m\longrightarrow N(\ell_p^{d_m})
\]
such that
\[
 \|x\|_\infty\le \|j_mx\|_N\le C\|x\|_\infty
 \qquad(m\ge1).
\]
For a free \(\mathcal U\), the map
\[
 x\longmapsto [j_m(x_1,\ldots,x_m)]_{\mathcal U}
\]
embeds \(\ell_\infty\), and hence \(c_0\), into
\(F=(N(\ell_p^{d_m}))_{\mathcal U}\). Since \(c_0\) is not weakly
sequentially complete, neither is \(F\). Proposition 5 applies. \(\square\)

Equivalently, the adjoints \(j_m^*\) are uniform quotient maps
\[
 \mathcal B(\ell_p^{d_m})\twoheadrightarrow\ell_1^m.
\]
They yield a quotient of the bounded block sum onto
\[
 \left(\bigoplus_m\ell_1^m\right)_{\ell_\infty},
\]
which is non-Grothendieck because it contains a complemented copy of
\(\ell_1\). Explicitly, embed \(a\in\ell_1\) as its coherent truncations
\((P_ma)_m\). A left inverse sends a bounded family of zero-padded vectors in
\(\ell_1^m\) to its weak-star ultralimit in \(\ell_1=c_0^*\). This is the
finite-dimensional form of the same mechanism.

### 10.4 What remains unverified

No proof was found that \(Z_p\) fails finite cotype. For \(p>2\), the tensor
\(\ell_{p'}\widehat\otimes_\pi\ell_p\) has one exponent below 2 and one above
2. The standard theorem giving cotype \(\max(q,r)\) for
\(L_q\widehat\otimes_\pi L_r\) assumes both exponents are at least 2. Known
failures of finite cotype obtained from locally decodable codes concern
threefold tensor products and do not settle this conjugate twofold case.
The tensor \(Z_p\) contains 1-complemented isometric copies of both factors, so
if it has cotype \(q<\infty\), necessarily \(q\ge\max(p,p')\).

Accordingly, Proposition 6 is a rigorous test, not a counterexample. An actual
negative solution would follow from either of the following concrete objects:

1. a bounded weakly Cauchy, nonconvergent sequence in some
   \((N(\ell_p^{d_n}))_{\mathcal U}\); or
2. uniform embeddings \(\ell_\infty^m\hookrightarrow N(\ell_p^{d_m})\),
   equivalently uniform quotient maps
   \(\mathcal B(\ell_p^{d_m})\twoheadrightarrow\ell_1^m\).

The elementary candidates checked in this audit do not provide either object.
Matrix coefficients glue to a partial-permutation detector or factor through a
reflexive row/column space; diagonal and fixed-band constructions factor through
\(\ell_\infty\) or a reflexive \(\ell_r\); normalized traces are detected by the
identity; and translation constructions give isometric \(\ell_1^m\) subspaces
but no verified uniformly bounded projections onto them.

There is also a useful exact obstruction to the character construction from
Section 5. Over the reals, take \(G_n=(\mathbb F_2)^n\), \(d_n=|G_n|\), and
the coordinate characters \(\chi_i\). The contractions
\[
 Q_n:\mathcal B(\ell_p(G_n))\longrightarrow\ell_\infty^n,
 \qquad
 Q_n(T)_i=d_n^{-1}\langle T\chi_i,\chi_i\rangle,
\]
are metric quotient maps. Indeed, for every sign vector \(\varepsilon\), a
translation of \(G_n\) is an \(\ell_p\)-isometry sent by \(Q_n\) to
\(\varepsilon\); convexity gives the whole unit cube. Hence the block map
\[
 Q:\left(\bigoplus_n\mathcal B(\ell_p(G_n))\right)_{\ell_\infty}
   \twoheadrightarrow
   \left(\bigoplus_n\ell_\infty^n\right)_{\ell_\infty}
   \cong\ell_\infty
\]
is a quotient. Every functional built from these selected coordinate-character
coefficients, including arbitrary finitely additive mixtures, lies in the range
of \(Q^*\). A weak-star null sequence in that range is weakly null because
\(\ell_\infty\) is Grothendieck. Thus the character example is a near miss, not
a counterexample. For complex scalars, \((\mathbb Z/4\mathbb Z)^n\) gives the
same conclusion with quotient constant at most \(\sqrt2\), since the convex
hull of the fourth roots of unity contains the disk of radius \(1/\sqrt2\).

## References used in this audit

- M. González and T. Kania, *Grothendieck spaces: the landscape and
  perspectives*, [arXiv:2102.03838](https://arxiv.org/abs/2102.03838).
- A. Arias and J. Farmer, *On the structure of tensor products of \(\ell_p\)
  spaces*, [arXiv:math/9402205](https://arxiv.org/abs/math/9402205).
- M. I. Kadec and A. Pełczyński, *Bases, lacunary sequences and complemented
  subspaces in the spaces \(L_p\)*, Studia Math. 21 (1962), 161--176,
  [DOI:10.4064/sm-21-2-161-176](https://doi.org/10.4064/sm-21-2-161-176).
- S. Heinrich, *Ultraproducts in Banach space theory*, J. Reine Angew. Math.
  313 (1980), 72--104.
- Q. Bu, *Weakly sequential completeness of the projective tensor product
  \(L^p[0,1]\widehat\otimes X\)*, Proc. Amer. Math. Soc. 131 (2003), 381--389,
  [DOI:10.1090/S0002-9939-03-07052-7](https://doi.org/10.1090/S0002-9939-03-07052-7).
- Y. Raynaud, *On ultrapowers of non commutative \(L_p\) spaces*, J. Operator
  Theory 48 (2002), 41--68,
  [journal page](https://jot.theta.ro/jot/archive/2002-048-001/2002-048-001-003.html).
- A. Kitover and M. Orhon, *Weak Sequential Completeness in Banach
  \(C(K)\)-modules of finite multiplicity*,
  [arXiv:1408.0040](https://arxiv.org/abs/1408.0040).
- Q. Xu, *Operator space Grothendieck inequalities for noncommutative
  \(L_p\)-spaces*, [arXiv:math/0505306](https://arxiv.org/abs/math/0505306).
- J. Briët, A. Naor, and O. Regev, *Locally decodable codes and the failure of
  cotype for projective tensor products*,
  [arXiv:1208.0539](https://arxiv.org/abs/1208.0539).
- K. Beanland, T. Kania, and N. J. Laustsen, *The algebras of bounded operators
  on the Tsirelson and Baernstein spaces are not Grothendieck spaces*,
  [arXiv:1707.08399](https://arxiv.org/abs/1707.08399).
