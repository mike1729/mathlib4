# Another attempt at the remaining Grothendieck problems

**Date:** 2026-09-05.

**Question:** Is \(\mathcal B(\ell_p)\) Grothendieck for
\(1<p<\infty\), \(p\ne2\)?

**Outcome:** no proof or counterexample to the main question. This attempt
gives an explicit reduction to the corona of one fixed operator ultraproduct,
proves that its invisible nuclear kernel retains all the relevant finite
dimensional geometry, and excludes countable atomic mixtures of internal
functionals as counterexamples. These are arguments developed and checked
within this session, without independent referee or formal verification.

This continues [the first September attempt](grothendieck-attempt-2026-09-05.md)
and [the August attempt](grothendieck-attempt-2026-08-16.md). The results here
do not depend on the proposed uniformly convex sum theorem.

All spaces may be real or complex. Fix \(1<p<\infty\), put
\(p'=p/(p-1)\), and fix an arbitrary free ultrafilter \(\mathcal U\) on
\(\mathbb N\). Write
\[
 Z_p=N(\ell_p),\qquad
 F_{\mathcal U}=(N(\ell_p^n))_{\mathcal U},\qquad
 A_{\mathcal U}=(\mathcal B(\ell_p^n))_{\mathcal U},\qquad
 X_{\mathcal U}=(\ell_p^n)_{\mathcal U}.
\]
The nuclear norm is denoted by \(\|\cdot\|_N\). The canonical trace pairing
embeds \(F_{\mathcal U}\) isometrically in \(A_{\mathcal U}^*\).

## 1. The whole operator problem fits inside one ultraproduct corona

The canonical action identifies \(A_{\mathcal U}\) isometrically with a
closed algebra of operators on \(X_{\mathcal U}\). Isometry follows by
choosing coordinate unit vectors almost attaining each operator norm.
Uniform reflexivity gives
\(X_{\mathcal U}^*=(\ell_{p'}^n)_{\mathcal U}\), so every rank-one operator
on \(X_{\mathcal U}\) is internal. The abstract \(L^p\)-space
\(X_{\mathcal U}\) has the metric approximation property, so finite-rank
operators are norm dense in its compact operators. Thus
\(\mathcal K(X_{\mathcal U})\subseteq A_{\mathcal U}\). Put
\[
 C_{\mathcal U}=A_{\mathcal U}/\mathcal K(X_{\mathcal U}).
\]

### Proposition 1

There are contractions
\[
 J:\mathcal B(\ell_p)\longrightarrow C_{\mathcal U},\qquad
 R:C_{\mathcal U}\longrightarrow\mathcal B(\ell_p),\qquad RJ=I.
\]
In particular, \(J\) is an isometry and its range is 1-complemented.

### Proof

Set \(d_n=m_n=\lfloor\sqrt n\rfloor\). Identify the first \(d_nm_n\)
coordinates of \(\ell_p^n\) with \(m_n\) copies of \(\ell_p^{d_n}\).
Let \(P_d\) be the first-coordinate projection on \(\ell_p\). Define
\[
 \widetilde J(T)_n=
 \operatorname{diag}_{m_n}(P_{d_n}TP_{d_n})\oplus0.
\]
Then \(\widetilde J:\mathcal B(\ell_p)\to A_{\mathcal U}\) is an
isometry. For \(B\in\mathcal B(\ell_p^n)\), write \(B_{jj}\) for its
\(j\)-th diagonal \(d_n\)-block and define
\[
 R_n(B)=\frac1{m_n}\sum_{j=1}^{m_n}B_{jj}.
\]
Each \(R_n\) is contractive. After zero extension to \(\ell_p\), define
\[
 \widetilde R([B_n])x=
 \mathop{\mathrm{weak}\!\lim}_{n\to\mathcal U}R_n(B_n)x.
\]
Reflexivity of \(\ell_p\) makes this a well-defined contraction, and
\(\widetilde R\widetilde J=I\).

It remains to show that \(\widetilde R\) annihilates
\(\mathcal K(X_{\mathcal U})\). If \(B=x\otimes f\) has rank one, split
\(x\) and \(f\) into their \(d_n\)-blocks. Hölder gives
\[
 \|R_n(x\otimes f)\|_N
 \le\frac1{m_n}\sum_{j=1}^{m_n}\|x_j\|_p\|f_j\|_{p'}
 \le\frac{\|x\|_p\|f\|_{p'}}{m_n}.
\]
Every rank-one operator on \(X_{\mathcal U}\) has representatives of this
form with uniformly bounded factors. Consequently its image under
\(\widetilde R\) is zero. The same follows for finite-rank operators and,
by continuity, for compact operators. Therefore \(\widetilde R\) factors
through a contraction \(R\) on \(C_{\mathcal U}\). Take
\(J=q\widetilde J\), where \(q\) is the quotient map. Then \(RJ=I\).
\(\square\)

### Consequence

For this one fixed free ultrafilter,
\[
 \boxed{\mathcal B(\ell_p)\text{ is Grothendieck}
 \iff C_{\mathcal U}\text{ is Grothendieck}.}                 \tag{1}
\]
The same equivalence holds with the property replaced by either

- having no quotient isomorphic to \(c_0\); or
- having a weakly sequentially complete dual.

Indeed, the bounded block sum
\(W_p=(\bigoplus_n\mathcal B(\ell_p^n))_{\ell_\infty}\) is complemented
in \(\mathcal B(\ell_p)\); \(A_{\mathcal U}\), and hence
\(C_{\mathcal U}\), is a quotient of \(W_p\); and Proposition 1 embeds
\(\mathcal B(\ell_p)\) complementably in \(C_{\mathcal U}\). Each of the
three properties passes to quotients and complemented subspaces. For the
dual WSC property, use the adjoint embedding and heredity of WSC to closed
subspaces.

Thus the full problem can occur at one fixed base point, and even among
functionals annihilating all compact operators on \(X_{\mathcal U}\).
The earlier internal-sequence result does not settle this: the full dual
\(C_{\mathcal U}^*\) also contains external functionals.

## 2. Amplification preserves nuclear geometry while erasing operator norm

For positive integers \(d,m\), define
\[
 \mathcal A_{d,m}:N(\ell_p^d)\longrightarrow N(\ell_p^{dm}),
 \qquad
 \mathcal A_{d,m}(u)=\frac1m\operatorname{diag}_m(u).
\]
Then
\[
 \boxed{\|\mathcal A_{d,m}(u)\|_N=\|u\|_N,
 \qquad
 \|\mathcal A_{d,m}(u)\|_{\mathrm{op}}
 =\frac1m\|u\|_{\mathrm{op}}.}                              \tag{2}
\]
The nuclear upper bound follows by placing a nuclear decomposition in each
block. For the lower bound, choose a contraction \(T\) norming \(u\) by
trace duality and pair with \(\operatorname{diag}_m(T)\), also a contraction.
The operator norm equality is the norm formula for block-diagonal operators
on an \(\ell_p\)-sum.

Define the closed subspace
\[
 D_{\mathcal U}=
 \{[u_n]\in F_{\mathcal U}:\lim_{\mathcal U}\|u_n\|_{\mathrm{op}}=0\}.
\]
This is the kernel of the contractive map from the nuclear ultraproduct to
\(A_{\mathcal U}\). It is also exactly
\[
 D_{\mathcal U}=F_{\mathcal U}\cap\mathcal K(X_{\mathcal U})^\perp
 \quad\text{inside }A_{\mathcal U}^*.                         \tag{3}
\]
To check (3), pairing \([u_n]\) with an internal rank-one operator
\([x_n\otimes f_n]\) gives \(\lim_{\mathcal U}f_n(u_nx_n)\). This vanishes
for every such rank-one operator exactly when the induced operator on
\(X_{\mathcal U}\) is zero. Isometry of the canonical operator action
then says precisely that \(\lim_{\mathcal U}\|u_n\|_{\mathrm{op}}=0\).
Consequently \(D_{\mathcal U}\) embeds canonically and isometrically in
\(C_{\mathcal U}^*\).

### Proposition 2

Every separable Banach space finitely representable in \(Z_p=N(\ell_p)\)
embeds isometrically in \(D_{\mathcal U}\).

### Proof

Let \(Y\) be such a space. Choose increasing finite-dimensional
\(Y_k\subseteq Y\) with dense union, numbers \(\varepsilon_k\downarrow0\),
and maps
\[
 T_k:Y_k\longrightarrow N(\ell_p^{d_k}),\qquad
 (1-\varepsilon_k)\|y\|\le\|T_ky\|_N
 \le(1+\varepsilon_k)\|y\|.
\]
These exist because coordinate compressions converge to the identity in
nuclear norm, uniformly on each finite-dimensional subspace of \(Z_p\).
Enlarge the \(d_k\) to make them strictly increasing.

For \(n\ge d_1\), put
\[
 k(n)=\max\{k:kd_k\le n\},\qquad
 m(n)=\left\lfloor\frac n{d_{k(n)}}\right\rfloor.
\]
For \(y\in\bigcup_kY_k\), at all sufficiently large indices define
\[
 V_n(y)=\mathcal A_{d_{k(n)},m(n)}(T_{k(n)}y)\oplus0
 \in N(\ell_p^n).
\]
Use zero at the finitely many initial indices where \(y\notin Y_{k(n)}\).
Equation (2) gives
\[
 \|V_n(y)\|_N=\|T_{k(n)}y\|_N\longrightarrow\|y\|,
 \qquad
 \|V_n(y)\|_{\mathrm{op}}
 \le\frac{(1+\varepsilon_{k(n)})\|y\|}{m(n)}\longrightarrow0,
\]
because \(m(n)\ge k(n)\to\infty\). The map
\(y\mapsto[V_n(y)]\) is linear after taking ultraproduct classes and
extends to the desired isometry into the closed space \(D_{\mathcal U}\).
\(\square\)

### Exact WSC consequence

Combining Proposition 2 with local reflexivity gives
\[
 \boxed{
 D_{\mathcal U}\text{ is WSC}
 \iff F_{\mathcal U}\text{ is WSC}
 \iff\mathcal B(\ell_p)^*\text{ is WSC}.}                    \tag{4}
\]
For the first nontrivial direction, if \(D_{\mathcal U}\) is WSC, every
separable subspace of \(Z_p^{**}\) is WSC: it is finitely representable in
\(Z_p\) by local reflexivity and embeds in \(D_{\mathcal U}\).
WSC is separably determined, so \(Z_p^{**}=\mathcal B(\ell_p)^*\) is WSC.
The converse follows from the closed-subspace embeddings
\(D_{\mathcal U}\subseteq F_{\mathcal U}\subseteq W_p^*
\subseteq\mathcal B(\ell_p)^*\).

In particular, the normalized identities \([I_n/n]\) were not an isolated
pathology. The kernel they illustrate already contains isometric copies of
every separable space relevant to the WSC obstruction. No estimate using
only small operator norms of nuclear representatives can discard this
kernel: amplification preserves their entire nuclear-norm geometry.

## 3. A positive result: countable atomic internal mixtures are harmless

This result applies to arbitrary finite-dimensional Banach spaces \(E_n\),
without assumptions involving \(p\). Put
\[
 W=(\bigoplus_nE_n)_{\ell_\infty},\quad K=\beta\mathbb N.
\]
For \(t\in K\), let \(G_t=(E_n^*)_t\), embedded in \(W^*\) by its
canonical ultrafilter pairing. At a principal ultrafilter, this simply
means \(E_n^*\). For a finite collection of distinct points of \(K\),
disjoint clopen neighborhoods and coordinate normers show that these
embeddings have an isometric \(\ell_1\)-sum:
\[
 Y_{\mathrm{int}}=
 \left(\bigoplus_{t\in K}G_t\right)_{\ell_1}
 \subseteq W^*.
\]
Every element of this sum has countable support, and its central variation is
\[
 \mu_s=\sum_t\|s_t\|\delta_t,
 \qquad\mu_s(A)=\|s\pi_A\|.
\]

### Proposition 3

If \(s_i\in Y_{\mathrm{int}}\) is weak-star null on \(W\), then it is
weakly null. The ultrafilters and the number of nonzero fiber components
may vary with \(i\).

### Proof

First, for any weak-star null sequence in \(W^*\), its central variations
form a relatively weakly compact subset of \(M(K)\). Here is a short proof
of the scalar step. If disjoint sets \(A_j\subseteq\mathbb N\) satisfy
\(\mu_{s_{i_j}}(A_j)>\varepsilon\), choose unit vectors \(x_j\) supported
on \(A_j\) with \(|s_{i_j}(x_j)|>\varepsilon/2\). Pasting these vectors
defines a contraction \(L:\ell_\infty\to W\). The scalar Grothendieck
theorem makes \(L^*s_i\) weakly null. Its atomic restriction
\((s_i(x_j))_j\) is weakly null in \(\ell_1\), hence norm null by Schur,
contradicting the selected diagonal entries. The violating indices can
be chosen increasing since each one positive finite measure has vanishing
mass on a disjoint sequence. The Dieudonné–Grothendieck criterion and
clopen approximation in \(K\) now give the stated relative weak compactness.

Let \(S\subseteq K\) be the countable union of the supports of the
\(s_i\). The measures \(\mu_{s_i}\) belong to the closed subspace
\(\ell_1(S)\subseteq M(K)\). Their relative weak compactness there and the
Schur property imply uniform control of the atomic tails: for every
\(\varepsilon>0\) there is a finite \(F\subseteq S\) such that
\[
 \sup_i\sum_{t\notin F}\|s_{i,t}\|<\varepsilon.               \tag{5}
\]

Fix \(t\in S\). We claim that \(s_{i,t}\) is weak-star null on \(W\).
Choose \(F\) as in (5), including \(t\), and a clopen set separating
\(t\) from \(F\setminus\{t\}\). Its characteristic function is a fixed
coordinate multiplier \(\pi_A\), and
\[
 \|s_i\pi_A-s_{i,t}\|<\varepsilon\quad\text{for every }i.
\]
For fixed \(x\in W\), \(s_i(\pi_Ax)\to0\). Letting
\(\varepsilon\downarrow0\) proves the claim.

For a free \(t\), every bounded functional on a separable subspace of
\(G_t\) is represented by one element of \((E_n)_t\). To recall the proof,
the internal pairing is norming; use finite-dimensional Hahn–Banach
approximation on the first \(k\) members of a dense sequence, and then
diagonalize coordinate representatives along the free ultrafilter. This
produces a single representative agreeing on the dense sequence, hence
everywhere. It follows that a sequence in \(G_t\) which is weak-star null
on \(W\) is weakly null in \(G_t\). For principal \(t\), the assertion is
immediate from finite dimension.

Thus every coordinate sequence \(s_{i,t}\) is weakly null. Finite sums
are weakly null, and (5) approximates \(s_i\) uniformly in norm by these
finite sums. Testing an arbitrary element of \(Y_{\mathrm{int}}^*\)
proves weak nullity in \(Y_{\mathrm{int}}\), and consequently in \(W^*\).
\(\square\)

This rules out arbitrary countable atomic mixtures of canonical nuclear
functionals, not just a sequence from one fixed fiber. It does not rule out
external functionals in an atomic fiber, or nonatomic central variation.

## 4. What this attempt leaves open, in a more concentrated form

Räbiger's characterization, (1), and (4) give
\[
 \boxed{\mathcal B(\ell_p)\text{ is Grothendieck}
 \iff
 \begin{cases}
 D_{\mathcal U}\text{ is weakly sequentially complete},\\
 C_{\mathcal U}\text{ has no quotient isomorphic to }c_0.
 \end{cases}}                                               \tag{6}
\]
Both assertions in (6) remain unproved for \(p\ne2\).

The first can be stated entirely in terms of finite matrices. Suppose
\(u_{k,n}\in N(\ell_p^n)\) satisfy
\[
 \sup_{k,n}\|u_{k,n}\|_N<\infty,
 \qquad \lim_{\mathcal U}\|u_{k,n}\|_{\mathrm{op}}=0
 \quad\text{for every }k,
\]
and, for every bounded family \(T_n\in\mathcal B(\ell_p^n)\), the limit
\[
 \lim_{k\to\infty}\lim_{n\to\mathcal U}
       \operatorname{tr}(T_nu_{k,n})                          \tag{7}
\]
exists. The unresolved assertion is that there is one bounded nuclear
family \(u_n\), with \(\lim_{\mathcal U}\|u_n\|_{\mathrm{op}}=0\), such
that (7) equals \(\lim_{\mathcal U}\operatorname{tr}(T_nu_n)\) for every
bounded operator family \((T_n)\). The separable exact norming lemma makes
the hypothesis exactly weak Cauchyness in \(D_{\mathcal U}\); the requested
representation is its weak limit. Equivalently, the canonical image of
\(D_{\mathcal U}\) must be weak-star sequentially closed in
\(C_{\mathcal U}^*\). A diagonal selection that only handles a countable
list of operator tests does not prove this statement: all bounded operator
families must be handled by the same representative.

There is also a quantitative restriction on any possible counterexample.
For an internal dual pair \(F_{\mathcal U}\subseteq A_{\mathcal U}^*\),
if a weak-star null sequence \(\phi_i\) satisfies
\(\operatorname{dist}(\phi_i,F_{\mathcal U})\to0\), choose approximating
internal \(u_i\) in norm. Then \(u_i\) is weak-star null and hence weakly
null by the separable norming argument above. Thus \(\phi_i\) is weakly
null too. If a weak-star null sequence is not weakly null, first select a
subsequence detected uniformly by one bidual functional. On a further tail
of that subsequence its distance from \(F_{\mathcal U}\) must be bounded
below by a positive constant; otherwise a further subsequence with distance
tending to zero contradicts that detector.

Using Proposition 1, any counterexample for \(\mathcal B(\ell_p)\) can
therefore be transported to \(C_{\mathcal U}^*\subseteq A_{\mathcal U}^*\)
and then pulled back to \(W_p^*\). Its central variations there all have
the form \(\|\phi_i\|\delta_{\mathcal U}\), yet it stays a positive
distance from the internal nuclear fiber after selecting a subsequence.
Indeed, a coordinate cut acts on \(A_{\mathcal U}\) as zero or identity
according to whether the cut belongs to \(\mathcal U\).

The remaining obstruction is therefore not a failure to control a family
of scalar base measures. It is the behavior of external dual functionals
at even a single ultrafilter, with all compact-operator tests removed.

## 5. Literature checked and limits of the attempt

- M. González and T. Kania, *Grothendieck spaces: the landscape and
  perspectives*, [arXiv:2102.03838](https://arxiv.org/abs/2102.03838).
  Problem 28 states the operator question; Theorem 3.1.7 gives the WSC plus
  no-\(c_0\)-quotient characterization used in (6).
- S. Heinrich, *Ultraproducts in Banach space theory*, J. Reine Angew. Math.
  313 (1980), 72–104,
  [paper](https://www.digizeitschriften.de/download/pdf/243919689_0313/log9.pdf).
  The standard inputs are duality for ultraproducts of uniformly reflexive
  spaces, finite representability, and local reflexivity.
- A. Grothendieck, *Sur les applications linéaires faiblement compactes
  d'espaces du type C(K)*, Canadian J. Math. 5 (1953), 129–173,
  [DOI](https://doi.org/10.4153/CJM-1953-017-4).
  The scalar theorem and scalar measure criterion used in Proposition 3.
- Q. Bu, *Semi-embeddings and weakly sequential completeness of the
  projective tensor product*, Studia Math. 169 (2005), 287–294,
  [paper](https://www.impan.pl/shop/publication/transaction/download/product/90344).
  WSC results for genuine projective tensor products do not control the
  invisible kernel in Proposition 2.
- A. Rueda Zoca, *Superreflexive tensor product spaces*, Ann. Funct. Anal.
  16 (2025), article 18,
  [arXiv:2409.20220](https://arxiv.org/abs/2409.20220).
  Non-superreflexivity of infinite-dimensional tensor products does not
  imply failure of WSC: \(\ell_1\) is the elementary distinction.

No finite-cotype failure, weakly Cauchy nonconvergent nuclear sequence, or
weak-star null external \(\ell_1\)-sequence was constructed. The research
outcome is the three proved reductions/exclusions above, not a resolution
of either remaining condition in (6).

A further attempt now proves WSC for every finitely generated diagonal
submodule of the nuclear ultraproduct and strengthens Proposition 2 to
annihilators of arbitrary separable families of operator tests. See
[the matrix-limit attempt](/Users/michal/Workspace/mathlib4/grothendieck-matrix-limits-2026-09-05.md)
for the proofs and the remaining gap.
