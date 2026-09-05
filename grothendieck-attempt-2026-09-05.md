# Grothendieck problem: continuation of the August attempt

**Date:** 2026-09-05.  
**Main question:** Is \(\mathcal B(\ell_p)\) Grothendieck for
\(1<p<\infty\), \(p\ne2\)?  
**Outcome:** the main question is not solved here. This note gives a full
proposed argument for the uniformly convex block-sum subproblem, and an exact
reduction of the weak sequential completeness problem to one fixed nuclear
ultraproduct. The first argument would answer Problem 29 in the
González–Kania survey; it is a research argument requiring independent scrutiny,
not a result found in the literature. Neither result proves Problem 28.

The starting documents are [the original notes](grothendieck.md) and
[the August attempt](grothendieck-attempt-2026-08-16.md).
The uniformly convex argument is also available as a
[standalone proof](grothendieck-uniformly-convex-sums.md).
The [subsequent operator attempt](grothendieck-remaining-problems-2026-09-05.md)
reduces the full question to one operator-ultraproduct corona and proves
that the invisible nuclear kernel retains the entire WSC obstruction.
Scalar fields may be real or complex. Write WSC for weak sequential
completeness and rwc for relative weak compactness.

## 1. Uniformly convex block sums: an argument avoiding disintegration

### Proposed theorem

Suppose \((E_n)\) are uniformly convex Banach spaces with a common modulus of
convexity. Then
\[
 W=\left(\bigoplus_{n\ge1} E_n\right)_{\ell_\infty}
\]
is a Grothendieck space.

The proof below does not identify the dual with a Bochner space, and does not
assert that a singular summand is L-embedded. It uses scalar measures on
\(K=\beta\mathbb N\) and a reflexive space obtained by completing a seminorm.

### 1.1 Variation over the index set

For \(A\subseteq\mathbb N\), let \(\pi_Ax=\mathbf1_Ax\). For
\(s\in W^*\), define
\[
 \mu_s(A)=\|s\circ\pi_A\|.
\]
Because \(W=\pi_AW\oplus_\infty\pi_{A^c}W\),
\[
 \|s\|=\|s\pi_A\|+\|s\pi_{A^c}\|.
\]
Applying this to finite partitions shows that \(\mu_s\) is a positive,
finitely additive measure with total mass \(\|s\|\). Identify it with its
regular Borel extension to \(K\), using the same notation. For \(x\in W\),
write \(r_x\in C(K)\) for the continuous extension of the bounded scalar
sequence \((\|x_n\|)\).

Finite partitions according to the values of \(r_x\), followed by uniform
approximation, give
\[
 |s(x)|\le\int_K r_x\,d\mu_s.                       \tag{1}
\]
More generally, for \(g\in C(K)=\ell_\infty\),
\[
 |s(gx)|\le\int_K |g|r_x\,d\mu_s.                  \tag{2}
\]
These statements require no geometry of the \(E_n\).

### 1.2 Weak-star null sequences have weakly compact scalar variations

Let \((s_i)\subset W^*\) be weak-star null. It is norm bounded. We first show
that for every disjoint sequence \((A_j)\) of subsets of \(\mathbb N\),
\[
 \sup_i\mu_{s_i}(A_j)\longrightarrow0.              \tag{3}
\]
If this fails, choose, after passage to subsequences, distinct increasing
indices \(i_j\), a number \(\varepsilon>0\), and vectors
\(x_j\in B_W\) supported on \(A_j\), such that
\[
 |s_{i_j}(x_j)|\ge\varepsilon.
\]
The indices can be made increasing because any one finite positive measure
assigns mass bounded away from zero to only finitely many disjoint sets.

Define a contraction \(J:\ell_\infty\to W\) by setting
\((Ja)_n=a_j(x_j)_n\) when \(n\in A_j\), and zero outside their union.
The sequence \(J^*s_i\) is weak-star null in \(\ell_\infty^*\), and hence
weakly null by the scalar Grothendieck theorem. The atomic restriction map
\[
 R:\ell_\infty^*\to\ell_1,
 \qquad R\rho=(\rho(e_j))_j
\]
is bounded. The Schur property therefore gives
\(\|RJ^*s_i\|_1\to0\), contradicting
\(|(RJ^*s_{i_j})_j|\ge\varepsilon\). This proves (3).

We next apply the Dieudonné–Grothendieck criterion to
\(\{\mu_{s_i}\}\subset M(K)\). If this family were not rwc, there would be
pairwise disjoint open sets \(U_j\subset K\), selected indices \(i_j\), and
\(\varepsilon>0\) with \(\mu_{s_{i_j}}(U_j)>\varepsilon\).
Regularity and the clopen basis of \(\beta\mathbb N\) give clopen sets
\(C_j\subset U_j\) with \(\mu_{s_{i_j}}(C_j)>\varepsilon/2\).
The disjoint clopens correspond to disjoint subsets of \(\mathbb N\),
contradicting (3). Thus
\[
 \{\mu_{s_i}:i\ge1\}\text{ is rwc in }M(K).          \tag{4}
\]

Choose a finite positive regular measure
\[
 \lambda_0=\sum_{i=1}^\infty
       \frac{2^{-i}}{1+\|s_i\|}\mu_{s_i}.
\]
If \(\lambda_0=0\), every \(s_i=0\). Otherwise normalize it to a probability
measure \(\lambda\). Each \(\mu_{s_i}\ll\lambda\). The densities
\(f_i=d\mu_{s_i}/d\lambda\) form a relatively weakly compact subset of
\(L^1(\lambda)\): the map \(f\mapsto f\lambda\) is an isometry onto a closed
linear subspace of \(M(K)\), and (4) applies in that subspace. By the
Dunford–Pettis criterion,
\[
 \lim_{M\to\infty}\sup_i\int_K(f_i-M)_+\,d\lambda=0. \tag{5}
\]

### 1.3 The reflexive space associated with a scalar measure

For a probability measure \(\lambda\) on \(K\), put
\[
 q_\lambda(x)=\left(\int_K r_x^2\,d\lambda\right)^{1/2}.
\]
Let \(H_\lambda\) be the completion of \(W/\ker q_\lambda\) in this norm,
and \(j_\lambda:W\to H_\lambda\) the canonical contraction.

**Lemma.** \(H_\lambda\) is uniformly convex, and therefore reflexive.

**Proof with an explicit modulus.** Choose a common nondecreasing modulus
\(0<\delta(t)\le1\), for \(0<t\le2\). For a bounded scalar sequence
\(a\), write \(\|a\|_{2,\lambda}\) for the \(L^2(\lambda)\)-norm of its
continuous extension to \(K\). All the inequalities below are first
coordinatewise inequalities on \(\mathbb N\), and then are integrated
over \(K\). In particular, no vector-valued measurable bundle is assumed.

Suppose \(q_\lambda(x),q_\lambda(y)\le1\) and
\(q_\lambda(x-y)\ge\varepsilon\), where \(0<\varepsilon\le2\). Put
\[
 a_n=\|x_n\|,\quad b_n=\|y_n\|,\quad
 c_n=\min(a_n,b_n),\quad u_n=(a_n+b_n)/2.
\]
We prove the estimate
\[
 q_\lambda((x+y)/2)^2
 \le1-\frac{3\varepsilon^2}{64}\delta(\varepsilon/4). \tag{UC}
\]

If \(\|a-b\|_{2,\lambda}\ge\varepsilon/2\), the scalar parallelogram
identity and the triangle inequality give
\[
 q_\lambda((x+y)/2)^2\le\|u\|_{2,\lambda}^2
 =\tfrac12(\|a\|_{2,\lambda}^2+\|b\|_{2,\lambda}^2)
   -\tfrac14\|a-b\|_{2,\lambda}^2
 \le1-\varepsilon^2/16.
\]
This implies (UC), since \(\delta\le1\).

In the other case, define
\[
 v_n=\begin{cases}(c_n/a_n)x_n,&a_n>0,\\0,&a_n=0,\end{cases}
 \qquad
 w_n=\begin{cases}(c_n/b_n)y_n,&b_n>0,\\0,&b_n=0.\end{cases}
\]
Then \(\|v_n\|=\|w_n\|=c_n\). If \(e_n=\|v_n-w_n\|\), then
\[
 \|x_n-y_n\|\le e_n+|a_n-b_n|,\qquad e_n\le2c_n.
\]
Consequently \(\|e\|_{2,\lambda}\ge\varepsilon/2\). Set
\(t=\varepsilon/4\) and \(A=\{n:e_n\ge t c_n\}\); write \(\widehat A\)
for the corresponding clopen subset of \(K\). Since
\(\|c\|_{2,\lambda}\le1\),
\[
 \int_{\widehat A}e^2\,d\lambda
 \ge\varepsilon^2/4-t^2\int_{K\setminus\widehat A}c^2\,d\lambda
 \ge3\varepsilon^2/16,
 \qquad
 \int_{\widehat A}c^2\,d\lambda\ge3\varepsilon^2/64.
\]
For \(n\in A\) with \(c_n>0\), apply uniform convexity to
\(v_n/c_n,w_n/c_n\). The case \(c_n=0\) is automatic. In both cases,
\[
 \|(x_n+y_n)/2\|
 \le\|(v_n+w_n)/2\|+|a_n-b_n|/2
 \le u_n-\delta(t)c_n\qquad(n\in A).
\]
Outside \(A\), the upper bound \(u_n\) holds. Because \(u_n\ge c_n\),
\[
 u_n^2-(u_n-\delta(t)c_n)^2
 =\delta(t)c_n(2u_n-\delta(t)c_n)\ge\delta(t)c_n^2.
\]
Integrating proves (UC).

To pass to the completion, approximate two vectors in its unit ball by
vectors from the quotient, and divide the approximants by their common
maximum norm or by one, whichever is larger. If the original separation
is at least \(\varepsilon\), the approximating separation is eventually
at least \(\varepsilon/2\). Thus a valid modulus for \(H_\lambda\) is
\[
 \delta_{H_\lambda}(\varepsilon)
 \ge1-\sqrt{1-\frac{3\varepsilon^2}{256}\delta(\varepsilon/8)}>0.
\]
Reflexivity follows from the Milman–Pettis theorem. \(\square\)

Consequently, the set of functionals \(s\in W^*\) satisfying
\(\mu_s\le M\lambda\) is contained in the weakly compact set
\[
 j_\lambda^*(M B_{H_\lambda^*}).                    \tag{6}
\]
Indeed, (1) and Cauchy–Schwarz imply
\[
 |s(x)|\le M\int_K r_x\,d\lambda\le Mq_\lambda(x),
\]
so \(s\) extends to an element of \(M B_{H_\lambda^*}\).

### 1.4 Truncating the densities, not the vector sections

This step handles Borel cutoffs explicitly; no Borel subset of \(K\) is
silently identified with a subset of \(\mathbb N\).

For \(s\in W^*\) and \(x\in W\), the functional
\[
 C(K)\ni g\longmapsto s(gx)
\]
is represented by a scalar regular measure \(m_{s,x}\). By (2),
\[
 |m_{s,x}|\le r_x\mu_s.                            \tag{7}
\]
For any bounded Borel function \(h\) on \(K\), define a new element of
\(W^*\) by
\[
 s^h(x)=\int_K h\,dm_{s,x}.
\]
Linearity in \(x\) follows from uniqueness of the scalar representing
measure. For \(0\le h\le1\), (7) gives
\[
 |s^h(x)|\le\int_K h r_x\,d\mu_s,
 \qquad
 \|s-s^h\|\le\int_K(1-h)\,d\mu_s.                 \tag{8}
\]

Choose Borel versions of the densities \(f_i\), and put
\[
 h_{i,M}=\begin{cases}
 1,&f_i=0,\\
 \min(1,M/f_i),&f_i>0.
 \end{cases}
\]
Then \(h_{i,M}\mu_{s_i}=\min(f_i,M)\lambda\le M\lambda\).
The first inequality in (8) shows directly that
\[
 s_i^{h_{i,M}}\in j_\lambda^*(M B_{H_\lambda^*}),
\]
and the second gives
\[
 \|s_i-s_i^{h_{i,M}}\|
 \le\int_K(f_i-M)_+\,d\lambda.                     \tag{9}
\]
Equations (5), (6), and (9) approximate \(\{s_i\}\), uniformly in norm,
by weakly compact sets. To spell out the compactness argument, put
\(Y=W^*\) and embed it canonically in \(Y^{**}\). The weak-star closure
\(C\) of the bounded set \(\{s_i\}\) is compact. For every
\(\varepsilon>0\), it is contained in
\(K_\varepsilon+\varepsilon B_{Y^{**}}\) for a weakly compact subset
\(K_\varepsilon\subseteq Y\): this sum is weak-star compact and contains
the original sequence. Thus every point of \(C\) has distance zero from
the norm-closed copy of \(Y\), so belongs to it. The induced weak-star
topology there is the weak topology of \(Y\). This makes \(\{s_i\}\) rwc.

Finally, a rwc weak-star null sequence is weakly null. Otherwise a subsequence
separated from zero by some member of \(W^{**}\) would have a weakly convergent
further subsequence; its limit must be zero by weak-star nullity. This proves
the proposed theorem. \(\square\)

### Consequences and scope

The argument, if accepted, gives the following two consequences requested as
intermediate targets in the original notes:

1. \(\ell_\infty(E)\) is Grothendieck for every superreflexive \(E\), by
   applying an equivalent uniformly convex norm coordinatewise.
2. \((\bigoplus_n S_q^n)_{\ell_\infty}\) is Grothendieck for
   \(1<q<\infty\), since the Schatten \(q\)-norms have a common modulus of
   uniform convexity.

Neither consequence concerns the nuclear norm on \(N(\ell_p^n)\) or the
operator norm on \(\mathcal B(\ell_p^n)\).

## 2. Why the same argument does not prove the operator theorem

Put \(W_p=(\bigoplus_n\mathcal B(\ell_p^n))_{\ell_\infty}\), and fix a
free ultrafilter \(\mathcal U\). For each \(i\ge1\), define
\[
 \sigma_i((T_n))=\lim_{n\to\mathcal U}(T_n)_{ii},
\]
where the finitely many terms with \(n<i\) are set to zero.
Then \(\|\sigma_i\|=1\), and their variations over the block index all equal
the same point mass \(\delta_{\mathcal U}\). Nevertheless,
\[
 \left\|\sum_{i=1}^m a_i\sigma_i\right\|=
 \sum_{i=1}^m|a_i|.                               \tag{10}
\]
For the lower bound, take diagonal contractions whose first \(m\) entries
are phases norming the coefficients \(a_i\); the upper bound is the triangle
inequality. Thus the dominated set
\(\{s:\mu_s\le\delta_{\mathcal U}\}\) is not rwc.

This disproves, already at \(p=2\), the analogue of (6) for operator blocks.
In that case \(H_{\delta_{\mathcal U}}\) is simply the operator ultraproduct,
which is not reflexive. The example is not a counterexample to the
Grothendieck conjecture: \(\sigma_i((I_n))=1\), so it is not weak-star null.
It pinpoints the missing use of weak-star nullity beyond central variation
control.

## 3. One fixed nuclear ultraproduct captures the whole WSC question

Write
\[
 Z_p=N(\ell_p)=\ell_{p'}\widehat\otimes_\pi\ell_p,
 \qquad
 F_{p,\mathcal U}=\bigl(N(\ell_p^n)\bigr)_{\mathcal U},
\]
where \(\mathcal U\) is any fixed free ultrafilter on \(\mathbb N\).

### Proposition

The following statements are equivalent:

1. \(\mathcal B(\ell_p)^*=Z_p^{**}\) is WSC.
2. \(F_{p,\mathcal U}\) is WSC for this one fixed \(\mathcal U\).
3. Every Banach space finitely representable in \(Z_p\) is WSC.

In particular, proving WSC of the nuclear ultraproduct does not require a
subsequent disintegration theorem to obtain WSC of the global dual. This
corrects that part of Sections 6 and 9 of the August note. A separate
no-\(c_0\)-quotient argument is still needed for Grothendieck.

### Proof

**(1) implies (2).** The canonical pairing embeds
\(F_{p,\mathcal U}\) isometrically into \(W_p^*\):
\[
 [u_n]\longmapsto
 \left((T_n)\longmapsto\lim_{n\to\mathcal U}\operatorname{tr}(T_nu_n)\right).
\]
Coordinate normers prove isometry. The block-diagonal projection from
\(\mathcal B(\ell_p)\) onto its copy of \(W_p\) is contractive, so its adjoint
embeds \(W_p^*\) isometrically into \(\mathcal B(\ell_p)^*\). WSC passes to
closed subspaces by Hahn–Banach and weak closedness of norm-closed linear
subspaces.

**(2) implies (3).** It suffices to consider a separable Banach space \(Y\)
finitely representable in \(Z_p\). Indeed, any weakly Cauchy sequence belongs
to its separable closed linear span.

Choose increasing finite-dimensional subspaces \(Y_k\) with dense union in
\(Y\). Finite representability and coordinate compression give integers
\(d_k\), strictly increasing after enlarging them, and linear maps
\(T_k:Y_k\to N(\ell_p^{d_k})\) such that
\[
 (1-\varepsilon_k)\|y\|\le\|T_ky\|_N
 \le(1+\varepsilon_k)\|y\|,
 \qquad \varepsilon_k\longrightarrow0.
\]
Here the compression maps \(u\mapsto P_duP_d\) are contractions on
\(Z_p\), converge to the identity in nuclear norm, and therefore converge
uniformly on the unit ball of each finite-dimensional subspace.

For \(n\ge d_1\), set \(k(n)=\max\{k:d_k\le n\}\).
For \(y\in\bigcup_kY_k\), use \(T_{k(n)}y\), extended by zero to
\(N(\ell_p^n)\), whenever \(y\in Y_{k(n)}\), and use zero at the remaining
finitely many indices. This gives an isometric linear map
\[
 Y\longrightarrow F_{p,\mathcal U}
\]
after taking ultraproduct classes and completing. Linearity holds because
every finite collection of vectors eventually belongs to the same \(Y_k\).
The estimates tend to equality along every free \(\mathcal U\).
Thus \(Y\) is WSC if (2) holds.

**(3) implies (1).** The principle of local reflexivity says that
\(Z_p^{**}\) is finitely representable in \(Z_p\), so (3) applies.
\(\square\)

The proof also shows that every separable subspace of
\(\mathcal B(\ell_p)^*\) embeds isometrically into this fixed
\(F_{p,\mathcal U}\). This is a Banach-space embedding; it does not preserve
the original weak-star topology. That distinction prevents using the
August note's internal-sequence lemma to prove Grothendieck immediately.

## 4. What still has to be proved for the original problem

Räbiger's characterization and Section 3 give the exact remaining conjunction
\[
 \boxed{
 \mathcal B(\ell_p)\text{ is Grothendieck}
 \iff
 \begin{cases}
 F_{p,\mathcal U}\text{ is WSC},\\
 \mathcal B(\ell_p)\text{ has no quotient isomorphic to }c_0.
 \end{cases}}
\]
Neither condition is established here for \(p\ne2\). The second is
equivalent to absence of a weak-star null \(\ell_1\)-basic sequence in
\(\mathcal B(\ell_p)^*\). WSC of the original nuclear space is insufficient:
Section 3 requires the corresponding local property, not just WSC of
\(Z_p\) itself.

The August note's finite-cotype counterexample criterion survives this audit.
Failure of finite cotype in \(Z_p\) would put \(c_0\) into
\(F_{p,\mathcal U}\) through uniform finite-dimensional \(\ell_\infty\)
embeddings and disprove Grothendieck. No such embeddings are constructed
here. Conversely, finite cotype alone would not prove WSC.

## 5. Sources and verification boundary

The literature search located the main question as Problem 28, and the
superreflexive vector-sum question as Problem 29, in the survey below. It
did not locate a published resolution of either. Section 1 is an original
proposed argument, not a claim that the literature has already settled
Problem 29. Its key checkpoints are the scalar variation compactness in
Section 1.2, the finitely additive seminorm completion in Section 1.3, and
the scalar-measure Borel cutoff construction in Section 1.4. Section 2
exhibits the exact failure of its crucial reflexivity step for operator
blocks.

- M. González and T. Kania, *Grothendieck spaces: the landscape and
  perspectives*, [arXiv:2102.03838](https://arxiv.org/abs/2102.03838).
  Theorem 3.1.7 gives Räbiger's characterization; Section 5.3 records the
  operator question and the known finite-block isomorphism.
- A. Grothendieck, *Sur les applications linéaires faiblement compactes
  d'espaces du type C(K)*, Canadian J. Math. 5 (1953), 129–173,
  [DOI:10.4153/CJM-1953-017-4](https://doi.org/10.4153/CJM-1953-017-4).
  The scalar weak compactness criterion and the Stonean-space theorem are
  the scalar inputs to Section 1.2.
- S. Heinrich, *Ultraproducts in Banach space theory*, J. Reine Angew. Math.
  313 (1980), 72–104,
  [paper](https://www.digizeitschriften.de/download/pdf/243919689_0313/log9.pdf).
  Background for finite representability and local reflexivity.
- M. M. Day, *Some more uniformly convex spaces*, Bull. Amer. Math. Soc.
  47 (1941), 504–507,
  [DOI:10.1090/S0002-9904-1941-07499-9](https://doi.org/10.1090/S0002-9904-1941-07499-9).
  Related background on uniform convexity of direct sums. Section 1.3 now
  proves the needed estimate directly, including an explicit modulus.
- K. Ball, E. A. Carlen, and E. H. Lieb, *Sharp uniform convexity and
  smoothness inequalities for trace norms*, Invent. Math. 115 (1994),
  463–482, [DOI:10.1007/BF01231769](https://doi.org/10.1007/BF01231769).
  Supplies the Schatten-class uniform convexity used in the consequence.
- O. V. Kucher, *The Grothendieck property in the space
  \(\ell_\infty(E)\) and the weak Banach–Saks property in \(c_0(E)\)*,
  J. Math. Sci. 96 (1999), 2828–2833,
  [DOI:10.1007/BF02168989](https://doi.org/10.1007/BF02168989).
  The published abstract treats B-convex Banach lattices; it does not
  supply the non-lattice assertion of Section 1.

No Lean formalization or independent referee verification was performed.
