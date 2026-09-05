# Uniformly convex infinity sums are Grothendieck: a proposed proof

**Date:** 2026-09-05.

This note gives a complete candidate proof of the uniformly convex sum problem
in [the original research notes](grothendieck.md), including the missing weak
sequential completeness step. Its constant-summand case would answer Problem
29 of González–Kania positively. This is an original argument audited within
this session; it has not been independently refereed or formally verified.

The proof is over either the real or complex scalar field. A Banach space is
Grothendieck if every weak-star null sequence in its dual is weakly null.
We use rwc to mean relatively weakly compact.

## Theorem

Suppose \((E_n)\) are uniformly convex Banach spaces with a common modulus of
convexity. Then
\[
 W=\left(\bigoplus_{n\ge1} E_n\right)_{\ell_\infty}
\]
is a Grothendieck space.

The proof below does not identify the dual with a Bochner space, and does not
assert that a singular summand is L-embedded. It uses scalar measures on
\(K=\beta\mathbb N\) and a reflexive space obtained by completing a seminorm.

## 1. Variation over the index set

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

## 2. Weak-star null sequences have weakly compact scalar variations

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

## 3. The reflexive space associated with a scalar measure

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

## 4. Truncating the densities, not the vector sections

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
by weakly compact sets. Here is the precise compactness argument. Put
\(Y=W^*\), let \(\kappa:Y\to Y^{**}\) be its canonical embedding, and
let \(C\) be the weak-star closure of \(\kappa(\{s_i\})\) in \(Y^{**}\).
This closure is compact because the sequence is bounded. For every
\(\varepsilon>0\), the estimates give a weakly compact set \(K_\varepsilon\)
in \(Y\) with
\[
 C\subseteq\kappa(K_\varepsilon)+\varepsilon B_{Y^{**}}.
\]
Indeed, the set on the right is weak-star compact and contains every
\(\kappa(s_i)\). Hence every element of \(C\) has distance at most
\(\varepsilon\) from the norm-closed subspace \(\kappa(Y)\), for every
\(\varepsilon>0\), so \(C\subseteq\kappa(Y)\). The weak-star topology
of \(Y^{**}\) restricted to \(\kappa(Y)\) is its weak topology. Thus
\(\{s_i\}\) is rwc.

Finally, a rwc weak-star null sequence is weakly null. Otherwise a subsequence
separated from zero by some member of \(W^{**}\) would have a weakly convergent
further subsequence; its limit must be zero by weak-star nullity. This proves
the theorem. \(\square\)

## Consequences and scope

The theorem gives the following consequences:

1. \(\ell_\infty(E)\) is Grothendieck for every superreflexive \(E\), by
   applying an equivalent uniformly convex norm coordinatewise.
2. \((\bigoplus_n S_q^n)_{\ell_\infty}\) is Grothendieck for
   \(1<q<\infty\), since the Schatten \(q\)-norms have a common modulus of
   uniform convexity.

Neither consequence concerns the nuclear norm on \(N(\ell_p^n)\) or the
operator norm on \(\mathcal B(\ell_p^n)\).

## Boundary with the operator problem

This argument does not establish that \(\mathcal B(\ell_p)\) is Grothendieck.
The blocks \(\mathcal B(\ell_p^n)\), with their operator norms, contain the
diagonal \(\ell_\infty^n\) isometrically and do not have a common uniformly
convex renorming with uniform equivalence constants. In that setting, the
space \(H_\lambda\) constructed in the proof can be nonreflexive even when
\(\lambda\) is a single ultrafilter point mass. The obstruction is exhibited
explicitly in [the continuation, Section 2](grothendieck-attempt-2026-09-05.md).

## Inputs from the literature

The new argument is the assembly of scalar variation control, the explicit
reflexive completion, and Borel truncation of functionals. The standard
inputs are the scalar Grothendieck theorem, the Dieudonné–Grothendieck
criterion, the Schur property of \(\ell_1\), the scalar Radon–Nikodym and
Dunford–Pettis theorems, Milman–Pettis, and Eberlein–Šmulian. No vector
Radon–Nikodym representation or disintegration theorem is used.

- M. González and T. Kania, *Grothendieck spaces: the landscape and
  perspectives*, [arXiv:2102.03838](https://arxiv.org/abs/2102.03838),
  Section 5.4, Problem 29. This is the source for the problem, not the proof.
- A. Grothendieck, *Sur les applications linéaires faiblement compactes
  d'espaces du type C(K)*, Canadian J. Math. 5 (1953), 129–173,
  [DOI:10.4153/CJM-1953-017-4](https://doi.org/10.4153/CJM-1953-017-4).
  Scalar weak compactness and the Stonean-space theorem.
- K. Ball, E. A. Carlen, and E. H. Lieb, *Sharp uniform convexity and
  smoothness inequalities for trace norms*, Invent. Math. 115 (1994),
  463–482, [DOI:10.1007/BF01231769](https://doi.org/10.1007/BF01231769).
  Uniform convexity of the Schatten classes for the second corollary.
- O. V. Kucher, *The Grothendieck property in the space
  \(\ell_\infty(E)\) and the weak Banach–Saks property in \(c_0(E)\)*,
  J. Math. Sci. 96 (1999), 2828–2833,
  [DOI:10.1007/BF02168989](https://doi.org/10.1007/BF02168989).
  Earlier lattice results and the conjecture referenced in the survey.
