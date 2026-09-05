# Another attempt: testing the missing approximation step

Date: 2026-09-05.

This continues
[the diagonal-module attempt](/Users/michal/Workspace/mathlib4/grothendieck-matrix-limits-2026-09-05.md).
The general Grothendieck problem for \(\mathcal B(\ell_p)\) is not solved.
This attempt tests whether weak Cauchyness supplies an approximation
principle that would extend the preceding finite-generation theorem.
Two natural versions of that principle are false, even for weakly null
sequences. The counterexamples below concern those approximation
principles; they are not counterexamples to the Grothendieck property.

There is also a positive extension: nuclear ultraproduct subspaces
consisting of block-diagonal matrices with a uniformly bounded number
of retained rows per block are weakly sequentially complete. Both the
number and sizes of the blocks may grow without bound.

## 1. Setting

Fix \(1<p<\infty\), put \(q=p'=p/(p-1)\), and fix a free ultrafilter
\(\mathcal U\) on \(\mathbb N\). As before, write
\[
 F=(N(\ell_p^n))_{\mathcal U},\qquad
 D=\{[u_n]\in F:\lim_{\mathcal U}\|u_n\|_{\rm op}=0\},
 \qquad \mathscr H=(\ell_\infty^n)_{\mathcal U}.
\]
The algebra \(\mathscr H\) acts by diagonal multiplication on the left
and on the right. For finitely many \(v_1,\ldots,v_r\in F\), set
\[
 M_L(v_1,\ldots,v_r)=
 \overline{\mathscr H v_1+\cdots+\mathscr H v_r}.
\]
The previous attempt proves that every such module is weakly
sequentially complete (WSC).

A possible next step would have been:

> Every weakly Cauchy sequence in \(D\) can, for each \(\varepsilon>0\),
> be uniformly approximated within \(\varepsilon\) by one finitely
> generated left diagonal module.

Theorem 3 below disproves this statement in its strongest uniform
form: for one weakly null unit sequence, the supremum of the distances
is exactly one for every such module.

## 2. A finite-dimensional distance estimate

### Lemma 1

Let \(1<q<\infty\), \(V\subseteq\ell_q^d\) have dimension at most \(r\),
and \(0<t<1\). Then at most
\[
 C(r,q,t)=\left(\frac{r(1+t)}{1-t}\right)^q                 \tag{1}
\]
of the coordinate unit vectors \(e_k\) have distance less than \(t\)
from \(V\). Consequently, for \(K\le d\),
\[
 \sum_{k=1}^K\operatorname{dist}(e_k,V)
 \ge t\bigl(K-C(r,q,t)\bigr).                              \tag{2}
\]

**Proof.** The zero-dimensional case is immediate. Otherwise choose an
Auerbach basis \(w_1,\ldots,w_h\) of \(V\), \(h\le r\), with
\(\|w_j\|_q=\|\phi_j\|_{V^*}=1\) and biorthogonal coefficient functionals
\(\phi_j\). If \(\|e_k-v\|_q<t\) for some \(v\in V\), then
\[
 1-t<|v(k)|
 \le\sum_{j=1}^h|\phi_j(v)|\,|w_j(k)|
 \le(1+t)\sum_{j=1}^h|w_j(k)|.
\]
But
\[
 \sum_{k=1}^d\left(\sum_{j=1}^h|w_j(k)|\right)^q
 \le h^{q-1}\sum_{j=1}^h\|w_j\|_q^q=h^q\le r^q.
\]
This bounds the number of such indices \(k\) by (1), and (2) follows.
\(\square\)

When \(q\le2\), a useful sharper bound is
\[
 \sum_{k=1}^K\operatorname{dist}(e_k,V)\ge K-r.              \tag{3}
\]
To see this, project \(V\) onto the first \(K\) coordinates and then
take its Euclidean orthogonal projection \(P\).
The \(\ell_q\) distance dominates the Euclidean distance, so the sum
is at least
\(\sum_k\sqrt{1-\langle Pe_k,e_k\rangle}\ge K-\operatorname{rank}P\).

## 3. A weakly null sequence defeating finite left generation

Put \(d_n=\lfloor\sqrt n\rfloor\), \(m_n=\lfloor n/d_n\rfloor\), and
divide the first \(m_nd_n\) coordinates into \(m_n\) blocks of size
\(d_n\). For \(z\in\ell_q\), let \(f_{P_{d_n}z}\) be the functional
on \(\ell_p^{d_n}\) with coefficient vector \(P_{d_n}z\). Define
\[
 J_nz=\frac1{m_n}
 \operatorname{diag}_{m_n}(e_1\otimes f_{P_{d_n}z})\oplus0.
                                                               \tag{4}
\]
The block nuclear norm and operator norm formulas give
\[
 \|J_nz\|_N=\|P_{d_n}z\|_q,\qquad
 \|J_nz\|_{\rm op}=\frac{\|P_{d_n}z\|_q}{m_n}.
\]
Thus \(Jz=[J_nz]\) defines a linear isometry \(J:\ell_q\to D\).

### Proposition 2

The sequence \(u_k=Je_k\) has norm one and is weakly null in \(F\).

**Proof.** The unit vectors of \(\ell_q\) are weakly null. For every
\(\Phi\in F^*\), \(\Phi\circ J\in\ell_q^*\), so
\(\Phi(u_k)\to0\). This proves weak convergence against the entire
dual, without any diagonal selection of operator tests. \(\square\)

### Theorem 3

For every finite list \(v_1,\ldots,v_r\in F\), with
\(M=M_L(v_1,\ldots,v_r)\),
\[
 \boxed{\lim_{K\to\infty}\frac1K
      \sum_{k=1}^K\operatorname{dist}(u_k,M)=1.}             \tag{5}
\]
In particular,
\[
 \sup_k\operatorname{dist}(u_k,M)=1.
\]
This applies even when the proposed generators are allowed to lie
outside \(D\).

**Proof.** Let \(R_n\) first take the block-diagonal part relative to
the partition in (4), and then retain only the first row of each
block, discarding the remaining coordinates. This is a contractive
projection both in nuclear norm and in operator norm. Indeed,
block-diagonal extraction is an average of conjugations by sign
isometries, and the row selection is left multiplication by a
coordinate projection. It commutes with left diagonal multiplication.
Also \(R_nJ_nz=J_nz\).

Choose bounded representatives \(v_{j,n}\). In block \(b\), let
\(w_{j,b,n}\in\ell_q^{d_n}\) be \(m_n\) times the nonzero row of
\(R_nv_{j,n}\), and put
\[
 V_{b,n}=\operatorname{span}\{w_{1,b,n},\ldots,w_{r,b,n}\}.
\]
Its dimension is at most \(r\), independently of the sizes of the
coefficients or templates.

Fix \(K\). If \(y_k=\sum_{j=1}^r a_{k,j}v_j\), \(a_{k,j}\in\mathscr H\),
choose the corresponding representatives. For \(d_n\ge K\),
\[
\begin{aligned}
 \sum_{k=1}^K\|u_{k,n}-y_{k,n}\|_N
 &\ge\sum_{k=1}^K\|u_{k,n}-R_ny_{k,n}\|_N\\
 &\ge\frac1{m_n}\sum_{b=1}^{m_n}
          \sum_{k=1}^K\operatorname{dist}(e_k,V_{b,n})\\
 &\ge t\bigl(K-C(r,q,t)\bigr).
\end{aligned}                                               \tag{6}
\]
The second inequality uses the exact sum of the row norms for
block-diagonal rank-one row operators.

Take the ultralimit. Approximation in norm extends (6) to \(y_k\in M\).
Taking the infimum separately over each of the finitely many \(y_k\)
gives
\[
 \sum_{k=1}^K\operatorname{dist}(u_k,M)
 \ge t\bigl(K-C(r,q,t)\bigr).
\]
The distances are all at most one. Divide by \(K\), let \(K\to\infty\),
and then let \(t\uparrow1\). This proves (5). \(\square\)

The same counting argument works after any fixed internal diagonal
projection \(e\), with the lower bound multiplied by
\(\alpha=\|eu_k\|\), which is independent of \(k\).
For the closed left module generated by all the \(u_k\), every nonzero
such corner has \(\alpha>0\). It therefore cannot become finitely
generated on any nonzero internal diagonal corner.

There is an important limit to this obstruction: the sequence does
belong to a right cyclic module. Choose \(z\in\ell_q\) with all
coordinates nonzero. Right multiplication selecting the \(k\)-th
column in each block, with coefficient \(1/z_k\), sends \(Jz\) to
\(u_k\). Consequently this result does not rule out a method combining
left and right actions. Transposing the construction gives the
corresponding obstruction to finite *right* generation.

## 4. A larger class where weak Cauchy limits do exist

For each \(n\), partition \(\{1,\ldots,n\}\) into arbitrary blocks
\(B\), and choose a subset \(S_B\subseteq B\) with \(|S_B|\le r\),
where \(r\) is fixed independently of \(n\). Let \(G_n\) consist of
matrices supported in
\[
 \bigcup_B(S_B\times B).
\]
Thus these matrices are block diagonal and have at most \(r\)
prescribed nonzero rows in each block. Let \(R_n\) be the associated
block-diagonal extraction and row selection, as above, and set
\[
 G=(G_n)_{\mathcal U}\subseteq F.
\]

### Theorem 4

The spaces \(G\) and \(G\cap D\) are weakly sequentially complete.
They are ranges of contractive projections on \(F\) and \(D\),
respectively. There is no bound on the number or sizes of the blocks.

**Proof.** The projections \(R_n\) are contractions for both norms, so
their ultraproduct projects \(F\) onto \(G\) and preserves \(D\).

For \(v\in G_n\), write
\[
 \rho_n(v)=\sum_B\sum_{i\in S_B}
               \|\operatorname{row}_i(v|_B)\|_q.
\]
The row nuclear decomposition gives the first inequality in
\[
 \|v\|_N\le\rho_n(v)\le r^{1/q}\|v\|_N.                    \tag{7}
\]
For the second, the preceding attempt's disjoint-row estimate gives,
within each block,
\[
 \left(\sum_{i\in S_B}
       \|\operatorname{row}_i(v|_B)\|_q^p\right)^{1/p}
 \le\|v|_B\|_N.
\]
Apply Hölder to the at most \(r\) rows and then sum over blocks.
The nuclear norm is additive on these diagonal blocks, proving (7).

With norm \(\rho_n\), this is a Banach lattice of the form
\(\bigoplus_1\ell_q^{|B|}\), with one summand for each retained row.
It is \(q\)-concave with constant one: this is Minkowski's inequality
for the outer sum and the exact \(\ell_q\) identity inside each row.
Its ultraproduct has the same concavity estimate.

A Banach lattice with finite concavity exponent contains no sublattice
lattice isomorphic to \(c_0\): disjoint unit vectors would have partial
sums with norm at least \(K^{1/q}\). The Banach-lattice criterion
therefore makes this ultraproduct WSC. The uniform norm equivalence
(7) gives WSC of \(G\). Its closed subspace \(G\cap D\) is WSC as well.
\(\square\)

The example in Section 3 belongs to the case \(r=1\) of this theorem.
Thus there are WSC spaces inside \(D\) whose weakly null sequences
cannot be uniformly approximated by any finitely generated left
diagonal module.

The transpose statement, with at most \(r\) prescribed columns per
block, follows with \(p\) and \(q\) interchanged.

## 5. This larger approximation principle also fails

It is tempting to replace finitely generated modules by the spaces
in Theorem 4. Even that replacement does not approximate every
weakly Cauchy sequence uniformly.

Let \(S_n\) be the cyclic permutation matrix on \(\ell_p^n\), and put
\[
 w_k=[S_n^k/n]\in F\qquad(k\ge1).
\]

### Proposition 5

The sequence \(w_k\) has norm one, belongs to \(D\), and is weakly null.

**Proof.** A permutation matrix has nuclear norm \(n\): its column
decomposition gives the upper bound, and pairing with its inverse,
an operator contraction, gives the lower bound. Its operator norm
is one. Hence \(\|w_k\|=1\) and \(w_k\in D\).

For scalars \(a_1,\ldots,a_K\) and \(n>K\), each column of
\(\sum_{k=1}^K a_kS_n^k\) has \(\ell_p\)-norm
\(\|(a_k)\|_p\), and each row has \(\ell_q\)-norm
\(\|(a_k)\|_q\). The two nuclear decompositions imply
\[
 \left\|\sum_{k=1}^K a_kw_k\right\|
 \le\min\{\|(a_k)\|_p,\|(a_k)\|_q\}
 =\|(a_k)\|_s,\qquad s=\max\{p,q\}.                       \tag{8}
\]
This defines a bounded linear map \(\ell_s\to F\) sending \(e_k\)
to \(w_k\). Since \(1<s<\infty\), the sequence is weakly null.
\(\square\)

### Theorem 6

For every space \(G\) described in Theorem 4, with any fixed row bound
\(r\), any partitions, and any retained rows depending on \(n\),
\[
 \boxed{\lim_{K\to\infty}\frac1K
      \sum_{k=1}^K\operatorname{dist}(w_k,G)=1.}             \tag{9}
\]

**Proof.** Let \(c_{k,n}\) count the entries of the permutation matrix
\(S_n^k\) retained by \(R_n\). The deleted entries form a partial
permutation matrix, so
\[
 \|S_n^k/n-R_n(S_n^k/n)\|_N=1-\frac{c_{k,n}}n.
\]
This equals the distance to \(G_n\). Indeed, the transpose of the
deleted partial permutation is an operator contraction whose trace pairing annihilates
every matrix in \(G_n\) and takes that value on \(S_n^k/n\).
The same argument with internal operator tests shows
\[
 \operatorname{dist}(w_k,G)
 =1-\lim_{\mathcal U}\frac{c_{k,n}}n.                       \tag{10}
\]

For \(n>K\), the \(K\) shifts have disjoint matrix supports.
In block \(B\), at most \(|S_B||B|\) entries in total can be retained.
Consequently
\[
 \sum_{k=1}^K c_{k,n}
 \le\sum_B|S_B||B|\le rn.
\]
Using (10) and taking the ultralimit gives
\[
 \frac1K\sum_{k=1}^K\operatorname{dist}(w_k,G)\ge1-\frac rK.
\]
The reverse bound by one is immediate, proving (9). \(\square\)

The corresponding assertion for a fixed bound on retained columns is
proved by the same counting argument. The obstruction is to distance
from the whole proposed approximating space, not just to the error
of one particular choice of approximating matrices.

## 6. An alternate problem checked, but not completed

Problem 30 in the González–Kania survey asks whether an ultrapower of
a reflexive space can be Grothendieck without being reflexive.
The natural candidate
\[
 E=\left(\bigoplus_{d\ge1}\ell_\infty^d\right)_{\ell_2}
\]
is reflexive. Every free ultrapower \(E_{\mathcal U}\) contains
\(\ell_\infty\) isometrically: place the first \(n\) coordinates of a
bounded scalar sequence in the \(n\)-th block of the \(n\)-th
representative. Thus it is nonreflexive.

The lattice \(E\), and hence \(E_{\mathcal U}\), is 2-convex with
constant one. By lattice duality, \(E_{\mathcal U}^*\) is 2-concave
and therefore WSC. This establishes the dual-WSC half of Räbiger's
criterion. I did not prove that \(E_{\mathcal U}\) has no quotient
isomorphic to \(c_0\), so this is not an answer to Problem 30.
The known absence of *complemented* copies of \(c_0\) in such
ultrapowers does not establish the absence of \(c_0\) quotients.

## 7. What remains

The weak Cauchy limit assertion for all of \(D\) remains unproved.
Theorems 3 and 6 show that two candidate approximation steps would
be false, even in the Hilbert case \(p=2\), where the ultimate
Grothendieck conclusion is already known. Therefore their failure
does not favor a counterexample to the main problem.

A successful extension of the finite-generation argument must use
something other than uniform nuclear-norm approximation by those
modules. Theorem 4 supplies larger WSC subspaces, but Theorem 6
prevents using their uniform approximation as a general replacement.
No nonconvergent weakly Cauchy sequence, or quotient onto \(c_0\),
has been constructed.

The standard lattice input is the WSC criterion recorded as
Theorem 2.18 in A. Kitover and M. Orhon,
[*Weak sequential completeness in Banach \(C(K)\)-modules of finite
multiplicity*](https://arxiv.org/pdf/1408.0040).
The finite-dimensional estimates, embeddings, and distance
obstructions above are proved explicitly here.

The problem statements and the characterization separating dual WSC
from the \(c_0\)-quotient obstruction are in M. González and T. Kania,
[*Grothendieck spaces: the landscape and
perspectives*](https://arxiv.org/abs/2102.03838).

These are mathematical proofs and checks of proposed lemmas, not
Lean-verified results. No claim of novelty in the literature is made.
