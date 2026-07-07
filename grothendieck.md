# Is $\mathcal B(\ell_p)$ a Grothendieck space? — research notes

**Question.** Is the Banach space $\mathcal B(\ell_p)$ of bounded operators on $\ell_p$ a *Grothendieck space* for $1<p<\infty$, $p\neq 2$? More generally (Kania): is $\mathcal B(X)$ Grothendieck for every superreflexive $X$?

**Status.** OPEN. On Kania's published problem list ([arXiv:2102.03838](https://arxiv.org/abs/2102.03838)). These notes record a long solo investigation: the reduction is essentially complete, several special cases are *proved*, every counterexample candidate has been *defeated*, and the whole problem now sits on a single, precisely-named open lemma. No proof and no counterexample was found.

**My subjective lean at the end: ~82% that the answer is YES (Grothendieck) for all $1<p<\infty$.** This is a personal Bayesian read from the structure below, not a theorem.

**Update (2026-07-07).** Two developments this session. (i) **General condition (A) is fully settled — by literature I had missed**: Räbiger (1985) proved $\ell_\infty(\Gamma,L_p(\mu))$ is Grothendieck, Leung (1988) extended this to order-complete lattices (Orlicz with WSC dual); since $W_q$ is 1-complemented in $\ell_\infty(\ell_q)$, the whole necessary-condition family of §2 is now [L] (see the rewritten condition-(A) item and §2.5). (ii) A **new, fully rigorous quantitative theorem** (§2.5, Theorem A): *no weak\*-null sequence in $((\bigoplus_n E_n)_{\ell_\infty})^*$ is equivalent to the $\ell_1$-basis, whenever the $E_n$ are uniformly convex with a common modulus* — lattice-free, so it also covers Schatten summands and gives a partial answer to Kucher's open problem on $\ell_\infty(E)$, $E$ superreflexive. The kernel (§3, condition (B)) remains open; the cut-lemma mechanism of §2.5 stalls exactly at the non-uniform-convexity of matrix blocks, sharpening (not displacing) the dividing line of §3–4. **Lean now ~85% YES.** Checked (2026-07): no published solution of the main problem; Kucher's problem also still open.

> Legend: **[R]** = rigorous (I'm confident it's correct); **[S]** = sketch/near-proof with an identified gap; **[H]** = heuristic/conjectural; **[L]** = from the literature.

---

## 0. Definitions and basic reductions

- **Grothendieck space**: weak\*-convergent sequences in $X^*$ are weakly convergent. Equivalently every bounded operator $X\to c_0$ is weakly compact.
- **Property (V)** (Pełczyński): every unconditionally converging operator $X\to Y$ is weakly compact. Dual form: every (V)-set in $X^*$ is relatively weakly compact (rwc), where $K$ is a (V)-set if $\sup_{\phi\in K}|\phi(x_n)|\to0$ for every weakly unconditionally Cauchy (wuC) series $\sum x_n$.
- **L-embedded**: $X^{**}=X\oplus_1 X_s$ (an L-summand of its bidual). **M-embedded**: $X$ is an M-ideal in $X^{**}$.
- $N(\ell_p)$ = nuclear operators $=\ell_{p'}\hat\otimes_\pi\ell_p$; $\mathcal K(\ell_p)$ = compacts; $\mathcal C_p=\mathcal B(\ell_p)/\mathcal K(\ell_p)$ = Calkin space.

**Transpose duality [R].** $T\mapsto T^{*}$ gives $\mathcal B(\ell_p)\cong\mathcal B(\ell_{p'})$ isometrically, so WLOG **$p\ge 2$** throughout.

**Known landscape [L].**
- $\mathcal B(\ell_2)$ is Grothendieck (it's a von Neumann algebra; Pfitzner 1994: all $C^*$-algebras have property (V)). Von Neumann algebras are the **only** known infinite-dim spaces with $\mathcal B(X)$ Grothendieck.
- Counterexamples (reflexive, $\mathcal B(X)$ NOT Grothendieck): $X=(\bigoplus_n\ell_1^n)_{\ell_p}$ (Kania, [arXiv:1211.2867](https://arxiv.org/abs/1211.2867)); $X=$ Tsirelson, Baernstein (Beanland–Kania–Laustsen, [arXiv:1707.08399](https://arxiv.org/abs/1707.08399)). **All are reflexive but NOT superreflexive** — they carry asymptotic-$\ell_1$ structure. Mechanism (BKL): $X\supseteq$ complemented $(\bigoplus\ell_1^{m_n})_E$ with $m_n\to\infty$ $\Rightarrow$ $\mathcal B(X)\supseteq$ complemented $\ell_1$ $\Rightarrow$ not Grothendieck. **Superreflexivity (uniform convexity) of $\ell_p$ blocks this engine** — this is the core reason to expect YES.

---

## 1. The reduction architecture [R]

Combine the following (each rigorous, standard tools cited):

1. **Grothendieck $\iff$** every weak\*-null sequence in $\mathcal B(\ell_p)^*$ is weakly null.
2. **L-decomposition.** $\ell_p$ ($1<p<\infty$) has Kalton's property (M), MCAP, no $\ell_1$; by **Kalton–Werner**, $\mathcal K(\ell_p)$ is an M-ideal in $\mathcal B(\ell_p)$. Hence
   $$\mathcal B(\ell_p)^* = N(\ell_p)\ \oplus_1\ \mathcal C_p^*,\qquad \mathcal C_p^*=\mathcal K(\ell_p)^\perp\ \text{(``singular'' functionals).}$$
   Here $\mathcal K(\ell_p)^*=N(\ell_p)$, $N(\ell_p)^*=\mathcal B(\ell_p)$ (reflexivity + AP), and $N(\ell_p)$ is **L-embedded** with $N(\ell_p)^{**}=\mathcal B(\ell_p)^*$.
3. **Normal part — Pfitzner 2010** ("Phillips' lemma for L-embedded spaces", Arch. Math.). The L-projection $N^{**}\to N$ is $\sigma(N^{**},N^*)$-to-weakly sequentially continuous. Since $\sigma(N^{**},N^*)=\sigma(\mathcal B^*,\mathcal B)$, a weak\*-null $\Phi_k=\nu_k+\sigma_k$ has $\nu_k\to0$ **weakly**. So $\Phi_k$ weakly null $\iff\sigma_k$ weakly null.
4. **No complemented $c_0$.** $\mathcal B(\ell_p)=N(\ell_p)^*$ is a dual space, and **no dual space contains a complemented $c_0$** (proof: $X^*$ is 1-complemented in $X^{***}$ via $\kappa_X^*$; a complemented $c_0$ would lift to a complemented $c_0$ in $\ell_\infty=c_0^{**}$, contradicting Phillips–Sobczyk).
5. **The implication.** For a dual space, **property (V) + no complemented $c_0$ $\Rightarrow$ Grothendieck** [L, standard]. The $c_0$-direction: $\Theta\colon X\to c_0$ not weakly compact $\Rightarrow$ fixes $c_0$ $\Rightarrow$ complemented $c_0$ in $X$ — impossible. The Schur property of $\ell_1=c_0^*$ is essential here (see §7, why order-$p$ fails).

**Net reduction:** the whole problem $=$ the **corona lemma**:
$$\boxed{\text{weak*-null singular } (\sigma_k)\subseteq \mathcal C_p^* \ \Longrightarrow\ \text{weakly null.}}$$

### The contradiction engine [R]
If $(\sigma_k)$ weak\*-null, not weakly null, then not rwc. Suppose one can produce a **disjoint-block witness**: operators $T_j$ in the unit ball with pairwise disjoint column-supports $C_j$ and row-supports $R_j$, $|\sigma_{k_j}(T_j)|\ge\delta$, and tail control $|\sigma_{k_j}(\sum_{i\ne j}\epsilon_iT_i)|<\delta/2$. Disjoint supports make $T=\sum_i\epsilon_iT_i$ bounded ($\|T\|=\sup_i\|T_i\|$, since $\|Tx\|_p^p=\sum_i\|T_iP_{C_i}x\|_p^p\le\|x\|_p^p$), and $\sigma_{k_j}(T)\ge\delta/2$ for all $j$ contradicts $\sigma_{k_j}(T)\to0$. **So the corona lemma reduces to producing this disjoint-block witness from "weak\*-null + not rwc"** — the *disjointification lemma*. (Caveat: singular functionals are NOT SOT-continuous, so the tail estimate must be delivered by the disjointification, not term-by-term.)

---

## 2. What is PROVED

- **[R] Diagonal part of the corona is weakly null.** The diagonal expectation $\mathbb E\colon\mathcal B(\ell_p)\to\ell_\infty$, $\mathbb E(T)=\sum_n T_{nn}\,e_n\otimes e_n^*$, is a norm-1 projection (all $p$; average over sign-isometries). For singular $\sigma$, $\bar a\mapsto\sigma(D_a)$ is a measure $\mu_\sigma\in M(\mathbb N^*)=(\ell_\infty/c_0)^*$. Weak\*-null $\Rightarrow\mu_{\sigma_k}$ weak\*-null; since **$\ell_\infty/c_0=C(\mathbb N^*)$ is Grothendieck** (Grothendieck–Seever; $\mathbb N^*$ an F-space), $\mu_{\sigma_k}\to0$ weakly, so $\sigma_k\circ\mathbb E\to0$ weakly.
  - **Consequence:** the corona lemma reduces to **off-diagonal** singular functionals (vanishing on the masa $\ell_\infty$). The whole $\beta\mathbb N$/corona/set-theoretic part is handled. *Only off-diagonal operator structure remains.*
  - Each individual diagonal $T\mapsto T^{(d)}$ (entries $T_{n,n+d}$, extracted by torus averaging, norm $\le1$) gives a weakly-null part too — **but they don't recombine**: triangular truncation is unbounded and $(\|T^{(d)}\|)_d\notin\ell_q$ uniformly, so the off-diagonal does NOT decompose into diagonals.

- **[R] The model family is isometrically $\ell_{p'}$.** $\sigma_k(T)=\lim_{\mathcal U}T_{n+k,n}$ (single off-diagonals at infinity) satisfies $\|\sum_k a_k\sigma_k\|=\|a\|_{p'}$ exactly (upper bound = per-column Hölder; lower bound = lattice-disjoint windows via a residue-class trick). Since $1<p'<\infty$, the span is reflexive, so $(\sigma_k)$ is weakly null. **Uniform in $p$; uses Hölder + lattice disjointness, NO Hilbert structure.** Also $\sum_k|\sigma_k(T)|^p\le\|T\|^p$ (the "column $\ell_p$-capacity" bound).

- **[R] Condition (A): $W_q=(\bigoplus_n\ell_q^n)_{\ell_\infty}$, the key case.** $W_q$ is complemented in $\mathcal B(\ell_q)$ (necessary condition). It's a dual space, predual $(\bigoplus\ell_{q'}^n)_{\ell_1}$ is L-embedded, reduce to corona as above. **Single-ultrafilter singular functionals $\sigma_k(\cdot)=\lim_{\mathcal U}\langle x_n,f_n^{(k)}\rangle$ are isometric to a sequence in the ultraproduct $(\ell_{q'}^n)_{\mathcal U}=L^{q'}(\mu)$, which is uniformly convex hence REFLEXIVE, hence weakly null.** This is the cleanest result of the investigation. *Mechanism: with no operator structure, singular functionals are vector values at infinity, landing in a reflexive ultraproduct.*
  - **[L] General condition (A): SETTLED (found 2026-07-07).** Räbiger (1985, Sitzungsber. Heidelb. Akad.): $\ell_\infty(\Gamma, L_p(\mu))$ is Grothendieck for all $1<p<\infty$, any $\Gamma,\mu$. Leung (PAMS 1988) generalized to $\ell_\infty(\Gamma,E)$ for countably order-complete Banach lattices $E$ with (technical conditions satisfied by) Orlicz spaces with WSC dual. Now $W_q=(\bigoplus\ell_q^n)_{\ell_\infty}$ is **1-complemented in $\ell_\infty(\ell_q)$** via $(x_n)\mapsto(P_nx_n)$ (coordinate truncations), and the Grothendieck property passes to complemented subspaces and quotients. Hence **$W_q$ AND the corona bundle $Q=W_q/(\bigoplus\ell_q^n)_{c_0}$ are Grothendieck for all $1<q<\infty$** — the full necessary-condition family, subsuming the single-ultrafilter computation above. (My Cembranos-blocking heuristic was the right instinct; the real proof is lattice-theoretic.) Related: Leung–Räbiger (Illinois J. Math): if $(\bigoplus_\gamma E_\gamma)_{\ell_\infty}$ has property (V), it is Grothendieck iff each $E_\gamma$ is (modulo real-valued measurable cardinals). Still open in general: **Kucher's problem** (González–Kania survey, Problem 29): is $\ell_\infty(E)$ Grothendieck for every superreflexive $E$? Our $W_q$ sits in the settled $L_p$-lattice corner of it; §2.5 contributes the no-$\ell_1$ half in general.

- **[S] ARO (asymptotically-rank-one) families.** For $\sigma_k(T)=\lim_{\mathcal U}T_{r_m(k),c_m(k)}$: failure of the $\ell_p$-capacity bound forces (via **König duality** — no small line-cover $\Rightarrow$ large matching) a partial-permutation subfamily, whose signed sub-permutation cover is an $\ell_p$-contraction breaking weak\*-nullity. Near-proof; gap is a König/ultrafilter simultaneity step.

### 2.5 NEW (2026-07-07): the u.c. cut lemma; no weak\*-null $\ell_1$ in duals of uniformly convex $\ell_\infty$-sums [R]

**Setting.** $W=(\bigoplus_n E_n)_{\ell_\infty}$, each $E_n$ uniformly convex with a **common** modulus $\delta(\cdot)$ ($\delta(t)>0$ for $t>0$; dimensions arbitrary, no lattice structure assumed). For $A\subseteq\mathbb N$, $\pi_A x = \mathbf 1_A\cdot x$ is an M-projection on $W$, so for **every** $s\in W^*$: $\|s\|=\|s\pi_A\|+\|s\pi_{A^c}\|$. Hence $\mu_s(A):=\|s\pi_A\|$ is a finitely additive measure on $\mathcal P(\mathbb N)$ with $\mu_s(\mathbb N)=\|s\|$ (the *variation of $s$ over the base*). Weak\*-null means $\sigma_k(x)\to0$ for all $x\in W$ (no predual needed; $E_n$ u.c. $\Rightarrow$ reflexive $\Rightarrow$ $W=((\bigoplus E_n^*)_{\ell_1})^*$ anyway).

**Cut Lemma [R].** *Let $\sigma,\tau\in W^*$, $\|\sigma\|=\|\tau\|=1$, and suppose both $\|\sigma+\tau\|\ge2(1-\eta)$ and $\|\sigma-\tau\|\ge2(1-\eta)$. Then for every $t\in(0,1)$ there is $A\subseteq\mathbb N$ with*
$$\|\tau\pi_A\|\ \ge\ 1-\big(3\eta+\tfrac t2\big),\qquad \|\sigma\pi_A\|\ \le\ \frac{3\eta}{\delta(t)}.$$
*In particular, with $\beta(\eta):=\inf_{t}\max\{3\eta/\delta(t),\,3\eta+t/2\}\to0$ as $\eta\to0$: bi-directionally near-$\ell_1$ pairs are $\beta$-base-separated.*

*Proof.* Pick $x,y\in B_W$ with $(\sigma+\tau)(x)\ge2-3\eta$ and $(\sigma-\tau)(y)\ge2-3\eta$. Since each functional has norm $1$: $\sigma(x),\tau(x),\sigma(y)\ge1-3\eta$ and $\tau(y)\le-(1-3\eta)$. Put $z=(x+y)/2\in B_W$, so $\sigma(z)\ge1-3\eta$, and set $A:=\{n:\|x_n-y_n\|_{E_n}\ge t\}$.
(a) Off $A$ the coordinates of $x-y$ have norm $<t$, so $|\tau(\pi_{A^c}(x-y))|\le t$, while $\tau(x-y)\ge2-6\eta$; since $\|\pi_A(x-y)\|\le2$, $\|\tau\pi_A\|\ge\frac{2-6\eta-t}{2}=1-3\eta-\frac t2$.
(b) On $A$, uniform convexity gives $\|z_n\|\le1-\delta(t)$; hence
$1-3\eta\le\sigma(z)=\sigma(\pi_Az)+\sigma(\pi_{A^c}z)\le\|\sigma\pi_A\|(1-\delta(t))+\|\sigma\pi_{A^c}\|=1-\delta(t)\|\sigma\pi_A\|$, so $\|\sigma\pi_A\|\le3\eta/\delta(t)$. $\square$

**Theorem A [R].** *$W^*$ contains no weak\*-null sequence equivalent to the unit vector basis of $\ell_1$.*

*Proof.* Suppose $(\sigma_k)$ is weak\*-null and $\ell_1$-basic. Fix $\eta\in(0,\tfrac18]$ with $\beta:=\beta(\eta)\le\tfrac18$. By James's non-distortion of $\ell_1$, pass to normalized **blocks** $(\sigma_i')$ that are $(1+\eta)$-equivalent to the $\ell_1$-basis, i.e. $\|\sum c_i\sigma_i'\|\ge(1-\eta)\sum|c_i|$; blocks of a weak\*-null sequence with uniformly $\ell_1$-bounded coefficients are again weak\*-null. Rename $\sigma_i:=\sigma_i'$, $\mu_i:=\mu_{\sigma_i}$ ($\mu_i(\mathbb N)=1$). Dichotomy on the variations:

**Branch 1 (disjoint humps — the "vector Phillips" step; uses neither u.c. nor $\ell_1$-ness).** Suppose there are $\delta>0$, disjoint $(A_j)$ and a subsequence $(i_j)$ with $\mu_{i_j}(A_j)\ge\delta$. By **Rosenthal's lemma** [Diestel–Uhl I.4.1] there is an infinite $M$ with $\mu_{i_j}\big(\bigcup_{l\in M,\,l\ne j}A_l\big)<\delta/4$ for $j\in M$. Pick $x_j\in B_W$ supported in $A_j$ with $\sigma_{i_j}(x_j)\ge\tfrac34\mu_{i_j}(A_j)\ge\tfrac34\delta$ (norming for $\|\sigma\pi_{A_j}\|$), and set $x:=\sum_{j\in M}x_j\in B_W$ (disjoint supports, sup-norm). Then for $j\in M$: $\sigma_{i_j}(x)\ge\tfrac34\delta-\tfrac14\delta=\tfrac\delta2$, contradicting weak\*-nullity.

**Branch 2 (uniformly exhaustive variations).** Otherwise $\sup_i\mu_i(A_j)\to_j0$ for every disjoint $(A_j)$ (a single f.a. $\mu_i$ can put mass $\ge\delta$ on at most $1/\delta$ disjoint sets, so violating indices must $\to\infty$ — Branch 1). Bounded uniformly exhaustive (= uniformly strongly additive) sequences of f.a. measures on a $\sigma$-field admit a **control measure** $\lambda$ with $\{\mu_i\}$ uniformly $\lambda$-continuous [Diestel–Uhl §I.5, via Rosenthal's lemma]. Pass to the Radon extensions $\hat\mu_i,\hat\lambda$ on $\beta\mathbb N$ (Stone space of $\mathcal P(\mathbb N)$; clopens $\leftrightarrow$ subsets of $\mathbb N$); uniform continuity transfers from clopens to Borel sets by regularity. So the densities $f_i:=d\hat\mu_i/d\hat\lambda\in L^1(\hat\lambda)$ form a bounded **uniformly integrable** family; by Dunford–Pettis it is relatively weakly compact: WLOG $f_i\to f$ weakly in $L^1(\hat\lambda)$. By Mazur, choose successive convex blocks $g_k=\sum_{i\in F_k}a_if_i$ ($F_1<F_2<\dots$, $a_i\ge0$, $\sum_{F_k}a_i=1$) with $\|g_k-f\|_1\to0$, and set $u_k:=\sum_{i\in F_k}a_i\sigma_i$, so $1-\eta\le\|u_k\|\le1$.
*Density comparison:* $\mu_{u_k}\le\sum_{F_k}a_i\mu_i$ on $\mathcal P(\mathbb N)$, hence $\hat\mu_{u_k}\le\sum a_i\hat\mu_i$ on Borel sets, so $f_{u_k}:=d\hat\mu_{u_k}/d\hat\lambda\le g_k$ a.e., while $\int f_{u_k}=\|u_k\|\ge1-\eta=\int g_k-\eta$; therefore $\|g_k-f_{u_k}\|_1\le\eta$.
*Cut:* for $k\ne k'$ the normalizations $\hat u_k=u_k/\|u_k\|$, $\hat u_{k'}$ satisfy $\|\hat u_k\pm\hat u_{k'}\|\ge(1-\eta)\big(\tfrac1{\|u_k\|}+\tfrac1{\|u_{k'}\|}\big)\ge2(1-\eta)$ (disjoint index blocks of a $(1+\eta)$-$\ell_1$ sequence). The Cut Lemma yields $A$ with $\|u_{k'}\pi_A\|\ge(1-\beta)(1-\eta)$ and $\|u_k\pi_A\|\le\beta$. Hence on $\hat A\subseteq\beta\mathbb N$:
$$\int_{\hat A}g_{k'}\ \ge\ \int_{\hat A}f_{u_{k'}}\ \ge\ (1-\beta)(1-\eta),\qquad \int_{\hat A}g_k\ \le\ \int_{\hat A}f_{u_k}+\eta\ \le\ \beta+\eta.$$
But $\|g_k-g_{k'}\|_1\to0$, while the two integrals differ by $\ge(1-\beta)(1-\eta)-(\beta+\eta)\ge\tfrac{49}{64}-\tfrac14>\tfrac13$: contradiction. $\square$

**Corollary (partial answer to Kucher's Problem 29) [R].** For every superreflexive $E$ (renorm u.c. by Enflo; the adjoint of the coordinatewise isomorphism transports weak\* topologies), **no weak\*-null sequence in $\ell_\infty(E)^*$ is an $\ell_1$-sequence.** Same for $(\bigoplus E_n)_{\ell_\infty}$ with a common modulus after renorming — e.g. Schatten summands $S_q^n$.

**Remarks.**
- **Where the mechanism lives.** Branch 1 is Phillips-type and holds for arbitrary summands; ALL the geometry is in the Cut Lemma, which needs exactly uniform convexity of the $E_n$ (of the *spaces*, not their duals). Failure is sharp: for $E_n=\ell_1^n$ the dual pair $f=(1,1),\,g=(1,-1)\in\ell_\infty^2$ is bi-directionally $\ell_1$ with **no** base separation — precisely the diagonal-$\ell_\infty^n$ fiber obstruction of condition (B) (§3), and consistent with Kania's counterexample being built from $\ell_1^n$'s. $\mathcal B(\ell_q^k)$ contains the diagonal $\ell_\infty^k$ isometrically (not even strictly convex), so the lemma stalls exactly at condition (B).
- **What is still missing for full Grothendieck of non-lattice u.c. sums** (e.g. $(\bigoplus S_q^n)_{\ell_\infty}$): only the *ghost half* — every weak\*-null **weakly Cauchy** sequence in the singular part $Z^\perp=((\bigoplus E_n)_{c_0})^\perp$ is weakly null; this would follow from WSC (or L-embeddedness) of $Z^\perp$. For $L_p$/Orlicz lattices Räbiger–Leung close this half by lattice methods. By Rosenthal's dichotomy + Theorem A, **Grothendieck $=$ Theorem A $+$ ghost half**; the sketchy direct-integral route to the ghost half (fibers $=$ reflexive ultraproducts over a control measure, Bochner-$L^1$ rwc theory) looks classical-assemblable but is NOT written down — status [S].
- **New crisp intermediate problem ("quantized condition (A)"):** is $(\bigoplus_n S_q^n)_{\ell_\infty}$ Grothendieck for $q\ne2$? Strictly between settled (A) and the kernel (B): non-lattice (so Räbiger–Leung don't apply), but u.c. summands (so Theorem A applies — no weak\*-null $\ell_1$). At $q=2$: $S_2^n=\ell_2^{n^2}$, known.
- **$p$-cut calculus on $\mathcal B(\ell_p)$ itself.** One-sided (column) cuts are not M-projections but satisfy $\|T\|\le(\sum_i\|TP_{B_i}\|^{p'})^{1/p'}$, dually $\sum_i\|\sigma(\cdot P_{B_i})\|^{p}\le\|\sigma\|^{p}$ — re-deriving the column $\ell_p$-capacity bound of the model family (§2) as a *structure* statement: column-disjoint singular families are $\ell_{p'}$-dominated, never $\ell_1$. Bi-disjoint block compressions ARE L-additive ($\sum_i\|\sigma(P_{R_i}\cdot P_{C_i})\|\le\|\sigma\|$) but non-exhaustive (off-block mass is lost; triangular truncation unbounded), and the block fibers $\mathcal B(\ell_p^k)$ are not u.c. — so the cut machinery reduces the kernel to condition (B) yet again, now mechanistically.

---

## 3. The open kernel

> **Bi-factor disjointification lemma ($\ell_p$-Pfitzner).** A weak\*-null, not-rwc sequence of *off-diagonal* singular functionals on $\mathcal B(\ell_p)$ admits a disjoint-block witness (§1). Equivalently: a weak\*-null sequence in (the relevant part of) $N(L^q(\mu))$ is relatively weakly compact.

**Equivalent forms** (all shown equivalent / sufficient during the investigation):
- cotype-$p$ bound $\sum_k|\sigma_k(T)|^p\le C\|T\|^p$ (i.e. $\ell_{p'}$-domination of $(\sigma_k)$) — **sufficient**, possibly stronger than needed;
- the evaluation map $\Theta\colon\mathcal B(\ell_p)\to c_0,\ \Theta(T)=(\sigma_k(T))$, **factors through a reflexive $L_p$** (a non-commutative Maurey factorization);
- "no weak\*-null $\ell_1$-sequence of singular functionals" $+$ WSC of $\mathcal C_p^*$;
- the WSC of $\mathcal C_p^*$ itself reduces (3-space property + the proven diagonal piece) to the **off-diagonal quotient**.

For $p=2$ this lemma is **Pfitzner 1994** (spectral excision + SVD). For $p\ne2$ it is open.

**Progress note (2026-07-07).** In the third equivalent form above, the first conjunct — "no weak\*-null $\ell_1$-sequence of singular functionals" — is now a **theorem at the $\ell_\infty$-sum level** for arbitrary uniformly convex summands (§2.5, Theorem A), by lattice-free cut methods. At the full $\mathcal B(\ell_p)$ level both conjuncts remain open: the bi-factor cut structure is only sub-L-additive (§2.5, last remark), which is another exact fingerprint of the (B)-obstruction.

**Why it's hard — the off-diagonal / $p=2$ specialness.** L-disjointness in $N(\ell_p)$ is NOT coordinate (bi-)disjointness: the **Hadamard rotation** $h\otimes h$ gives L-orthogonal but non-bi-disjoint nuclear operators (at $p=2$ these are SVD-disjoint; for $p\ne2$ they are genuinely rotated). The transition is exhibited cleanly by ultraproducts:
- **(A) space summands $\ell_q^n$**: dual $\ell_{q'}^n$ **uniformly convex** $\Rightarrow$ fiber $(\ell_{q'}^n)_{\mathcal U}=L^{q'}$ **reflexive** $\Rightarrow$ easy.
- **(B) operator summands $M_n^{(q)}$**: dual $N(\ell_q^n)\supseteq\ell_1^n$ (diagonal nuclear ops, $\|D_a\|_N=\|a\|_1$) **not uniformly convex** $\Rightarrow$ fiber $(N(\ell_q^n))_{\mathcal U}=N(L^q(\mu))$ **non-reflexive** $\Rightarrow$ reflexivity argument breaks $\Rightarrow$ open. **Condition (B) is equivalent in difficulty to the whole problem.**

So the **dividing line is uniform convexity of the summands** (vindicated mechanistically): uniformly convex $\Rightarrow$ reflexive fiber $\Rightarrow$ Grothendieck; the matrix algebra fails it precisely because of the off-diagonal/diagonal-$\ell_\infty^n$ content.

---

## 4. The "$p=2$ is special" signature

Every orthogonality/averaging tool that proves the $p=2$ case has no $p\ne2$ analogue, for a structural reason:

| tool (works at $p=2$) | why $p=2$ | $p\ne2$ obstruction |
|---|---|---|
| spectral excision (Pfitzner) | functional calculus, positivity | none |
| SVD / bi-factor disjointness | orthogonal singular subspaces | L-disjoint $\ne$ coordinate-disjoint (Hadamard) |
| symmetry / averaging | rich unitary group | only signed permutations (**Lamperti**) |
| randomization + hypercontractivity | Rademacher chaos $\to$ Hilbert–Schmidt $=$ operator norm | chaos sees HS, **blind to $\ell_p$** geometry |
| non-commutative Maurey factorization | Pisier–Haagerup via $C^*$ | open for $\ell_p$-operator algebras |

**The $p\ne2$ substitute that DOES work uniformly: lattice disjointness** (disjoint coordinate supports $\Rightarrow$ norm $=$ sup), available from $\ell_p$'s unconditional basis. This is the right orthogonality-replacement; it powers the model family and the cover argument. The gap is making it deliver a *uniform (rank-free) constant* for growing rank — which is where **uniform convexity of $\ell_p$** should enter (it's the one asymptotic invariant preserved with the same modulus by the ultrapower that resolves the bidual).

---

## 5. Approaches tried — fates

- **Property (V) + dual-space** [R architecture] — correct; reduces to the kernel.
- **WSC of $\mathcal C_p^*$** — would suffice with "no $\ell_1$"; itself $C^*$-dependent at $p=2$ (Calkin is a $C^*$-algebra $\Rightarrow$ vN-predual $\Rightarrow$ L-embedded $\Rightarrow$ WSC). For $p\ne2$ not automatic; reduces (3-space) to the off-diagonal. NOT actually needed — property (V) route avoids it.
- **Random Lamperti signs + hypercontractivity** [DEAD] — $\mathbb E_\varepsilon|\sigma(D_\varepsilon T D_\varepsilon)|^2\sim\sum_{ij}|T_{ij}|^2|\nu_{ji}|^2$ is Hilbert–Schmidt-weighted; HS $\ne\ell_p$ operator norm for $p\ne2$. Randomization collapses to $p=2$.
- **Exotic ideal quotients** [VOID] — I wrongly thought $\mathcal B(\ell_p)$ had $2^{\mathfrak c}$ closed ideals. **Correction (Gohberg–Markus–Fel'dman):** $\mathcal K(\ell_p)$ is the UNIQUE proper closed ideal of $\mathcal B(\ell_p)$, $1\le p<\infty$ — SAME as $\mathcal B(\ell_2)$. (Pitt: operators $\ell_p\to\ell_2$ are compact for $p>2$, so the $\ell_2$-factorable ideal $=\mathcal K$.) The many-ideals results are for $\mathcal B(\ell_p\oplus\ell_q)$, $\mathcal B(L_p)$, not single $\ell_p$. So the Calkin $\mathcal C_p$ is the only quotient and is simple; *the ideal structure is identical to $p=2$, the difference is purely geometric.* No exotic counterexamples.
- **Condition (A) via ultraproduct** [R key case] — proved; confirms uniform convexity = dividing line.
- **Order-$p$ Pełczyński property** [DEAD] — too weak: $V_p$ + no compl $c_0$ does NOT give Grothendieck, because the order-$p$ argument routes through reflexive $\ell_p$ (no Schur), losing the $c_0$-detection. Grothendieck is intrinsically an **order-1 / $c_0$** phenomenon; the $\ell_p$-tailored order-$p$ is orthogonal to it.
- **Hadamard / Hausdorff–Young** [R, defensive] — rotated L-orthogonal families are NOT counterexamples: diagonal ones see $I$ (not weak\*-null); off-diagonal ones can't be $\ell_1$ because the common-norming cover is a Hadamard-conjugated permutation of $\ell_p$-norm $\sim d^{|1/p-1/2|}\to\infty$. $\ell_p$ rigidity shields $p\ne2$.

---

## 6. Counterexample search — exhausted

Every natural source has been closed:
- asymptotic-$\ell_1$ engine (BKL) — absent (superreflexivity);
- coordinate-disjoint families — killed by the cover (König);
- rotated/Hadamard families — killed by Hausdorff–Young rigidity;
- exotic ideal quotients — don't exist (GMF; unique ideal $\mathcal K$).

No counterexample mechanism survives. This asymmetry (counterexamples consistently die; the proof consistently almost-works) is the main reason for leaning YES.

---

## 7. Honest assessment & suggested next steps

**Lean ~82% YES.** For: superreflexivity blocks the only known counterexample engine; predual L-embedded + WSC; diagonal/corona provably fine; condition (A) proven; ideal structure identical to $p=2$; lattice disjointness is a working $p$-uniform orthogonality-substitute. Against: the kernel is genuinely unproven and of Pfitzner-level depth; the recurring $p=2$ signature (SVD/orthogonality/HS) leaves a real chance that $p=2$ is the *only* Grothendieck case.

**The single remaining theorem to prove (or refute):**
> Bi-factor lattice disjointification on $L^q(\mu)$ with a constant depending only on the modulus of convexity — equivalently, a **non-commutative Maurey / $p$-summing factorization for $\ell_p$-operator algebras** (the analogue of Pisier–Haagerup's $C^*$ result).

**Concrete next directions (ranked; updated 2026-07-07):**
1. **Non-commutative Maurey factorization for $\mathcal B(\ell_p)$**: extend Pisier's non-commutative $p$-summing/Grothendieck theory (currently $C^*$/operator-space, $p=2$) to $\ell_p$-operator algebras. The operator-space $L_p$ Grothendieck theorem (Junge–Parcet, [arXiv:math/0505306](https://arxiv.org/abs/math/0505306)) factors cb-maps through *column ⊕ row* — structurally our off-diagonal decomposition; the gap is cb vs. plain bounded.
2. **Quantized condition (A): is $(\bigoplus_n S_q^n)_{\ell_\infty}$ Grothendieck?** New cleanest finite-effort target (replaces the old item 3, which is now DONE via Räbiger–Leung — see §2). Theorem A (§2.5) already gives the no-weak\*-null-$\ell_1$ half; what's missing is only the ghost/WSC half for the singular part — try (i) the direct-integral/Bochner-$L^1$ route sketched in §2.5, or (ii) L-embeddedness of $Z^\perp$ (is the singular part of an L-embedded space L-embedded? — check Pfitzner/HWW IV before working). A positive answer would be the first Grothendieck $\ell_\infty$-sum of genuinely non-commutative non-$C^*$ blocks — one floor below the kernel.
3. **Quantitative Grothendieck + interpolation in $1/p$ around $2$** ([arXiv:1605.04900](https://arxiv.org/abs/1605.04900); Kalenda–Spurný). A holomorphic-family Grothendieck modulus finite at $p=2$ could give a neighborhood — the first new case.
4. **The measure-theoretic form $\mathcal B(L^q(\mu))$** (the universal problem after ultrapower): for $q<2$, exploit stable/Gaussian kernel structure absent in $\ell_q$.
5. ~~Settle general condition (A)~~ **DONE 2026-07-07** (literature: Räbiger 1985 / Leung 1988 + 1-complementation of $W_q$ in $\ell_\infty(\ell_q)$; §2). Also write up Theorem A (§2.5) — it is plausibly a publishable note toward Kucher's Problem 29 regardless of the main problem.

---

## 8. Key references

- González–Kania, *Grothendieck spaces: the landscape and perspectives*, [arXiv:2102.03838](https://arxiv.org/abs/2102.03838) — survey, problem list; §5.4–5.5 for $\ell_\infty$-sums (Räbiger/Leung/Leung–Räbiger statements quoted there), Problem 29 (Kucher).
- F. Räbiger, *Beiträge zur Strukturtheorie der Grothendieck-Räume*, Sitzungsber. Heidelb. Akad. Wiss. (1985) — $\ell_\infty(\Gamma,L_p(\mu))$ is Grothendieck.
- D. H. Leung, *Weak\* convergence on higher duals of Orlicz spaces*, Proc. Amer. Math. Soc. 103 (1988) — $\ell_\infty(\Gamma,E)$ Grothendieck for suitable order-complete lattices $E$; Orlicz case.
- D. H. Leung, F. Räbiger, *Complemented copies of $c_0$ in $\ell_\infty$-sums of Banach spaces*, Illinois J. Math. — property (V) $\Rightarrow$ (Grothendieck $\iff$ summands Grothendieck).
- O. V. Kucher — the $\ell_\infty(E)$/superreflexive problem (via survey, Problem 29).
- Diestel–Uhl, *Vector Measures* (AMS Surveys 15) — Rosenthal's lemma (I.4.1), control measures for uniformly strongly additive sequences (§I.5).
- R. C. James — non-distortability of $\ell_1$ (used in §2.5).
- Kania, *A reflexive Banach space whose algebra of operators is not a Grothendieck space*, [arXiv:1211.2867](https://arxiv.org/abs/1211.2867).
- Beanland–Kania–Laustsen, *The algebras of operators on Tsirelson and Baernstein spaces are not Grothendieck*, [arXiv:1707.08399](https://arxiv.org/abs/1707.08399) — Lemma 2.2 (complemented $(\bigoplus X_n)_{\ell_\infty}$), Cor 2.3.
- Pfitzner, *Weak compactness in the dual of a $C^*$-algebra is determined commutatively* (Math. Ann. 1994) — $C^*$-algebras have (V).
- Pfitzner, *Phillips' lemma for L-embedded Banach spaces* (Arch. Math. 2010); *The dual of a non-reflexive L-embedded space contains $\ell^\infty$* ([arXiv:1004.0203](https://arxiv.org/abs/1004.0203)).
- Kalton–Werner, *Property (M), M-ideals, and almost isometric structure* — $\mathcal K(X)$ M-ideal characterization.
- Junge–Parcet, *Operator space Grothendieck inequalities for noncommutative $L_p$*, [arXiv:math/0505306](https://arxiv.org/abs/math/0505306).
- Cembranos / Freniche — $C(K,X)$ complemented $c_0$; $C(K)$ Grothendieck iff F-space-ish.
- Gohberg–Markus–Fel'dman — $\mathcal K$ unique proper closed ideal of $\mathcal B(\ell_p)$. Pietsch, *Operator Ideals*.
- Pełczyński's property (V\*) of order $p$, [arXiv:1607.02163](https://arxiv.org/abs/1607.02163) (tried; too weak — see §5).

---

*These notes summarize an exploratory investigation. The reduction (§1) and the proved cases (§2) I'm confident in; the kernel (§3) is genuinely open. Cross-check the [R] claims before building on them.*
