# Brief: the PSL(2,q) case, q ≡ 1 mod 4 — sharpest open target

Everything here is either proved by hand (P) or is an already-refereed result from swarm 2, with
the source file named (R). Nothing in this file is a conjecture unless it says so.

---

## 0. The statement to prove

Let $q$ be an odd prime power with $q \equiv 1 \pmod 4$ and $q \ge 13$. Let $K = \mathbb F_q$,
$\Omega = \mathbf P^1(K)$, $G = \operatorname{PGL}(2,q)$ acting on $\Omega$, and
$\mathbb G = \operatorname{PSL}(2,q) \le G$ the index-$2$ subgroup of elements whose matrix has
square determinant.

A set $S \subseteq G$ is a **clique** if $ab^{-1}$ is fixed-point-free on $\Omega$ for all
distinct $a,b \in S$; it is **valid** if $|S| = q$ and $1 \in S$. (Equivalently, by Lemma 1.2 of
m8, $\mathrm{ev}_x \colon S \to \Omega$, $s \mapsto s(x)$, is injective for every $x$; then the
**missing map** $f$ is the unique permutation with $f(x) \notin \{s(x): s \in S\}$, and
$T = S \cup \{f\}$ is sharply transitive.)

> **TARGET.** There is no valid clique $S \subseteq \mathbb G$.
>
> Equivalently: every valid $S \subseteq \operatorname{PSL}(2,q)$ satisfies $|{\langle S\rangle}| = q+1$ (so it is *good*, and in fact good inside a regular subgroup of $G$ that is not itself in $\mathbb G$).
>
> **Equivalently, geometrically (see §6):** no $q$ points of $\operatorname{PSL}(2,q) \subset \mathbf P^3$ have all joins external to the quadric $Q = \{\det = 0\}$.

**Why this is the crux** (m8, Theorem F). A counterexample to the full stability conjecture has
$\langle T\rangle \in \{A_{q+1}, S_{q+1}\}$, and the alternative $\langle T \rangle = A_{q+1}$
forces $S \subseteq \mathbb G$ and $\langle S\rangle = \mathbb G$. Moreover for $q \equiv 1 \pmod 4$
with $q \notin \{11,23,59\}$ the group $\mathbb G$ contains **no regular subgroup of order $q+1$
at all** (§3.3), so in that range *every* valid $S \subseteq \mathbb G$ is a counterexample:
TARGET is exactly equivalent to the stability conjecture restricted to this arithmetic case.
$q = 9$ is precisely the known failure ($\mathbb G = A_6$; 180 of the 828 valid sets lie in it,
and they are exactly the 180 bad ones).

---

## 1. Conventions and notation

* $K = \mathbb F_q$, $\Omega = K \cup \{\infty\}$, $|G| = q(q^2-1)$, $|\mathbb G| = q(q^2-1)/2$.
* For $s = [M] \in G$: **elliptic** = fixed-point-free on $\Omega$ = characteristic polynomial
  irreducible = the ratio of eigenvalues is *not* "realised over $K$" in the sense of §3.1.
* Normal form (m8, Theorem A): after right-translating by $u \in G$ (and $u$ can be taken in
  $\mathbb G$ without loss), $S = \{g_\beta = [\begin{smallmatrix}\beta & b_\beta\\ 1 & d_\beta\end{smallmatrix}] : \beta \in K\}$,
  $\Delta_\beta = \beta d_\beta - b_\beta \neq 0$, missing map $\varphi = f \circ u$ with
  $\varphi(\infty) = \infty$, $c = \varphi^{-1}|_K$.
* $\sigma$-dictionary (m8, Theorem B): $\sigma_y(\beta) = \Delta_\beta/(\beta-y) - d_\beta$ is a
  bijection $K \setminus \{y\} \to K \setminus \{c(y)\}$; **stability $\iff$ $c$ is affine**.
* $S \subseteq \mathbb G$ $\iff$ all $\Delta_\beta$ lie in the class $\mathrm{cl}(\det u)$; with
  $u \in \mathbb G$: $\iff$ **all $\Delta_\beta$ are squares** (m8, Theorem C(iii)). Since all
  $\Delta_\beta$ always lie in a single square class, "the clique is in $\mathbb G$" is a
  *square-class* condition — this is the only place the arithmetic enters.

---

## 2. The two reformulations worth keeping in mind

**(a) Parity form.** $\mathbb G = G \cap A_{q+1}$ for odd $q$ (m8, Lemma 3.2), i.e.

$$S \subseteq \mathbb G \iff \text{every } s \in S \text{ is an even permutation of } \Omega,$$

and then $f$ is even too, so $T \subseteq A_{q+1}$. Conversely $T \subseteq A_{q+1} \Rightarrow
S \subseteq \mathbb G$. So TARGET is: *no sharply transitive set of $q+1$ even permutations of
$\Omega$ has $q$ of its elements in $\operatorname{PGL}(2,q)$.*

**(b) Product-set/Sidon form.** Write $R = S\cdot S^{-1} \setminus \{1\}$, $|R| \le q^2-q$.
Verified exhaustively at $q = 4,5,7,9,11$ (m3): **good** $\iff |S\cdot S| = q+1 \iff |S\cdot S^{-1}| = q+1$;
**bad** $\iff |S\cdot S| = q^2$ and $|S\cdot S^{-1}| = q^2-q+1$. So in the bad case the maps
$S \times S \to G$, $(s,t) \mapsto st$, and $S\times S \to G$, $(s,t) \mapsto st^{-1}$ are
*injective* — $S$ is a **Sidon set of size $q$** (a "perfect difference set of the multiplicative
kind"). A proof of TARGET therefore has two cases:

* **good case**: $S$ sits in a coset of a regular subgroup $H$ of order $q+1$; then §3.3 kills
  $S \subseteq \mathbb G$ outright (a regular $H \subseteq \mathbb G$ does not exist, and if
  $S \subseteq H$ with $|S| = q > |H \cap \mathbb G| = (q+1)/2$ then $S \not\subseteq \mathbb G$).
  **So the good case of TARGET is already dead** (this is F3 recast; it needs no new idea).
* **bad case**: $S$ is a Sidon $q$-set of elliptic elements of $\mathbb G$ with $\langle S\rangle = \mathbb G$. **This is the whole remaining problem.**

It would already be a real theorem to prove: *a Sidon set of size $q$ in $\operatorname{PSL}(2,q)$
cannot consist of elliptic elements with pairwise elliptic ratios* — or even to prove that
$|S\cdot S| = q^2$ forces $\langle S\rangle \ne \mathbb G$.

---

## 3. Facts about $\operatorname{PSL}(2,q)$, $q$ odd (proved by hand — use freely, they are cheap and correct)

**3.1 Elliptic elements.**
For $[M] \in G$ with eigenvalues $\lambda,\mu$: split $\iff \lambda,\mu \in K \iff (\operatorname{tr} M)^2 - 4\det M$ is a square.
Traces $0$ are the ambiguous case: the involution $[M]$ with $\operatorname{tr} M = 0$ is split iff $-\det M$ is a square.
The number of elliptic elements of $G$ is $q^2(q-1)/2$ (equivalently: $q(q-1)/2$ unordered
elliptic classes $[\rho], \rho \in \mathbb F_{q^2}^\times \setminus K^\times$ up to inversion, with
class sizes summing correctly — check $q=9$: 324, the tabulated value).

**3.2 Involutions.**
An involution of $\mathbb G$ has $\operatorname{tr} = 0$ and square determinant, hence is elliptic
$\iff -1$ is a nonsquare $\iff q \equiv 3 \pmod 4$. Therefore, **for $q \equiv 1\pmod 4$ every
involution of $\mathbb G$ is split**, and consequently **every element of $S \setminus \{1\}$ has
odd order dividing $(q+1)/2$** (TARGET's range). At $q = 9$: all $8$ non-identity elements of a
bad set have order $5$ — consistent.

**3.3 Half-tori, and no regular subgroup of order $q+1$.**
The split tori of $\mathbb G$ are cyclic of order $(q-1)/2$, the non-split ones cyclic of order
$(q+1)/2$; every elliptic element of $\mathbb G$ lies in a unique non-split torus, and
$C_{\mathbb G}(t) = T$ for $t \in T \setminus \{1\}$. Consequently:
* $\#$ non-split tori $= q(q-1)/2$; $\#$ elliptic elements $= q(q-1)^2/4$.
* $N_{\mathbb G}(T) \cong D_{q+1}$ (order $q+1$), acting on $\Omega$ with **two orbits of size $(q+1)/2$** — so it is *not* regular.
* An element of order $q+1$ in $G$ is semisimple non-split with determinant a generator of $K^\times$; hence it is not in $\mathbb G$ for $q > 3$. So $\mathbb G$ has **no cyclic subgroup of order $q+1$**.
* Hence, by Dickson, for $q \equiv 1 \pmod 4$, $q \notin \{11,23,59\}$: **$\mathbb G$ has no subgroup of order $q+1$ that is transitive on $\Omega$** — the two candidates $C_{q+1}, D_{q+1}$ are excluded by the two bullets above and $A_4,S_4,A_5$ occur only at $q=11,23,59$.

**3.4 Every non-identity element of $S$ is a derangement,** because $1 \in S$ and $s\cdot 1^{-1} = s$
must be elliptic. Also $f$ is a derangement ($f(x) = x$ would force some $s \in S$ to fix $x$,
but $1$ does and it is unique by injectivity of $\mathrm{ev}_x$). Hence **$T = S\cup\{f\}$ is a
sharply transitive set of $q+1$ permutations of $\Omega$ exactly one of which is not a
derangement.**

---

## 4. What sharp transitivity alone can never give (read this before choosing a direction)

**(P) The fundamental identity.** $T$ sharply transitive $\iff$
$$\sum_{t \in T} P_t = J \quad (\text{all-ones matrix}),\qquad\text{i.e.}\qquad \sum_{s\in S} P_s = J - P_f,$$
where $P_g$ is the permutation matrix of $g$ on $\Omega$.

**(P) The invisibility theorem.** Let $\pi$ be the permutation representation of $G$ on
$\mathbb C^\Omega$. Since $G$ is $2$-transitive, $\pi = 1 \oplus \mathrm{St}$ with both
multiplicities $1$, so by the double centraliser theorem the image of the group algebra is
$$\mathbb C[G]\pi \;=\; \operatorname{End}(1) \oplus \operatorname{End}(\mathrm{St}) \;=\; \{M : M\mathbf 1 = \lambda \mathbf 1,\ M^T\mathbf 1 = \lambda \mathbf 1 \text{ for one } \lambda\},$$
of dimension $1 + (q-1)^2$ — and it contains **every** permutation matrix of $\Omega$. Hence:

* "$\sum_{s \in S} P_s = J - P_f$" is satisfied by *every* valid clique, of either sign type; it carries **no** information about $S \subseteq \mathbb G$;
* the m5 identity $\bigl(\sum_{s\in S} P_s\bigr)^k = (-1)^k P_{f^k} + \frac{q^k - (-1)^k}{q+1}J$ is a formal consequence of it and is likewise empty;
* **the condition $S \subseteq \mathbb G$ is a sign/determinant condition, and the sign character of $G$ is not a constituent of $\pi$.** Therefore no argument that uses only the action of $G$ on $\Omega$ (spectral, Delsarte, LP, character-theoretic on $\pi$, "design" arguments, association schemes) can possibly prove TARGET. This is a theorem, not a heuristic: it is why all of §8 failed.

**Consequence.** Any proof of TARGET must use one of:
(i) the *linear* $2$-dimensional structure (traces, determinants, eigenvalues, the normal form), i.e. the geometry of §6;
(ii) the subgroup structure of $\mathbb G$ (tori, Borel subgroups, maximal subgroups, Dickson);
(iii) an argument that uses *more than the first two moments* of the pair structure — e.g. products of three or more elements, where the Sidon property bites.

---

## 5. The verified structural toolkit (refereed, from swarm 2)

* **Tangent lemma with defect** (m1/m4/m6/m7; verified 16032/16032 at $q=9$): for a clique $A$ with missing map $\varphi$ and elements whose four corner entries vanish as $a_1=0,b_2=0,c_3=0,d_4=0$, $\frac{b_1}{c_1}\frac{d_2}{a_2}\frac{a_3}{d_3}\frac{c_4}{b_4} = \Psi := \frac{\varphi^{-1}(0)\varphi(\infty)}{\varphi(0)\varphi^{-1}(\infty)}$. For sharply transitive sets $\Psi = 1$ (Eberhard's Lemma 2, formalized in `RequestProject/Lemma2.lean`).
* **Defect of translates** (m7 Thm 6): with $A_0 = f^{-1}(0)$, $B_0 = f^{-1}(\infty)$, $G(x) = f(x)\frac{B_0-x}{A_0-x}$: $\ \Psi(Su) = \frac{G(u(\infty))}{G(u(0))}$ for all $u \in G$; hence $\Psi \equiv 1 \iff G$ constant $\iff f \in G$. **This is the sharpest known "one free function" form of the conjecture.** Note $Su \subseteq \mathbb G$ for $u \in \mathbb G$, so in TARGET's setting the translates are restricted to a subgroup of index 2.
* **Triple-product criterion** (m1): $S$ is good $\iff$ no triple $g,h,k \in S$ has $hk^{-1}g$ hyperbolic.
* **Cap identity** (m5): $\operatorname{cap}_A(g) := \#\{x : g(x) \in A(x)\}$, $\ \sum_{g(x)=y}\operatorname{cap}_A(g) = q-1+\delta_{xy}$, $\ \sum_g \operatorname{cap}_A(g) = q^2$; good sets have $\max\operatorname{cap} = q-1$, bad $q=9$ sets have $\max \operatorname{cap} = 1$; large-cap theorem reduces (R1) $2\le\kappa\le q-2$, (R2) a transposition shape, (R3) Sidon.
* **Excess identity** (m6): for $n_i = \#\{t \in T\setminus\{g,h\} : \operatorname{agr}(gh,t) = i\}$, $\sum n_i = q-1$, $\sum i\,n_i = q+1$, hence $\sum (i-1)n_i = 2$.
* **Linear case** (m8 Thm E): if the $q$ points $[M_s] \in \mathbf P^3$ are collinear then $f \in G$. Good configurations need **not** be linear (m8 §6), so this is strictly weaker.
* **Spread bound**: $S \not\subseteq H$ (regular $H$) $\Rightarrow |S \cap H| \le (q+1)/2$ (verified $q \le 11$).
* **Anisotropy criterion** (m3): in the normal form $s_v = [\begin{smallmatrix}v & a_ve_v\\ 1 & e_v\end{smallmatrix}]$, $s_vs_w^{-1}$ elliptic $\iff \beta(v,w)^2 - 4Q(v)Q(w)$ is a nonsquare, with $Q(v) = e_v(v-a_v)$, $\beta(v,w) = e_w(v-a_w) + e_v(w-a_v)$; and $s_v$ elliptic $\iff (v-e_v)^2 + 4a_ve_v$ nonsquare. $a$ is always injective, $e$ is injective for odd $q$.

---

## 6. The geometry: $\operatorname{PSL}(2,q)$ as a hyperboloid in $\mathbf P^3$

This dictionary is standard but has not been written down in this project yet; it makes TARGET a
clean incidence statement. $V = M_2(K)$ with $Q(M) = \det M$, $\beta(M,N) = \operatorname{tr}(M\,\mathrm{adj}(N)) = \operatorname{tr}(MN^{-1})$ for $N \in SL_2$; $\beta(M,M) = 2\det M$. Then

* the points of $G = \operatorname{PGL}(2,q)$ are the points of $\mathbf P^3 = \mathbf P(V)$, and $Q$ cuts out the **hyperbolic quadric** $Q^+(3,q) = \{[M] : \det M = 0\}$ (the singular matrices);
* $\mathbb G = \{[M] : \det M \in (K^\times)^2\}$ is the set of points of $\mathbf P^3$ whose *unique* representative with $\det = 1$ exists, i.e. $\mathbb G = \{[M] : \det M = 1\}$ as a point set = the **"unit hyperboloid"**;
* for $s,t \in \mathbb G$ with lifts $M_s, M_t \in SL_2(K)$: $st^{-1}$ is elliptic $\iff \beta(M_s,M_t)^2 - \beta(M_s,M_s)\beta(M_t,M_t) = \beta(M_s,M_t)^2 - 4$ is a nonsquare $\iff$ the plane $\langle M_s, M_t\rangle$ is **anisotropic** $\iff$ the line $\overline{[M_s][M_t]}$ is **external** to $Q$.

So: **valid $S \subseteq \mathbb G$ = a set of $q$ points of the hyperboloid $\{\det = 1\}$ with all pairwise joins external to $Q^+(3,q)$** (a *partial flock of deficiency one* in the sense of m8's dictionary, with the extra arithmetic condition that the points lie on the hyperboloid).

Two immediate, useful consequences, both cheap:

* **External lines meet $\mathbb G$ in exactly $(q+1)/2$ points.** Every external line is $A \cdot \mathbb F_{q^2}^\times$ for some $A$ (a Singer cycle); its $q+1$ points are the classes $[AF]$, $F \in \mathbb F_{q^2}^\times/K^\times$. Since $\det(AF) = \det A \cdot N(F)$ with $N$ the norm, the square class of the determinant is constant on a point; the set $\{F : N(F) \in (K^\times)^2\}$ is a subgroup of $\mathbb F_{q^2}^\times$ of index $2$ that contains $K^\times$, hence gives exactly $(q+1)/2$ points on the line. So $q$ points of $\mathbb G$ are never collinear. (This kills the *collinear* good case transparently; the general good case is killed in §2(a) by counting $|S| = q > (q+1)/2 = |H \cap \mathbb G|$.)
* the **Gram matrix** $\Gamma = (\beta(M_s,M_t))_{s,t \in S}$ is a $q \times q$ symmetric matrix over $K$ with $\Gamma_{ss} = 2$ and $\Gamma_{st} \in \mathcal T := \{x \in K : x^2-4 \text{ nonsquare}\}$ for $s\ne t$ (note $2 \notin \mathcal T$), and $\operatorname{rank}\Gamma \le 4$. Conversely any such Gram data with rank $\le 4$ and the right square class of $\det$ gives points of $\mathbb G$. **So TARGET is equivalent to the non-existence of such a Gram matrix of rank $\le 4$ that also comes from points with square determinant.** The rank constraint is what a "linear-algebra over $\mathbb F_q$" attack should use; the *collinear* (Singer-cycle) case is exactly $\operatorname{rank} \le 2$, which is already impossible by the previous bullet.

---

## 7. Dead ends — do not spend time here (two full swarms burned on these)

1. **Wilson products / Segre tangent lemma alone.** The $q$-set (deficiency one) loses one factor; the resulting invariant is $\Psi$, and $\Psi = 1$ is not available — only the *translate* identity of §5 (m7). Naive adaptation gives the gap, not the theorem.
2. **Moments, spectral, Hoffman, Delsarte, LP, design theory, and character theory of the permutation representation** — provably impossible, see §4. (Also: moments 1–3 of the "agreement" statistics are Poisson(1) for *every* derangement; the Hoffman bound equals $v/(q+1)$ and is attained by Borel subgroups.)
3. **Cap/Sidon dichotomy pushed by counting alone** (m5): reduces to (R1) $2\le\kappa\le q-2$, (R2), (R3); (R1) genuinely fails at $q=5,7$, so no counting proof can work below $q\ge 11$ without new input.
4. **Product-set / approximate-subgroup theorems** (Kemperman, Helfgott, tripling): tried; the available exponents do not give structure at $|S| \sim |G|^{1/3}$.
5. **Loop/associator reformulation** (m3): no lever found in the loop axioms.
6. **Galois descent to prime fields** (m1): abandoned, no theorem.
7. **Retracted claims** (do not resurrect, they are FALSE): "$S\cap S^{-1} = \{1\}$ for bad $S$"; "every elliptic element is in $\mathbb G$"; "the $\mathbb G$-coset is odd iff $q\equiv 3$"; "reflections of $D_{2(q+1)}$ fix one point"; "$S \subseteq T$ in the dihedral case by Cauchy–Davenport" ($C_{q+1}$ is composite); "bad $q=9$ sets have $f$ of type $(8,2)$" (they are all $(4,4,2)$).

---

## 8. Directions that are open and not obviously blocked

Pick one, register it, and be brutally honest about whether it proves the TARGET or only a case.

**D1 (half-torus spread, dimension count).** $S \setminus\{1\}$ is $q-1$ elliptic elements of $\mathbb G$, each in a half-torus $C_{(q+1)/2}$ which contains only $(q-1)/2$ elliptic elements. Use the anisotropy criterion $(\beta^2 - 4Q(v)Q(w)$ nonsquare$)$ *and* the single-element constraint to bound the size of a clique that meets every half-torus in $\le 2$ elements. At $q=9$ that bound is attained ($q=9$, all 8 in distinct tori). **Question: what is the true maximum size of a clique of elliptic elements in $\operatorname{PSL}(2,q)$ for $q\equiv1\pmod4$?** If it is $\le q-1$ for $q\ge13$ then TARGET follows. No such bound exists in the literature that I know of; a proof would be new. Careful: it must be a *proof for all $q$*, not a computation.

**D2 (Sidon rigidity).** In the bad case $S$ is a *perfect* Sidon set ($|SS| = q^2$). Exploit injectivity of $S\times S \to G$ multiplicatively: consider the $q^3$ products $s_1s_2s_3$ and their collisions; a single forced collision contradicts Sidon. (m6's excess identity $\sum(i-1)n_i = 2$ already shows collisions are forced at the level of "agreement", so look for the same phenomenon at the level of *products*: e.g. show that some $s_1s_2 = s_3s_4$ with $(s_1,s_2)\ne(s_3,s_4)$ is forced by counting $|SS|$ against the structure of $\mathbb G$.)

**D3 (the $\mathbb G$-restricted defect).** In TARGET, $Su \subseteq \mathbb G$ for every $u \in \mathbb G$ (normality of $\mathbb G$ in $G$). m7's identity $\Psi(Su) = G(u(\infty))/G(u(0))$ then says: the "cross-ratio defect function" $G$ takes equal values at the pairs $\{u(\infty), u(0)\}$ for *all* $u \in \mathbb G$. That is a very rigid system of equations on the single function $G$ (a derangement-related rational function of one variable). If one can show it forces $G$ constant (i.e. $f \in G$) **without** using the translates outside $\mathbb G$, TARGET follows — this is the most "local" open route and it is the one m7 recommended. Warning: for $q=9$ the system is consistent (bad sets exist), so any such proof must lose at $q=9$ for a *specific reason* — identify it (probably the existence of the order-5 half-torus with $(q-1)/2 = 4$ elements and $8$ tori).

**D4 (Gram-matrix / quadratic-form attack, §6).** The $q\times q$ Gram matrix has diagonal $2$, off-diagonal in $\mathcal T$ (never $2$), rank $\le 4$. Look for a rank/arithmetic obstruction: e.g. compute $\det$ of a $5\times 5$ minor, or use the fact that $\operatorname{rank}\le 4$ forces a nontrivial linear relation $\sum_i \lambda_i M_{s_i} = 0$ in $M_2(K)$ and translate that relation back to Möbius data. (A $4$-term relation is "3 points collinear on a plane", a $q$-term relation is what one needs.)

**D5 (subgroup structure / maximal subgroups).** $S \subseteq \mathbb G$, $|S| = q$, $S$ generates $\mathbb G$. Use the maximal subgroups (Borel $q(q-1)/2$, dihedral $q+1$ and $q-1$, $A_4,S_4,A_5$) and the fact that $S \cap B_x = \{1\}$ for every point stabiliser $B_x$ (because every non-identity element of $S$ is a derangement). How large can a subset $S \subseteq \mathbb G$ with $S\cap \bigcup_x B_x = \{1\}$ and pairwise elliptic ratios be? Note $|S| = q$ is *much* larger than any subgroup of $\mathbb G$ whose non-identity elements are all derangements (max $(q+1)/2$).

**D6 (the $\mathbb G$-coset / determinant square-class bookkeeping).** In the normal form with $u \in \mathbb G$ all $\Delta_\beta$ are squares (m8 Thm C). The $\sigma$-dictionary is a statement about the *functions* $b_\beta, d_\beta$ only. So TARGET is a statement about functions $b,d \colon K \to K$ and the permutation $c$ they define:
> *for $q\equiv1\pmod4$, if $\sigma_y(\beta) = \Delta_\beta/(\beta-y)-d_\beta$ is a bijection $K\setminus\{y\}\to K\setminus\{c(y)\}$ for every $y$, and all $\Delta_\beta$ are squares, then $c$ is affine.*
That is a completely explicit finite-field problem with two unknown functions. Try to prove it directly (e.g. exploit $c$ affine $\iff$ $d$ affine $\iff$ ...; the system has a large symmetry group $u \mapsto u\circ w$, $w$ upper triangular).

**D7 (tori and reflections as a design).** The $q(q-1)/2$ half-tori come with their normalisers $D_{q+1} = T \cup (\text{split involutions})$. A split involution is never a ratio of two elements of $S$ (§3.2). Count incidences of $S$ with normalisers: each $s \in S\setminus\{1\}$ lies in exactly one $T$, hence in exactly one $N(T)$; the $(q+1)/2$ split involutions of $N(T)$ are all forbidden ratios. Use the forbidden-ratio structure together with $|S\cap N(T)|\le ?$ to bound $|S|$.

**D8 (a general theorem that would imply TARGET).** Any of:
* every Sidon set of size $q$ in $\operatorname{PSL}(2,q)$, $q$ odd, contains a split element (then $1\in S$ forces a split ratio);
* every $q$-set of elliptic elements of $\operatorname{PSL}(2,q)$ with pairwise elliptic ratios has $\langle S\rangle$ of order $q+1$;
* every sharply transitive set of $q+1$ even permutations of $q+1$ points, $q \equiv 1 \pmod 4$, contains at most $q-1$ Möbius maps.

**D9 (look for the $q\equiv 3$ asymmetry).** For $q \equiv 3 \pmod 4$ the target analogue is *false to state this way* ($D_{q+1}$ is regular and inside $A_{q+1}$). Understand exactly which step of a would-be proof uses $q\equiv1$; that step is where the theorem must live.

---

## 9. Rules of engagement

* **No computational verification of the conjecture for any value of $q$.** The person explicitly
  forbade it (their words: "Do not make verification for q=23 or any other value of q"). The data
  for $q \le 19$ is already tabulated and is in `results/stability.md`. You may use a small
  symbolic check to sanity-check a *lemma* or an identity, but never as evidence for the theorem,
  and never as a search for counterexamples.
* Do **not** restart, resume or re-read the two finished swarms as if they were live; their
  content is summarised in §5, §7 and in `.ultramath/smvrhlrqe/m*/`.
* A proof must be a proof for all $q \equiv 1 \pmod 4$, $q \ge 13$. A reduction of TARGET to a
  clean statement is a *reportable partial result* — say precisely what is reduced to what.
* Deliverables: `report.md` in your own member directory — (i) the precise statement you prove,
  (ii) the proof, (iii) the exact gap if incomplete, (iv) what you checked and how, (v) what you
  tried that failed. Register a *distinct* direction on the board before starting.
* Referee standard: someone else must be able to check every line. No "it seems", no "one can
  show" without the computation.

---

## 10. Referee log — corrections to this brief (added while swarm `smvrks9r0` runs)

Read this section before trusting §1 or §5 above. Each item was checked by hand and, where stated,
by brute force for small $q$ (lemma checks only — no verification of the conjecture).

**(R1) §5 "defect of translates" is a tautology: direction D3 is DEAD.** m9 proved (see
`.ultramath/smvrks9r0/m9/report.md`, Thm A) that
$$\Psi(u)=\frac{\varphi^{-1}(0)\varphi(\infty)}{\varphi(0)\varphi^{-1}(\infty)}=\frac{G(u(\infty))}{G(u(0))},\qquad
G(x)=f(x)\frac{B_0-x}{A_0-x},\ \varphi=f\circ u,$$
holds for **every injective** $f$ and every $u\in G$ — no clique hypothesis, no algebra of the tangent
lemma. Moreover (m9 Thm B) for all $\alpha\neq\beta$ there is $u\in\mathbb G$ with $u(0)=\alpha$,
$u(\infty)=\beta$ (the coset $\{u:u(0)=\alpha,u(\infty)=\beta\}$ is a coset of the diagonal torus,
which meets both determinant classes). Hence restricting to $u\in\mathbb G$ restricts nothing, and
the whole "defect system" excludes no $f$. What survives is only the trivial equivalence
"$\Psi\equiv1$ on all $u$ $\iff$ $G$ constant $\iff$ $f\in G$", which is the conjecture itself, not
a lever. **Do not build on D3 / the m7 identity.**

**(R2) §1's "all $\Delta_\beta$ always lie in a single square class" is FALSE.** Counterexample: the
Singer-cycle clique in normal form is
$$g_\beta=\begin{pmatrix}\beta&\delta\\1&\beta\end{pmatrix},\qquad \delta\ \text{a nonsquare},\qquad
\Delta_\beta=\beta^2-\delta,$$
and $\beta^2-\delta$ takes **both** square classes (checked for $q=5,7,11,13,17$; the set is a clique
— all pairwise quotients elliptic — in each case, and $\Delta_0=-\delta$ is a nonsquare while
$\beta^2=\delta$ never happens, so both classes occur as soon as $q\ge5$). The correct statement is
$$\operatorname{cl}(\Delta_\beta)=\operatorname{cl}(\det s_\beta)\cdot\operatorname{cl}(\det u),$$
so with $u\in\mathbb G$: $\ S\subseteq\mathbb G\iff$ all $\Delta_\beta$ are squares (this equivalence
is correct and is all that is used), but nothing forces a single class in general. (m8's Theorem
C(iii) as originally written is wrong in that clause; its equivalence is fine.)

**(R3) §5's anisotropy criterion is CORRECT as printed.** With $Q(v)=e_v(v-a_v)$ and
$\beta(v,w)=e_w(v-a_w)+e_v(w-a_v)$ (this is $\operatorname{tr}(A\operatorname{adj}B)$, which equals
$\operatorname{tr}A\operatorname{tr}B-\operatorname{tr}(AB)$): the identity
$\beta(A,B)^2-4Q(A)Q(B)=\det(B)^2\bigl(\operatorname{tr}(AB^{-1})^2-4\det(AB^{-1})\bigr)$ holds, so
the criterion is equivalent to irreducibility of the characteristic polynomial of $st^{-1}$ —
verified by brute force over *all* pairs for $q=7,11,13$ (63 252 / 1 208 900 / 3 502 512 pairs, zero
disagreements). A report that "the printed form makes $\beta^2-4Q(v)Q(w)$ a perfect square" is
wrong; ask for its computation.

**(R4) New proved theorems from this swarm (usable freely).**
* (m9 Thm D) For $q\equiv1\ (4)$, $q\ge13$: **every valid $S\subseteq\mathbb G$ generates
  $\mathbb G$**. Complete maximal-subgroup analysis (Borel; dihedral $q-1$; dihedral $q+1$; $A_4,S_4$
  impossible by orbit-size; $A_5$ only at $q=29$, killed by the ratio bound $15<28$ on
  $\mathrm{Cay}(A_5,\text{involutions})$; subfield groups give $|S|\le q_0+1<q$). So
  TARGET $\iff$ no valid clique *generating* $\mathbb G$ exists.
* (m9 Thm A+B) the defect identity is vacuous — see (R1).
* (m9 Thm C, Cor C2) **collision trichotomy**: for $g,h\in S\setminus\{1\}$, either $gh\in S$, or
  there is $t\in S\setminus\{g,h\}$ with $\#\mathrm{Fix}(t^{-1}gh)=2$ (then $t^{-1}gh$ is hyperbolic
  with multiplier $\Psi(Su)\neq1$), or $\#\mathrm{Fix}(f^{-1}gh)\ge3$ (then $f=gh\in G$, good case).
  In the bad case the third alternative is impossible, and Cor C2 shows some pair is in the second.
* (m10 Thm C) for $q\equiv1\ (4)$: if $tut^{-1}=u^{-1}$ with $u$ a non-involution then $t^2=1$;
  hence **no element of $S$ inverts a non-involution**, i.e. for every half-torus $T$, if
  $|S\cap T|\ge2$ then $S\cap N(T)\subseteq T$. Also **squaring is injective on the elliptic set**
  (one-line proof: $u^2=v^2$ with $u,v$ elliptic forces $u^2$ elliptic, hence $u^2$ lies in the
  unique half-torus $T_u=T_v$, on which squaring is injective since $(q+1)/2$ is odd).
* (m10 Thm B.1) for $s\neq t$: $(2+\beta_{st})(2-\beta_{st})$ is a nonsquare, so exactly one of
  $[M_s+M_t],[M_s-M_t]$ is a $\mathbb G$-point. Note this is *equivalent* to the clique condition
  (it is just $\beta^2-4$ nonsquare rewritten), so it is a restatement, not new leverage.

**(R5) Directions after the corrections.** D3 is dead (R1); D5 is largely done (R4, m9 Thm D).
Live: **D1** (half-torus spread, now with the no-inversion lemma R4), **D6** (explicit two-function
problem), **D2** (Sidon rigidity — m9 Thm E shows pure product counting cannot decide it, so it must
be combined with the agreement/collision structure of R4), **D4** (Gram/polar rank).

## 11. State of the campaign after the round-3 referee checks (swarm `smvrks9r0`)

Everything below is refereed-correct: proved by at least one member with the proof read, or
proved twice/three times independently, or checked numerically by me where stated.

**(P1) A valid clique spans $\mathbf P^3$; its Gram matrix has rank exactly 4.** Proved three times
independently (m2 Thm B, m5 (B), m6 Thm A). The key bound: an exterior set of $Q^+(3,q)$ contained
in a plane has at most $(q+3)/2$ points — through a point $p\notin C=\Pi\cap Q$ there are at most
$(q+1)/2$ external lines, and in a tangent plane every line meets $Q$. I read m2's proof and
checked the bound numerically (largest plane clique $4,4,7,7$ for $q=5,7,11,13$, against
$(q+3)/2=4,5,7,8$). Consequences: $X$ is never collinear, never coplanar, never inside a Singer
cycle, never inside the union of two intersecting external lines. **The linear case (m8 Thm E) and
every planar case are closed.**

**(P2) TARGET $\iff$ no valid clique generating $\mathbb G$.** Proved twice (m9 Thm D, m6 Thm D).
Complete maximal-subgroup analysis; the only survivor $A_5$ at $q=29$ is killed by the ratio bound
$15<28$ on $\mathrm{Cay}(A_5,\text{involutions})$.

**(P3) The defect-of-translates identity is vacuous.** Proved three times (m9 Thm A/B, m2 Thm C,
m5). It holds for every injective $f$, and every pair $(\alpha,\beta)$ is $(u(0),u(\infty))$ for some
$u\in\mathbb G$. D3 is dead; nothing follows from it.

**(P4) Pair-level data can never contradict anything.** For $q\equiv1\ (4)$ and $X\in SL_2(K)$
elliptic of odd order: $X=Y^2$ with $Y\in SL_2(K)$ elliptic, hence $X+I=\operatorname{tr}(Y)Y$ and
$$2+\operatorname{tr}X=\operatorname{tr}(Y)^2\ \text{is always a nonzero square},\qquad
2-\operatorname{tr}X=-(2+\operatorname{tr}X)^{-1}\operatorname{disc}(X)\ \text{is always a nonsquare}.$$
(m5 (C), m10 §6.2.) So the "$\pm$ square-class" colouring of pairs is constant and carries no
information: **any proof must use $\ge3$ elements.**

**(P5) Corrections to earlier text in this brief.**
* (m2) In the bad case $|S\cdot S| = q^2 - q + 1$, **not** $q^2$: with $1\in S$ the $q-1$ collisions
  $s\cdot 1 = 1\cdot s$ are forced, so $q^2-q+1$ is the maximum and the Sidon statement is
  "no collisions other than those".
* (m2) "$S\subseteq\mathbb G\Rightarrow f$ is even" is FALSE in general: at $q=9$ the bad sets have
  $f$ of cycle type $(4,4,2)$, which is odd, and $\langle T\rangle = S_{10}$. The evenness of $f$
  holds only in the alternative $\langle T\rangle = A_{q+1}$ (m8 Thm F).
* (m5) §1's "single square class" — corrected in (R2) above; and m5's own claim that the printed
  anisotropy criterion is a perfect square is WRONG (checked over all pairs at $q=7,11,13$).

**(P6) The reduction I now regard as the sharpest (m6 §7 + referee).** If every exterior set of size
$q$ of $Q^+(3,q)$ extended to one of size $q+1$, then TARGET would follow outright: a maximal
exterior set is (classically) a coset $cH$ with $H\cong C_{q+1}$ regular in $\mathrm{PGL}(2,q)$, so
$S\subseteq cH$, while $|cH\cap\mathbb G|=(q+1)/2<q$ kills $S\subseteq\mathbb G$. So **TARGET is the
deficiency-one extension problem for exterior sets of $Q^+(3,q)$, restricted to the square-determinant
half.** Count the admissible extension points of a $q$-set $X$: a point $p$ is admissible iff
$\beta(p,x)^2-4$ is a nonsquare for every $x\in X$; a character sum over the $q$ conditions, with
(P1) supplying rank 4, is the natural attack.

**(P7) Matrix form of the remaining case — CORRECTED (m5 (A) + referee; my earlier version was
wrong).** In the chart of m5 (A) put $\beta_{bg}:=D_b+D_g-(b-g)(d_b-d_g)$; then
$\beta_{bg}=\operatorname{tr}(M_b\operatorname{adj}M_g)$ is the Gram pairing and
$$W_{bg}:=\beta_{bg}^2-4D_bD_g$$
is the discriminant that the clique condition makes a nonsquare. I previously asserted
$W=\mathbf 1\hat E^{\mathsf t}+\hat E\mathbf 1^{\mathsf t}+B$ with $\hat E_b=D_b-b d_b$ and
$\operatorname{rank}W\le4$; **that is false** — that identity is for $\beta$, not for $W$. m5
refuted it with an explicit example ($b=(1,2,3,4,6)$, $d=(2,5,7,11,13)$, $D=(4,9,16,25,36)$:
$\det W_5\equiv-1384942737600\not\equiv0 \pmod{101}$ while $\det\Gamma_5=0$), which I reproduced.
The true statements: $\Gamma=(\beta_{bg})$ is a Gram matrix of $q$ points of $\mathbf P^3$, so
$\operatorname{rank}\Gamma\le4$ *automatically* and all its $5\times5$ minors vanish identically;
$W$ is quadratic in the $D_b$ and has rank $q$ generically. **So there is no rank obstruction on
$W$, and the "$5\times5$ minors force $d$ affine" programme is dead.** The correct rank-4 object is
$T_{bg}=\operatorname{tr}(M_bM_g^{-1})$: diagonal $2$, off-diagonal in
$\mathcal T=\{x:\chi(x^2-4)=-1\}$, rank exactly $4$ — which is just (P1) rescaled. The content of
the problem is entirely in those per-entry square classes, not in linear algebra over the Gram
matrix.

## 12. Referee log, round 4: two exhaustion results and one referee error

**(E1) The "two-way count" is circular — the counting program is exhausted (m9 §8, checked).** In the
bad case put $X=\#\{(g,h,t)\in(S\setminus\{1\})^3:\ t^{-1}gh$ has exactly two fixed points$\}$. Then
$$\frac{q^3-2q^2+1}{2}\ \ge\ X\ \ge\ \max\{2q^2-9q+4,\ q^2-3q+1\ \text{if }\kappa\le2\},$$
and at $q=13$ the window is $225\le X\le930$ — non-empty. I recomputed both bounds from m9's
derivations (upper: per $t$, $\#\{k\in SS\setminus\{t\}:\mathrm{agr}(k,t)=2\}\le(q^2-Z_t)/2$ and
$\sum_t Z_t=q^2-1$; lower: $3-\kappa(k)$ per pair from the excess identity and
$\sum\kappa=q^2-1$). The exact reason it cannot collide:
$$n_2(t)-n_0(t)=1-Z_t,\qquad n_0(t)=\#(SS\cap t\mathcal E),$$
so an upper bound on $X$ *is* a cap statement for the product set $SS$ one level up — the same
problem, not a consequence of any agreement identity. **Do not re-enter the agreement/counting
route.**

**(E2) The plane count cannot be lifted to $\mathbf P^3$ (m6 §8, checked).** Through a point
$P\in\mathbb G$ there are $\asymp q^2/2$ external lines (exactly $q(q-1)/2$ Singer cycles through
$[1]$; $\frac{q^2\pm q}{2}$ in general, by determinant class), while only $q-1$ joins have to be
accommodated. So "count the external lines through a point" is a proof only in a plane, which is
why (P1) is the end of that road. A proof needs a mechanism forcing $q$ points of the
square-determinant half into a plane, or the extension count (P6).

**(E3) Referee error, corrected.** I asserted in a verdict that in the bad case "$f\notin G$, so $f$
and $gh\in G$ agree in at most 2 points, hence alternative (c) of the collision trichotomy never
occurs". **Wrong**: $f$ is an arbitrary permutation, and agreement in 3 (or more, short of $q+1$)
points does not force $f=gh$. Only $q+1$ agreements do. m9 caught it; the trichotomy stands as
proved and (P6)/§11 do not depend on the false reading.

**(E4) Directions now closed, with reasons, so nobody reopens them:** spectral/character on
$\pi$ (§4); defect of translates (§10 R1); Delsarte clique-number bounds (m1: any bound uniform in
$q$ would also hold at $q=9$ where TARGET is false); circle-partition cross-adjacency counting (m4:
the cross-adjacency is $\approx q/2$, far too dense); power-map symmetry $S\mapsto S^l$ (m4: true,
but symmetrising gives only the average multiplicity, no contradiction); triple/orientation
encoding (m8: exact dictionary, but it only reproduces the anisotropy criterion); cross-ratio /
$\mathbb F_{q^2}$ multiplier dictionary (m7: same re-derivation); parity/Hall–Paige (m10: no
carrier); agreement counting (E1); genus/cycle type (m6 §6: vacuous).

**Live when this was written:** m2 (ratio-map collision from the exact two-function normal form),
m5 (the $q\times q$ matrix $W=\mathbf 1\hat E^{\mathsf t}+\hat E\mathbf 1^{\mathsf t}+B$ of rank 4,
square diagonal, nonsquare off-diagonal — all $5\times5$ minors vanish, (P7)), m3 (Witt/polar
structure of the split $4$-space), m6 (the extension count of (P6)).

**(E5) Second referee error, corrected: the rank/minor programme on $W$ is dead.** I had claimed
$W_{bg}=\hat E_b+\hat E_g+b d_g+g d_b$ (with $\hat E_b=D_b-bd_b$), hence $\operatorname{rank}W\le4$
and a $5\times5$-minor computation forcing $d$ affine. That identity is for
$\beta_{bg}=\operatorname{tr}(M_b\operatorname{adj}M_g)$, not for the discriminant
$W_{bg}=\beta_{bg}^2-4D_bD_g$. m5's counterexample ($b=(1,2,3,4,6)$, $d=(2,5,7,11,13)$,
$D=(4,9,16,25,36)$: $\det W_5\equiv-1384942737600\equiv33\pmod{101}$, $\det\Gamma_5=0$) I
reproduced; see the corrected (P7) above. Consequence: $\Gamma$'s rank-$\le4$ and its vanishing
minors are automatic, $W$ has generic rank $q$, and **no linear-algebra/rank argument over the Gram
matrix can exclude a configuration** — consistent with §4's invisibility theorem, of which this is
the matrix-level shadow. The entire content sits in the per-entry square classes
$T_{bg}=\operatorname{tr}(M_bM_g^{-1})\in\mathcal T$, $T_{bb}=2$.
