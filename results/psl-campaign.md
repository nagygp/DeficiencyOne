# Campaign report: the PSL(2,q) case, q ≡ 1 mod 4 (swarm `smvrks9r0`, closed)

**Outcome: the target is not proved.** The run closed when its model budget was spent (2 318 of
2 400 calls, 10 members, ~1 h 50 m of wall clock). What it produced is a set of *proved* reductions
and a long list of routes closed with proofs rather than assertions; the open statement is now
narrow and precisely stated. This file is the summary; the refereed detail is in
[psl-brief.md](psl-brief.md) (§10–§12 are the referee logs) and in the member reports under
`.ultramath/smvrks9r0/`.

## The target

$q$ odd, $q\equiv1\pmod4$, $q\ge13$; $S\subseteq\operatorname{PSL}(2,q)\subset\operatorname{PGL}(2,q)$
acting on $\mathbf P^1(\mathbb F_q)$, $|S|=q$, $1\in S$, $st^{-1}$ fixed-point-free for all distinct
$s,t\in S$. **Claim: no such $S$ exists.** Equivalently (Theorem F of the earlier swarms): the
stability conjecture for $\mathrm{PGL}(2,q)$ in the arithmetic case $q\equiv1\pmod4$, $q\notin\{11,23,59\}$.
It is false at $q=9$ ($\mathbb G=A_6$, 180 bad sets), and true for all $q\le19$ that were
exhaustively checked (earlier work).

## What is now proved (refereed; proofs in the member reports and the brief)

1. **Rank 4.** A valid clique's $q$ points $[M_s]$ on the hyperboloid $\{\det=1\}\subset\mathbf P^3$
   with all joins external to $Q^+=\{\det=0\}$ **span $\mathbf P^3$**: an exterior set inside a plane
   has at most $(q+3)/2$ points. Proved three times independently (m2 Thm B, m5 (B), m6 Thm A); I
   checked m2's proof line by line and the bound numerically ($4,4,7,7$ for $q=5,7,11,13$ against
   $(q+3)/2$). Consequences: no collinear, coplanar, Singer-cycle or two-half-torus configurations.
2. **The group is generated.** $\langle S\rangle=\mathrm{PSL}(2,q)$ for every valid $S$
   (m9 Thm D, independently m6 Thm D): complete Dickson analysis, the last case $A_5$ at $q=29$
   killed by the ratio bound $15<28$ on $\mathrm{Cay}(A_5,\text{involutions})$. So the target is
   equivalent to "no valid clique generating $\mathbb G$".
3. **Pair data is constant.** For $X\in SL_2$ elliptic of odd order ($q\equiv1\pmod4$),
   $X=Y^2$ with $Y$ elliptic, so $X+I=\operatorname{tr}(Y)Y$ and
   $2+\operatorname{tr}X=\operatorname{tr}(Y)^2$ is *always* a square while $2-\operatorname{tr}X$
   is *always* a nonsquare. Any proof must use $\ge3$ elements.
4. **The extension reduction (sharpest known).** If every exterior set of size $q$ of $Q^+(3,q)$
   extended to one of size $q+1$, the target would follow: a maximal exterior set is a coset $cH$
   of a regular $C_{q+1}$, and $|cH\cap\mathbb G|=(q+1)/2<q$. So the problem *is* the deficiency-one
   extension problem, restricted to the square-determinant half.
5. **Corrections to the inherited record** (found by members, verified by me): in the bad case
   $|SS|=q^2-q+1$ (not $q^2$: the collisions $s\cdot1=1\cdot s$ are forced); "$S\subseteq\mathbb G
   \Rightarrow f$ even" is false in general ($q=9$ has $f$ of type $(4,4,2)$, so $\langle T\rangle=S_{10}$);
   "all $\Delta_\beta$ lie in one square class" is false (Singer: $\Delta_\beta=\beta^2-\delta$).

## Routes closed with proof (do not reopen)

Spectral/character/Delsarte/LP on the permutation representation (the image of $\mathbb C[G]$ is
$\mathrm{End}(1)\oplus\mathrm{End}(\mathrm{St})$, which contains every permutation matrix; the sign
character is not a constituent — the target's hypothesis is invisible there); the "defect of
translates" identity (a tautology for arbitrary injective $f$); clique-number bounds uniform in $q$
(they would hold at $q=9$, where the target is false); agreement/two-way counting (provably
circular: it reduces to a cap statement for $SS$ one level up); rank/minor arguments on the Gram
matrix (its rank and vanishing minors are automatic); affine/collinear and planar configurations;
proper subgroups; pure product and triple-product counting; power-map symmetry $S\mapsto S^l$;
the triple/orientation dictionary; the cross-ratio $F_{q^2}$ dictionary; parity/Hall–Paige (no
carrier); genus/cycle-type constraints (vacuous); the char-$p$ Bamberg–Mattheus engines (they need a
*complete* sharply transitive set, and $\mathrm{Sym}^d$ is not a $\mathbb G$-module for odd $d$).

## The open statement, cleanly

> There is no Sidon set $S\subseteq\mathrm{PSL}(2,q)$ ($q\equiv1\pmod4$, $q\ge13$) with $1\in S$,
> $|S|=q$, all $st^{-1}$ ($s\ne t$) fixed-point-free, and $|S\cdot S|=q^2-q+1$.

Equivalently: no $q$ points of $\{\det=1\}$ spanning $\mathbf P^3$ with all pairwise joins external
to $\{\det=0\}$; equivalently: every such exterior set extends to one of size $q+1$.

## Leads for a next attempt

* **Bamberg–Mattheus, arXiv:2608.17371**, "no sharply transitive subsets of $\mathrm{SL}(2,q)$ for
  $q\ge13$" — cited by m9 as an analogous theorem with two engines (local trace counts; the
  char-$p$ vanishing $\sum_s \mathrm{Sym}^d(s)=0$). **I could not verify it: arXiv answered 429 to
  this machine and I did not work around it.** If real, it is the closest known result and the
  first thing to read.
* **The $q=9$ specimen.** It satisfies every necessary condition proved here (square $D_b$,
  nonsquare $W_{bg}$, Sidon, generating, rank 4, non-affine $x$). Computing its shape in the exact
  normal form $s_v(y)=v+\mu_v/(x_v-y)$ (m2's Thm A) or in the $(b,d_b,D_b)$ chart (m5's (A)) should
  isolate the arithmetic coincidence that makes $q+1=10$ work, and hence the lemma to prove for
  $q\ge13$. This was in progress when the budget ran out (m5 d14).
* **The extension count.** Count the admissible $p\in\mathbf P^3\setminus Q$ with
  $\chi(\beta(p,M_s)^2-4)=-1$ for all $s$; showing it is $\ge1$ proves the target (see 4 above).

## Referee's own errors, for the record

Four of my six suggested continuations were closed by the swarm, two of them as *my* mistakes:
(a) I claimed in the bad case that $f\notin G$ forces agreement with $gh$ in $\le2$ points — false,
$f$ is not Möbius (m9); (b) I claimed the discriminant array $W=\beta^2-4D_bD_g$ has rank $\le4$ by
an identity that holds for $\beta$, not $W$ — refuted by an explicit $5\times5$ minor (m5), which I
reproduced. Both are corrected in the brief ((E3), (E5)). The other closed suggestions were
trivially true (incidence with torus normalisers), constant (the $\pm$ colouring), false
($S^2$ a clique), circular (two-way counting), or equivalent to the target (ratio-map collision).
