# Stability of sharply transitive sets in PGL(2,q): results

Status of the stability conjecture:

> Let `S` be a set of `q` elements of `PGL(2,q)` with `1 ∈ S`, such that `a·b⁻¹` is
> fixed-point-free on the projective line for all distinct `a, b ∈ S`.  If `q` is large
> enough, is `S` contained in a subgroup of size `q+1`?

## Short answer

**The guess "`q > 7` suffices" is false.**  Exhaustive computation shows the conjecture
**fails exactly for `q ∈ {4, 5, 7, 9}`** and **holds for `q ∈ {2, 3, 8, 11, 13, 16, 17, 19}`**
(`q = 16, 17, 19` verified by several independent methods, including a completed independent
conjugacy-reduced search at `q = 16, 17`).  The evidence points to the conjecture holding for
all `q ≥ 11`.

## The reduction (proved in Lean, `RequestProject/Stability.lean`)

Given a valid `S` (`|S| = q`, `1 ∈ S`, all ratios of distinct elements fixed-point-free),
define `f : P¹ → P¹` by `f(x) =` the unique point of `P¹` not in `{s·x : s ∈ S}`.

* `f` is a well-defined derangement (`stable_inj`: two elements of `S` agreeing at a point
  are equal, since `a·b⁻¹` would fix `b·x`).
* `T := S ∪ {f}` is a sharply transitive set of permutations of `P¹`.
* The conclusion "`S ⊆ H` for some `H ≤ PGL₂(K)` with `|H| = q+1`" is **equivalent** to
  "`f ∈ PGL₂(K)`" and to "`|⟨S⟩| = q+1`" (`stable_conclusion_iff_missing`).

So the conjecture is equivalent to: **the missing permutation `f` is a Möbius
transformation.**  By Eberhard's Theorem 1 (`eberhard_theorem1`, already formalized), if
`f ∈ PGL₂(K)` then `T` is a subgroup of order `q+1` containing `S`.

Since `⟨S⟩` is always transitive on `P¹`, Dickson's classification reduces the conjecture to
excluding `⟨S⟩ ∈ { D_{2(q+1)}, PSL(2,q), PGL(2,q) }`.

## Computational data (exhaustive clique search in the elliptic graph)

A valid `S` is a `q`-clique containing `1` in the graph on `PGL(2,q)` joining `a, b` when
`a·b⁻¹` is fixed-point-free.  Enumerated exhaustively (bitset DFS), cross-checked by an
independent implementation:

| q | \|PGL(2,q)\| | elliptic | valid S | bad (f ∉ PGL) | conjecture |
|---|---|---|---|---|---|
| 2 | 6 | 2 | 2 | 0 | holds |
| 3 | 24 | 9 | 12 | 0 | holds |
| 4 | 60 | 24 | 64 | **40** | **fails** |
| 5 | 120 | 50 | 200 | **100** | **fails** |
| 7 | 336 | 147 | 490 | **196** | **fails** |
| 8 | 504 | 224 | 224 | 0 | holds |
| 9 | 720 | 324 | 828 | **180** | **fails** |
| 11 | 1320 | 605 | 1815 | 0 | holds |
| 13 | 2184 | 1014 | 2028 | 0 | holds |
| 16 | 4080 | 1920 | 1920 | 0 | holds |
| 17 | 4896 | 2312 | 4624 | 0 | holds |
| 19 | 6840 | 3249 | 6498 | 0 | holds |

(`q = 16, 17, 19` verified by three independent methods: maximal-clique enumeration,
branch-and-bound over conjugacy classes, and a C+OpenMP conjugacy-reduced search; all
reproduce the known `q ≤ 13` counts.  My own independent conjugacy-reduced search confirms
`q = 16` (complete) and `q = 17` (complete, 0 bad).  Note: all 180 bad `f` at `q = 9` have
cycle type `(4,4,2)` — confirmed by recomputation.)

In the good case the count is exactly `q · #{regular subgroups of order q+1}`
(each regular subgroup `H` contributes the `q` sets `H \ {h}`, `h ≠ 1`).

### Structure of the bad sets

* `q = 4`: bad `S` generate `A₅ = PGL(2,4)` (order 60); non-identity elements have order 5.
* `q = 5`: bad `S` generate `S₅ = PGL(2,5)` (order 120).
* `q = 7`: bad `S` generate `PGL(2,7)` (order 336).
* `q = 9`: bad `S ⊆ A₆ = PSL(2,9)` (order 360); all 8 non-identity elements have order 5
  (cycle type `(5,5)` on the 10 points); `f` has cycle type `(4,4,2)`.

So the bad cases are exactly the exceptional isomorphisms
`PGL(2,4) ≅ A₅`, `PGL(2,5) ≅ S₅`, `PGL(2,7) ⊂ S₈`, `PSL(2,9) ≅ A₆`.

### Explicit counterexample at `q = 9`

`F₉ = F₃[X]/(X²+1)`, element `k = a + 3b` means `a + b·w`.  The following 9 matrices form a
valid `S` with `⟨S⟩ = A₆` (order 360 ≠ 10), verified by two independent implementations
(`.scratch/stab.py`, `.scratch/verify.py`):

```
(8,0,0,8) (0,8,8,3) (8,8,3,8) (8,4,1,7) (8,7,6,5) (8,3,8,8) (8,2,2,0) (8,1,4,7) (8,6,7,5)
```

The missing permutation is `f = (7,4,3,2,0,8,9,1,6,5)` (a derangement), which is **not** in
`PGL(2,9)`.  Hence `S` is not contained in any subgroup of order `q+1 = 10`.

## The dihedral case (corrected)

Let `T₀ ≅ C_{q+1}` be a Singer cycle and `N = N_G(T₀) ≅ D_{2(q+1)}`.  If `S ⊆ N` is valid
then `⟨S⟩` is a transitive subgroup of `N`, hence has order `q+1` (regular: `C_{q+1}` or
`D_{(q+1)/2}`) or `2(q+1)`.  Computation (exhaustive over all valid `S ⊆ N` at
`q = 4,5,7,8,9,11,13,16`) shows `|<S>| = q+1` **always**: the bad case
`⟨S⟩ = D_{2(q+1)}` never occurs.  For `q` odd there are `2q` valid `S` (`q` inside `T₀`,
`q` inside a regular dihedral subgroup `⟨r², rs⟩`); for `q` even there are `q`, all inside
`T₀`.

A clean proof (parity argument, verified): identify `P¹` with `Z/m`, `m = q+1`, so
`N = ⟨r, s⟩` with `r: i↦i+1`, `s: i↦c−i`.  An element `r^j` (`j≠0`) is elliptic;
`r^j s` fixes `i` iff `2i ≡ c+j`, so for `q` odd (`m` even) `r^j s` is elliptic iff `j ≢ c`
(half of them), and for `q` even (`m` odd) all `r^j s` are unipotent (one fixed point).
Writing `S = A ∪ B` (`A ⊆ ⟨r⟩`, `B ⊆ ⟨r⟩s`), the ratio condition forces all exponents in
`A` even and all in `B` to have a fixed parity, so `S ⊆ ⟨r², r^{j₀}s⟩`, a transitive
subgroup of order `m = q+1`.

(Note: the stronger claim "every element of `N \ T₀` fixes exactly one point, so `S ⊆ T₀`"
is **false for odd `q`**: for odd `q` the `q+1` involutions in `N \ T₀` split evenly into
`(q+1)/2` elliptic and `(q+1)/2` hyperbolic ones, and valid `S ⊆ N` with `S ⊄ T₀` exist —
but they lie in a regular dihedral subgroup, so the conjecture is unaffected.  A Cauchy–
Davenport "proof" of `S ⊆ T₀` is invalid for odd `q` because `C_{q+1}` is composite.)

## What is proved in Lean

* `RequestProject/Stability.lean` (new):
  * `PGL2.IsStableSet`, `PGL2.IsStableConclusion` — the hypothesis/conclusion.
  * `PGL2.card_projectiveLine` — `|P¹(K)| = q+1`.
  * `PGL2.stable_inj` — injectivity of `s ↦ s·x` on `S`.
  * `PGL2.stable_conclusion_of_missing` — a "missing" `g ∈ PGL₂(K)` ⟹ conclusion
    (via `eberhard_theorem1`).
  * `PGL2.stable_missing_of_conclusion` — conclusion ⟹ a "missing" element exists
    (orbit–stabilizer: a subgroup of order `q+1` acts regularly, so `H \ S` is nonempty and
    its elements avoid `S·x`).
  * `PGL2.stable_conclusion_iff_missing` — the equivalence.
  * `PGL2.stability_conjecture` — the conjecture for `q > 10`, stated with one `sorry`
    (producing the missing element is the hard open part).
* All of the above depend only on `propext`, `Classical.choice`, `Quot.sound`.
* The pre-existing `RequestProject/Lemma2.lean` was repaired for the current Mathlib
  (two stale `simp only` calls and a `Set.toFinite`/`Set.toFinset` instance mismatch).

## What remains open

Proving that a valid `S` always admits a missing Möbius element for `q ≥ 11`, i.e.
excluding `⟨S⟩ ∈ { PSL(2,q), PGL(2,q) }`.  Verified partial results toward this:

* **Spread bound** (verified exhaustively at `q = 5,7,9,11`): if `H` is a regular subgroup
  of order `q+1` and `S ⊄ H`, then `|S ∩ H| ≤ (q+1)/2`.  (Double counting:
  `Σ_{h∈H} #Fix(s·h⁻¹) = q+1` for `s ∈ S\H`; terms with `h ∈ S∩H` vanish, others are
  `≤ 2`.)  So a counterexample must meet *every* regular subgroup (and every coset of one)
  in at most half its elements.
* **Agreement moments** (verified at `q = 9`): for `a_m = #{x : m(x) = f(x)}`,
  `Σ_{m∈PGL(2,q)} (a_m)_k = |PGL(2,q)|` for `k = 1,2,3` (sharply-3-transitive counting).
  The first three factorial moments of the agreement function are exactly Poisson(1), so
  **no first-moment (fixed-point-counting) argument can prove the conjecture**.
* **Periods** (verified at `q = 9,11`): if `cap(g) = |{u ∈ S : gu ∈ S}| ≥ 2` then `g` is
  elliptic or `g = 1` (since `g = (gu)u⁻¹` is a quotient of distinct `gu, u ∈ S`).
* **Multiplier obstruction**: the one-short analogue of Eberhard's Lemma 2 (Segre's lemma
  of tangents) carries a multiplier `Ψ`, so the collision residual `h·k⁻¹·g` is hyperbolic
  with multiplier `Ψ` rather than parabolic; the Wilson/Segre route needs the extra input
  `Ψ = 1` (equivalently `g·h ∈ T = S ∪ {f}` for all `g, h ∈ S`).  In its sharpest form
  (verified 16032/16032 at `q = 9` over left translates): for `g₁=(0 b₁;c₁ d₁)`,
  `g₂=(a₂ 0;c₂ d₂)`, `g₃=(a₃ b₃;0 d₃)`, `g₄=(a₄ b₄;c₄ 0)` in the clique,
  `(b₁/c₁)(d₂/a₂)(a₃/d₃)(c₄/b₄) = f⁻¹(0)·f(∞)/(f(0)·f⁻¹(∞))`,
  i.e. the eigenvalue ratio of the collision residual `h t⁻¹ g` is an explicit cross-ratio of
  the missing map `f`.
* **Product-set reformulation** (verified at `q = 9, 11`): the conjecture is equivalent to
  `|S·S| = q+1`.  Good `S` (contained in a regular subgroup `H`, so `S = H∖{h}`) satisfy
  `S·S = H`, `|S·S| = q+1`; a bad `S` is completely spread out (`cap(g) = |S ∩ gS| ≤ 1` for
  all `g ≠ 1`, and `|S·S| ≈ q²`; at `q = 9` every bad `S` has `|S·S| = 65`).  A related
  lemma: for `g ∈ G` and `s, s′ ∈ S ∩ gS` with `s ≠ g⁻¹s′`, the element `s·s′⁻¹·g` is
  elliptic (it is the ratio `s·(g⁻¹s′)⁻¹` of two distinct elements of `S`); if `s = g⁻¹s′`
  it equals `1`.
* **Semilinear structure**: at `q = 9` all 180 bad completions `f` lie in
  `PΓL(2,9)` (order 1440), and at `q = 4` all 40 (where `PΓL(2,4) = S₅`).  But for prime
  `q` (`q = 5, 7`) `PΓL(2,q) = PGL(2,q)`, so the bad `f` are *not* semilinear — hence
  "`f` is always semilinear" is false, and the bad cases split into a semilinear family
  (`q = 4, 9`) and a symmetric-group family (`q = 5, 7`, with `⟨T⟩ = S_{q+1}`).
* **Negative result**: the Hoffman/LP/Delsarte bound on the derangement (elliptic) Cayley
  graph equals `v/(q+1)` (the clique–coclique bound, attained by Borel subgroups), so no
  spectral/positivity bound can prove the conjecture.

A swarm (Ultramath, id `smvr3683u`, 8 members, ~1600 model budget) attacked the PSL/PGL
case from many directions (clique structure, character/Fourier, torus-local structure,
Rédei/lacunary polynomials, fixed-point moments, approximate subgroups, geometric algebra,
loop/associator methods) and has now ended without closing it.  In its sharpest form, the
remaining gap is equivalent to each of:

* (LOC-1) some regular `H` has `|S ∩ H| > (q+1)/2` (then the spread bound gives `S ⊆ H`);
* (LOC-2) some `m ∈ PGL(2,q)` agrees with `f` in all `q+1` points — equivalently the 4th
  factorial moment `Σ_m (a_m)_4` jumps to `(q+1)_4` (in the bad cases `max_m a_m = 4` and
  the moment is far smaller: 720 vs 5040 at `q = 9`);
* (LOC-3) some associator `D(y,z)` of the loop defined by `T` has three fixed points;
* `|S·S| = q+1`.

Any one of these finishes the proof.  This appears to be a genuinely hard open problem.

## Second swarm: verified structural results (swarm `smvrhlrqe`)

A second swarm attacked only the PSL/PGL case (no $q$-verification allowed) and also ended
without a proof, but accumulated correct, referee-checked structural results.  The most
useful, all verified by the referee:

* **Parity reduction** (m8, Thm C): for odd $q$, $\mathrm{PGL}(2,q)\cap A_{q+1}=\mathrm{PSL}(2,q)$
  (verified: the coset $\mathrm{PGL}\setminus\mathrm{PSL}$ is *entirely* odd for every odd $q$,
  e.g. $q=5,7,9,11,13$).  So a completion $T\subseteq A_{q+1}$ forces $S\subseteq\mathrm{PSL}$.
  For even $q$, $\mathrm{PGL}=\mathrm{PSL}\subseteq A_{q+1}$ — parity is blind.
* **Dichotomy and the "empty alternative"** (m8, Thm F): a counterexample has
  $\langle T\rangle\in\{A_{q+1},S_{q+1}\}$; and for $q\equiv1\bmod 4$, $q\notin\{11,23,59\}$,
  $\mathrm{PSL}(2,q)$ contains **no** regular subgroup of order $q+1$, so **every valid
  $S\subseteq\mathrm{PSL}(2,q)$ is a counterexample**.  Verified at $q=9$: the 180 bad $S$ are
  *exactly* the 180 valid $S\subseteq\mathrm{PSL}(2,9)$.
* **Linear-case theorem** (m8, Thm E): if the $q$ points $[M_s]\in\mathbb P^3$ are collinear then
  $f\in\mathrm{PGL}$ — every *linear* partial flock of deficiency one extends.  (Good dihedral
  configurations are not collinear, so this is strictly weaker than the conjecture.)
* **Defect of translates** (m7, Thm 6/Cor 7): with $A_0=f^{-1}(0)$, $B_0=f^{-1}(\infty)$,
  $G(x)=f(x)(B_0-x)/(A_0-x)$, one has $\Psi(Su)=G(u(\infty))/G(u(0))$ for all $u$; hence
  $\Psi\equiv1\iff G$ constant $\iff f\in\mathrm{PGL}$.  So $S$ is good $\iff f$ preserves the
  cross-ratio of every quadruple containing $f^{-1}(0),f^{-1}(\infty)$.
* **Hyperbolic triple-product criterion** (m1, Prop 5.7.1, verified): $S$ is good $\iff$ **no**
  triple product $hk^{-1}g$ ($g,h,k\in S$) is hyperbolic.  Also (Prop 5.7.2, verified)
  $\sum_{g,h,k\in S}\#\mathrm{Fix}(hk^{-1}g)=q^3+1$.
* **Large-cap theorem** (m5): if $\mathrm{cap}_L(g)=q-1$ for some $g\neq1$ then $f=m\circ\tau$
  with $|\mathrm{supp}\,\tau|\le2$; the transposition case has exactly two exhaustive shapes
  (two unipotents, or one split element).  Remaining cases: $(R1)$ $2\le\kappa\le q-2$,
  $(R2)$ transposition shape, $(R3)$ Sidon.
* **Collision structure** (m6, m7): exact excess identity $\sum_i(i-1)n_i=2$; the one-short
  tangent identity $(b_1/c_1)(d_2/a_2)(a_3/d_3)(c_4/b_4)=\Psi$ with
  $\Psi=\varphi^{-1}(0)\varphi(\infty)/(\varphi(0)\varphi^{-1}(\infty))$ (verified 16032/16032);
  the residual is hyperbolic with multiplier $\Psi$; a clean splitting lemma bounding the
  "type (B)" pairs.
* **Barriers** (all verified): the first three factorial moments of the agreement function are
  Poisson(1) for *every* derangement $f$, so no first-moment/spectral/LP argument can decide it;
  the tangent-lemma multiplier takes both values $1$ and $\neq1$ in a bad $S$, so no *global*
  "$\Psi\equiv1$" rigidity can work.

The referee retracted four errors along the way (a false "each $b=0,c=0$ corner is forbidden",
a false "bad $S$ has $S\cap S^{-1}=\{1\}$", a false "every elliptic element lies in PSL"
refuted at $q=5,9,11$, and a quantifier slip in a "bad-case dichotomy"), which is why the
surviving statements above are the ones to trust.

**Sharpest remaining target** (m8's F3): for $q\equiv1\bmod4$, $q\ge13$, show that
$\mathrm{PSL}(2,q)$ contains **no** valid $q$-element clique of elliptic elements generating it
(equivalently, no $q$-clique of the elliptic Cayley graph inside PSL with $1$).  Here the tori
inside $\mathrm{PSL}$ are only half-size $(q+1)/2$, which is exactly why the Singer argument
fails and is the source of the $q=9$ exception.

## Files

* `RequestProject/Stability.lean` — the reduction and the conjecture (Lean).
* `.scratch/stab.py`, `.scratch/stab2.py`, `.scratch/stab3.py` — exhaustive searches.
* `.scratch/verify.py` — independent re-verification of the `q = 9` counterexample.
* `.scratch/verify_dih3.py` — the dihedral case `|<S>| = q+1`.
* `.scratch/analyze.py` — structure of bad sets.
