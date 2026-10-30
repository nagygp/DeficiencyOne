# CONTEXT CHECKPOINT — stability of sharply transitive sets in PGL(2,q)

Repo root: `/workspace/nucleus/work/projects/default/repo` (git repo with **no commits**; all
files untracked). Lean 4.33.1 + Mathlib at `/opt/mathlib`. 4 CPUs, 15 GB.

## 1. The problem, and the answer as established

**Stability conjecture.** `S ⊆ PGL(2,q)`, `|S| = q`, `1 ∈ S`, and `a·b⁻¹` is fixed-point-free
(*elliptic*) on `P¹(F_q)` for all distinct `a,b ∈ S` ⟹ `S ⊆ H` for some `H ≤ PGL(2,q)` of
order `q+1`.

**Established (exhaustive computation, multiple independent implementations):** the
conjecture **fails exactly for `q ∈ {4,5,7,9}`** and **holds for `q ∈ {2,3,8,11,13,16,17,19}`**
(so `q ≥ 11` holds on the verified range). **The guess "q > 7 suffices" is FALSE** — `q = 9`
is the counterexample. Nothing beyond `q = 19` has been verified, and the person has
forbidden further `q`-verification (see §6).

| q | \|PGL\| | elliptic | valid S | bad | ⟨S⟩ of bad sets |
|---|---|---|---|---|---|
| 2 | 6 | 2 | 2 | 0 | — |
| 3 | 24 | 9 | 12 | 0 | — |
| 4 | 60 | 24 | 64 | **40** | A₅ = PGL(2,4), elements of order 5 |
| 5 | 120 | 50 | 200 | **100** | S₅ = PGL(2,5) |
| 7 | 336 | 147 | 490 | **196** | PGL(2,7), order 336 |
| 8 | 504 | 224 | 224 | 0 | — |
| 9 | 720 | 324 | 828 | **180** | A₆ = PSL(2,9), order 360 |
| 11 | 1320 | 605 | 1815 | 0 | — |
| 13 | 2184 | 1014 | 2028 | 0 | — |
| 16 | 4080 | 1920 | 1920 = 16·120 | 0 | — |
| 17 | 4896 | 2312 | 4624 = 17·272 | 0 | — |
| 19 | 6840 | 3249 | (not counted) | 0 | — |

In the good case the number of valid `S` is exactly `q · #{regular subgroups of order q+1}`
(each regular `H` contributes the `q` sets `H∖{h}`, `h ≠ 1`).

**Explicit `q = 9` counterexample.** `F₉ = F₃[X]/(X²+1)`; the integer `k = a+3b` encodes
`a + b·w`. The nine matrices (entries in `F₉`)

```
(8,0,0,8) (0,8,8,3) (8,8,3,8) (8,4,1,7) (8,7,6,5) (8,3,8,8) (8,2,2,0) (8,1,4,7) (8,6,7,5)
```

form a valid `S` with `⟨S⟩ = A₆ = PSL(2,9)` (order 360 ≠ 10). The missing permutation is
`f = (7,4,3,2,0,8,9,1,6,5)`, a derangement of cycle type `(4,4,2)`, **not** Möbius. Verified by
two independent implementations (`.scratch/stab.py`, `.scratch/verify.py`). All 180 bad `f` at
`q = 9` have cycle type `(4,4,2)`; all 8 non-identity elements of a bad `S` have cycle type
`(5,5)` and lie in 8 **distinct** Singer cycles (`max_T |S∩T| = 2`).

## 2. The reduction (proved in Lean, standard axioms only)

For valid `S` define `f(x)` = the unique point of `P¹` outside `{s(x) : s ∈ S}`. Then `f` is a
derangement, `T := S ∪ {f}` is sharply transitive, and

```
S ⊆ H (|H| = q+1)  ⟺  f ∈ PGL(2,q)  ⟺  |⟨S⟩| = q+1  ⟺  |S·S| = q+1.
```

`⟨S⟩` is always transitive, so by Dickson `⟨S⟩ ∈ {C_{q+1}, D_{(q+1)/2}, A₄(11), S₄(23), A₅(59)}`
(good, order `q+1`) or `∈ {D_{2(q+1)}, PSL(2,q), PGL(2,q)}` (bad).

**Settled for all `q`: the dihedral case `⟨S⟩ = D_{2(q+1)}` cannot occur.** Identify `P¹` with
`Z/m`, `m = q+1`, `N = ⟨r,s⟩`, `r^j: i↦i+j`, `r^j s: i↦j−i`. Elliptic: `r^j` (`j≠0`) always;
`r^j s` iff `q` odd and `j` odd (for `q` even every `r^j s` is unipotent). `1 ∈ S` kills
hyperbolic involutions; then `S ⊆ ⟨r⟩` or `S ⊆ ⟨r², rs⟩` (a **regular** subgroup of order
`q+1`). Verified exhaustively (`q=4,5,7,8,9,11,13,16`): `2q` valid `S ⊆ N` for `q` odd, `q` for
`q` even, all with `|⟨S⟩| = q+1`.

**So the whole problem is `⟨S⟩ ∈ {PSL(2,q), PGL(2,q)}` for `q ≥ 11` — still OPEN.**

## 3. NEW TARGET (the person's current request)

> **For `q ≡ 1 mod 4`, `q ≥ 13`, show `PSL(2,q)` admits no valid `q`-element clique of elliptic
> elements generating it.**

Why this is the sharpest target (all verified):
* `PGL(2,q) ∩ A_{q+1} = PSL(2,q)` for **every odd `q`** (verified: the coset `PGL∖PSL` is
  *entirely* odd at `q = 5,7,9,11,13`). For **even** `q`, `PGL = PSL ⊆ A_{q+1}` and parity is
  blind (m2).
* A counterexample has `⟨T⟩ ∈ {A_{q+1}, S_{q+1}}` (m8, Thm F); `⟨T⟩ = A_{q+1}` forces
  `S ⊆ PSL` and `⟨S⟩ = PSL`.
* For `q ≡ 1 mod 4`, `q ∉ {11,23,59}`, **`PSL(2,q)` contains no regular subgroup of order
  `q+1`** (C_{q+1} and D_{q+1} both have non-square determinant class), so by the parity
  reduction **every valid `S ⊆ PSL(2,q)` is automatically a counterexample** (m8, F3).
* **Verified at `q = 9`:** of the 828 valid `S`, exactly 180 lie in `PSL(2,9)`, and those 180
  are **exactly** the 180 bad `S`. So `q = 9` is precisely the failure of the new target.
* Inside `PSL(2,q)` (`q` odd) the tori are only **half-size**: `C_{(q+1)/2}` instead of
  `C_{q+1}`. This halving is exactly why the Singer/regular-subgroup argument fails and why
  `q = 9` is exceptional. Any proof must exploit it.

Facts to start from (verified for `q = 9`, formula-checked):
* `|PSL(2,q)| = q(q²−1)/2`.
* Non-identity elements of a half-torus `C_{(q+1)/2}` number `(q−1)/2`; the number of such
  tori in `PSL(2,q)` is `q(q−1)/2` for `q ≡ 1 mod 4`; hence the number of elliptic elements in
  `PSL(2,q)` is `q(q−1)²/4` (checks: `q = 9` gives 144, the correct count of order-5 elements
  in A₆).
* Two elements of one torus are automatically compatible (their ratio is in the torus,
  non-identity, hence elliptic), but a full torus supplies only `(q−1)/2` elements — far short
  of `q`. Hence `S` must be spread over many tori (at `q = 9`: 8 elements over ≥8 PGL-tori,
  `max_T |S∩T| = 2`).
* Available machinery: the pairwise anisotropy criterion (`s_v s_w⁻¹` elliptic ⟺
  `β(v,w)² − 4Q(v)Q(w)` a non-square, `Q(v) = e_v(v−a_v)`, `β(v,w) = e_w(v−a_w)+e_v(w−a_v)`,
  in the normal form `s_v = [v, a_v e_v; 1, e_v]`), the single-element constraints
  `T_v = (v−e_v)² + 4a_v e_v` non-square for all `v`, the injectivity of `a` and (odd `q`) of
  `e` (m3), the σ-dictionary (m8), the spread/cap identities (m5, m2), and the defect
  formalism (§4).

## 4. Verified structural results available (all referee-checked)

* **Tangent lemma with defect** (m1/m4/m6/m7, verified 16032/16032 at `q=9`): for a clique `A`
  with missing map `φ` and elements with `a₁=0, b₂=0, c₃=0, d₄=0`,
  `(b₁/c₁)(d₂/a₂)(a₃/d₃)(c₄/b₄) = Ψ := φ⁻¹(0)φ(∞)/(φ(0)φ⁻¹(∞))`. For a regular set `Ψ = 1`
  (Eberhard's Lemma 2, formalized). The collision residual `h k⁻¹ g` is **hyperbolic** with
  eigenvalue ratio `Ψ`, not parabolic; `Ψ = 1 ⟺ gh ∈ T`.
* **Defect of translates** (m7): with `A₀ = f⁻¹(0)`, `B₀ = f⁻¹(∞)`,
  `G(x) = f(x)(B₀−x)/(A₀−x)`, one has `Ψ(Su) = G(u(∞))/G(u(0))` for every `u ∈ G`; hence
  `Ψ ≡ 1 ⟺ G` constant `⟺ f ∈ PGL`. (**recommended as the main lever**)
* **Hyperbolic triple-product criterion** (m1, verified `q=5,9,11`): `S` is good ⟺ **no**
  `h k⁻¹ g` (`g,h,k ∈ S`) is hyperbolic. Also `Σ_{g,h,k∈S} #Fix(h k⁻¹ g) = q³ + 1` (verified).
* **Large-cap theorem** (m5): if `cap_L(g) = q−1` for some `g ≠ 1` then `f = m∘τ` with
  `m ∈ PGL`, `|supp τ| ≤ 2`; the transposition case has exactly two exhaustive shapes
  (C1) two unipotents / (C2) one split element. Remaining: (R1) `2 ≤ κ ≤ q−2`, (R2) that shape,
  (R3) Sidon (`κ = 1`).
* **Cap identity / Sidon** (m5): `Σ_{g(x)=y} cap_L(g) = q−1+δ_{xy}`, `Σ_g cap_L(g) = q²`;
  Sidon ⟺ `cap ≤ 1` off `1`. Good `S`: `max cap = q−1`; bad at `q=9`: `max cap = 1`; at
  `q=5,7`: `2`.
* **Collision structure** (m6): with `n_i = #{t ∈ T∖{g,h} : agr(gh,t) = i}`,
  `Σ n_i = q−1`, `Σ i n_i = q+1`, hence the **excess identity** `Σ (i−1)n_i = 2`.
  The "triple lemma" is valid **only for `t ∈ S`** (for `t = f`, `h f⁻¹ g` is not Möbius).
* **Product/ratio sets**: `|S·S| = q+1` good, `q²` bad; `|S·S⁻¹| = q+1` good, `q²−q+1` bad
  (verified: 5/13 at `q=4`, 10/73 at `q=9`, 12 at `q=11`).
* **Spread bound**: `S ⊄ H` (regular `H`) ⟹ `|S∩H| ≤ (q+1)/2` (verified `q=5,7,9,11`).
* **Moments**: `Σ_{m∈PGL} (a_m)_k = |PGL|` for `k = 1,2,3`, where `a_m = #{x : m(x)=f(x)}`
  (Poisson(1)); `Σ_m (a_m)_4` = number of ordered 4-tuples preserving the cross-ratio; at
  `q = 9` bad: 720 vs `(q+1)_4 = 5040`, `max_m a_m = 4`. **No first-moment / spectral / LP /
  Delsarte argument can work**; the Hoffman bound equals `v/(q+1)` and is attained.
* **Character-theoretic** (m1): in the bad case `(q+1)χ(1) + Σ_{e∈E} χ(e) ≥ 0` for all
  irreducible `χ`; equivalent cuspidal form `Re |E|⁻¹ Σ_{e∈E} θ(ν_e) ≤ 1/2 + 1/(2q)`.
  Non-vacuous but compatible with the spread case.
* **Char-2 obstruction** (m2, verified): for `q` even, if `f` has a 2-cycle then `S` is a
  counterexample; good `f` has none. So for even `q`, conjecture ⟺ "`f` without 2-cycles ⟹ good".
* **Linear case** (m8, proved): if the `q` points `[M_s] ∈ PG(3,q)` are collinear then
  `f ∈ PGL` — every *linear* partial flock of deficiency one extends. Strictly weaker than the
  conjecture (good dihedral configurations are not collinear).
* **Geometric dictionary**: valid `S` = `q` points of `PG(3,q)∖Q⁺` with all joins external ⟺
  *partial flock of deficiency one* of `Q⁺(3,q)`; good ⟺ collinear on an external line. External
  lines = `A·F` for `A ∈ G`, `F ≅ F_{q²}` a field.
* **Normal forms**: `f(∞)=0`, `S = {1} ∪ {s_v = [v, a_v e_v; 1, e_v] : v ∈ F_q^*}`, `a_v = s_v(0) ≠ v`;
  `a` injective always, `e` injective for `q` odd (m3). Pole form (m2): `s(x) = α + β/(x−p)`,
  `α = a/c`, `p = −d/c`, `β = b/c + αp`; pair invariant
  `V = (α−α′)(p−p′) **−** (β+β′)` (the `+` sign is wrong except in char 2).
  m8's σ-dictionary: `σ_y(β) = Δ_β/(β−y) − d_β` is a bijection `K∖{y} → K∖{c(y)}`, `c = φ⁻¹|_K`;
  **SC ⟺ c affine**.
* **Semilinear structure**: at `q = 9` all 180 bad `f` lie in `PΓL(2,9)∖PGL`; at `q = 4` all 40
  (where `PΓL(2,4) = S₅`). But for **prime** `q`, `PΓL = PGL`, so the bad `f` at `q = 5,7` are
  *not* semilinear.

## 5. What was tried and FAILED, and why (do not redo)

| approach | outcome |
|---|---|
| Wilson products / Segre tangent lemma, naive adaptation | Gives `Ψ = 1` as the gap, not `Ψ = 1`. The q-set loses to the defect; only 2 of the 4 corner slots are forced, the `d = 0` slot is the exceptional element. |
| Moments / spectral / Hoffman / Delsarte / LP | **Provably impossible**: moments 1–3 are Poisson(1) for every derangement; Hoffman bound `= v/(q+1)` attained by Borel subgroups. |
| Character theory (cuspidal/Fourier inequalities) | Yields `Re avg θ ≤ 1/2 + 1/(2q)`, compatible with the spread case; gives no contradiction. |
| Cap/Sidon dichotomy (m5) | Reduces to (R1) `2 ≤ κ ≤ q−2`, (R2) transposition shape, (R3) Sidon. **(R1) genuinely fails at `q = 5,7`**, so any proof needs `q ≥ 11`. |
| Product-set / approximate subgroup (m3 d10) | Reached the reformulation `|S·S| = q+1`; no structure theorem (Kemperman/Helfgott) was successfully applied. |
| Loop / associator (m3 d7) | Abandoned: "no lever" — nothing in the loop axioms forces three fixed points. |
| Galois descent to prime fields (m1 d8) | Abandoned on budget; no theorem produced. |
| Representation theory (m5) | Proved **all linear identities are tautological**: `(Σ_{s∈S}P_s)^t = (−1)^t P_{f^t} + ((q^t−(−1)^t)/(q+1))J` — so no linear/spectral route can work. |
| Pole normal form / Rédei (m2) | Reduced to "Conjecture C" (a perfect covering of `F_q∖{−a₀p₀}` by `q` one-variable square-class sets). The `q = 8` diagnostic shows **size alone cannot exclude it** (`|Z_s| = 3 = q/2−1` for every failure set). |
| Covering/completion criterion (m2) | Equivalent reformulation only; no contradiction extracted. |
| Parity / sign arguments | **Blind for even `q`** (`PGL = PSL ⊆ A_{q+1}`); for odd `q` gives only `PGL ∩ A_{q+1} = PSL`, which *is* useful (leads to the new target) but does not finish. |

**Errors found in swarm work (already retracted — do not resurrect):**
1. "bad `S` has `S ∩ S⁻¹ = {1}`" — **FALSE** (`q=5`: 40/100 bad `S` contain `g, g⁻¹`; `q=7`: 56/196).
   Root cause: a quantifier slip ("for every pair" vs "there exists a pair"). This referee had
   wrongly endorsed it once.
2. "every elliptic element lies in `PSL(2,q)`" — **FALSE** (`q=5`: all 200 valid `S` contain
   elements outside PSL, 400 such elements; `q=9`: 648/828; `q=11`: 605/1815). The Singer-cycle
   generator is the counterexample. Only the *conditional* version is true: `T ⊆ A_{q+1} ⟹ S ⊆ PSL`.
3. "the `PGL∖PSL` coset is odd iff `q ≡ 3 mod 4`" — **FALSE**; it is entirely odd for **every**
   odd `q` (verified `q = 5,7,9,11,13`).
4. "the tangent lemma degenerates because `b = 0, c = 0` elements cannot be elliptic" — **FALSE**;
   the lemma is applied to a *translate* `S·u`, whose elements need not be elliptic.
5. "each reflection of `D_{2(q+1)}` fixes exactly one point" — **FALSE** for odd `q`:
   `(q+1)/2` are elliptic.
6. "`S ⊆ T` in the dihedral case" via Cauchy–Davenport — **FALSE**; `C_{q+1}` is composite, the
   theorem does not apply. Correct conclusion: `S` lies in a *regular* subgroup of order `q+1`.
7. A claim that a bad `q=9` set has `f` of cycle type `(8,2)` — **FALSE**; all 180 are `(4,4,2)`.

## 6. Constraints and preferences (person's words)

* **"Do not make verification for q=23 or any other value of q."** — no further computational
  `q`-verification. (Verification already done up to `q = 19` stands.)
* Second swarm brief (verbatim in the task): *"PROVE the PSL/PGL case … for all q >= 11. (Do NOT
  do computational verification for specific values of q — that is explicitly forbidden; the
  task is a general mathematical proof.)"*
* Earlier: the person wanted "Sharply transitive sets in PGL(2,q).tar.gz" used as the base, and
  asked to check whether `q > 7` suffices (answer: no, `q = 9` fails).
* Style: the person is fine with long autonomous runs and wants refereed, honest reports.

## 7. Files and identifiers

* `RequestProject/Stability.lean` — **new**, the reduction. Contains `PGL2.IsStableSet`,
  `PGL2.IsStableConclusion`, `PGL2.card_projectiveLine`, `PGL2.stable_inj`,
  `PGL2.stable_conclusion_of_missing`, `PGL2.stable_missing_of_conclusion`,
  `PGL2.stable_conclusion_iff_missing` (all proved, axioms `propext, Classical.choice,
  Quot.sound`), and `PGL2.stability_conjecture` (stated, **one `sorry`** at the hard step).
* `RequestProject/Lemma2.lean` — **repaired** for the current Mathlib (three fixes: removed a
  stale `simp only at h`; `simp only at hall` → `norm_num at hall`; `(Set.toFinite S).toFinset`
  → `S.toFinset` in `prod_slopes`/`prod_single` because the `Fintype ↑S` instances differ).
* `RequestProject/{Defs,Basic,Theorem1}.lean` — unchanged, build.
* **Build:** `cd repo && for f in Defs Basic Lemma2 Theorem1 Stability; do LEAN_PATH=.:$LEAN_PATH lean -o RequestProject/$f.olean RequestProject/$f.lean; done`.
  Result: 0 errors; `Stability.lean` has exactly 1 `sorry`. (Do not leave `.olean`/`.ir` files
  in `RequestProject/`; they are regenerable.)
* `results/stability.md` — the full referee write-up (data table, counterexample, corrected
  dihedral case, all verified partial results, the second swarm's results).
* `.scratch/` — scripts: `stab.py` (field + PGL model + exhaustive search), `stab2.py` (bitset),
  `stab3.py` (conjugacy-reduced), `verify.py` (independent `q=9` check), `verify_dih3.py`,
  `verify_m2.py`, `verify_tangent.py`, `check_m2_V.py`, `analyze.py`. `.scratch/` is a cache.
* Swarm records: `.ultramath/smvr3683u/` (swarm 1, ended), `.ultramath/smvrhlrqe/` (swarm 2,
  `state: exhausted`). Both are **done**; do not restart them. Reports worth reading:
  `.ultramath/smvrhlrqe/m8/stability-structures.md` (Thm C, Thm E, Thm F/F3),
  `.ultramath/smvrhlrqe/m7/SUMMARY.md` (defect of translates),
  `.ultramath/smvrhlrqe/m1/report.md` (triple-product criterion),
  `.ultramath/smvrhlrqe/m5/cap_theorem.md` (large-cap theorem),
  `.ultramath/smvrhlrqe/m3/paper.md` (normal form, anisotropy, `E_v`).

## 8. Concrete next steps for the new target

**Goal:** for `q ≡ 1 mod 4`, `q ≥ 13`, `PSL(2,q)` has no valid `q`-clique of elliptic elements
generating it. (No `q`-verification allowed; a general proof is wanted.)

1. **Work entirely inside `PSL(2,q)`.** Replace the Singer-cycle/regular-subgroup machinery by
   the half-tori `C_{(q+1)/2}`. Count: `q(q−1)/2` such tori, `(q−1)/2` non-identity elements
   each, `q(q−1)²/4` elliptic elements total. A `q`-clique with `1` uses `q−1` elliptic
   elements, so it can occupy at most `⌊2(q−1)/(q−1)⌋ = 2` per torus if it met only `(q−1)/2`
   tori; exploit that `q−1` is much larger than `(q−1)/2`.
2. **Use the `q = 9` structure as the model to contradict.** At `q = 9`: 8 elements of order 5 in
   8 distinct tori, `max_T |S∩T| = 2`, `|S·S| = 65 ≫ 10`, `cap ≡ ≤1`. Show that for
   `q ≥ 13` the same "spread" configuration cannot reach size `q` — e.g. bound the size of a
   clique that meets every half-torus in at most 2 elements using the anisotropy criterion
   `β² − 4Q(v)Q(w)` non-square and the constraint `T_v` non-square.
3. **Try m7's defect-of-translates identity in `PSL` form.** `Ψ(Su) = G(u(∞))/G(u(0))` with
   `G(x) = f(x)(B₀−x)/(A₀−x)`. Inside `PSL`, the translates `u` are restricted, so the system
   of cross-ratio equations is over a smaller group — look for inconsistency.
4. **Exploit `q ≡ 1 mod 4`.** Then `−1` is a square, `(q+1)/2` is odd, and `C_{(q+1)/2}` has odd
   order (so no involutions inside the half-tori). Compare with `q ≡ 3 mod 4` where `D_{q+1}`
   lives in `A_{q+1}` and the situation is genuinely different. Never conflate the two cases.
5. **Sanity anchors (already computed, do not recompute):** `q = 9` is the unique known failure
   of the new target (180 = exactly the valid `S ⊆ PSL(2,9)`); `q = 5, 13, 17` are `≡ 1 mod 4`
   but `q = 5` is below range and `q = 13, 17` have no bad `S` at all.
6. If a swarm is used, seed it **only** with §3 and §8 and forbid `q`-verification. Two previous
   8-member swarms (16 member-runs) produced the verified structure in §4 but no proof.
