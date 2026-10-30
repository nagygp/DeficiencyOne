# Deficiency-one formalization

Lean 4 / Mathlib formalization of

> G. Korchmáros, G. P. Nagy, T. Szőnyi,
> *Fixed points and rigidity in the deficiency-one case over prime-power fields*

The paper's source is at `../attachments/you-are-an-expert-hyxg/` (`.tex` and `.pdf`).

## Layout: one file per section of the paper

| paper | file | contents |
| --- | --- | --- |
| §1 Introduction | `Defs.lean` | `PGL2 K`, `P1 K`, the action on `Ω = ℙ¹`, `IsAdmissible`, `IsMissingPerm`, `numFixed` (`f`), `IsSplit`/`IsNonsplit`, `invCoord`/`lineForm`/`IsCollinear`, `hammingDist`, `agreementSet`; all of `card_P1`, `invCoord_normalized`, `exists_isMissingPerm`, `even_numFixed` **proved** — the file is `sorry`-free |
| §2 The fixed-point bound | `Section2FixedPointBound.lean` | **Lemma 4** `card_zeros_derivative_le` (**proved**, plus the `p^r` and `ZMod p` forms), **Lemma 5** `missingPerm_ne_one` (**proved**) |
| §3 Covering curves | `Section3PositiveFixedGap.lean` | counting identity `2e + f = q + 1` (**proved**), `t = q - e` (**proved**), split involutions fix exactly two points (**proved**), **Lemma 6** in full (`d(σ u) = d(u)` and the Menelaus cross-ratio identity, **proved**), `h_u ∘ σ = h_u` (**proved**), **Proposition 9** (cover by `3f−6` lines, **proved**), Theorem 8 (**proved**), Lemma 7's parity (**proved**), the conjugation of the involution plane (`lineForm_conj`, `Tmat`, **proved**); still `sorry`: Theorem 11 (f = 2 ⟹ collinear), Lemma 12 (line bound), Lemma 10 |
| §4 Rigidity | `Section4Rigidity.lean` | **Corollary 16** `hammingDist_ge_div_three` (**proved** from Theorem 15), the counting identity `d_H + |agreement| = q + 1` (**proved**); still `sorry`: **Lemma 14** (interpolation), **Theorem 15** (Hamming rigidity), **Theorem 17** (common fixed point) |
| affine model (§2–3 tool) | `AffineModel.lean` | `coord : ℙ¹ ≃ K ∪ {∞}` with equivariance, `mobius`, the involutions `s_u = [[u, c-u²],[1,-u]]`, the structure `AffineData` packaging `σ(∞)=∞` with `s_u(X)=u+d(u)/(X-u)` and `σ(x)=x-d'(x)`, and the conjugation lemmas |
| main results | `MainTheorem.lean` | **Theorem 1** `numFixed_le`, **Theorem 2** `card_le_mul_sqrt_add`, **Theorem 3** `hammingDist_ge` — all three **proved**, the file is `sorry`-free; the unproved inputs sit in §3 (Lemma 12) and §4 (Theorems 15, 17) |

## Status

| result | status |
| --- | --- |
| Lemma 4 (`Polynomial.card_zeros_derivative_le`) | proved, no `sorry`; axioms `propext, Classical.choice, Quot.sound` |
| `card_P1` | proved |
| affine model: `coord`, `ptFin`/`ptInf`, `equivWithTop`, `coord_smul`, `mobius`, `invMat`, `invGL`, `invClass`, `mobius_invGL_fin`, `exists_smul_eq_ptInf`, `numFixed_conjPerm`, `isAdmissible_conjSet`, `isMissingPerm_conjSet` | proved |
| Theorem 1 `numFixed_le` | **proved, no `sorry`**; axioms `propext, Classical.choice, Quot.sound` |
| `numFixed_le_normalized` | proved, no `sorry` |
| Lemma 5 `missingPerm_ne_one` | proved, no `sorry` (uses `eberhard_theorem1` and `card_le_four_of_forall_sq`) |
| `card_le_four_of_forall_sq` (elementary abelian 2-subgroups of `PGL₂(K)`, `K` odd, have order ≤ 4) | proved, no `sorry` (via `not_four_anticommute` + `anticommute_lifts_of_commute`) |
| `Polynomial.deriv_eq_sum` (Lagrange identity), `interpPoly`, `sum_univ_eq_zero` | proved |
| `Defs`: `invCoord_normalized`, `exists_isMissingPerm`, `even_numFixed` | **proved, no `sorry`**; `Defs.lean` is `sorry`-free |
| §3 `lineForm_v2` (the line of a difference `ρ_c - ρ_a`) | **proved, no `sorry`** |
| §3 `rho_triple_eval_zero` (the three factors of `H` vanish at every graph point; extracted from `cover_polynomial`) | **proved, no `sorry`** |
| §3 conjugation of the involution plane: `tz`, `Nmat`, `pair`, `Tmat`, `pair_eq_trace`, `pair_Tmat`, `card_conjSet`, `Tmat_ne_zero`, `lineForm_conj` | **proved, no `sorry`** |
| §3 counting: `card_fixPoints_of_isSplit` (a split involution fixes exactly two points), `two_mul_card_splitPart_add_numFixed` (`2e + f = q + 1`), `card_nonsplitPart` (`t = q - e`) | proved, no `sorry` |
| §3 Lemma 6, **both** assertions: `cover_menelaus_d` (`d(σ u) = d(u)`) and `cover_menelaus_cross` (the Menelaus cross-ratio identity) | proved, no `sorry` |
| §3 Lemma 7 in full, on `Ω`: `huOmg` (`h_u` extended by `h_u(∞) = 1`), `huOmg_comp_sigma` (`h_u ∘ σ = h_u`), `huOmg_comp_sv` (`h_u ∘ s_u = h_u`), and `cover_fibre_parity` (fibre parity), via `hu_sv_invariant`, `even_card_of_involutive_no_fixed`, `even_sub_of_even` | proved, no `sorry` |
| §3 Theorem 8 ingredients: `fixedFin` (`E`, the finite fixed points of `σ`), `mem_fixedFin`, `numFixed_eq_fixedFin_card` (`f = |E| + 1`), `rho` (`ρ_c(X,Y) = (Y-(X-c)²)/d(c)`), `rho_eval` (`ρ_c(u,d(u)) = h_u(c)`), `rho_totalDegree_le` (`deg ρ_c ≤ 2`), `rho_eval_at`, `rho_sub_one_ne_zero` (`ρ_c - 1 ≠ 0`), `rho_eq_rho_imp` (`ρ_c = ρ_a ⟹ c = a`), `card_fibre_one`/`card_fibre_at` (the fibres of `h_u` over `F` are singletons), `sv_fix_ne_ptInf`/`sv_fix_quad` (fixed points of `s_u`), `out_invClass_eq_smul`/`invCoord_invClass` (the involution-plane coordinates of `s_u` are `[u : d(u)-u² : 1]` up to a scalar) | proved, no `sorry` |
| §3 product machinery: `prod_erase_zero_eq_neg_one`, `prod_erase_zero_erase`, `prod_erase_sub_eq_neg_one`, `prod_erase_erase_sub`, `prod_erase_erase_sub'`, `prod_menelaus`, `prod_special`, `label_eq_iff`, `sv`/`sv_mem`/`sv_ptInf`/`sv_sq`/`sv_apply`/`coord_sv_smul`, `sf_sf`, `factor_eq_sv` | proved, no `sorry` |
| §3 **Theorem 8** `cover_polynomial` | **proved, no `sorry`** |
| §3 **Proposition 9** `exists_cover_by_lines` | **proved, no `sorry`** (both branches) |
| §3 `exists_nonsplit_cover_normalized`, `exists_nonsplit_cover` (the nonsplit half of Prop 9: `f − 1` lines `L_c`), `isInvolution_conj`, `isSplit_conj` | **proved, no `sorry`** |
| §3 chunk (1) of Lemma 10: `exists_conj_eq_diag` (every split involution is conjugate to `diag(1,-1)`), `eq_diagInv_of_fixes`, `exists_translate`, `fixedPointFree_conj`, `card_splitLine_conj` (the conjugation transport of the counted set) and `exists_reduce_diag` (the reduction with its side conditions) | **proved, no `sorry`** |
| §3 chunk (2) of Lemma 10: `line_parametrize` (the line `L` with `[1 : 0 : 0] ∉ L` is parametrized by `ℙ¹`: `lineForm_coord_ne_zero`, `invCoord_injOn_involutions`, `exists_involution_on_line`), with `lineForm_diagInv_iff`, `tz_injective_on_trace_zero`, `invCoord_one_eq_zero` | **proved, no `sorry`** |
| §3 chunk (3) of Lemma 10: `exists_fixed_point_diag_mul_iff` and its `-4BC` form `exists_fixed_point_diag_mul_iff_four` (`diag(1,-1)·s` has a fixed point on `ℙ¹` iff `-BC` is a square), with `exists_fixed_point_iff_eigenvector`, `gl_smul_eq_mulVec`, `Dmat`, `isSquare_four_mul` | **proved, no `sorry`** |
| §3 chunk (4) of Lemma 10: `card_nonsquare_neg` (`2 * #{x : -x a nonsquare} = q - 1`), `card_nonsquare_bc` (`2 * #{[B:C] : -B*C a nonsquare} = q - 1`), with `card_nonsquare_eq_card_ne_zero_isSquare`, `IsNonsquareBC` and its values at `ptInf` / `ptFin t` | **proved, no `sorry`** |
| §1 `eq_of_isMissingPerm` (uniqueness of the missing permutation) | **proved, no `sorry`** |
| §3 **Lemma 10** `split_off_line` | **proved, no `sorry`** (assembled from chunks (1)–(4) via `split_off_line_normalized`) |
| §3: `numFixed_eq_two_imp_collinear` (Thm 11), `card_lineTrace_le` (Lemma 12) | stated, `sorry` |
| §4 `hammingDist_ge_div_three` (Cor 16) | **proved, no `sorry`** (contrapositive of Theorem 15), depends on `sorryAx` only through `hamming_rigidity` |
| §4: `interpolation_rigidity` (Lemma 14), `hamming_rigidity` (Thm 15), `common_fixed_point_rigidity` (Thm 17) | stated, `sorry` |
| **Theorem 3** `hammingDist_ge` | **proved, no `sorry`** (contrapositive of Theorem 17 plus the counting identity), depends on `sorryAx` only through `common_fixed_point_rigidity` |
| **Theorem 2** `card_le_mul_sqrt_add` | **proved, no `sorry`** (nonsplit cover by `f − 1` lines + Lemma 12 + `2e + f = q + 1`); depends on `sorryAx` only through `card_lineTrace_le` |
| Lemma 13 | not formalized: needs the two-cycle normalization `σ(0)=∞, σ(∞)=0` |

Sorry inventory: **5** — `Defs` 0, §3 2, §4 3, `MainTheorem` 0. §1, §2, the affine model and the
file of main results are `sorry`-free. All three main theorems are proved; what remains unproved
elsewhere is Lemma 12 for Theorem 2 and Theorems 15/17 for Theorem 3.

The three remaining §3 gaps and what they need:

* `split_off_line` (Lemma 10) — **proved**, from the four chunks below plus
  `split_off_line_normalized`, which combines them: `exists_reduce_diag` (chunk 1),
  `exists_involution_on_line`/`invCoord_injOn_involutions`/`lineForm_coord_ne_zero` (chunk 2),
  `exists_fixed_point_diag_mul_iff` (chunk 3) and `card_nonsquare_bc` (chunk 4), with
  `isNonsquareBC_mk` and `isSquare_sq_mul` bridging the last two.
  (1) The reduction to `R = [1 : 0 : 0]`: every split involution is conjugate to `diag(1,-1)`
  (`exists_conj_eq_diag`) and the counted set transports along the conjugation of the involution
  plane (`card_splitLine_conj`, `exists_reduce_diag`).
  (4) Exactly `(q-1)/2` points `[B : C]` of `ℙ¹(K)` have `-B*C` a nonsquare (`card_nonsquare_bc`).
  (2) The parametrization `L(K) ↪ ℙ¹`: for a line through no `[1 : 0 : 0]`, the projection
  `[A : B : C] ↦ [B : C]` is a bijection from the involutions of `L` onto the points of `ℙ¹` with
  `A² + BC ≠ 0` (`line_parametrize`).
  (3) The dictionary "`diag(1,-1)·s` has no fixed point on `ℙ¹` ⟺ `-4BC` is a nonsquare": the lift
  `diag(1,-1)·P = [[A, B], [-C, A]]` has characteristic determinant `(A - a)² + BC`, which vanishes
  for some `a` exactly when `-BC` is a square (`exists_fixed_point_diag_mul_iff`), and a projectivity
  has a fixed point exactly when a lift has an eigenvector
  (`exists_fixed_point_iff_eigenvector`).
* `numFixed_eq_two_imp_collinear` (Theorem 11) — needs Lemma 10 together with the `f - 1`
  nonsplit-cover lines of Proposition 9, which are now available (`exists_nonsplit_cover`); the
  remaining ingredient is `split_off_line`.
* `card_lineTrace_le` (Lemma 12) — the paper's proof invokes the Hasse–Weil bound for a genus-one
  curve (eq. `cover-quartic-sum`, citing Silverman Ch. V §1) and quadratic character sums over
  `𝔽_q`. Neither is in Mathlib, so Theorem 2 is blocked on a formalization of the Hasse bound.

### Hypotheses of the affine-model lemmas in §3

`AffineData` records only the normalization `σ(∞) = ∞`, the labelling `S = {s_u}`, the values
`d(u) ≠ 0` with an interpolating polynomial of degree `≤ q - 1`, and `sf u = u - d'(u)`. That is
**not** enough to force `d(σ u) = d(u)`: for a generic nowhere-zero `d` and its interpolant `D`,
the map `u ↦ u - D'(u)` violates it (checked numerically for `q = 5, 7, 11`). The implication
needs the incidence identity (1) linking `S` and `σ`, so `cover_menelaus_d`,
`cover_menelaus_cross`, `cover_hu_comp_sigma`, `cover_fibre_parity` and `cover_polynomial` carry
`IsAdmissible S`, `IsMissingPerm S σ` and `σ * σ = 1` as explicit hypotheses — the standing ones
of the paper's §§2–4.

### Lemma 7 as stated

`cover_fibre_parity` is now stated on `ℙ¹` (not on the affine line) and uses `huOmg`, the extension
of `h_u` with `h_u(∞) = 1`. This is required: the paper's fibre is `Ω = ℙ¹` and `s_u` swaps `u`
with `∞` (`sv_smul_ptFin_self`), so `s_u` does not act on `𝔽_q`. Both invariances
(`huOmg_comp_sigma`, `huOmg_comp_sv`) are proved, which is what makes the parity argument
available, and the parity count is now proved: `cover_fibre_parity`.

`../RequestProject/` is a **different** development (Eberhard's sharply transitive sets, for the
stability conjecture) and defines its own `PGL2`; do not import the two together.

## Building

```
./build.sh
```

There is no lakefile: the script drives `lean` directly and writes object files to
`../.scratch/build` (a cache) so the files can import each other as `DeficiencyOne.<Name>`.
It needs the toolchain on `PATH` and `LEAN_PATH` pointing at Mathlib, which this VM provides.

## Numerical check of Lemma 4

```
python3 lemma4_sanity.py
```

searches random polynomials of degree at most `q−1` over `F_9, F_25, F_27, F_49, F_7` and
compares the largest number of zeros of `d'` with the bound `q − q/p − 1`. No violations; the
bound is attained for `q = 7`, where it coincides with the root bound.
