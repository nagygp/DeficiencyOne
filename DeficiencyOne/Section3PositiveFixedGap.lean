/-
Copyright (c) 2026 The Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Mathlib Contributors
-/
import Mathlib
import DeficiencyOne.AffineModel

/-!
# §3. Covering curves and the positive fixed-point gap

Statements from Section 3 of the paper. This section works under the hypotheses of Theorem 1
and, for the covering-curve construction, assumes `f > 0` and the normalization

`σ(∞) = ∞`, `S = {s_u : X ↦ u + d(u) / (X - u) | u ∈ 𝔽_q}`,

in which `d(u) ≠ 0` for every `u`. Writing `F = Fix_Ω(σ)` and `E = F \ {∞}`, the paper proves:

* **Lemma 6** (`cover_menelaus_d`, `cover_menelaus_cross`) : `d(σ(x)) = d(x)`, and the
  Menelaus-type cross-ratio identity `(u-b) d(a) (σ(b)-a) = (u-a) d(b) (σ(a)-b)`.
* **Lemma 7** (`huOmg_comp_sigma`, `huOmg_comp_sv`, `cover_fibre_parity`) : the function
  `h_u(x) = (d(u) - (u-x)(u-σ(x)))/d(x)`, extended by `h_u(∞) = 1` (`huOmg`), is invariant under
  `σ` and under `s_u`, and every fibre of `h_u` has a number of `σ`-fixed points congruent mod 2
  to its number of `s_u`-fixed points. The fibre is taken in `Ω = ℙ¹`, since `s_u` swaps `u` with
  `∞` and so does not act on the affine line.
* **Theorem 8** (`cover_polynomial`) : for `f ≥ 4` and distinct `a, b ∈ E`, there is a nonzero
  polynomial `H(X, Y)` with `H(u, d(u)) = 0` for all `u ∈ 𝔽_q` and `deg H ≤ 6f - 12` (the paper
  writes it down explicitly as a product of the factors `ρ_c - 1`, `ρ_c - ρ_a`, `ρ_c - ρ_b`).
* **Proposition 9** (`exists_cover_by_lines`) : the graph points of the nonsplit elements of
  `S` are covered by the explicit polynomial `N(X,Y) = ∏_{c ∈ E} (Y - (X-c)² - d(c))` of degree
  `2(f-1)`; in the involution plane they are covered by at most `f - 1` lines, and the whole of
  `S` by at most `3f - 6` lines when `f ≥ 4` (**proved**: `exists_cover_by_lines_of_fixes_ptInf`
  in the normalization `σ(∞) = ∞`, and `exists_cover_by_lines` in general, the general case by
  conjugating a fixed point of `σ` to `∞` and pulling the lines back along the conjugation of
  the involution plane).
* **Conjugation of the involution plane** (`tz`, `pair`, `Tmat`, `pair_Tmat`, `lineForm_conj`,
  `Tmat_ne_zero`) : conjugation by `A ∈ GL₂(K)` acts linearly on the coordinates `[A : B : C]`,
  so it maps lines to lines and preserves incidences; the dual map `Tmat A` is injective. This is
  what transports a line cover across a change of coordinates.
* **Lemma 10** (`split_off_line`) : if `R` is a split involution and `L` a line of the
  involution plane with `R ∉ L`, then exactly `(q-1)/2` points of `L(𝔽_q)` represent involutions
  compatible with `R`.
* **Theorem 11** (`numFixed_eq_two_imp_collinear`) : if `f = 2` then `S` is collinear.
* **Lemma 12** (`card_lineTrace_le`) : if `S` is noncollinear then every projective line `L` of
  the involution plane satisfies `|S ∩ L| ≤ 2√q + 12`.
* **Theorem 13** (two fixed points, `MainTheorem.lean`) : the quantitative conclusion, i.e.
  Theorem 2 of the paper.

The Lemmas 6, 7 and 10 and Theorem 8 are stated in the affine model of `AffineModel.lean`, in
terms of the structure `AffineData` that bundles the normalization `σ(∞) = ∞`, the labelling
`s_u` of `S` and the polynomial `d`.

We also record here the counting identity of the preamble of §3, `2e + f = q + 1` where `e` is
the number of split elements of `S`, and its consequence `t = q - e` for the number `t` of
nonsplit elements.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Classical
open scoped Matrix

namespace PGL2

variable {K : Type*} [Field K] [Fintype K]

/-! ### Split and nonsplit members of `S` -/

/-- The split elements of `S`. -/
def splitPart (S : Set (PGL2 K)) : Set (PGL2 K) := {s ∈ S | IsSplit s}

/-- The nonsplit elements of `S`. -/
def nonsplitPart (S : Set (PGL2 K)) : Set (PGL2 K) := {s ∈ S | IsNonsplit s}

/-- The affine coordinate is injective. -/
lemma coord_injective : Function.Injective (coord (K := K)) := by
  intro a b h
  rw [← ptOf_coord a, ← ptOf_coord b, h]

/-- Fix points are carried along by conjugation: `y` is fixed by `g s g⁻¹` exactly when
`g⁻¹ • y` is fixed by `s`. -/
lemma mem_fixPoints_conj {g s : PGL2 K} {y : P1 K} :
    y ∈ fixPoints (g * s * g⁻¹) ↔ g⁻¹ • y ∈ fixPoints s := by
  simp only [fixPoints, Set.mem_ofPred_eq, conj_smul]
  constructor
  · intro h
    have h' := congrArg (fun z => g⁻¹ • z) h
    rwa [← mul_smul, inv_mul_cancel, one_smul] at h'
  · intro h
    rw [h, ← mul_smul, mul_inv_cancel, one_smul]

/-- Conjugation preserves the number of fixed points. -/
lemma card_fixPoints_conj (g s : PGL2 K) :
    Nat.card (fixPoints (g * s * g⁻¹)) = Nat.card (fixPoints s) := by
  classical
  refine Nat.card_congr ?_
  refine
    { toFun := fun y => ⟨g⁻¹ • y.1, (mem_fixPoints_conj (s := s)).1 y.2⟩
      invFun := fun x => ⟨g • x.1, (mem_fixPoints_conj (s := s)).2 ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · show g⁻¹ • (g • _) ∈ fixPoints s
    simpa only [← mul_smul, inv_mul_cancel, one_smul] using x.2
  · intro y
    apply Subtype.ext
    simp only [← mul_smul, mul_inv_cancel, one_smul]
  · intro x
    apply Subtype.ext
    simp only [← mul_smul, inv_mul_cancel, one_smul]

/-- The lift of an involution fixing `∞` is an upper triangular matrix with trace `0` whose
off-diagonal entry `(0,1)` may be nonzero; consequently the involution acts on the affine line
as `x ↦ -x - M₁₀/M₀₀`, a reflection with exactly one fixed point, and it fixes `∞` as well. -/
lemma card_fixPoints_of_smul_ptInf {t : PGL2 K} (ht : IsInvolution t)
    (h2 : (2 : K) ≠ 0) (hinf : t • (ptInf : P1 K) = ptInf) : Nat.card (fixPoints t) = 2 := by
  classical
  set g : GL (Fin 2) K := Quotient.out t with hg
  set M : Matrix (Fin 2) (Fin 2) K := (g : Matrix (Fin 2) (Fin 2) K) with hM
  have hMdet : M.det ≠ 0 := Matrix.GeneralLinearGroup.det_ne_zero g
  -- fixing `∞` forces the lower-left entry to vanish
  have hnone : mobius g none = none := by
    have h := coord_smul t (ptInf : P1 K)
    rw [hinf, coord_ptInf] at h
    exact h.symm
  have h10 : M 1 0 = 0 := by
    by_contra h
    simp only [mobius, mobiusMat, ← hM, if_neg h] at hnone
    exact absurd hnone (by simp)
  -- the trace vanishes, and invertibility keeps the remaining diagonal entry nonzero
  have htr : M 0 0 + M 1 1 = 0 := by
    have h := trace_zero_of_isInvolution ht
    rw [Matrix.trace_fin_two, ← hM] at h
    exact h
  have h11' : M 1 1 = -M 0 0 := by linear_combination htr
  have ha : M 0 0 ≠ 0 := by
    intro h
    have hz : M 1 1 = 0 := by rw [h11', h, neg_zero]
    have hd : M.det = 0 := by rw [Matrix.det_fin_two, h10, hz]; ring
    exact hMdet hd
  -- the action on the affine line
  have hmob : ∀ x : K, mobius g (some x) = some ((M 0 0 * x + M 0 1) / (-(M 0 0))) := by
    intro x
    have hden : M 1 0 * x + M 1 1 ≠ 0 := by
      rw [h10, zero_mul, zero_add, h11']
      exact neg_ne_zero.mpr ha
    simp only [mobius, mobiusMat, ← hM, if_neg hden]
    rw [h10, zero_mul, zero_add, h11']
  have hcoord : ∀ z : K, coord (t • ptFin z) = some ((M 0 0 * z + M 0 1) / (-(M 0 0))) := by
    intro z
    rw [coord_smul, coord_ptFin, ← hg]
    exact hmob z
  have hiff : ∀ x : K, (M 0 0 * x + M 0 1) / (-(M 0 0)) = x ↔ 2 * (M 0 0) * x = -(M 0 1) := by
    intro x
    have hna : -(M 0 0) ≠ 0 := neg_ne_zero.mpr ha
    rw [div_eq_iff hna]
    constructor <;> intro h <;> linear_combination h
  have hkey : ∀ x : K, t • ptFin x = ptFin x ↔ x = -(M 0 1) / (2 * M 0 0) := by
    intro x
    have h2a : 2 * (M 0 0) ≠ 0 := mul_ne_zero h2 ha
    have hcoordx : t • ptFin x = ptFin x ↔ (M 0 0 * x + M 0 1) / (-(M 0 0)) = x := by
      constructor
      · intro h
        have hs : some ((M 0 0 * x + M 0 1) / (-(M 0 0))) = some x := by
          rw [← hcoord x, h, coord_ptFin]
        exact Option.some.inj hs
      · intro h
        apply coord_injective
        rw [hcoord x, coord_ptFin]
        exact congrArg some h
    rw [hcoordx, hiff x, eq_div_iff h2a]
    constructor <;> intro h <;> linear_combination h
  have hset : fixPoints t = ({ptInf, ptFin (-(M 0 1) / (2 * M 0 0))} : Set (P1 K)) := by
    ext y
    have hy : y = ptOf (coord y) := (ptOf_coord y).symm
    cases hc : coord y with
    | none =>
      have hy' : y = ptInf := by rw [hy, hc]; rfl
      rw [hy', fixPoints, Set.mem_ofPred_eq, hinf, Set.mem_insert_iff, Set.mem_singleton_iff]
      simp
    | some x =>
      have hy' : y = ptFin x := by rw [hy, hc]; rfl
      rw [hy', fixPoints, Set.mem_ofPred_eq, hkey x, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · intro h; exact Or.inr (by rw [h])
      · intro h
        rcases h with h | h
        · exact absurd h (ptFin_ne_ptInf x)
        · exact ptFin_injective h
  rw [hset, Nat.card_coe_set_eq, Set.ncard_pair (ptFin_ne_ptInf _).symm]

/-- A split involution fixes exactly two points of the projective line (the "two" in
`2e + f = q + 1`). -/
lemma card_fixPoints_of_isSplit (hodd : Odd (Nat.card K)) {s : PGL2 K} (hs : IsSplit s) :
    Nat.card (fixPoints s) = 2 := by
  classical
  obtain ⟨hsinv, x, hx⟩ := hs
  have hx' : s • x = x := hx
  -- move the fixed point to `∞`
  obtain ⟨g, hg⟩ := exists_smul_eq_ptInf x
  have hcancel : ∀ y : P1 K, g⁻¹ • (g • y) = y := by
    intro y
    rw [smul_smul, inv_mul_cancel, one_smul]
  have hfix : (g * s * g⁻¹) • (ptInf : P1 K) = ptInf := by
    rw [conj_smul, ← hg, hcancel, hx', hg]
  have hinv : IsInvolution (g * s * g⁻¹) := by
    refine ⟨?_, ?_⟩
    · intro h
      have h' : s = 1 := by
        calc s = g⁻¹ * (g * s * g⁻¹) * g := by group
          _ = g⁻¹ * 1 * g := by rw [h]
          _ = 1 := by group
      exact hsinv.1 h'
    · calc (g * s * g⁻¹) * (g * s * g⁻¹) = g * (s * s) * g⁻¹ := by group
        _ = g * 1 * g⁻¹ := by rw [hsinv.2]
        _ = 1 := by group
  rw [← card_fixPoints_conj g s]
  exact card_fixPoints_of_smul_ptInf hinv (two_ne_zero_of_odd_card hodd) hfix

/-- The counting identity of §3: if `e` is the number of split elements of `S` and `f` the
number of fixed points of the missing permutation, then `2e + f = q + 1`.

Distinct elements of `S` have disjoint fixed-point sets, and a point is fixed by `σ` exactly
when no element of `S` fixes it, by equation (1); these sets therefore partition `Ω`. -/
theorem two_mul_card_splitPart_add_numFixed (hodd : Odd (Nat.card K)) (hq : 5 ≤ Nat.card K)
    {S : Set (PGL2 K)} (hS : IsAdmissible S) (hcard : Nat.card S = Nat.card K)
    {σ : Equiv.Perm (P1 K)} (hσ : IsMissingPerm S σ) (hσ2 : σ * σ = 1) :
    2 * Nat.card (splitPart S) + numFixed σ = Nat.card K + 1 := by
  classical
  -- an element of `S` fixing a given point is unique
  have huniq : ∀ (x : P1 K) (s t : PGL2 K), s ∈ S → t ∈ S → s • x = x → t • x = x → s = t := by
    intro x s t hs ht hsx htx
    by_contra hne
    have h := hS.2 s hs t ht hne x
    rw [mul_smul, htx, hsx] at h
    exact h rfl
  -- every point moved by `σ` is fixed by some element of `S`
  have hex : ∀ x : P1 K, σ x ≠ x → ∃ s : PGL2 K, s ∈ S ∧ s • x = x :=
    fun x hx => (hσ x x).2 (Ne.symm hx)
  -- a choice of such an element, as a function on the moved points
  let sfun : {x : P1 K // σ x ≠ x} → PGL2 K := fun x => Classical.choose (hex x.1 x.2)
  have sfun_mem : ∀ x : {x : P1 K // σ x ≠ x}, sfun x ∈ S :=
    fun x => (Classical.choose_spec (hex x.1 x.2)).1
  have sfun_fix : ∀ x : {x : P1 K // σ x ≠ x}, sfun x • x.1 = x.1 :=
    fun x => (Classical.choose_spec (hex x.1 x.2)).2
  -- the pairs (split element of `S`, point it fixes)
  let P : Type _ := {p : ↥(splitPart S) × P1 K // p.2 ∈ fixPoints (p.1 : PGL2 K)}
  have hbij : Nat.card P = Nat.card {x : P1 K // σ x ≠ x} := by
    let toP : P → {x : P1 K // σ x ≠ x} := fun p =>
      ⟨p.1.2, fun h => ((hσ p.1.2 p.1.2).1 ⟨p.1.1, p.1.1.2.1, p.2⟩) h.symm⟩
    let ofP : {x : P1 K // σ x ≠ x} → P := fun x =>
      ⟨(⟨sfun x, sfun_mem x, hS.1 _ (sfun_mem x), ⟨x.1, sfun_fix x⟩⟩, x.1), sfun_fix x⟩
    have hleft : ∀ p, ofP (toP p) = p := by
      intro p
      apply Subtype.ext
      apply Prod.ext
      · apply Subtype.ext
        exact huniq p.1.2 (sfun (toP p)) (p.1.1 : PGL2 K) (sfun_mem (toP p)) p.1.1.2.1
          (sfun_fix (toP p)) p.2
      · rfl
    have hright : ∀ x, toP (ofP x) = x := by
      intro x
      apply Subtype.ext
      rfl
    exact Nat.card_congr { toFun := toP, invFun := ofP, left_inv := hleft, right_inv := hright }
  -- the same pairs, counted over the label
  have hP : Nat.card P = 2 * Nat.card (splitPart S) := by
    have ec : P ≃ (Σ s : ↥(splitPart S), ↥(fixPoints (s : PGL2 K))) :=
      { toFun := fun p => ⟨p.1.1, ⟨p.1.2, p.2⟩⟩
        invFun := fun q => ⟨(q.1, q.2.1), q.2.2⟩
        left_inv := fun p => by apply Subtype.ext; rfl
        right_inv := fun q => by apply Sigma.ext <;> rfl }
    rw [Nat.card_congr ec, Nat.card_sigma]
    have h2' : ∀ s : ↥(splitPart S), Nat.card ↥(fixPoints (s : PGL2 K)) = 2 :=
      fun s => card_fixPoints_of_isSplit hodd s.2.2
    rw [Finset.sum_congr rfl (fun s _ => h2' s), Finset.sum_const, Finset.card_univ,
      ← Nat.card_eq_fintype_card (α := ↥(splitPart S))]
    rw [Nat.nsmul_eq_mul, mul_comm]
  -- the points moved by `σ` are all points but its fixed points
  have hcompl : Nat.card {x : P1 K // σ x ≠ x} + numFixed σ = Nat.card K + 1 := by
    have h1 : Fintype.card {x : P1 K // σ x ≠ x} =
        Fintype.card (P1 K) - Fintype.card {x : P1 K // σ x = x} :=
      Fintype.card_subtype_compl (fun x : P1 K => σ x = x)
    have h2 : Fintype.card {x : P1 K // σ x = x} = numFixed σ := Nat.card_eq_fintype_card.symm
    have h3 : Fintype.card (P1 K) = Nat.card K + 1 := by
      rw [← Nat.card_eq_fintype_card, card_P1]
    have h4 : numFixed σ ≤ Nat.card K + 1 := by
      rw [← h2, ← h3]
      exact Fintype.card_subtype_le _
    have h5 : Nat.card {x : P1 K // σ x ≠ x} = Fintype.card {x : P1 K // σ x ≠ x} :=
      Nat.card_eq_fintype_card
    rw [h5, h1, h2, h3]
    omega
  rw [← hP, hbij]
  exact hcompl

/-- Consequently the number of nonsplit elements of `S` is `t = q - e = (q + f - 1) / 2`. -/
theorem card_nonsplitPart (hodd : Odd (Nat.card K)) (hq : 5 ≤ Nat.card K)
    {S : Set (PGL2 K)} (hS : IsAdmissible S) (hcard : Nat.card S = Nat.card K)
    {σ : Equiv.Perm (P1 K)} (hσ : IsMissingPerm S σ) (hσ2 : σ * σ = 1) :
    Nat.card (nonsplitPart S) = Nat.card K - Nat.card (splitPart S) := by
  classical
  have hdisj : Disjoint (splitPart S) (nonsplitPart S) := by
    rw [Set.disjoint_left]
    intro s hs hs'
    exact hs'.2.2 hs.2.2.choose hs.2.2.choose_spec
  have hunion : splitPart S ∪ nonsplitPart S = S := by
    ext s
    constructor
    · rintro (h | h)
      · exact h.1
      · exact h.1
    · intro hs
      by_cases hsp : (fixPoints s).Nonempty
      · exact Or.inl ⟨hs, hS.1 s hs, hsp⟩
      · exact Or.inr ⟨hs, hS.1 s hs, fun x hx => hsp ⟨x, hx⟩⟩
  have hsum : Nat.card (splitPart S) + Nat.card (nonsplitPart S) = Nat.card S := by
    have hu := Set.ncard_union_eq hdisj
    have e3 : S.ncard = (splitPart S).ncard + (nonsplitPart S).ncard := by
      rw [← hu, hunion]
    rw [Nat.card_coe_set_eq (splitPart S), Nat.card_coe_set_eq (nonsplitPart S),
      Nat.card_coe_set_eq S, e3]
  omega

/-! ### The case of two fixed points -/

/-- **Theorem 11 of the paper.** If `f = 2`, then `S` is contained in a projective line of the
involution plane.

In the paper's normalization `F = {∞, c}`, the line is given explicitly by
`d(u) = (u-c)² + d(c)` and `σ(u) = 2c - u` for `u ∈ 𝔽_q`. -/
theorem numFixed_eq_two_imp_collinear (hodd : Odd (Nat.card K)) (hq : 5 ≤ Nat.card K)
    {S : Set (PGL2 K)} (hS : IsAdmissible S) (hcard : Nat.card S = Nat.card K)
    {σ : Equiv.Perm (P1 K)} (hσ : IsMissingPerm S σ) (hf : numFixed σ = 2) :
    IsCollinear S := by
  sorry

/-! ### The line-intersection estimate -/

/-- **Lemma 12 of the paper.** If `S` is noncollinear, then every projective line `L` of the
involution plane meets `S` in at most `2√q + 12` points.

(This is the estimate that turns the explicit cover of Proposition 9 into a lower bound for
`f`: `3f - 6` lines, each carrying at most `2√q + 12` points, must cover `q` points.) -/
theorem card_lineTrace_le (hodd : Odd (Nat.card K)) (hq : 5 ≤ Nat.card K)
    {S : Set (PGL2 K)} (hS : IsAdmissible S) (hcard : Nat.card S = Nat.card K)
    {σ : Equiv.Perm (P1 K)} (hσ : IsMissingPerm S σ) (hnc : ¬ IsCollinear S)
    {v : Fin 3 → K} (hv : v ≠ 0) :
    (Nat.card (lineTrace v S) : ℝ) ≤ 2 * Real.sqrt (Nat.card K) + 12 := by
  sorry

/-! ### The finite fixed points of `σ` and the count `f = |E| + 1` -/

/-- `E`, the finite fixed points of `σ`: the labels `c` with `σ(c) = c`, i.e. `sf c = c`. -/
noncomputable def fixedFin {S : Set (PGL2 K)} {σ : Equiv.Perm (P1 K)} (A : AffineData S σ) :
    Finset K :=
  Finset.univ.filter (fun c => A.sf c = c)

lemma mem_fixedFin {S : Set (PGL2 K)} {σ : Equiv.Perm (P1 K)} (A : AffineData S σ) {c : K} :
    c ∈ fixedFin A ↔ A.sf c = c := by
  classical
  simp [fixedFin]

/-- `f = |E| + 1`: the fixed points of `σ` on `Ω` are `∞` and the `ptFin c` with `sf c = c`. -/
lemma numFixed_eq_fixedFin_card {S : Set (PGL2 K)} {σ : Equiv.Perm (P1 K)} (A : AffineData S σ) :
    numFixed σ = (fixedFin A).card + 1 := by
  classical
  unfold numFixed
  have hE1 : {y : P1 K // σ y = y} ≃ {c : Option K // σ (ptOf c) = ptOf c} :=
    equivWithTop.subtypeEquiv (fun y => by
      show (σ y = y) ↔ (σ (ptOf (coord y)) = ptOf (coord y))
      rw [ptOf_coord y])
  have hE2 : {c : Option K // σ (ptOf c) = ptOf c} ≃
      Option {u : K // σ (ptFin u) = ptFin u} := by
    refine {
      toFun := fun c => match c with
        | ⟨none, h⟩ => none
        | ⟨some u, h⟩ => some ⟨u, (h : σ (ptFin u) = ptFin u)⟩
      invFun := fun c => match c with
        | none => ⟨none, A.σ_inf⟩
        | some u => ⟨some u.1, u.2⟩
      left_inv := by
        intro c
        obtain ⟨c1, h⟩ := c
        cases c1 with
        | none => rfl
        | some u => rfl
      right_inv := by
        intro c
        cases c with
        | none => rfl
        | some u => rfl }
  have hE3 : {u : K // σ (ptFin u) = ptFin u} ≃ {u : K // A.sf u = u} :=
    { toFun := fun u => ⟨u.1, ptFin_injective (by rw [← A.σ_fin u.1]; exact u.2)⟩
      invFun := fun u => ⟨u.1, by rw [A.σ_fin u.1, u.2]⟩
      left_inv := fun u => rfl
      right_inv := fun u => rfl }
  rw [Nat.card_congr (hE1.trans (hE2.trans (Equiv.optionCongr hE3)))]
  rw [Nat.card_eq_fintype_card, Fintype.card_option, ← Nat.card_eq_fintype_card]
  congr 1
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, fixedFin]

/-! ### The Menelaus identity and the invariant function (Lemmas 6 and 7) -/

/-! ### The Menelaus computation of Lemma 6

The proof of `d(σ u) = d(u)` is the product identity

`∏ v, ((x - v) * (sf x - v) - d v) = - d x`,

whose value is symmetric under `x ↔ sf x`; since `sf` is an involution, applying it twice gives
`d (sf x) = d x`. To evaluate the product: the factor with `v = x` is `- d x`, and for `v ≠ x`
the factor is `(x - v) * (sf x - s_v(x))` using `d v = (x - v)(s_v(x) - v)`, where `s_v` is the
involution of `S` labelled by `v`. The incidence identity (1) says the `s_v(x)`, `v ∈ 𝔽_q`, are
exactly the points other than `σ x`; since `s_x(x) = ∞`, the finite ones are `𝔽_q ∖ {sf x}`, so
the remaining two products are both `-1` (the product of `c - v` over `v ≠ c`). -/

/-- `sf` is an involution. -/
lemma sf_sf {S : Set (PGL2 K)} {σ : Equiv.Perm (P1 K)} (A : AffineData S σ)
      (hσ2 : σ * σ = 1) (x : K) : A.sf (A.sf x) = x := by
  have h : σ (σ (ptFin x)) = ptFin x := by
      have h2 : (σ * σ) (ptFin x) = (1 : Equiv.Perm (P1 K)) (ptFin x) := by rw [hσ2]
      simpa using h2
  rw [A.σ_fin, A.σ_fin] at h
  exact ptFin_injective h

/-- The element of `S` labelled by `v`. -/
noncomputable def sv {S : Set (PGL2 K)} {σ : Equiv.Perm (P1 K)} (A : AffineData S σ)
      (v : K) : PGL2 K := invClass v (A.d v) (A.d_ne v)

lemma sv_mem {S : Set (PGL2 K)} {σ : Equiv.Perm (P1 K)} (A : AffineData S σ) (v : K) :
      sv A v ∈ S := (A.isNormal _).2 ⟨v, rfl⟩

/-- `s_v` sends `∞` to `ptFin v`. -/
lemma sv_ptInf {S : Set (PGL2 K)} {σ : Equiv.Perm (P1 K)} (A : AffineData S σ) (v : K) :
      sv A v • (ptInf : P1 K) = ptFin v := by
  apply coord_injective
  have h : sv A v = ((invGL v (A.d v) (A.d_ne v) : GL (Fin 2) K) : PGL2 K) := rfl
  rw [h, coord_smul_class, coord_ptInf, mobius_invGL_inf, coord_ptFin]

/-- The affine coordinate of `s_v • x`. -/
lemma coord_sv_smul {S : Set (PGL2 K)} {σ : Equiv.Perm (P1 K)} (A : AffineData S σ)
      (v x : K) :
      coord (sv A v • ptFin x) = if v = x then none else some (v + A.d v / (x - v)) := by
  rw [sv, coord_smul_invClass]
  by_cases h : v = x
  · subst h
    rw [if_pos rfl, mobius_invGL_at]
  · rw [if_neg h, mobius_invGL_fin _ _ _ (A.d_ne v) (Ne.symm h)]

/-- Two distinct elements of `S` cannot agree at a point. -/
lemma eq_of_smul_eq_sv {S : Set (PGL2 K)} {σ : Equiv.Perm (P1 K)} (A : AffineData S σ)
      (hS : IsAdmissible S) (x : P1 K) {s t : PGL2 K} (hs : s ∈ S) (ht : t ∈ S)
      (h : s • x = t • x) : s = t := by
  by_contra hne
  have h' := hS.2 s hs t ht hne x
  have heq : (s * t) • x = x := by
      rw [mul_smul, ← h, ← mul_smul, (hS.1 s hs).2, one_smul]
  exact h' heq

/-- The labels are determined by the point they send `x` to, so `v ↦ s_v • x` is injective. -/
lemma sv_smul_injective {S : Set (PGL2 K)} {σ : Equiv.Perm (P1 K)} (A : AffineData S σ)
      (hS : IsAdmissible S) (x : K) : Function.Injective (fun v => sv A v • ptFin x) := by
  intro v₁ v₂ h
  have heq : sv A v₁ = sv A v₂ :=
      eq_of_smul_eq_sv A hS (ptFin x) (sv_mem A v₁) (sv_mem A v₂) h
  have h2 : sv A v₁ • (ptInf : P1 K) = sv A v₂ • ptInf := by rw [heq]
  rw [sv_ptInf, sv_ptInf] at h2
  exact ptFin_injective h2


/-- The product of the nonzero elements of a finite field is `-1`. -/
lemma prod_erase_zero_eq_neg_one : ∏ u ∈ Finset.univ.erase (0 : K), u = -1 := by
  have hunits : ∏ x : Kˣ, (x : K) = -1 := by
    calc ∏ x : Kˣ, (x : K) = ((∏ x : Kˣ, x : Kˣ) : K) := by rw [Units.coe_prod]
      _ = ((-1 : Kˣ) : K) := by rw [FiniteField.prod_univ_units_id_eq_neg_one]
      _ = -1 := rfl
  rw [← hunits]
  refine Finset.prod_bij (fun (u : K) (hu : u ∈ Finset.univ.erase (0 : K)) =>
    Units.mk0 u (Finset.mem_erase.1 hu).1) ?_ ?_ ?_ ?_
  · intro u _; exact Finset.mem_univ _
  · intro u₁ h₁ u₂ h₂ heq
    exact Units.ext_iff.1 heq
  · intro x _
    refine ⟨(x : K), ?_, ?_⟩
    · rw [Finset.mem_erase]
      exact ⟨Units.ne_zero x, Finset.mem_univ _⟩
    · exact Units.ext rfl
  · intro u _; rfl


/-- `∏ (c - v)` over all `v ≠ c` is `-1`. -/
lemma prod_erase_sub_eq_neg_one (c : K) : ∏ v ∈ Finset.univ.erase c, (c - v) = -1 := by
  rw [← prod_erase_zero_eq_neg_one]
  refine Finset.prod_bij (fun (v : K) (_ : v ∈ Finset.univ.erase c) => c - v) ?_ ?_ ?_ ?_
  · intro v hv
    rw [Finset.mem_erase]
    refine ⟨?_, Finset.mem_univ _⟩
    intro h
    exact (Finset.mem_erase.1 hv).1 (by rw [sub_eq_zero.1 h])
  · intro v₁ _ v₂ _ heq
    exact sub_right_injective heq
  · intro u hu
    refine ⟨c - u, ?_, ?_⟩
    · rw [Finset.mem_erase]
      refine ⟨?_, Finset.mem_univ _⟩
      intro h
      exact (Finset.mem_erase.1 hu).1 (by rw [sub_eq_self.1 h])
    · rw [sub_sub_cancel]
  · intro v _; rfl


/-- The labels of the points `s_v(x)`, `v ≠ x`, are exactly `K ∖ {sf x}`: this is the incidence
identity (1) together with `s_x(x) = ∞`. -/
lemma label_eq_iff {S : Set (PGL2 K)} {σ : Equiv.Perm (P1 K)} (A : AffineData S σ)
      (hσ : IsMissingPerm S σ) (x : K) :
      ∀ w : K, (∃ v : K, v ≠ x ∧ v + A.d v / (x - v) = w) ↔ w ≠ A.sf x := by
  intro w
  constructor
  · rintro ⟨v, hvx, hvw⟩
    have hc := coord_sv_smul A v x
    rw [if_neg hvx] at hc
    have hpt : sv A v • ptFin x = ptFin w := by
      apply coord_injective
      rw [hc, hvw, coord_ptFin]
    have hmem : ptFin w ≠ σ (ptFin x) := (hσ (ptFin x) (ptFin w)).1 ⟨sv A v, sv_mem A v, hpt⟩
    intro hw
    exact hmem (by rw [A.σ_fin, hw])
  · intro hw
    have hne : ptFin w ≠ σ (ptFin x) := by
      rw [A.σ_fin]
      exact fun h => hw (ptFin_injective h)
    obtain ⟨s, hs, hsw⟩ := (hσ (ptFin x) (ptFin w)).2 hne
    obtain ⟨v, rfl⟩ := (A.isNormal s).1 hs
    have hcoord : coord (sv A v • ptFin x) = some w := by
      rw [show sv A v • ptFin x = ptFin w from hsw, coord_ptFin]
    have hc := coord_sv_smul A v x
    rw [hcoord] at hc
    by_cases hvx : v = x
    · rw [if_pos hvx] at hc
      exact absurd hc (by simp)
    · rw [if_neg hvx] at hc
      exact ⟨v, hvx, (Option.some.inj hc.symm)⟩


/-- **The product identity of Lemma 6**: `∏ v, ((x - v)(sf x - v) - d v) = - d x`. -/
lemma prod_menelaus {S : Set (PGL2 K)} {σ : Equiv.Perm (P1 K)} (A : AffineData S σ)
      (hS : IsAdmissible S) (hσ : IsMissingPerm S σ) (x : K) :
      ∏ v : K, ((x - v) * (A.sf x - v) - A.d v) = -A.d x := by
  classical
  have hF : (x - x) * (A.sf x - x) - A.d x = -A.d x := by ring
  have hprod : ∏ v ∈ Finset.univ.erase x, ((x - v) * (A.sf x - v) - A.d v) = 1 := by
    have key : ∀ v ∈ Finset.univ.erase x,
        ((x - v) * (A.sf x - v) - A.d v) = (x - v) * (A.sf x - (v + A.d v / (x - v))) := by
      intro v hv
      have hvx : v ≠ x := (Finset.mem_erase.1 hv).1
      have hne : x - v ≠ 0 := sub_ne_zero.2 (Ne.symm hvx)
      obtain ⟨a, ha⟩ : ∃ a : K, a = A.d v / (x - v) := ⟨_, rfl⟩
      have hvda : (x - v) * a = A.d v := by rw [ha, mul_comm, div_mul_cancel₀ _ hne]
      rw [← ha, ← hvda]
      ring
    rw [Finset.prod_congr rfl key, Finset.prod_mul_distrib, prod_erase_sub_eq_neg_one x]
    have h2' : ∏ v ∈ Finset.univ.erase x, (A.sf x - (v + A.d v / (x - v))) = -1 := by
      rw [← prod_erase_sub_eq_neg_one (A.sf x)]
      refine Finset.prod_bij (fun (v : K) (_ : v ∈ Finset.univ.erase x) =>
        v + A.d v / (x - v)) ?_ ?_ ?_ ?_
      · intro v hv
        rw [Finset.mem_erase]
        exact ⟨(label_eq_iff A hσ x _).1 ⟨v, (Finset.mem_erase.1 hv).1, rfl⟩, Finset.mem_univ _⟩
      · intro v₁ h₁ v₂ h₂ heq
        refine sv_smul_injective A hS x ?_
        refine coord_injective ?_
        have c₁ := coord_sv_smul A v₁ x
        have c₂ := coord_sv_smul A v₂ x
        rw [if_neg (Finset.mem_erase.1 h₁).1] at c₁
        rw [if_neg (Finset.mem_erase.1 h₂).1] at c₂
        rw [c₁, c₂, heq]
      · intro w hw
        obtain ⟨v, hvx, hvw⟩ := (label_eq_iff A hσ x w).2 (Finset.mem_erase.1 hw).1
        exact ⟨v, by rw [Finset.mem_erase]; exact ⟨hvx, Finset.mem_univ v⟩, hvw⟩
      · intro v _; rfl
    rw [h2', mul_neg_one, neg_neg]
  rw [← Finset.mul_prod_erase Finset.univ
    (fun v => (x - v) * (A.sf x - v) - A.d v) (Finset.mem_univ x), hF, hprod, mul_one]


/-- **Lemma 6 of the paper**, first assertion: in the normalization `σ(∞) = ∞` the values `d(u)`
are constant along the orbits of `σ`, `d(σ(x)) = d(x)`.

The hypotheses `IsAdmissible S`, `IsMissingPerm S σ` and `σ * σ = 1` are those of Theorem 1 and
are genuinely needed: `AffineData` alone does not tie `d` to `σ`. -/
theorem cover_menelaus_d (hodd : Odd (Nat.card K)) (hq : 5 ≤ Nat.card K)
      {S : Set (PGL2 K)} (hS : IsAdmissible S) {σ : Equiv.Perm (P1 K)} (hσ : IsMissingPerm S σ)
      (hσ2 : σ * σ = 1) (A : AffineData S σ) (u : K) :
      A.d (A.sf u) = A.d u := by
  -- the product identity, applied at `u` and at `sf u`; the product is symmetric in the two
  have h1 : ∏ v : K, ((u - v) * (A.sf u - v) - A.d v) = -A.d u := prod_menelaus A hS hσ u
  have h2 : ∏ v : K, ((A.sf u - v) * (A.sf (A.sf u) - v) - A.d v) = -A.d (A.sf u) :=
      prod_menelaus A hS hσ (A.sf u)
  rw [sf_sf A hσ2 u] at h2
  have hsymm : ∏ v : K, ((A.sf u - v) * (u - v) - A.d v)
        = ∏ v : K, ((u - v) * (A.sf u - v) - A.d v) :=
      Finset.prod_congr rfl (fun v _ => by ring_nf)
  rw [hsymm, h1] at h2
  exact (neg_injective h2).symm

/-- `∏ s` over `K ∖ {0, t}` is `-1/t`. -/
lemma prod_erase_zero_erase (t : K) (ht : t ≠ 0) :
      ∏ s ∈ (Finset.univ.erase (0 : K)).erase t, s = -1 / t := by
  have hmem : t ∈ Finset.univ.erase (0 : K) := by
    rw [Finset.mem_erase]
    exact ⟨ht, Finset.mem_univ _⟩
  have h := Finset.mul_prod_erase (Finset.univ.erase (0 : K)) (fun s => s) hmem
  rw [prod_erase_zero_eq_neg_one] at h
  rw [eq_div_iff ht, mul_comm]
  exact h


/-- `∏ (a - w)` over `w ∈ K ∖ {u, a}` is `-1/(a - u)`. -/
lemma prod_erase_erase_sub {u a : K} (hau : a ≠ u) :
      ∏ w ∈ (Finset.univ.erase u).erase a, (a - w) = -1 / (a - u) := by
  have hua : u ≠ a := Ne.symm hau
  have ht : a - u ≠ 0 := sub_ne_zero.2 hau
  rw [← prod_erase_zero_erase (a - u) ht]
  refine Finset.prod_bij (fun (w : K) (_ : w ∈ (Finset.univ.erase u).erase a) => a - w)
    ?_ ?_ ?_ ?_
  · intro w hw
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hw ⊢
    obtain ⟨hwa, hwu⟩ := hw
    exact ⟨fun h => hwu (sub_right_injective h), sub_ne_zero.2 (Ne.symm hwa)⟩
  · intro w₁ _ w₂ _ heq
    exact sub_right_injective heq
  · intro s hs
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hs
    obtain ⟨hsu, hs0⟩ := hs
    refine ⟨a - s, ?_, ?_⟩
    · simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      exact ⟨fun h => hs0 (sub_eq_self.1 h), fun h => hsu (by rw [← h]; ring)⟩
    · ring
  · intro w _; rfl


/-- `∏ (y - w)` over `w ∈ K ∖ {c, y}` is `-1/(y - c)`. -/
lemma prod_erase_erase_sub' {c y : K} (hyc : y ≠ c) :
      ∏ w ∈ (Finset.univ.erase c).erase y, (y - w) = -1 / (y - c) := by
  have ht : y - c ≠ 0 := sub_ne_zero.2 hyc
  rw [← prod_erase_zero_erase (y - c) ht]
  refine Finset.prod_bij (fun (w : K) (_ : w ∈ (Finset.univ.erase c).erase y) => y - w)
    ?_ ?_ ?_ ?_
  · intro w hw
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hw ⊢
    obtain ⟨hwy, hwc⟩ := hw
    exact ⟨fun h => hwc (sub_right_injective h), sub_ne_zero.2 (Ne.symm hwy)⟩
  · intro w₁ _ w₂ _ heq
    exact sub_right_injective heq
  · intro s hs
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hs
    obtain ⟨hsc, hs0⟩ := hs
    refine ⟨y - s, ?_, ?_⟩
    · simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      exact ⟨fun h => hs0 (sub_eq_self.1 h), fun h => hsc (by rw [← h]; ring)⟩
    · ring
  · intro w _; rfl


/-- For `w ≠ a` the Menelaus factor is `(a - w)(b - s_w(a))`. -/
lemma factor_eq_sv {S : Set (PGL2 K)} {σ : Equiv.Perm (P1 K)} (A : AffineData S σ)
      {a b w : K} (haw : a ≠ w) :
      (a - w) * (b - w) - A.d w = (a - w) * (b - (w + A.d w / (a - w))) := by
  have hne : a - w ≠ 0 := sub_ne_zero.2 haw
  obtain ⟨c, hc⟩ : ∃ c : K, c = A.d w / (a - w) := ⟨_, rfl⟩
  have hd : (a - w) * c = A.d w := by rw [hc, mul_comm, div_mul_cancel₀ _ hne]
  rw [← hc, ← hd]
  ring

/-- Every `s_u` is an involution. -/
lemma sv_sq {S : Set (PGL2 K)} {σ : Equiv.Perm (P1 K)} (A : AffineData S σ)
      (hS : IsAdmissible S) (u : K) : sv A u * sv A u = 1 :=
  (hS.1 _ (sv_mem A u)).2

/-- `s_u(a) = b` in affine coordinates. -/
lemma sv_apply {S : Set (PGL2 K)} {σ : Equiv.Perm (P1 K)} (A : AffineData S σ)
      {a b u : K} (hau : u ≠ a) (hu : u + A.d u / (a - u) = b) :
      sv A u • ptFin a = ptFin b := by
  apply coord_injective
  rw [coord_sv_smul A u a, if_neg hau, hu, coord_ptFin]

/-- With `s_u(a) = b` and `a ≠ b`, the label `u` differs from `a`. -/
lemma ne_a_of_sv {S : Set (PGL2 K)} {σ : Equiv.Perm (P1 K)} (A : AffineData S σ)
      {a b u : K} (hab : a ≠ b) (hu : u + A.d u / (a - u) = b) : a ≠ u := by
  rintro rfl
  rw [sub_self, div_zero, add_zero] at hu
  exact hab hu

/-- With `s_u(a) = b` and `a ≠ b`, the label `u` differs from `b`. -/
lemma ne_b_of_sv {S : Set (PGL2 K)} {σ : Equiv.Perm (P1 K)} (A : AffineData S σ)
      {a b u : K} (hab : a ≠ b) (hu : u + A.d u / (a - u) = b) : u ≠ b := by
  intro hub
  have h2 : A.d b / (a - b) = 0 := by
      have h := hu
      rw [hub] at h
      linear_combination h
  rw [div_eq_zero_iff] at h2
  rcases h2 with h | h
  · exact A.d_ne b h
  · exact absurd h (sub_ne_zero.2 hab)

/-- **The key product of the Menelaus identity.** If `s_u(a) = b` with `a ≠ b` and
`b ≠ σ(a)`, then `∏_{w ≠ u} ((a-w)(b-w) - d w) = -d(a)/((a-u)(b-σa))`: split off the factor
`w = a` (which is `-d a`), use `(a-w)(b-w) - d w = (a-w)(b - s_w(a))` for the rest, and note
that `{s_w(a) : w ≠ a, u} = 𝔽_q ∖ {σa, b}`. -/
lemma prod_special {S : Set (PGL2 K)} {σ : Equiv.Perm (P1 K)} (A : AffineData S σ)
      (hS : IsAdmissible S) (hσ : IsMissingPerm S σ) {a b u : K}
      (hab : a ≠ b) (hbu : b ≠ A.sf a) (hu : u + A.d u / (a - u) = b) :
      ∏ w ∈ Finset.univ.erase u, ((a - w) * (b - w) - A.d w)
        = -(A.d a) / ((a - u) * (b - A.sf a)) := by
  classical
  have hau : a ≠ u := ne_a_of_sv A hab hu
  have hua : u ≠ a := Ne.symm hau
  have hmem : a ∈ Finset.univ.erase u := by
    rw [Finset.mem_erase]
    exact ⟨hau, Finset.mem_univ _⟩
  rw [← Finset.mul_prod_erase (Finset.univ.erase u)
    (fun w => (a - w) * (b - w) - A.d w) hmem]
  have hfa : (a - a) * (b - a) - A.d a = -A.d a := by ring
  have hstep : ∏ w ∈ (Finset.univ.erase u).erase a, ((a - w) * (b - w) - A.d w)
      = (∏ w ∈ (Finset.univ.erase u).erase a, (a - w))
        * ∏ w ∈ (Finset.univ.erase u).erase a, (b - (w + A.d w / (a - w))) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun w hw => by
      rw [Finset.mem_erase] at hw
      exact factor_eq_sv A (Ne.symm hw.1))
  have hpa : ∏ w ∈ (Finset.univ.erase u).erase a, (a - w) = -1 / (a - u) :=
    prod_erase_erase_sub hau
  have hpb : ∏ w ∈ (Finset.univ.erase u).erase a, (b - (w + A.d w / (a - w)))
      = -1 / (b - A.sf a) := by
    rw [← prod_erase_erase_sub' hbu]
    refine Finset.prod_bij (fun (w : K) (_ : w ∈ (Finset.univ.erase u).erase a) =>
      w + A.d w / (a - w)) ?_ ?_ ?_ ?_
    · intro w hw
      rw [Finset.mem_erase, Finset.mem_erase] at hw ⊢
      obtain ⟨hwa, hwu, -⟩ := hw
      refine ⟨?_, ?_, Finset.mem_univ _⟩
      · intro hcon
        have hpt : sv A w • ptFin a = sv A u • ptFin a := by
          apply coord_injective
          rw [coord_sv_smul A w a, coord_sv_smul A u a, if_neg hwa, if_neg hua, hcon, hu]
        exact hwu (sv_smul_injective A hS a hpt)
      · exact (label_eq_iff A hσ a _).1 ⟨w, hwa, rfl⟩
    · intro w₁ h₁ w₂ h₂ heq
      rw [Finset.mem_erase, Finset.mem_erase] at h₁ h₂
      have hpt : sv A w₁ • ptFin a = sv A w₂ • ptFin a := by
        apply coord_injective
        rw [coord_sv_smul A w₁ a, coord_sv_smul A w₂ a, if_neg h₁.1, if_neg h₂.1]
        rw [heq]
      exact sv_smul_injective A hS a hpt
    · intro t ht
      rw [Finset.mem_erase, Finset.mem_erase] at ht
      obtain ⟨htb, htsa, -⟩ := ht
      obtain ⟨w, hwa, hwt⟩ := (label_eq_iff A hσ a t).2 htsa
      refine ⟨w, ?_, hwt⟩
      rw [Finset.mem_erase, Finset.mem_erase]
      refine ⟨hwa, ?_, Finset.mem_univ _⟩
      intro hwu
      exact htb (by rw [← hwt, hwu, hu])
    · intro w _; rfl
  rw [hfa, hstep, hpa, hpb]
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_inv]
  ring


/-- **Lemma 6 of the paper**, second assertion: the Menelaus-type identity. If `s_u(a) = b` with
`a ≠ b` and `b ≠ σ(a)`, then `(u-b) d(a) (σ(b)-a) = (u-a) d(b) (σ(a)-b)`.

Evaluating `prod_special` at `(a,b)` and at `(b,a)` gives two expressions for the same product,
and comparing them is exactly the identity. -/
theorem cover_menelaus_cross (hodd : Odd (Nat.card K)) (hq : 5 ≤ Nat.card K)
      {S : Set (PGL2 K)} (hS : IsAdmissible S) {σ : Equiv.Perm (P1 K)} (hσ : IsMissingPerm S σ)
      (hσ2 : σ * σ = 1) (A : AffineData S σ)
      {a b u : K} (hab : a ≠ b) (hbu : b ≠ A.sf a) (hu : u + A.d u / (a - u) = b) :
      (u - b) * A.d a * (A.sf b - a) = (u - a) * A.d b * (A.sf a - b) := by
  classical
  have hau : a ≠ u := ne_a_of_sv A hab hu
  have hua : u ≠ a := Ne.symm hau
  have hub : u ≠ b := ne_b_of_sv A hab hu
  have hba : a ≠ A.sf b := by
    intro h
    apply hbu
    calc b = A.sf (A.sf b) := (sf_sf A hσ2 b).symm
      _ = A.sf a := by rw [h]
  have hsa : sv A u • ptFin a = ptFin b := sv_apply A hua hu
  have hsb : sv A u • ptFin b = ptFin a := by
    have h2 : sv A u • (sv A u • ptFin a) = ptFin a := by
      rw [← mul_smul, sv_sq A hS u, one_smul]
    rwa [hsa] at h2
  have hu' : u + A.d u / (b - u) = a := by
    have hc := coord_sv_smul A u b
    rw [if_neg hub] at hc
    rw [hsb, coord_ptFin] at hc
    exact Option.some.inj hc.symm
  have hI := prod_special A hS hσ hab hbu hu
  have hII := prod_special A hS hσ hab.symm hba hu'
  have hsymm : (∏ w ∈ Finset.univ.erase u, ((b - w) * (a - w) - A.d w))
      = ∏ w ∈ Finset.univ.erase u, ((a - w) * (b - w) - A.d w) :=
    Finset.prod_congr rfl (fun w _ => by ring)
  rw [hsymm, hI] at hII
  have hX : (b - u) * (a - A.sf b) ≠ 0 :=
    mul_ne_zero (sub_ne_zero.2 (Ne.symm hub)) (sub_ne_zero.2 hba)
  have hY : (a - u) * (b - A.sf a) ≠ 0 := mul_ne_zero (sub_ne_zero.2 hau) (sub_ne_zero.2 hbu)
  have hA := (div_eq_div_iff hY hX).1 hII
  rw [neg_mul, neg_mul] at hA
  have hkey : A.d b * ((a - u) * (b - A.sf a))
      = A.d a * ((b - u) * (a - A.sf b)) := (neg_injective hA).symm
  calc (u - b) * A.d a * (A.sf b - a)
      = A.d a * ((b - u) * (a - A.sf b)) := by ring
    _ = A.d b * ((a - u) * (b - A.sf a)) := hkey.symm
    _ = (u - a) * A.d b * (A.sf a - b) := by ring


/-- The function `h_u` of Lemma 7, restricted to the affine line,
`h_u(x) = (d(u) - (u-x)(u-σ(x)))/d(x)`. -/
noncomputable def hu {S : Set (PGL2 K)} {σ : Equiv.Perm (P1 K)} (A : AffineData S σ)
      (u x : K) : K := (A.d u - (u - x) * (u - A.sf x)) / A.d x

/-- **Lemma 7 of the paper**, invariance: `h_u ∘ σ = h_u`. -/
theorem cover_hu_comp_sigma (hodd : Odd (Nat.card K)) (hq : 5 ≤ Nat.card K)
      {S : Set (PGL2 K)} (hS : IsAdmissible S) {σ : Equiv.Perm (P1 K)} (hσ : IsMissingPerm S σ)
      (hσ2 : σ * σ = 1) (A : AffineData S σ) (u x : K) :
      hu A u (A.sf x) = hu A u x := by
  rw [hu, hu, sf_sf A hσ2 x, cover_menelaus_d hodd hq hS hσ hσ2 A x]
  ring_nf

/-- `h_u` extended to the whole projective line by `h_u(∞) = 1` (equation (3) of the paper).
This is the form in which Lemma 7 applies: both `σ` and `s_u` act on all of `Ω`, whereas `s_u`
swaps `u` with `∞` and so does not act on the affine line. -/
noncomputable def huOmg {S : Set (PGL2 K)} {σ : Equiv.Perm (P1 K)} (A : AffineData S σ) (u : K) :
      P1 K → K :=
  fun x => (coord x).elim 1 (fun y => hu A u y)

@[simp] lemma huOmg_ptInf {S : Set (PGL2 K)} {σ : Equiv.Perm (P1 K)} (A : AffineData S σ)
      (u : K) : huOmg A u (ptInf : P1 K) = 1 := by
  simp [huOmg]

@[simp] lemma huOmg_ptFin {S : Set (PGL2 K)} {σ : Equiv.Perm (P1 K)} (A : AffineData S σ)
      (u y : K) : huOmg A u (ptFin y) = hu A u y := by
  simp [huOmg]

lemma huOmg_of_coord {S : Set (PGL2 K)} {σ : Equiv.Perm (P1 K)} (A : AffineData S σ)
      {u : K} {x : P1 K} {y : Option K} (h : coord x = y) :
      huOmg A u x = y.elim 1 (fun z => hu A u z) := by
  simp [huOmg, h]

/-- `h_u(u) = 1`, so the extension to `∞` is consistent with `s_u` swapping `u` and `∞`. -/
lemma hu_self {S : Set (PGL2 K)} {σ : Equiv.Perm (P1 K)} (A : AffineData S σ) (u : K) :
      hu A u u = 1 := by
  rw [hu]
  simp [A.d_ne u]

/-- `h_u ∘ σ = h_u` on `Ω`. -/
lemma huOmg_comp_sigma (hodd : Odd (Nat.card K)) (hq : 5 ≤ Nat.card K)
      {S : Set (PGL2 K)} (hS : IsAdmissible S) {σ : Equiv.Perm (P1 K)} (hσ : IsMissingPerm S σ)
      (hσ2 : σ * σ = 1) (A : AffineData S σ) (u : K) (x : P1 K) :
      huOmg A u (σ x) = huOmg A u x := by
  have hx : x = ptOf (coord x) := (ptOf_coord x).symm
  cases hc : coord x with
  | none =>
      have h1 : x = ptInf := by rw [hx, hc]; rfl
      rw [h1, A.σ_inf]
  | some y =>
      have h1 : x = ptFin y := by rw [hx, hc]; rfl
      rw [h1, A.σ_fin, huOmg_ptFin, huOmg_ptFin]
      exact cover_hu_comp_sigma hodd hq hS hσ hσ2 A u y

/-- `s_u` acts on finite points away from its label. -/
lemma sv_smul_ptFin {S : Set (PGL2 K)} {σ : Equiv.Perm (P1 K)} (A : AffineData S σ)
      {u y : K} (hyu : y ≠ u) :
      sv A u • ptFin y = ptFin (u + A.d u / (y - u)) := by
  apply coord_injective
  rw [coord_sv_smul A u y, if_neg (Ne.symm hyu), coord_ptFin]

/-- `s_u` swaps `u` and `∞`. -/
lemma sv_smul_ptFin_self {S : Set (PGL2 K)} {σ : Equiv.Perm (P1 K)} (A : AffineData S σ)
      (u : K) : sv A u • ptFin u = (ptInf : P1 K) := by
  apply coord_injective
  rw [coord_sv_smul A u u, if_pos rfl, coord_ptInf]


/-- `h_u` is invariant under `s_u` as well; on finite points this is the Menelaus identity. -/
lemma hu_sv_invariant (hodd : Odd (Nat.card K)) (hq : 5 ≤ Nat.card K)
      {S : Set (PGL2 K)} (hS : IsAdmissible S) {σ : Equiv.Perm (P1 K)} (hσ : IsMissingPerm S σ)
      (hσ2 : σ * σ = 1) (A : AffineData S σ) (u : K) {y : K} (hyu : y ≠ u) :
      hu A u (u + A.d u / (y - u)) = hu A u y := by
  set b : K := u + A.d u / (y - u) with hbdef
  by_cases hby : b = y
  · rw [hby]
  by_cases hbs : b = A.sf y
  · rw [hbs]
    exact cover_hu_comp_sigma hodd hq hS hσ hσ2 A u y
  -- the Menelaus identity, with `a = y` and `b = s_u(y)`
  have hcross := cover_menelaus_cross hodd hq hS hσ hσ2 A (u := u) (a := y) (b := b)
      (fun h => hby h.symm) hbs (by rw [hbdef])
  have hdu₁ : A.d u = (b - u) * (y - u) := by
      have h1 : A.d u / (y - u) = b - u := by rw [hbdef]; ring
      rw [← h1, div_mul_cancel₀ _ (sub_ne_zero.2 hyu)]
  have hdu : A.d u = (u - y) * (u - b) := by rw [hdu₁]; ring
  have hbb : hu A u b * A.d b = (u - b) * (A.sf b - y) := by
      rw [hu, div_mul_cancel₀ _ (A.d_ne b), hdu]
      ring
  have hyy : hu A u y * A.d y = (u - y) * (A.sf y - b) := by
      rw [hu, div_mul_cancel₀ _ (A.d_ne y), hdu]
      ring
  have hcancel : A.d y * A.d b ≠ 0 := mul_ne_zero (A.d_ne y) (A.d_ne b)
  have hc' : (hu A u b * A.d b) * A.d y = (hu A u y * A.d y) * A.d b := by
      rw [hbb, hyy]
      linear_combination hcross
  have key : hu A u b * (A.d y * A.d b) = hu A u y * (A.d y * A.d b) := by
      linear_combination hc'
  exact mul_right_cancel₀ hcancel key

/-- `h_u ∘ s_u = h_u` on `Ω`. -/
lemma huOmg_comp_sv (hodd : Odd (Nat.card K)) (hq : 5 ≤ Nat.card K)
      {S : Set (PGL2 K)} (hS : IsAdmissible S) {σ : Equiv.Perm (P1 K)} (hσ : IsMissingPerm S σ)
      (hσ2 : σ * σ = 1) (A : AffineData S σ) (u : K) (x : P1 K) :
      huOmg A u (sv A u • x) = huOmg A u x := by
  have hx : x = ptOf (coord x) := (ptOf_coord x).symm
  cases hc : coord x with
  | none =>
      have h1 : x = ptInf := by rw [hx, hc]; rfl
      rw [h1, sv_ptInf, huOmg_ptFin, huOmg_ptInf, hu_self]
  | some y =>
      have h1 : x = ptFin y := by rw [hx, hc]; rfl
      rw [h1]
      by_cases hyu : y = u
      · subst hyu
        rw [sv_smul_ptFin_self, huOmg_ptInf, huOmg_ptFin, hu_self]
      · rw [sv_smul_ptFin A hyu, huOmg_ptFin, huOmg_ptFin]
        exact hu_sv_invariant hodd hq hS hσ hσ2 A u hyu

/-- In `ℕ` (truncated subtraction) the difference of two even numbers is even. -/
lemma even_sub_of_even {a b : ℕ} (ha : Even a) (hb : Even b) : Even (a - b) := by
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  exact ⟨x - y, by omega⟩

/-- **Lemma 7 of the paper**, fibre parity, stated on the whole projective line as in the paper:
for every value `z`, the number of fixed points of `σ` in the fibre `h_u = z` is congruent
modulo two to the number of fixed points of `s_u` in that fibre.

Both `σ` and `s_u` act on `Ω`, and `s_u` swaps `u` with `∞` (`sv_smul_ptFin_self`), so the fibre
has to be taken inside `ℙ¹` rather than on the affine line: `h_u` is the extension `huOmg` with
`h_u(∞) = 1`. -/
theorem cover_fibre_parity (hodd : Odd (Nat.card K)) (hq : 5 ≤ Nat.card K)
      {S : Set (PGL2 K)} (hS : IsAdmissible S) {σ : Equiv.Perm (P1 K)} (hσ : IsMissingPerm S σ)
      (hσ2 : σ * σ = 1) (A : AffineData S σ) (u z : K) :
      Even (Nat.card {x : P1 K // σ x = x ∧ huOmg A u x = z} -
        Nat.card {x : P1 K // sv A u • x = x ∧ huOmg A u x = z}) := by
  classical
  have hmapσ : ∀ x : P1 K, huOmg A u x = z → huOmg A u (σ x) = z := fun x hx => by
      rw [huOmg_comp_sigma hodd hq hS hσ hσ2 A u x, hx]
  have hmapu : ∀ x : P1 K, huOmg A u x = z → huOmg A u (sv A u • x) = z := fun x hx => by
      rw [huOmg_comp_sv hodd hq hS hσ hσ2 A u x, hx]
  -- for a fibre-preserving involution `g` of `ℙ¹`, the size of the fibre and the number of its
  -- `g`-fixed points have the same parity
  have key : ∀ (g : P1 K → P1 K), (∀ x, g (g x) = x) →
        (∀ x, huOmg A u x = z → huOmg A u (g x) = z) →
        Even (Nat.card {x : P1 K // huOmg A u x = z}
          + Nat.card {x : P1 K // g x = x ∧ huOmg A u x = z}) := by
      intro g hg hpres
      -- the non-fixed points of the fibre, carrying a fixed-point-free involution
      let g' : {x : P1 K // g x ≠ x ∧ huOmg A u x = z} → {x : P1 K // g x ≠ x ∧ huOmg A u x = z} :=
        fun x => ⟨g x.1, by
          refine ⟨?_, hpres x.1 x.2.2⟩
          rw [hg x.1]
          exact fun h => x.2.1 h.symm⟩
      have hinv : Function.Involutive g' := fun x => by
        apply Subtype.ext
        exact hg x.1
      have hff : ∀ x, g' x ≠ x := fun x h => x.2.1 (congrArg Subtype.val h)
      have hev : Even (Nat.card {x : P1 K // g x ≠ x ∧ huOmg A u x = z}) := by
        rw [Nat.card_eq_fintype_card]
        exact even_card_of_involutive_no_fixed g' hinv hff
      have hsplit : Nat.card {x : P1 K // huOmg A u x = z}
          = Nat.card {x : P1 K // g x = x ∧ huOmg A u x = z}
            + Nat.card {x : P1 K // g x ≠ x ∧ huOmg A u x = z} := by
        rw [← Nat.card_sum]
        refine Nat.card_congr ?_
        exact (Equiv.sumCompl (fun y : {x : P1 K // huOmg A u x = z} => g y.1 = y.1)).symm.trans
          (Equiv.sumCongr
            { toFun := fun y => ⟨y.1.1, y.2, y.1.2⟩
              invFun := fun x => ⟨⟨x.1, x.2.2⟩, x.2.1⟩
              left_inv := fun y => by apply Subtype.ext; apply Subtype.ext; rfl
              right_inv := fun x => by apply Subtype.ext; rfl }
            { toFun := fun y => ⟨y.1.1, y.2, y.1.2⟩
              invFun := fun x => ⟨⟨x.1, x.2.2⟩, x.2.1⟩
              left_inv := fun y => by apply Subtype.ext; apply Subtype.ext; rfl
              right_inv := fun x => by apply Subtype.ext; rfl })
      rw [hsplit]
      have hEq : Nat.card {x : P1 K // g x = x ∧ huOmg A u x = z}
            + Nat.card {x : P1 K // g x ≠ x ∧ huOmg A u x = z}
            + Nat.card {x : P1 K // g x = x ∧ huOmg A u x = z}
          = Nat.card {x : P1 K // g x ≠ x ∧ huOmg A u x = z}
            + 2 * Nat.card {x : P1 K // g x = x ∧ huOmg A u x = z} := by ring
      rw [hEq]
      exact hev.add (even_two_mul _)
  have hA := key σ (fun x => by
        have h2 : (σ * σ) x = (1 : Equiv.Perm (P1 K)) x := by rw [hσ2]
        simpa using h2) hmapσ
  have hB := key (fun x => sv A u • x) (fun x => by
        rw [← mul_smul, sv_sq A hS u, one_smul]) hmapu
  have hEq2 : Nat.card {x : P1 K // σ x = x ∧ huOmg A u x = z}
          + Nat.card {x : P1 K // sv A u • x = x ∧ huOmg A u x = z}
          + 2 * Nat.card {x : P1 K // huOmg A u x = z}
        = (Nat.card {x : P1 K // huOmg A u x = z}
            + Nat.card {x : P1 K // σ x = x ∧ huOmg A u x = z})
          + (Nat.card {x : P1 K // huOmg A u x = z}
            + Nat.card {x : P1 K // sv A u • x = x ∧ huOmg A u x = z}) := by ring
  have hAB2 : Even (Nat.card {x : P1 K // σ x = x ∧ huOmg A u x = z}
          + Nat.card {x : P1 K // sv A u • x = x ∧ huOmg A u x = z}
          + 2 * Nat.card {x : P1 K // huOmg A u x = z}) := by
      rw [hEq2]
      exact hA.add hB
  have hAB : Even (Nat.card {x : P1 K // σ x = x ∧ huOmg A u x = z}
          + Nat.card {x : P1 K // sv A u • x = x ∧ huOmg A u x = z}) := by
      have h1 : Nat.card {x : P1 K // σ x = x ∧ huOmg A u x = z}
            + Nat.card {x : P1 K // sv A u • x = x ∧ huOmg A u x = z}
          = (Nat.card {x : P1 K // σ x = x ∧ huOmg A u x = z}
              + Nat.card {x : P1 K // sv A u • x = x ∧ huOmg A u x = z}
              + 2 * Nat.card {x : P1 K // huOmg A u x = z})
            - 2 * Nat.card {x : P1 K // huOmg A u x = z} := (Nat.add_sub_cancel _ _).symm
      rw [h1]
      exact even_sub_of_even hAB2 (even_two_mul _)
  have hfin : Nat.card {x : P1 K // σ x = x ∧ huOmg A u x = z}
          - Nat.card {x : P1 K // sv A u • x = x ∧ huOmg A u x = z}
        = (Nat.card {x : P1 K // σ x = x ∧ huOmg A u x = z}
            + Nat.card {x : P1 K // sv A u • x = x ∧ huOmg A u x = z})
          - 2 * Nat.card {x : P1 K // sv A u • x = x ∧ huOmg A u x = z} := by omega
  rw [hfin]
  exact even_sub_of_even hAB (even_two_mul _)


/-! ### An explicit covering polynomial (Theorem 8) -/

/-! ### The polynomials `ρ_c` of Theorem 8 -/

/-- The polynomial `ρ_c(X,Y) = (Y - (X-c)²)/d(c)` of equation (5) of the paper. -/
noncomputable def rho {S : Set (PGL2 K)} {σ : Equiv.Perm (P1 K)} (A : AffineData S σ) (c : K) :
      MvPolynomial (Fin 2) K :=
  MvPolynomial.C (A.d c)⁻¹ *
      (MvPolynomial.X 1 - (MvPolynomial.X 0 - MvPolynomial.C c) ^ 2)

/-- Equation (6) of the paper: `ρ_c(u, d(u)) = h_u(c)` for `c ∈ F`. This is where `σ(c) = c`
enters: `h_u(c)` has the factor `u - σ(c)`, which becomes `u - c`. -/
lemma rho_eval {S : Set (PGL2 K)} {σ : Equiv.Perm (P1 K)} (A : AffineData S σ)
      {c u : K} (hc : A.sf c = c) :
      MvPolynomial.eval ![u, A.d u] (rho A c) = hu A u c := by
  simp only [rho, MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_sub,
      MvPolynomial.eval_pow, MvPolynomial.eval_X, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hu, hc, div_eq_mul_inv, sq]
  ring

/-- `ρ_c` has total degree at most two, so a product of `3f - 6` such factors has degree at most
`6f - 12`. -/
lemma rho_totalDegree_le {S : Set (PGL2 K)} {σ : Equiv.Perm (P1 K)} (A : AffineData S σ)
      (c : K) : (rho A c).totalDegree ≤ 2 := by
  rw [rho]
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, Nat.zero_add]
  refine (MvPolynomial.totalDegree_sub _ _).trans (max_le ?_ ?_)
  · rw [MvPolynomial.totalDegree_X]; norm_num
  · refine (MvPolynomial.totalDegree_pow _ 2).trans ?_
    have h2 : (MvPolynomial.X (0 : Fin 2) - MvPolynomial.C c :
        MvPolynomial (Fin 2) K).totalDegree ≤ 1 := by
      refine (MvPolynomial.totalDegree_sub _ _).trans (max_le ?_ ?_)
      · rw [MvPolynomial.totalDegree_X]
      · rw [MvPolynomial.totalDegree_C]; exact Nat.zero_le 1
    calc 2 * (MvPolynomial.X (0 : Fin 2) - MvPolynomial.C c).totalDegree ≤ 2 * 1 :=
          Nat.mul_le_mul_left 2 h2
        _ = 2 := by norm_num

/-- Evaluating `ρ_c` at a point `(u, y)`. -/
lemma rho_eval_at {S : Set (PGL2 K)} {σ : Equiv.Perm (P1 K)} (A : AffineData S σ)
      (u y c : K) :
      MvPolynomial.eval ![u, y] (rho A c) = (A.d c)⁻¹ * (y - (u - c) ^ 2) := by
  simp [rho]

/-- `ρ_c - 1 ≠ 0`: the value at `(c, 0)` is `-1`. (The paper compares the coefficient of `Y`.) -/
lemma rho_sub_one_ne_zero {S : Set (PGL2 K)} {σ : Equiv.Perm (P1 K)} (A : AffineData S σ)
      (c : K) : rho A c - 1 ≠ 0 := by
  intro h
  have e := congrArg (MvPolynomial.eval ![c, (0 : K)]) h
  rw [map_sub, map_one, rho_eval_at] at e
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_self, sub_zero, mul_zero,
      zero_sub] at e
  exact one_ne_zero (neg_eq_zero.mp e)

/-- If `ρ_c = ρ_a` then `c = a`. (The paper compares the coefficients of `Y`, giving
`d(c) = d(a)`, and then of `X`, giving `c = a` since the characteristic is odd.) Evaluating at
`(c, 0)` delivers both steps at once: it forces `(c - a)² = 0`. -/
lemma rho_eq_rho_imp {S : Set (PGL2 K)} {σ : Equiv.Perm (P1 K)} (A : AffineData S σ)
      {c a : K} (h : rho A c = rho A a) : c = a := by
  have e := congrArg (MvPolynomial.eval ![c, (0 : K)]) h
  rw [rho_eval_at, rho_eval_at] at e
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_self, sub_zero, mul_zero,
      zero_sub] at e
  have hda : (A.d a)⁻¹ ≠ 0 := inv_ne_zero (A.d_ne a)
  have hsq : (c - a) ^ 2 = 0 := by
      rw [mul_neg] at e
      exact mul_eq_zero.mp (neg_eq_zero.mp e.symm) |>.resolve_left hda
  rw [pow_two] at hsq
  exact sub_eq_zero.mp (mul_self_eq_zero.mp hsq)

/-! ### The fixed points of `s_u` and the fibres of `h_u` over `F` -/

/-- A point fixed by `s_u` is never `∞`, since `s_u` sends `∞` to `ptFin u`. -/
lemma sv_fix_ne_ptInf {S : Set (PGL2 K)} {σ : Equiv.Perm (P1 K)} (A : AffineData S σ) (u : K)
      {x : P1 K} (hx : sv A u • x = x) : x ≠ ptInf := by
  intro h
  rw [h, sv_ptInf] at hx
  exact ptFin_ne_ptInf u hx

/-- A finite fixed point `ptFin y` of `s_u` satisfies `(y - u)² = d(u)`: this is the quadratic
that limits `s_u` to two fixed points. -/
lemma sv_fix_quad {S : Set (PGL2 K)} {σ : Equiv.Perm (P1 K)} (A : AffineData S σ) (u : K)
      {y : K} (hy : sv A u • ptFin y = ptFin y) : (y - u) ^ 2 = A.d u := by
  have hyu : y ≠ u := by
      intro h
      rw [h, sv_smul_ptFin_self] at hy
      exact ptFin_ne_ptInf u hy.symm
  rw [sv_smul_ptFin A hyu] at hy
  have h2 : u + A.d u / (y - u) = y := ptFin_injective hy
  have h3 : A.d u / (y - u) = y - u := by linear_combination h2
  have hne : y - u ≠ 0 := sub_ne_zero.2 hyu
  have h4 : A.d u = (y - u) * (y - u) := by
      calc A.d u = (A.d u / (y - u)) * (y - u) := (div_mul_cancel₀ _ hne).symm
        _ = (y - u) * (y - u) := by rw [h3]
  rw [h4, pow_two]

/-- If the fibre of `h_u` over `1` meets `F` only in `∞` — i.e. `h_u` is never `1` on `E` — then
that fibre meets `F` in exactly one point. -/
lemma card_fibre_one {S : Set (PGL2 K)} {σ : Equiv.Perm (P1 K)} (A : AffineData S σ) (u : K)
      (h : ∀ c ∈ fixedFin A, hu A u c ≠ 1) :
      Nat.card {x : P1 K // σ x = x ∧ huOmg A u x = 1} = 1 := by
  classical
  have hset : ({x : P1 K | σ x = x ∧ huOmg A u x = 1} : Set (P1 K)) = {ptInf} := by
      ext x
      constructor
      · rintro ⟨h1, h2⟩
        have hx' : x = ptOf (coord x) := (ptOf_coord x).symm
        cases hc : coord x with
        | none => rw [hx', hc]; rfl
        | some c =>
          exfalso
          have hxc : x = ptFin c := by rw [hx', hc]; rfl
          rw [hxc, A.σ_fin] at h1
          have hfc : A.sf c = c := ptFin_injective h1
          rw [hxc, huOmg_ptFin] at h2
          exact h c ((mem_fixedFin A).2 hfc) h2
      · intro hx
        rw [Set.mem_singleton_iff] at hx
        subst hx
        exact ⟨A.σ_inf, huOmg_ptInf A u⟩
  change Nat.card ↥({x : P1 K | σ x = x ∧ huOmg A u x = 1} : Set (P1 K)) = 1
  rw [Nat.card_coe_set_eq, hset]
  simp

/-- If `h_u` separates `c₀` from the rest of `E` and `h_u(c₀) ≠ 1`, then the fibre of `h_u` over
`h_u(c₀)` meets `F` in exactly one point, namely `ptFin c₀`. -/
lemma card_fibre_at {S : Set (PGL2 K)} {σ : Equiv.Perm (P1 K)} (A : AffineData S σ) (u : K)
      {c₀ : K} (hc₀ : c₀ ∈ fixedFin A) (h1 : hu A u c₀ ≠ 1)
      (h : ∀ c ∈ fixedFin A, c ≠ c₀ → hu A u c ≠ hu A u c₀) :
      Nat.card {x : P1 K // σ x = x ∧ huOmg A u x = hu A u c₀} = 1 := by
  classical
  have hf0 : A.sf c₀ = c₀ := (mem_fixedFin A).1 hc₀
  have hset : ({x : P1 K | σ x = x ∧ huOmg A u x = hu A u c₀} : Set (P1 K)) = {ptFin c₀} := by
      ext x
      constructor
      · rintro ⟨hσ, hh⟩
        have hx' : x = ptOf (coord x) := (ptOf_coord x).symm
        cases hc : coord x with
        | none =>
          exfalso
          rw [hx', hc] at hh
          rw [show ptOf (none : Option K) = (ptInf : P1 K) from rfl, huOmg_ptInf] at hh
          exact h1 hh.symm
        | some c =>
          have hxc : x = ptFin c := by rw [hx', hc]; rfl
          rw [hxc, A.σ_fin] at hσ
          have hfc : A.sf c = c := ptFin_injective hσ
          rw [hxc, huOmg_ptFin] at hh
          by_cases hcc : c = c₀
          · rw [hxc, hcc]; exact Set.mem_singleton _
          · exact absurd hh (h c ((mem_fixedFin A).2 hfc) hcc)
      · intro hx
        rw [Set.mem_singleton_iff] at hx
        subst hx
        exact ⟨by rw [A.σ_fin, hf0], huOmg_ptFin A u c₀⟩
  change Nat.card ↥({x : P1 K | σ x = x ∧ huOmg A u x = hu A u c₀} : Set (P1 K)) = 1
  rw [Nat.card_coe_set_eq, hset]
  simp

/-! ### The involution-plane coordinates of `s_u`, and the lines cut out by Theorem 8 -/

/-- A lift of `invClass u c` is a nonzero scalar multiple of `invMat u c`. -/
lemma out_invClass_eq_smul (u c : K) (hc : c ≠ 0) :
      ∃ lam : K, lam ≠ 0 ∧ ((Quotient.out (invClass u c hc) : GL (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) = lam • invMat u c := by
  classical
  set s : GL (Fin 2) K := Quotient.out (invClass u c hc) with hs
  have hcl : (s : PGL2 K) = ((invGL u c hc : GL (Fin 2) K) : PGL2 K) := by
      have h1 : (s : PGL2 K) = invClass u c hc := Quotient.out_eq _
      rw [h1]
      rfl
  have hmem : s * (invGL u c hc)⁻¹ ∈ Subgroup.center (GL (Fin 2) K) :=
      QuotientGroup.eq_iff_div_mem.mp hcl
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hmem
  obtain ⟨w, hw⟩ := hmem
  refine ⟨(w : K), w.ne_zero, ?_⟩
  have hGL : s = Matrix.GeneralLinearGroup.scalar (Fin 2) w * invGL u c hc := by
      rw [hw]
      group
  have hmat := congrArg (fun x : GL (Fin 2) K => (x : Matrix (Fin 2) (Fin 2) K)) hGL
  rw [Matrix.GeneralLinearGroup.coe_mul, invGL_coe] at hmat
  rw [hmat]
  ext i j
  fin_cases i <;> fin_cases j <;>
      simp [Matrix.GeneralLinearGroup.scalar, Matrix.diagonal, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.smul_apply, smul_eq_mul]

/-- The involution-plane coordinates of `s_u`: `[u : d(u) - u² : 1]`, up to the scalar coming
from the chosen representative. -/
lemma invCoord_invClass (u c : K) (hc : c ≠ 0) :
      ∃ lam : K, lam ≠ 0 ∧ invCoord (invClass u c hc) = lam • ![u, c - u ^ 2, (1 : K)] := by
  classical
  obtain ⟨lam, hlam, hM⟩ := out_invClass_eq_smul u c hc
  refine ⟨lam, hlam, ?_⟩
  unfold invCoord
  rw [hM]
  ext i
  fin_cases i <;>
    simp [Matrix.smul_apply, invMat, smul_eq_mul]

/-- The value of a linear form at `s_u`, read in the coordinates `[u : d(u) - u² : 1]`. -/
lemma lineForm_sv {S : Set (PGL2 K)} {σ : Equiv.Perm (P1 K)} (A : AffineData S σ)
      (v : Fin 3 → K) (u : K) :
      lineForm v (sv A u) = 0 ↔ v 0 * u + v 1 * (A.d u - u ^ 2) + v 2 = 0 := by
  classical
  obtain ⟨lam, hlam, hcoord⟩ := invCoord_invClass u (A.d u) (A.d_ne u)
  have hsv : sv A u = invClass u (A.d u) (A.d_ne u) := rfl
  rw [hsv]
  unfold lineForm
  rw [hcoord, Fin.sum_univ_three]
  have h0 : (![u, A.d u - u ^ 2, (1 : K)] 0) = u := by simp
  have h1 : (![u, A.d u - u ^ 2, (1 : K)] 1) = A.d u - u ^ 2 := by simp
  have h2 : (![u, A.d u - u ^ 2, (1 : K)] 2) = (1 : K) := by simp
  simp only [Pi.smul_apply, smul_eq_mul, h0, h1, h2]
  have hfac : v 0 * (lam * u) + v 1 * (lam * (A.d u - u ^ 2)) + v 2 * (lam * 1)
        = lam * (v 0 * u + v 1 * (A.d u - u ^ 2) + v 2) := by ring
  rw [hfac, mul_eq_zero]
  simp [hlam]

/-- The factor `ρ_c - 1` of Theorem 8 vanishes at the graph point `(u, d(u))` exactly when `s_u`
lies on the line of the involution plane with coefficient vector `[2c, 1, -(c² + d(c))]`. -/
lemma lineForm_v1 {S : Set (PGL2 K)} {σ : Equiv.Perm (P1 K)} (A : AffineData S σ) (c u : K) :
      lineForm ![2 * c, (1 : K), -(c ^ 2 + A.d c)] (sv A u) = 0
        ↔ MvPolynomial.eval ![u, A.d u] (rho A c) = 1 := by
  rw [lineForm_sv, rho_eval_at]
  simp
  constructor
  · intro h
    have h2 : A.d u - (u - c) ^ 2 = A.d c := by linear_combination h
    rw [h2, inv_mul_cancel₀ (A.d_ne c)]
  · intro h
    have h2 : A.d u - (u - c) ^ 2 = A.d c := by
      have h1 := congrArg (fun t => A.d c * t) h
      rw [mul_inv_cancel_left₀ (A.d_ne c), mul_one] at h1
      exact h1
    linear_combination h2


/-- The factor `ρ_c - ρ_{a'}` vanishes at `(u, d(u))` exactly when `s_u` lies on the
corresponding line. -/
lemma lineForm_v2 {S : Set (PGL2 K)} {σ : Equiv.Perm (P1 K)} (A : AffineData S σ)
      (c a' u : K) :
      lineForm ![2 * c * (A.d c)⁻¹ - 2 * a' * (A.d a')⁻¹,
               (A.d c)⁻¹ - (A.d a')⁻¹,
               -(c ^ 2) * (A.d c)⁻¹ + a' ^ 2 * (A.d a')⁻¹] (sv A u) = 0
        ↔ MvPolynomial.eval ![u, A.d u] (rho A c - rho A a') = 0 := by
  rw [lineForm_sv, map_sub, rho_eval_at, rho_eval_at]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  have key : (2 * c * (A.d c)⁻¹ - 2 * a' * (A.d a')⁻¹) * u
        + ((A.d c)⁻¹ - (A.d a')⁻¹) * (A.d u - u ^ 2)
        + (-c ^ 2 * (A.d c)⁻¹ + a' ^ 2 * (A.d a')⁻¹)
      = (A.d c)⁻¹ * (A.d u - (u - c) ^ 2) - (A.d a')⁻¹ * (A.d u - (u - a') ^ 2) := by ring
  rw [key]



/-- **The three factors of `H` vanish at every graph point.** For `a ≠ b` in `E = Fix(σ) \\ {∞}`,
the product of the evaluations of the three products `∏_{c ∈ E}(ρ_c - 1)`,
`∏_{c ∈ E \\ {a}}(ρ_c - ρ_a)` and `∏_{c ∈ E \\ {a,b}}(ρ_c - ρ_b)` at `(u, d(u))` is zero: otherwise
the three values `h_u(∞) = 1`, `h_u(a)`, `h_u(b)` would be pairwise distinct, each attained exactly
once on `F`, and Lemma 7 would force three distinct `y` with `(y - u)² = d(u)`.

This is the pigeonhole content of Theorem 8, factored out so that Proposition 9 can name the
covering lines. -/
lemma rho_triple_eval_zero (hodd : Odd (Nat.card K)) (hq : 5 ≤ Nat.card K)
      {S : Set (PGL2 K)} (hS : IsAdmissible S) {σ : Equiv.Perm (P1 K)} (hσ : IsMissingPerm S σ)
      (hσ2 : σ * σ = 1) (A : AffineData S σ) {a b : K} (ha : a ∈ fixedFin A)
      (hb : b ∈ fixedFin A) (hab : a ≠ b) (u : K) :
      MvPolynomial.eval ![u, A.d u] (∏ c ∈ fixedFin A, (rho A c - 1))
          * MvPolynomial.eval ![u, A.d u] (∏ c ∈ (fixedFin A).erase a, (rho A c - rho A a))
          * MvPolynomial.eval ![u, A.d u]
              (∏ c ∈ ((fixedFin A).erase a).erase b, (rho A c - rho A b)) = 0 := by
  classical
  have hfa : A.sf a = a := (mem_fixedFin A).1 ha
  have hfb : A.sf b = b := (mem_fixedFin A).1 hb
  have hba : b ≠ a := Ne.symm hab
  set H1 : MvPolynomial (Fin 2) K := ∏ c ∈ fixedFin A, (rho A c - 1) with hH1
  set H2 : MvPolynomial (Fin 2) K := ∏ c ∈ (fixedFin A).erase a, (rho A c - rho A a) with hH2
  set H3 : MvPolynomial (Fin 2) K :=
    ∏ c ∈ ((fixedFin A).erase a).erase b, (rho A c - rho A b) with hH3
  have hzero : MvPolynomial.eval ![u, A.d u] (H1 * H2 * H3) = 0 := by
    by_contra hne
    have hmul : MvPolynomial.eval ![u, A.d u] (H1 * H2 * H3)
        = MvPolynomial.eval ![u, A.d u] H1 * MvPolynomial.eval ![u, A.d u] H2
          * MvPolynomial.eval ![u, A.d u] H3 := by
      rw [map_mul, map_mul]
    have e1 : MvPolynomial.eval ![u, A.d u] H1
        = ∏ c ∈ fixedFin A, MvPolynomial.eval ![u, A.d u] (rho A c - 1) := by
      rw [hH1, map_prod]
    have e2 : MvPolynomial.eval ![u, A.d u] H2
        = ∏ c ∈ (fixedFin A).erase a,
            MvPolynomial.eval ![u, A.d u] (rho A c - rho A a) := by
      rw [hH2, map_prod]
    have e3 : MvPolynomial.eval ![u, A.d u] H3
        = ∏ c ∈ ((fixedFin A).erase a).erase b,
            MvPolynomial.eval ![u, A.d u] (rho A c - rho A b) := by
      rw [hH3, map_prod]
    have hne' : MvPolynomial.eval ![u, A.d u] H1 * MvPolynomial.eval ![u, A.d u] H2
        * MvPolynomial.eval ![u, A.d u] H3 ≠ 0 := by
      rwa [hmul] at hne
    have h12 : MvPolynomial.eval ![u, A.d u] H1 * MvPolynomial.eval ![u, A.d u] H2 ≠ 0 :=
      (mul_ne_zero_iff.1 hne').1
    rw [e1] at h12
    rw [e2] at h12
    rw [e3] at hne'
    have h2ne := (mul_ne_zero_iff.1 h12).2
    have h3ne := (mul_ne_zero_iff.1 hne').2
    have h1ne := (mul_ne_zero_iff.1 h12).1
    have hnu : ∀ c ∈ fixedFin A, hu A u c ≠ 1 := by
      intro c hc hc1
      have h0 := (Finset.prod_ne_zero_iff.1 h1ne) c hc
      rw [map_sub, map_one, rho_eval A ((mem_fixedFin A).1 hc), sub_eq_zero.2 hc1] at h0
      exact h0 rfl
    have hna : ∀ c ∈ (fixedFin A).erase a, hu A u c ≠ hu A u a := by
      intro c hc hce
      have hcE : c ∈ fixedFin A := (Finset.mem_erase.1 hc).2
      have h0 := (Finset.prod_ne_zero_iff.1 h2ne) c hc
      rw [map_sub, rho_eval A ((mem_fixedFin A).1 hcE), rho_eval A hfa,
        sub_eq_zero.2 hce] at h0
      exact h0 rfl
    have hnb : ∀ c ∈ ((fixedFin A).erase a).erase b, hu A u c ≠ hu A u b := by
      intro c hc hcb
      have hcE : c ∈ fixedFin A := (Finset.mem_erase.1 (Finset.mem_erase.1 hc).2).2
      have h0 := (Finset.prod_ne_zero_iff.1 h3ne) c hc
      rw [map_sub, rho_eval A ((mem_fixedFin A).1 hcE), rho_eval A hfb,
        sub_eq_zero.2 hcb] at h0
      exact h0 rfl
    have hva : hu A u a ≠ 1 := hnu a ha
    have hvb : hu A u b ≠ 1 := hnu b hb
    have hvab : hu A u b ≠ hu A u a := hna b (Finset.mem_erase.2 ⟨hba, hb⟩)
    have hcard1 : Nat.card {x : P1 K // σ x = x ∧ huOmg A u x = 1} = 1 :=
      card_fibre_one A u hnu
    have hcarda : Nat.card {x : P1 K // σ x = x ∧ huOmg A u x = hu A u a} = 1 :=
      card_fibre_at A u ha hva (fun c hcE hca => hna c (Finset.mem_erase.2 ⟨hca, hcE⟩))
    have hcardb : Nat.card {x : P1 K // σ x = x ∧ huOmg A u x = hu A u b} = 1 :=
      card_fibre_at A u hb hvb (fun c hcE hcb => by
        by_cases hca : c = a
        · rw [hca]; exact hvab.symm
        · exact hnb c (Finset.mem_erase.2 ⟨hcb, Finset.mem_erase.2 ⟨hca, hcE⟩⟩))
    have hne1 : Nat.card {x : P1 K // sv A u • x = x ∧ huOmg A u x = 1} ≠ 0 := by
      intro h0
      have hp := cover_fibre_parity hodd hq hS hσ hσ2 A u 1
      rw [hcard1, h0, Nat.sub_zero] at hp
      obtain ⟨k, hk⟩ := hp
      omega
    have hnea : Nat.card {x : P1 K // sv A u • x = x ∧ huOmg A u x = hu A u a} ≠ 0 := by
      intro h0
      have hp := cover_fibre_parity hodd hq hS hσ hσ2 A u (hu A u a)
      rw [hcarda, h0, Nat.sub_zero] at hp
      obtain ⟨k, hk⟩ := hp
      omega
    have hneb : Nat.card {x : P1 K // sv A u • x = x ∧ huOmg A u x = hu A u b} ≠ 0 := by
      intro h0
      have hp := cover_fibre_parity hodd hq hS hσ hσ2 A u (hu A u b)
      rw [hcardb, h0, Nat.sub_zero] at hp
      obtain ⟨k, hk⟩ := hp
      omega
    obtain ⟨x1⟩ := (Nat.card_ne_zero.1 hne1).1
    obtain ⟨x2⟩ := (Nat.card_ne_zero.1 hnea).1
    obtain ⟨x3⟩ := (Nat.card_ne_zero.1 hneb).1
    have key : ∀ (z : K) (x : {x : P1 K // sv A u • x = x ∧ huOmg A u x = z}),
        ∃ y : K, x.1 = ptFin y ∧ (y - u) ^ 2 = A.d u ∧ hu A u y = z := by
      intro z x
      have hx : x.1 = ptOf (coord x.1) := (ptOf_coord x.1).symm
      cases hc : coord x.1 with
      | none =>
        exact absurd (by rw [hx, hc]; rfl : x.1 = ptInf) (sv_fix_ne_ptInf A u x.2.1)
      | some y =>
        have hxy : x.1 = ptFin y := by rw [hx, hc]; rfl
        refine ⟨y, hxy, ?_, ?_⟩
        · apply sv_fix_quad A u
          rw [← hxy]; exact x.2.1
        · have h0 := x.2.2
          rw [hxy, huOmg_ptFin] at h0
          exact h0
    obtain ⟨y1, -, hq1, hv1⟩ := key 1 x1
    obtain ⟨y2, -, hq2, hv2⟩ := key (hu A u a) x2
    obtain ⟨y3, -, hq3, hv3⟩ := key (hu A u b) x3
    have hy12 : y1 ≠ y2 := by
      intro h
      rw [h] at hv1
      exact hva (hv2.symm.trans hv1)
    have hy13 : y1 ≠ y3 := by
      intro h
      rw [h] at hv1
      exact hvb (hv3.symm.trans hv1)
    have hy23 : y2 ≠ y3 := by
      intro h
      rw [h] at hv2
      exact hvab (hv3.symm.trans hv2)
    have hs2 : y1 + y2 = 2 * u := by
      have hf2 : (y1 - y2) * (y1 + y2 - 2 * u) = 0 := by linear_combination hq1 - hq2
      rcases mul_eq_zero.1 hf2 with h | h
      · exact absurd (sub_eq_zero.1 h) hy12
      · linear_combination h
    have hs3 : y1 + y3 = 2 * u := by
      have hf3 : (y1 - y3) * (y1 + y3 - 2 * u) = 0 := by linear_combination hq1 - hq3
      rcases mul_eq_zero.1 hf3 with h | h
      · exact absurd (sub_eq_zero.1 h) hy13
      · linear_combination h
    exact hy23 (by linear_combination hs2 - hs3)
  have hgoal : MvPolynomial.eval ![u, A.d u] (H1 * H2 * H3)
      = MvPolynomial.eval ![u, A.d u] (∏ c ∈ fixedFin A, (rho A c - 1))
        * MvPolynomial.eval ![u, A.d u] (∏ c ∈ (fixedFin A).erase a, (rho A c - rho A a))
        * MvPolynomial.eval ![u, A.d u]
            (∏ c ∈ ((fixedFin A).erase a).erase b, (rho A c - rho A b)) := by
    rw [map_mul, map_mul, hH1, hH2, hH3, map_prod, map_prod, map_prod]
  rw [← hgoal]
  exact hzero


/-- **Theorem 8 of the paper.** Suppose `f ≥ 4`. Then there is a nonzero polynomial `H` in two
variables with `H(u, d(u)) = 0` for every `u ∈ 𝔽_q` and total degree at most `6f - 12`.

The paper's `H` is the explicit product of the factors `ρ_c - 1`, `ρ_c - ρ_a` and `ρ_c - ρ_b`
over `c ∈ E = Fix(σ) \ {∞}`, namely `3f - 6` factors of degree at most two; `H` vanishes on the
graph points because otherwise the three values `h_u(∞) = 1`, `h_u(a)`, `h_u(b)` would be
pairwise distinct and each attained once on `F`, contradicting Lemma 7. -/
theorem cover_polynomial (hodd : Odd (Nat.card K)) (hq : 5 ≤ Nat.card K)
      {S : Set (PGL2 K)} (hS : IsAdmissible S) {σ : Equiv.Perm (P1 K)} (hσ : IsMissingPerm S σ)
      (hσ2 : σ * σ = 1) (A : AffineData S σ)
      (hf : 4 ≤ numFixed σ) :
      ∃ H : MvPolynomial (Fin 2) K, H ≠ 0 ∧ H.totalDegree ≤ 6 * numFixed σ - 12 ∧
        ∀ u : K, MvPolynomial.eval ![u, A.d u] H = 0 := by
  classical
  have hnf : numFixed σ = (fixedFin A).card + 1 := numFixed_eq_fixedFin_card A
  have hEge : 3 ≤ (fixedFin A).card := by omega
  have hE1 : 1 < (fixedFin A).card := by omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 hE1
  have hba : b ≠ a := Ne.symm hab
  have hfa : A.sf a = a := (mem_fixedFin A).1 ha
  have hfb : A.sf b = b := (mem_fixedFin A).1 hb
  set H1 : MvPolynomial (Fin 2) K := ∏ c ∈ fixedFin A, (rho A c - 1) with hH1
  set H2 : MvPolynomial (Fin 2) K := ∏ c ∈ (fixedFin A).erase a, (rho A c - rho A a) with hH2
  set H3 : MvPolynomial (Fin 2) K :=
    ∏ c ∈ ((fixedFin A).erase a).erase b, (rho A c - rho A b) with hH3
  refine ⟨H1 * H2 * H3, ?_, ?_, ?_⟩
  · refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
    · rw [hH1]
      exact Finset.prod_ne_zero_iff.2 (fun c _ => rho_sub_one_ne_zero A c)
    · rw [hH2]
      refine Finset.prod_ne_zero_iff.2 (fun c hc => ?_)
      rw [Finset.mem_erase] at hc
      exact sub_ne_zero.2 (fun h => hc.1 (rho_eq_rho_imp A h))
    · rw [hH3]
      refine Finset.prod_ne_zero_iff.2 (fun c hc => ?_)
      rw [Finset.mem_erase, Finset.mem_erase] at hc
      exact sub_ne_zero.2 (fun h => hc.1 (rho_eq_rho_imp A h))
  · have hfac : ∀ c : K, (rho A c - 1).totalDegree ≤ 2 := by
      intro c
      refine (MvPolynomial.totalDegree_sub _ _).trans (max_le (rho_totalDegree_le A c) ?_)
      rw [show (1 : MvPolynomial (Fin 2) K) = MvPolynomial.C 1 from MvPolynomial.C_1.symm,
        MvPolynomial.totalDegree_C]
      exact Nat.zero_le 2
    have hd1 : H1.totalDegree ≤ 2 * (fixedFin A).card := by
      rw [hH1]
      calc (∏ c ∈ fixedFin A, (rho A c - 1)).totalDegree
          ≤ ∑ c ∈ fixedFin A, (rho A c - 1).totalDegree :=
            MvPolynomial.totalDegree_finsetProd _ _
        _ ≤ ∑ _c ∈ fixedFin A, (2 : ℕ) := Finset.sum_le_sum (fun c _ => hfac c)
        _ = 2 * (fixedFin A).card := by rw [Finset.sum_const, Nat.nsmul_eq_mul, mul_comm]
    have hd2 : H2.totalDegree ≤ 2 * ((fixedFin A).erase a).card := by
      rw [hH2]
      calc (∏ c ∈ (fixedFin A).erase a, (rho A c - rho A a)).totalDegree
          ≤ ∑ c ∈ (fixedFin A).erase a, (rho A c - rho A a).totalDegree :=
            MvPolynomial.totalDegree_finsetProd _ _
        _ ≤ ∑ _c ∈ (fixedFin A).erase a, (2 : ℕ) :=
            Finset.sum_le_sum (fun c _ =>
              (MvPolynomial.totalDegree_sub _ _).trans
                (max_le (rho_totalDegree_le A c) (rho_totalDegree_le A a)))
        _ = 2 * ((fixedFin A).erase a).card := by
            rw [Finset.sum_const, Nat.nsmul_eq_mul, mul_comm]
    have hd3 : H3.totalDegree ≤ 2 * (((fixedFin A).erase a).erase b).card := by
      rw [hH3]
      calc (∏ c ∈ ((fixedFin A).erase a).erase b, (rho A c - rho A b)).totalDegree
          ≤ ∑ c ∈ ((fixedFin A).erase a).erase b, (rho A c - rho A b).totalDegree :=
            MvPolynomial.totalDegree_finsetProd _ _
        _ ≤ ∑ _c ∈ ((fixedFin A).erase a).erase b, (2 : ℕ) :=
            Finset.sum_le_sum (fun c _ =>
              (MvPolynomial.totalDegree_sub _ _).trans
                (max_le (rho_totalDegree_le A c) (rho_totalDegree_le A b)))
        _ = 2 * (((fixedFin A).erase a).erase b).card := by
            rw [Finset.sum_const, Nat.nsmul_eq_mul, mul_comm]
    have hc1 : ((fixedFin A).erase a).card = (fixedFin A).card - 1 :=
      Finset.card_erase_of_mem ha
    have hc2 : (((fixedFin A).erase a).erase b).card = (fixedFin A).card - 1 - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨hba, hb⟩), hc1]
    rw [hc1] at hd2
    rw [hc2] at hd3
    calc (H1 * H2 * H3).totalDegree
        ≤ (H1 * H2).totalDegree + H3.totalDegree := MvPolynomial.totalDegree_mul _ _
      _ ≤ (H1.totalDegree + H2.totalDegree) + H3.totalDegree := by
          have h := MvPolynomial.totalDegree_mul H1 H2
          omega
      _ ≤ 2 * (fixedFin A).card + 2 * ((fixedFin A).card - 1)
            + 2 * ((fixedFin A).card - 1 - 1) := by omega
      _ = 6 * numFixed σ - 12 := by omega
  · intro u
    rw [hH1, hH2, hH3, map_mul, map_mul]
    exact rho_triple_eval_zero hodd hq hS hσ hσ2 A ha hb hab u


/-! ### Conjugation of the involution plane

`PGL₂(K)` acts on the involution plane (the trace-zero `2 × 2` matrices modulo scalars) by
conjugation, and this action is linear in the coordinates `[A : B : C]` of `Defs.lean`. Hence a
projective change of coordinates maps lines of the involution plane to lines and preserves
incidences. This is what lets the normalization `σ(∞) = ∞` of §3 be assumed without loss of
generality: a covering of the conjugate of `S` by lines is transported back by the dual linear map
`Tmat`, which is injective (`Tmat_ne_zero`), so it does not increase the number of lines.
-/

noncomputable def tz (M : Matrix (Fin 2) (Fin 2) K) : Fin 3 → K :=
  ![M 0 0 - (M 0 0 + M 1 1) / 2, M 0 1, M 1 0]

noncomputable def Nmat (v : Fin 3 → K) : Matrix (Fin 2) (Fin 2) K := !![v 0, v 2; v 1, 0]

noncomputable def pair (v : Fin 3 → K) (M : Matrix (Fin 2) (Fin 2) K) : K :=
  v 0 * tz M 0 + v 1 * tz M 1 + v 2 * tz M 2

lemma invCoord_eq_tz (g : PGL2 K) : invCoord g = tz (Quotient.out g : GL (Fin 2) K) := rfl

lemma tz_smul (mu : K) (M : Matrix (Fin 2) (Fin 2) K) : tz (mu • M) = mu • tz M := by
  ext i
  fin_cases i <;> simp [tz, Matrix.smul_apply, smul_eq_mul] <;> ring

lemma trace_Nmat (v : Fin 3 → K) : (Nmat v).trace = v 0 := by
  simp [Nmat, Matrix.trace_fin_two]

lemma trace_mul_gen (P M : Matrix (Fin 2) (Fin 2) K) :
    (P * M).trace = P 0 0 * M 0 0 + P 0 1 * M 1 0 + P 1 0 * M 0 1 + P 1 1 * M 1 1 := by
  simp only [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  ring

lemma trace_Nmat_mul (v : Fin 3 → K) (M : Matrix (Fin 2) (Fin 2) K) :
    (Nmat v * M).trace = v 0 * M 0 0 + v 1 * M 0 1 + v 2 * M 1 0 := by
  rw [trace_mul_gen]
  simp [Nmat]
  ring

lemma pair_eq_trace (v : Fin 3 → K) (M : Matrix (Fin 2) (Fin 2) K) :
    pair v M = (Nmat v * M).trace - (M.trace / 2) * v 0 := by
  rw [trace_Nmat_mul, div_eq_mul_inv]
  simp only [pair, tz, Matrix.trace_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

lemma trace_conj (A : GL (Fin 2) K) (M : Matrix (Fin 2) (Fin 2) K) :
    (((A : Matrix (Fin 2) (Fin 2) K) * M * ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))).trace
      = M.trace := by
  rw [Matrix.trace_mul_cycle, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
    Matrix.GeneralLinearGroup.coe_one, Matrix.one_mul]

noncomputable def Tmat (A : GL (Fin 2) K) (v : Fin 3 → K) : Fin 3 → K :=
  let P : Matrix (Fin 2) (Fin 2) K :=
    ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * Nmat v * (A : Matrix (Fin 2) (Fin 2) K)
  ![2 * P 0 0 - v 0, P 1 0, P 0 1]

lemma trace_Tmat (A : GL (Fin 2) K) (v : Fin 3 → K) :
    ((((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * Nmat v
      * (A : Matrix (Fin 2) (Fin 2) K))).trace = v 0 := by
  rw [Matrix.trace_mul_cycle, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
    Matrix.GeneralLinearGroup.coe_one, Matrix.one_mul, trace_Nmat]

lemma trace_conj_gen (X M : Matrix (Fin 2) (Fin 2) K) (A : GL (Fin 2) K) :
    (X * ((A : Matrix (Fin 2) (Fin 2) K) * M * ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))).trace
      = ((((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * X
          * (A : Matrix (Fin 2) (Fin 2) K)) * M).trace := by
  rw [← Matrix.mul_assoc X ((A : Matrix (Fin 2) (Fin 2) K) * M)
      ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K),
    ← Matrix.mul_assoc X (A : Matrix (Fin 2) (Fin 2) K) M,
    Matrix.trace_mul_cycle,
    ← Matrix.mul_assoc ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) X
      (A : Matrix (Fin 2) (Fin 2) K)]

lemma pair_Tmat (h2 : (2 : K) ≠ 0) (A : GL (Fin 2) K) (v : Fin 3 → K)
    (M : Matrix (Fin 2) (Fin 2) K) :
    pair (Tmat A v) M =
      pair v ((A : Matrix (Fin 2) (Fin 2) K) * M * ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) := by
  have htr := trace_Tmat A v
  set P : Matrix (Fin 2) (Fin 2) K :=
    ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * Nmat v * (A : Matrix (Fin 2) (Fin 2) K) with hP
  have hT : Tmat A v = ![2 * P 0 0 - v 0, P 1 0, P 0 1] := rfl
  set w : Fin 3 → K := ![2 * P 0 0 - v 0, P 1 0, P 0 1] with hw
  have h1 : pair w M = (Nmat w * M).trace - (M.trace / 2) * w 0 := pair_eq_trace w M
  have h2' : pair v ((A : Matrix (Fin 2) (Fin 2) K) * M
      * ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))
      = (Nmat v * ((A : Matrix (Fin 2) (Fin 2) K) * M
          * ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))).trace
        - (M.trace / 2) * v 0 := by
    rw [pair_eq_trace, trace_conj]
  have hcyc : (Nmat v * ((A : Matrix (Fin 2) (Fin 2) K) * M
      * ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))).trace = (P * M).trace := by
    rw [trace_conj_gen]
  rw [hT, h1, h2', hcyc, trace_Nmat_mul, trace_mul_gen]
  have hP11 : P 1 1 = v 0 - P 0 0 := by
    have htr' : P 0 0 + P 1 1 = v 0 := by
      rw [hP, Matrix.trace_fin_two] at htr
      exact htr
    linear_combination htr'
  rw [hP11]
  simp only [hw, Matrix.trace_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, div_eq_mul_inv]
  field_simp
  ring

lemma exists_invCoord_eq_smul_tz {g : PGL2 K} (M : GL (Fin 2) K) (hM : (M : PGL2 K) = g) :
    ∃ mu : K, mu ≠ 0 ∧ invCoord g = mu • tz (M : Matrix (Fin 2) (Fin 2) K) := by
  classical
  set s : GL (Fin 2) K := Quotient.out g with hs
  have hcl : (s : PGL2 K) = (M : PGL2 K) := by
    rw [hs]
    exact (Quotient.out_eq g).trans hM.symm
  have hmem : s * M⁻¹ ∈ Subgroup.center (GL (Fin 2) K) := QuotientGroup.eq_iff_div_mem.mp hcl
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hmem
  obtain ⟨w, hw⟩ := hmem
  refine ⟨(w : K), w.ne_zero, ?_⟩
  have hGL : s = Matrix.GeneralLinearGroup.scalar (Fin 2) w * M := by
    rw [hw]; group
  have hmat : (s : Matrix (Fin 2) (Fin 2) K)
      = ((Matrix.GeneralLinearGroup.scalar (Fin 2) w : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
        * (M : Matrix (Fin 2) (Fin 2) K) := by
    rw [hGL, Matrix.GeneralLinearGroup.coe_mul]
  have hdiag : (Matrix.diagonal (fun _ : Fin 2 => (w : K))) * (M : Matrix (Fin 2) (Fin 2) K)
      = (w : K) • (M : Matrix (Fin 2) (Fin 2) K) := by
    ext i j
    rw [Matrix.diagonal_mul, Matrix.smul_apply, smul_eq_mul]
  rw [invCoord_eq_tz, ← hs, hmat, scalar_val, Matrix.scalar_apply, hdiag, tz_smul]


lemma lineForm_eq_smul_pair {g : PGL2 K} (M : GL (Fin 2) K) (hM : (M : PGL2 K) = g)
    (v : Fin 3 → K) :
    ∃ mu : K, mu ≠ 0 ∧ lineForm v g = mu * pair v (M : Matrix (Fin 2) (Fin 2) K) := by
  obtain ⟨mu, hmu, hcoord⟩ := exists_invCoord_eq_smul_tz M hM
  refine ⟨mu, hmu, ?_⟩
  rw [lineForm, hcoord, Fin.sum_univ_three]
  simp only [Pi.smul_apply, smul_eq_mul, pair]
  ring

lemma conj_mul_inv (A : GL (Fin 2) K) (X : Matrix (Fin 2) (Fin 2) K) :
    (A : Matrix (Fin 2) (Fin 2) K) * (((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * X
      * (A : Matrix (Fin 2) (Fin 2) K)) * ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = X := by
  simp only [← Matrix.mul_assoc]
  rw [← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel, Matrix.GeneralLinearGroup.coe_one,
    Matrix.one_mul, Matrix.mul_assoc, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
    Matrix.GeneralLinearGroup.coe_one, Matrix.mul_one]

lemma pair_kernel {v : Fin 3 → K} (h : ∀ M : Matrix (Fin 2) (Fin 2) K, pair v M = 0) : v = 0 := by
  have h0 := h !![1, 0; 0, -1]
  have h1 := h !![0, 1; 0, 0]
  have h2 := h !![0, 0; 1, 0]
  simp [pair, tz] at h0 h1 h2
  ext i
  fin_cases i
  · simpa using h0
  · simpa using h1
  · simpa using h2

lemma Tmat_ne_zero (h2 : (2 : K) ≠ 0) (A : GL (Fin 2) K) {v : Fin 3 → K} (hv : v ≠ 0) :
    Tmat A v ≠ 0 := by
  intro hT
  apply hv
  refine pair_kernel (fun M => ?_)
  have hzero : ∀ X : Matrix (Fin 2) (Fin 2) K, pair (Tmat A v) X = 0 := by
    intro X
    rw [hT]
    simp [pair, tz]
  have e := hzero (((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * M
    * (A : Matrix (Fin 2) (Fin 2) K))
  rw [pair_Tmat h2 A v] at e
  rw [conj_mul_inv] at e
  exact e

lemma lineForm_conj (h2 : (2 : K) ≠ 0) (A : GL (Fin 2) K) (s : PGL2 K) (v : Fin 3 → K) :
    lineForm v ((A : PGL2 K) * s * (A : PGL2 K)⁻¹) = 0 ↔ lineForm (Tmat A v) s = 0 := by
  classical
  set M : GL (Fin 2) K := Quotient.out s with hMdef
  have hMs : (M : PGL2 K) = s := Quotient.out_eq s
  have hmat : ((A * M * A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = (A : Matrix (Fin 2) (Fin 2) K) * (M : Matrix (Fin 2) (Fin 2) K)
        * ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
    rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul,
      Matrix.GeneralLinearGroup.coe_inv]
  have hconj : ((A * M * A⁻¹ : GL (Fin 2) K) : PGL2 K) = (A : PGL2 K) * s * (A : PGL2 K)⁻¹ := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hMs]
  obtain ⟨mu, hmu, h1⟩ := lineForm_eq_smul_pair (A * M * A⁻¹) hconj v
  obtain ⟨nu, hnu, h2'⟩ := lineForm_eq_smul_pair M hMs (Tmat A v)
  rw [h1, h2', hmat, pair_Tmat h2 A v (M : Matrix (Fin 2) (Fin 2) K)]
  constructor
  · intro hh
    rcases mul_eq_zero.1 hh with h | h
    · exact absurd h hmu
    · rw [h, mul_zero]
  · intro hh
    rcases mul_eq_zero.1 hh with h | h
    · exact absurd h hnu
    · rw [h, mul_zero]

/-- Conjugating a set of projective transformations does not change its cardinality. -/
lemma card_conjSet (g : PGL2 K) (S : Set (PGL2 K)) : Nat.card (conjSet g S) = Nat.card S := by
  have hset : conjSet g S = (fun s => g * s * g⁻¹) '' S := by
    ext t
    simp only [conjSet, Set.mem_ofPred_eq, Set.mem_image]
    exact ⟨fun h => ⟨h.choose, h.choose_spec.1, h.choose_spec.2.symm⟩,
      fun h => ⟨h.choose, h.choose_spec.1, h.choose_spec.2.symm⟩⟩
  rw [hset, Nat.card_image_of_injective ?_ _]
  intro a b hab
  have h := congrArg (fun t => g⁻¹ * t * g) hab
  group at h
  exact h

/-- **Proposition 9 of the paper**, nonsplit part, in the normalization `σ(∞) = ∞`: the nonsplit
elements of `S` lie on the `f - 1` lines `L_c : V + 2cU - (c² + d(c))W = 0`, `c ∈ E`.

The argument is the one of the paper: for a nonsplit `s_u` the fibre `h_u = 1` has no
`s_u`-fixed point, so by Lemma 7 (`cover_fibre_parity`) its number of `σ`-fixed points is even;
that number is positive since `∞` belongs to the fibre, so there is a further `σ`-fixed point
`c ∈ E` in the fibre, and `h_u(c) = 1` says exactly that `s_u` lies on `L_c`
(`lineForm_v1`). -/
theorem exists_nonsplit_cover_normalized (hodd : Odd (Nat.card K)) (hq : 5 ≤ Nat.card K)
    {S : Set (PGL2 K)} (hS : IsAdmissible S) (hcard : Nat.card S = Nat.card K)
    {σ : Equiv.Perm (P1 K)} (hσ : IsMissingPerm S σ) (hσ2 : σ * σ = 1)
    (A : AffineData S σ) :
    ∃ V : Finset (Fin 3 → K), V.card ≤ numFixed σ - 1 ∧
      ∀ s ∈ S, ¬ IsSplit s → ∃ v ∈ V, v ≠ 0 ∧ lineForm v s = 0 := by
  classical
  have hnf : numFixed σ = (fixedFin A).card + 1 := numFixed_eq_fixedFin_card A
  refine ⟨(fixedFin A).image (fun c : K => ![2 * c, (1 : K), -(c ^ 2 + A.d c)]), ?_, ?_⟩
  · calc ((fixedFin A).image (fun c : K => ![2 * c, (1 : K), -(c ^ 2 + A.d c)])).card
        ≤ (fixedFin A).card := Finset.card_image_le
      _ = numFixed σ - 1 := by omega
  · intro s hs hns
    obtain ⟨u, rfl⟩ := (A.isNormal s).1 hs
    have hnsp : ∀ x : P1 K, sv A u • x ≠ x := by
      intro x hx
      exact hns ⟨hS.1 _ hs, ⟨x, hx⟩⟩
    -- the fibre of `h_u` over `1` has no `s_u`-fixed point
    have hzero : Nat.card {x : P1 K // sv A u • x = x ∧ huOmg A u x = 1} = 0 := by
      rw [Nat.card_eq_zero]
      exact Or.inl ⟨fun x => hnsp x x.2.1⟩
    -- Lemma 7: its number of `σ`-fixed points is even, and it contains `∞`
    have hpar := cover_fibre_parity hodd hq hS hσ hσ2 A u 1
    rw [hzero, Nat.sub_zero] at hpar
    haveI : Nonempty {x : P1 K // σ x = x ∧ huOmg A u x = 1} :=
      ⟨⟨ptInf, A.σ_inf, huOmg_ptInf A u⟩⟩
    have hge2 : 2 ≤ Nat.card {x : P1 K // σ x = x ∧ huOmg A u x = 1} := by
      obtain ⟨k, hk⟩ := hpar
      have := Nat.card_pos (α := {x : P1 K // σ x = x ∧ huOmg A u x = 1})
      omega
    -- hence a second `σ`-fixed point of the fibre, i.e. some `c ∈ E` with `h_u(c) = 1`
    have hgot : ∃ c ∈ fixedFin A, hu A u c = 1 := by
      set F : Finset (P1 K) := Finset.univ.filter (fun x : P1 K => σ x = x ∧ huOmg A u x = 1)
        with hF
      have hcardF : F.card = Nat.card {x : P1 K // σ x = x ∧ huOmg A u x = 1} := by
        rw [hF, Nat.card_eq_fintype_card]
        exact (Fintype.card_subtype _).symm
      have h2 : 1 < F.card := by rw [hcardF]; omega
      obtain ⟨y1, hy1, y2, hy2, hy12⟩ := Finset.one_lt_card.1 h2
      rw [hF, Finset.mem_filter] at hy1 hy2
      obtain ⟨-, hy1σ, hy1h⟩ := hy1
      obtain ⟨-, hy2σ, hy2h⟩ := hy2
      have key : ∀ y : P1 K, σ y = y → huOmg A u y = 1 → y ≠ ptInf →
          ∃ c ∈ fixedFin A, hu A u c = 1 := by
        intro y hyσ hyh hyinf
        have hsome : ∃ c : K, y = ptFin c := by
          cases hc : coord y with
          | none =>
            exact absurd (by
              rw [show y = ptOf (coord y) from (ptOf_coord y).symm, hc]
              rfl) hyinf
          | some c =>
            exact ⟨c, by
              rw [show y = ptOf (coord y) from (ptOf_coord y).symm, hc]
              rfl⟩
        obtain ⟨c, hyc⟩ := hsome
        refine ⟨c, ?_, ?_⟩
        · refine (mem_fixedFin A).2 (ptFin_injective ?_)
          rw [← A.σ_fin, ← hyc]
          exact hyσ
        · rw [hyc, huOmg_ptFin] at hyh
          exact hyh
      by_cases h1 : y1 = ptInf
      · exact key y2 hy2σ hy2h (fun h => hy12 (h1.trans h.symm))
      · exact key y1 hy1σ hy1h h1
    obtain ⟨c, hcE, huc⟩ := hgot
    refine ⟨![2 * c, (1 : K), -(c ^ 2 + A.d c)], Finset.mem_image.2 ⟨c, hcE, rfl⟩, ?_, ?_⟩
    · intro h0
      have h1 : (![2 * c, (1 : K), -(c ^ 2 + A.d c)] : Fin 3 → K) 1 = 0 := by rw [h0]; rfl
      simp only [Matrix.cons_val_one] at h1
      exact one_ne_zero h1
    · exact (lineForm_v1 A c u).2 (by rw [rho_eval A ((mem_fixedFin A).1 hcE)]; exact huc)

lemma isInvolution_conj (g s : PGL2 K) : IsInvolution (g * s * g⁻¹) ↔ IsInvolution s := by
  unfold IsInvolution
  constructor
  · rintro ⟨hne, hsq⟩
    refine ⟨fun hs => hne (by rw [hs]; group), ?_⟩
    have h2 := congrArg (fun t => g⁻¹ * t * g) hsq
    group at h2
    exact h2
  · rintro ⟨hne, hsq⟩
    refine ⟨fun hc => hne (by
      have h2 := congrArg (fun t => g⁻¹ * t * g) hc
      group at h2
      exact h2), ?_⟩
    have h2 : (g * s * g⁻¹) * (g * s * g⁻¹) = g * (s * s) * g⁻¹ := by group
    rw [h2, hsq, mul_one, mul_inv_cancel]

lemma isSplit_conj (g s : PGL2 K) : IsSplit (g * s * g⁻¹) ↔ IsSplit s := by
  unfold IsSplit
  refine and_congr (isInvolution_conj g s) ?_
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨g⁻¹ • y, ?_⟩
    show s • (g⁻¹ • y) = g⁻¹ • y
    have h2 : g • (s • (g⁻¹ • y)) = y := by
      rw [← conj_smul]
      exact hy
    have h3 := congrArg (fun z => g⁻¹ • z) h2
    rwa [inv_smul_smul] at h3
  · rintro ⟨x, hx⟩
    refine ⟨g • x, ?_⟩
    show (g * s * g⁻¹) • (g • x) = g • x
    rw [conj_smul, inv_smul_smul, hx]

/-- **Proposition 9 of the paper**, nonsplit part, in general: if `f > 0`, the nonsplit elements of
`S` are covered by at most `f - 1` lines of the involution plane.

The normalization `σ(∞) = ∞` is reached by conjugating a fixed point of `σ` to `∞`
(`exists_smul_eq_ptInf`); conjugating `S` back maps the covering lines of
`exists_nonsplit_cover_normalized` to lines through the nonsplit elements of `S`
(`lineForm_conj`), and `Tmat B` is injective, so the number of lines does not grow. -/
theorem exists_nonsplit_cover (hodd : Odd (Nat.card K)) (hq : 5 ≤ Nat.card K)
    {S : Set (PGL2 K)} (hS : IsAdmissible S) (hcard : Nat.card S = Nat.card K)
    {σ : Equiv.Perm (P1 K)} (hσ : IsMissingPerm S σ) (hσ2 : σ * σ = 1)
    (hf : 0 < numFixed σ) :
    ∃ V : Finset (Fin 3 → K), V.card ≤ numFixed σ - 1 ∧
      ∀ s ∈ S, ¬ IsSplit s → ∃ v ∈ V, v ≠ 0 ∧ lineForm v s = 0 := by
  classical
  have hne : numFixed σ ≠ 0 := by omega
  obtain ⟨⟨x, hx⟩⟩ := (Nat.card_ne_zero.1 hne).1
  obtain ⟨g, hg⟩ := exists_smul_eq_ptInf x
  set σ' : Equiv.Perm (P1 K) := MulAction.toPerm g * σ * (MulAction.toPerm g)⁻¹ with hσ'def
  have hσ'coe : (σ' : P1 K → P1 K) = conjPerm g (σ : P1 K → P1 K) := by
    funext y
    rfl
  have hσ'sq : σ' * σ' = 1 := by
    rw [hσ'def]
    have e : MulAction.toPerm g * σ * (MulAction.toPerm g)⁻¹
          * (MulAction.toPerm g * σ * (MulAction.toPerm g)⁻¹)
        = MulAction.toPerm g * (σ * σ) * (MulAction.toPerm g)⁻¹ := by group
    rw [e, hσ2, mul_one, mul_inv_cancel]
  have hnf' : numFixed σ' = numFixed σ := by
    rw [hσ'coe]
    exact numFixed_conjPerm g (σ : P1 K → P1 K)
  have hgx : g⁻¹ • (ptInf : P1 K) = x := by
    rw [← hg, inv_smul_smul]
  have hinf' : σ' (ptInf : P1 K) = ptInf := by
    rw [hσ'coe]
    show g • σ (g⁻¹ • ptInf) = ptInf
    rw [hgx, hx, hg]
  have hmiss' : IsMissingPerm (conjSet g S) (σ' : P1 K → P1 K) := by
    rw [hσ'coe]
    exact isMissingPerm_conjSet g hσ
  have hcard' : Nat.card (conjSet g S) = Nat.card K := by rw [card_conjSet, hcard]
  obtain ⟨A⟩ := exists_affineData hodd hq (isAdmissible_conjSet g hS) hcard' hmiss' hinf'
  obtain ⟨V, hVcard, hVcov⟩ :=
    exists_nonsplit_cover_normalized hodd hq (isAdmissible_conjSet g hS) hcard' hmiss' hσ'sq A
  set B : GL (Fin 2) K := Quotient.out g with hBdef
  have hB : (B : PGL2 K) = g := Quotient.out_eq g
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd_card hodd
  refine ⟨V.image (Tmat B), ?_, ?_⟩
  · calc (V.image (Tmat B)).card ≤ V.card := Finset.card_image_le
      _ ≤ numFixed σ' - 1 := hVcard
      _ = numFixed σ - 1 := by rw [hnf']
  · intro s hs hns
    have ht : g * s * g⁻¹ ∈ conjSet g S := ⟨s, hs, rfl⟩
    have hns' : ¬ IsSplit (g * s * g⁻¹) := fun h => hns ((isSplit_conj g s).1 h)
    obtain ⟨v, hvV, hv0, hvline⟩ := hVcov _ ht hns'
    exact ⟨Tmat B v, Finset.mem_image.2 ⟨v, hvV, rfl⟩, Tmat_ne_zero h2 B hv0,
      (lineForm_conj h2 B s v).1 (by rw [hB]; exact hvline)⟩

/-! ### The covering of `S` by lines -/

/-- **Proposition 9 of the paper**, covering part, in the normalization `σ(∞) = ∞`: the whole set
`S` is covered by at most `3f - 6` lines of the involution plane. -/
theorem exists_cover_by_lines_of_fixes_ptInf (hodd : Odd (Nat.card K)) (hq : 5 ≤ Nat.card K)
    {S : Set (PGL2 K)} (hS : IsAdmissible S) (hcard : Nat.card S = Nat.card K)
    {σ : Equiv.Perm (P1 K)} (hσ : IsMissingPerm S σ) (hσ2 : σ * σ = 1) (hf : 4 ≤ numFixed σ)
    (hinf : σ ptInf = ptInf) :
    ∃ V : Finset (Fin 3 → K), V.card ≤ 3 * numFixed σ - 6 ∧
      ∀ s ∈ S, ∃ v ∈ V, v ≠ 0 ∧ lineForm v s = 0 := by
  classical
  obtain ⟨A⟩ := exists_affineData hodd hq hS hcard hσ hinf
  have hnf : numFixed σ = (fixedFin A).card + 1 := numFixed_eq_fixedFin_card A
  have hEge : 3 ≤ (fixedFin A).card := by omega
  have hE1 : 1 < (fixedFin A).card := by omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 hE1
  have hba : b ≠ a := Ne.symm hab
  have hfa : A.sf a = a := (mem_fixedFin A).1 ha
  have hfb : A.sf b = b := (mem_fixedFin A).1 hb
  set V1 : Finset (Fin 3 → K) :=
    Finset.image (fun c : K => ![2 * c, (1 : K), -(c ^ 2 + A.d c)]) (fixedFin A) with hV1
  set V2 : Finset (Fin 3 → K) := Finset.image
    (fun c : K => ![2 * c * (A.d c)⁻¹ - 2 * a * (A.d a)⁻¹,
      (A.d c)⁻¹ - (A.d a)⁻¹, -(c ^ 2) * (A.d c)⁻¹ + a ^ 2 * (A.d a)⁻¹])
    ((fixedFin A).erase a) with hV2
  set V3 : Finset (Fin 3 → K) := Finset.image
    (fun c : K => ![2 * c * (A.d c)⁻¹ - 2 * b * (A.d b)⁻¹,
      (A.d c)⁻¹ - (A.d b)⁻¹, -(c ^ 2) * (A.d c)⁻¹ + b ^ 2 * (A.d b)⁻¹])
    (((fixedFin A).erase a).erase b) with hV3
  refine ⟨V1 ∪ V2 ∪ V3, ?_, ?_⟩
  · have h12 := Finset.card_union_le V1 V2
    have h123 := Finset.card_union_le (V1 ∪ V2) V3
    have hc1 : V1.card ≤ (fixedFin A).card := Finset.card_image_le
    have hc2 : V2.card ≤ ((fixedFin A).erase a).card := Finset.card_image_le
    have hc3 : V3.card ≤ (((fixedFin A).erase a).erase b).card := Finset.card_image_le
    rw [Finset.card_erase_of_mem ha] at hc2
    rw [Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨hba, hb⟩),
      Finset.card_erase_of_mem ha] at hc3
    omega
  · -- covering: at the graph point `(u, d(u))` one of the three factors of `H` vanishes, and
    -- each vanishing factor names a line of `V1 ∪ V2 ∪ V3` through `s_u`
    intro s hs
    obtain ⟨u, hu'⟩ := (A.isNormal s).1 hs
    subst hu'
    have hz := rho_triple_eval_zero hodd hq hS hσ hσ2 A ha hb hab u
    have e1 : MvPolynomial.eval ![u, A.d u] (∏ c ∈ fixedFin A, (rho A c - 1))
        = ∏ c ∈ fixedFin A, MvPolynomial.eval ![u, A.d u] (rho A c - 1) := by rw [map_prod]
    have e2 : MvPolynomial.eval ![u, A.d u] (∏ c ∈ (fixedFin A).erase a, (rho A c - rho A a))
        = ∏ c ∈ (fixedFin A).erase a,
            MvPolynomial.eval ![u, A.d u] (rho A c - rho A a) := by rw [map_prod]
    have e3 : MvPolynomial.eval ![u, A.d u]
          (∏ c ∈ ((fixedFin A).erase a).erase b, (rho A c - rho A b))
        = ∏ c ∈ ((fixedFin A).erase a).erase b,
            MvPolynomial.eval ![u, A.d u] (rho A c - rho A b) := by rw [map_prod]
    have hV1mem : ∀ c ∈ fixedFin A,
        (![2 * c, (1 : K), -(c ^ 2 + A.d c)] : Fin 3 → K) ∈ V1 := by
      intro c hc
      rw [hV1]
      exact Finset.mem_image.2 ⟨c, hc, rfl⟩
    have hV2mem : ∀ c ∈ (fixedFin A).erase a,
        (![2 * c * (A.d c)⁻¹ - 2 * a * (A.d a)⁻¹, (A.d c)⁻¹ - (A.d a)⁻¹,
            -(c ^ 2) * (A.d c)⁻¹ + a ^ 2 * (A.d a)⁻¹] : Fin 3 → K) ∈ V2 := by
      intro c hc
      rw [hV2]
      exact Finset.mem_image.2 ⟨c, hc, rfl⟩
    have hV3mem : ∀ c ∈ ((fixedFin A).erase a).erase b,
        (![2 * c * (A.d c)⁻¹ - 2 * b * (A.d b)⁻¹, (A.d c)⁻¹ - (A.d b)⁻¹,
            -(c ^ 2) * (A.d c)⁻¹ + b ^ 2 * (A.d b)⁻¹] : Fin 3 → K) ∈ V3 := by
      intro c hc
      rw [hV3]
      exact Finset.mem_image.2 ⟨c, hc, rfl⟩
    -- the second component of a vector `α • [2c, 1, -(c² + d c)] - β • [2a, 1, -(a² + d a)]`
    -- vanishes only when `α = β`, and then the first forces `c = a`
    have hne2 : ∀ c a' : K, c ≠ a' →
        (![2 * c * (A.d c)⁻¹ - 2 * a' * (A.d a')⁻¹, (A.d c)⁻¹ - (A.d a')⁻¹,
            -(c ^ 2) * (A.d c)⁻¹ + a' ^ 2 * (A.d a')⁻¹] : Fin 3 → K) ≠ 0 := by
      intro c a' hca h0
      have h1 : (![2 * c * (A.d c)⁻¹ - 2 * a' * (A.d a')⁻¹, (A.d c)⁻¹ - (A.d a')⁻¹,
          -(c ^ 2) * (A.d c)⁻¹ + a' ^ 2 * (A.d a')⁻¹] : Fin 3 → K) 1 = 0 := by
        rw [h0]; rfl
      have h0' : (![2 * c * (A.d c)⁻¹ - 2 * a' * (A.d a')⁻¹, (A.d c)⁻¹ - (A.d a')⁻¹,
          -(c ^ 2) * (A.d c)⁻¹ + a' ^ 2 * (A.d a')⁻¹] : Fin 3 → K) 0 = 0 := by
        rw [h0]; rfl
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h1 h0'
      have hinv : (A.d c)⁻¹ = (A.d a')⁻¹ := sub_eq_zero.1 h1
      rw [hinv] at h0'
      have hfac : 2 * c * (A.d a')⁻¹ - 2 * a' * (A.d a')⁻¹ = 2 * (c - a') * (A.d a')⁻¹ := by
        ring
      rw [hfac] at h0'
      have h2K : (2 : K) ≠ 0 := two_ne_zero_of_odd_card hodd
      have hci : (A.d a')⁻¹ ≠ 0 := inv_ne_zero (A.d_ne a')
      rcases mul_eq_zero.1 h0' with h | h
      · rcases mul_eq_zero.1 h with h' | h'
        · exact absurd h' h2K
        · exact hca (sub_eq_zero.1 h')
      · exact absurd h hci
    rcases mul_eq_zero.1 hz with h12 | h3
    · rcases mul_eq_zero.1 h12 with h1 | h2
      · -- the factor `ρ_c - 1` vanishes: `h_u(c) = 1`, so `s_u` lies on the first line of `c`
        rw [e1] at h1
        obtain ⟨c, hcE, hc0⟩ := Finset.prod_eq_zero_iff.1 h1
        have hfac : A.sf c = c := (mem_fixedFin A).1 hcE
        have hv : hu A u c = 1 := by
          rw [map_sub, map_one, rho_eval A hfac] at hc0
          exact sub_eq_zero.1 hc0
        refine ⟨![2 * c, (1 : K), -(c ^ 2 + A.d c)], ?_, ?_, ?_⟩
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ (hV1mem c hcE))
        · intro h0
          have h1' : (![2 * c, (1 : K), -(c ^ 2 + A.d c)] : Fin 3 → K) 1 = 0 := by
            rw [h0]; rfl
          simp only [Matrix.cons_val_one] at h1'
          exact one_ne_zero h1'
        · refine (lineForm_v1 A c u).2 ?_
          rw [rho_eval A hfac]
          exact hv
      · -- the factor `ρ_c - ρ_a` vanishes: `h_u(c) = h_u(a)`, so `s_u` lies on the second line
        rw [e2] at h2
        obtain ⟨c, hc, hc0⟩ := Finset.prod_eq_zero_iff.1 h2
        rw [Finset.mem_erase] at hc
        obtain ⟨hca, hcE⟩ := hc
        have hfac : A.sf c = c := (mem_fixedFin A).1 hcE
        have hv : hu A u c = hu A u a := by
          rw [map_sub, rho_eval A hfac, rho_eval A hfa] at hc0
          exact sub_eq_zero.1 hc0
        refine ⟨![2 * c * (A.d c)⁻¹ - 2 * a * (A.d a)⁻¹, (A.d c)⁻¹ - (A.d a)⁻¹,
          -(c ^ 2) * (A.d c)⁻¹ + a ^ 2 * (A.d a)⁻¹], ?_, ?_, ?_⟩
        · have hc1 : c ∈ (fixedFin A).erase a := Finset.mem_erase.2 ⟨hca, hcE⟩
          exact Finset.mem_union_left _ (Finset.mem_union_right _ (hV2mem c hc1))
        · exact hne2 c a hca
        · refine (lineForm_v2 A c a u).2 ?_
          rw [map_sub, rho_eval A hfac, rho_eval A hfa, sub_eq_zero]
          exact hv
    · -- the factor `ρ_c - ρ_b` vanishes
      rw [e3] at h3
      obtain ⟨c, hc, hc0⟩ := Finset.prod_eq_zero_iff.1 h3
      rw [Finset.mem_erase, Finset.mem_erase] at hc
      obtain ⟨hcb, hca, hcE⟩ := hc
      have hfac : A.sf c = c := (mem_fixedFin A).1 hcE
      have hv : hu A u c = hu A u b := by
        rw [map_sub, rho_eval A hfac, rho_eval A hfb] at hc0
        exact sub_eq_zero.1 hc0
      refine ⟨![2 * c * (A.d c)⁻¹ - 2 * b * (A.d b)⁻¹, (A.d c)⁻¹ - (A.d b)⁻¹,
        -(c ^ 2) * (A.d c)⁻¹ + b ^ 2 * (A.d b)⁻¹], ?_, ?_, ?_⟩
      · have hc1 : c ∈ (fixedFin A).erase a := Finset.mem_erase.2 ⟨hca, hcE⟩
        exact Finset.mem_union_right _ (hV3mem c (Finset.mem_erase.2 ⟨hcb, hc1⟩))
      · exact hne2 c b hcb
      · refine (lineForm_v2 A c b u).2 ?_
        rw [map_sub, rho_eval A hfac, rho_eval A hfb, sub_eq_zero]
        exact hv

/-- **Proposition 9 of the paper**, covering part: if `f ≥ 4`, the whole set `S` is covered by
at most `3f - 6` projective lines of the involution plane, each of them given explicitly in the
paper (the factors of `H` in Theorem 8 together with the `f - 1` lines covering the nonsplit
members).

The lines are returned as their nonzero coefficient vectors. -/
theorem exists_cover_by_lines (hodd : Odd (Nat.card K)) (hq : 5 ≤ Nat.card K)
    {S : Set (PGL2 K)} (hS : IsAdmissible S) (hcard : Nat.card S = Nat.card K)
    {σ : Equiv.Perm (P1 K)} (hσ : IsMissingPerm S σ) (hσ2 : σ * σ = 1) (hf : 4 ≤ numFixed σ) :
    ∃ V : Finset (Fin 3 → K), V.card ≤ 3 * numFixed σ - 6 ∧
      ∀ s ∈ S, ∃ v ∈ V, v ≠ 0 ∧ lineForm v s = 0 := by
  classical
  by_cases hinf : σ ptInf = ptInf
  · exact exists_cover_by_lines_of_fixes_ptInf hodd hq hS hcard hσ hσ2 hf hinf
  · -- `σ` does not fix `∞`: move a fixed point of `σ` to `∞`, cover the conjugate of `S`, and pull
    -- the covering lines back along the conjugation of the involution plane
    have hne : numFixed σ ≠ 0 := by omega
    obtain ⟨⟨x, hx⟩⟩ := (Nat.card_ne_zero.1 hne).1
    obtain ⟨g, hg⟩ := exists_smul_eq_ptInf x
    set σ' : Equiv.Perm (P1 K) := MulAction.toPerm g * σ * (MulAction.toPerm g)⁻¹ with hσ'def
    have hσ'coe : (σ' : P1 K → P1 K) = conjPerm g (σ : P1 K → P1 K) := by
      funext y
      rfl
    have hσ'sq : σ' * σ' = 1 := by
      rw [hσ'def]
      have e : MulAction.toPerm g * σ * (MulAction.toPerm g)⁻¹
            * (MulAction.toPerm g * σ * (MulAction.toPerm g)⁻¹)
          = MulAction.toPerm g * (σ * σ) * (MulAction.toPerm g)⁻¹ := by group
      rw [e, hσ2, mul_one, mul_inv_cancel]
    have hnf' : numFixed σ' = numFixed σ := by
      rw [hσ'coe]
      exact numFixed_conjPerm g (σ : P1 K → P1 K)
    have hgx : g⁻¹ • (ptInf : P1 K) = x := by
      rw [← hg, inv_smul_smul]
    have hinf' : σ' (ptInf : P1 K) = ptInf := by
      rw [hσ'coe]
      show g • σ (g⁻¹ • ptInf) = ptInf
      rw [hgx, hx, hg]
    have hmiss' : IsMissingPerm (conjSet g S) (σ' : P1 K → P1 K) := by
      rw [hσ'coe]
      exact isMissingPerm_conjSet g hσ
    obtain ⟨V, hVcard, hVcov⟩ :=
      exists_cover_by_lines_of_fixes_ptInf hodd hq (isAdmissible_conjSet g hS)
        (by rw [card_conjSet, hcard]) hmiss' hσ'sq (by rw [hnf']; exact hf) hinf'
    set A : GL (Fin 2) K := Quotient.out g with hAdef
    have hA : (A : PGL2 K) = g := Quotient.out_eq g
    have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd_card hodd
    refine ⟨V.image (Tmat A), ?_, ?_⟩
    · calc (V.image (Tmat A)).card ≤ V.card := Finset.card_image_le
        _ ≤ 3 * numFixed σ' - 6 := hVcard
        _ = 3 * numFixed σ - 6 := by rw [hnf']
    · intro s hs
      have ht : g * s * g⁻¹ ∈ conjSet g S := ⟨s, hs, rfl⟩
      obtain ⟨v, hvV, hv0, hvline⟩ := hVcov _ ht
      exact ⟨Tmat A v, Finset.mem_image.2 ⟨v, hvV, rfl⟩, Tmat_ne_zero h2 A hv0,
        (lineForm_conj h2 A s v).1 (by rw [hA]; exact hvline)⟩


/-! ### Split involutions on a line (Lemma 10) -/

/-! #### Chunk (1) of Lemma 10: conjugation to the normal form `[1 : 0 : 0]`

`split_off_line` is proved in the normalization `R = diag(1,-1)`, i.e. the point `[1 : 0 : 0]` of
the involution plane, and transported back along the conjugation of the involution plane:

* `exists_conj_eq_diag` : every split involution is conjugate to `diag(1,-1)` — its two fixed
  points are moved to `0` and `∞` (`exists_smul_eq_ptInf`, `exists_translate`) and a conjugate
  fixing both is `diag(1,-1)` (`eq_diagInv_of_fixes`, where a lift is diagonal since it preserves
  the two coordinate lines, and its square is a scalar);
* `card_splitLine_conj` : conjugation by a lift `A` is a bijection from the counted set of
  `(R, v)` to that of `(A⁻¹ R A, Tmat A v)`, using `lineForm_conj` (the line `v` becomes
  `Tmat A v`), `isInvolution_conj` and `fixedPointFree_conj`;
* `exists_reduce_diag` : the two together, including the side conditions `v ≠ 0` and
  `lineForm v R ≠ 0`.
-/


/-- Being fixed-point-free is invariant under conjugation. -/
lemma fixedPointFree_conj (g u : PGL2 K) :
    (∀ x : P1 K, (g * u * g⁻¹) • x ≠ x) ↔ ∀ x : P1 K, u • x ≠ x := by
  constructor
  · intro h x hx
    apply h (g • x)
    rw [conj_smul, inv_smul_smul, hx]
  · intro h x hx
    have h1 : g • (u • (g⁻¹ • x)) = x := by rw [← conj_smul]; exact hx
    have h2 : u • (g⁻¹ • x) = g⁻¹ • x := by
      have := congrArg (fun z => g⁻¹ • z) h1
      rwa [inv_smul_smul] at this
    exact h (g⁻¹ • x) h2

section Transport

/-- **Chunk (1) of Lemma 10.** Conjugation transports the set counted in Lemma 10: for a lift `A`
of the conjugating element, `s ↦ A⁻¹ s A` is a bijection from the points of the line `v` whose
product with `R` is fixed-point-free onto the points of the line `Tmat A v` whose product with
`A⁻¹ R A` is fixed-point-free. -/
theorem card_splitLine_conj (h2 : (2 : K) ≠ 0) (A : GL (Fin 2) K) (R : PGL2 K)
    (v : Fin 3 → K) :
    Nat.card {s : PGL2 K // lineForm v s = 0 ∧ IsInvolution s ∧
        ∀ x : P1 K, (R * s) • x ≠ x}
      = Nat.card {t : PGL2 K // lineForm (Tmat A v) t = 0 ∧ IsInvolution t ∧
        ∀ x : P1 K, (((A : PGL2 K)⁻¹ * R * (A : PGL2 K)) * t) • x ≠ x} := by
  classical
  have keyL : ∀ u : PGL2 K,
      lineForm v ((A : PGL2 K) * u * (A : PGL2 K)⁻¹) = 0 ↔ lineForm (Tmat A v) u = 0 :=
    fun u => lineForm_conj h2 A u v
  have keyF : ∀ u : PGL2 K,
      (∀ x : P1 K, (((A : PGL2 K)⁻¹ * R * (A : PGL2 K)) * u) • x ≠ x) ↔
        ∀ x : P1 K, (R * ((A : PGL2 K) * u * (A : PGL2 K)⁻¹)) • x ≠ x := by
    intro u
    have hff := fixedPointFree_conj ((A : PGL2 K)⁻¹)
      (R * ((A : PGL2 K) * u * (A : PGL2 K)⁻¹))
    have hconj : ((A : PGL2 K)⁻¹ * (R * ((A : PGL2 K) * u * (A : PGL2 K)⁻¹))
        * ((A : PGL2 K)⁻¹)⁻¹) = ((A : PGL2 K)⁻¹ * R * (A : PGL2 K)) * u := by group
    rw [hconj] at hff
    exact hff
  have hcancel₁ : ∀ s : PGL2 K, (A : PGL2 K) * ((A : PGL2 K)⁻¹ * s * (A : PGL2 K))
      * (A : PGL2 K)⁻¹ = s := fun s => by group
  have hcancel₂ : ∀ t : PGL2 K, (A : PGL2 K)⁻¹ * ((A : PGL2 K) * t * (A : PGL2 K)⁻¹)
      * (A : PGL2 K) = t := fun t => by group
  refine Nat.card_congr ?_
  exact
  { toFun := fun s =>
      ⟨(A : PGL2 K)⁻¹ * s.1 * (A : PGL2 K),
        by
          have h := (keyL ((A : PGL2 K)⁻¹ * s.1 * (A : PGL2 K))).1
          rw [hcancel₁ s.1] at h
          exact h s.2.1,
        (isInvolution_conj ((A : PGL2 K)⁻¹) s.1).2 s.2.2.1,
        (keyF ((A : PGL2 K)⁻¹ * s.1 * (A : PGL2 K))).2 (by
          have h := s.2.2.2
          rwa [← hcancel₁ s.1] at h)⟩
    invFun := fun t =>
      ⟨(A : PGL2 K) * t.1 * (A : PGL2 K)⁻¹,
        (keyL t.1).2 t.2.1,
        (isInvolution_conj (A : PGL2 K) t.1).2 t.2.2.1,
        (keyF t.1).1 t.2.2.2⟩
    left_inv := fun s => Subtype.ext (hcancel₁ s.1)
    right_inv := fun t => Subtype.ext (hcancel₂ t.1) }

end Transport

noncomputable def diagInv : PGL2 K :=
  ((Matrix.GeneralLinearGroup.mkOfDetNeZero !![(1 : K), 0; 0, -1] (by
    rw [Matrix.det_fin_two]; norm_num)) : PGL2 K)

/-- A nonidentity involution of `ℙ¹` fixing both `∞` and `0` is the normal form `diag(1,-1)`: a
lift is diagonal (the two coordinate lines are preserved) and its square is a scalar, so its
diagonal entries are `a` and `-a`. -/
lemma eq_diagInv_of_fixes {s : PGL2 K} (hs : IsInvolution s)
    (hinf : s • (ptInf : P1 K) = ptInf) (h0 : s • (ptFin (0 : K)) = ptFin 0) :
    s = diagInv := by
  classical
  set M : GL (Fin 2) K := Quotient.out s with hMdef
  have hMs : (M : PGL2 K) = s := Quotient.out_eq s
  -- the lift fixes `∞` and `0` in Möbius coordinates
  have hminf : mobius M none = none := by
    have h2 : coord (M • (ptInf : P1 K)) = coord ptInf := by rw [← mk_smul, hMs, hinf]
    rwa [coord_smul_ptInf, coord_ptInf] at h2
  have hm0 : mobius M (some 0) = some 0 := by
    have h2 : coord (M • (ptFin (0 : K))) = coord (ptFin 0) := by rw [← mk_smul, hMs, h0]
    rwa [coord_smul_ptFin, coord_ptFin] at h2
  have h10 : (M : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
    by_contra h
    rw [mobius, mobiusMat, if_neg h] at hminf
    exact nomatch hminf
  have h11 : (M : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 0 := by
    intro h
    rw [mobius, mobiusMat, if_pos (by rw [h10, zero_mul, zero_add]; exact h)] at hm0
    exact nomatch hm0
  have h01 : (M : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 := by
    rw [mobius, mobiusMat, if_neg (by rw [h10, zero_mul, zero_add]; exact h11), h10, zero_mul,
      zero_add] at hm0
    have h : (M : Matrix (Fin 2) (Fin 2) K) 0 1 / (M : Matrix (Fin 2) (Fin 2) K) 1 1 = 0 := by
      simpa using Option.some.inj hm0
    rcases (div_eq_zero_iff).1 h with h' | h'
    · exact h'
    · exact absurd h' h11
  have h10' : ((Quotient.out s : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by simpa [hMdef] using h10
  have h01' : ((Quotient.out s : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 := by simpa [hMdef] using h01
  -- the lift squares to a scalar, so its diagonal entries are opposite
  obtain ⟨l, hl, hsq⟩ := sq_smul_of_isInvolution hs
  have h00 : (M : Matrix (Fin 2) (Fin 2) K) 0 0 ^ 2 = l := by
    have h := congrFun (congrFun hsq 0) 0
    simpa [hMdef, h10', Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, Matrix.one_apply,
      pow_two] using h
  have h11sq : (M : Matrix (Fin 2) (Fin 2) K) 1 1 ^ 2 = l := by
    have h := congrFun (congrFun hsq 1) 1
    simpa [hMdef, h10', h01', Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply,
      Matrix.one_apply, pow_two] using h
  have hdiag : (M : Matrix (Fin 2) (Fin 2) K) 1 1 = -((M : Matrix (Fin 2) (Fin 2) K) 0 0) := by
    have hfac : ((M : Matrix (Fin 2) (Fin 2) K) 0 0 - (M : Matrix (Fin 2) (Fin 2) K) 1 1)
        * ((M : Matrix (Fin 2) (Fin 2) K) 0 0 + (M : Matrix (Fin 2) (Fin 2) K) 1 1) = 0 := by
      linear_combination h00 - h11sq
    rcases mul_eq_zero.1 hfac with h | h
    · -- equal diagonal entries would make the lift a scalar, hence `s = 1`
      exfalso
      apply hs.1
      have hscal : (M : Matrix (Fin 2) (Fin 2) K)
          = (M : Matrix (Fin 2) (Fin 2) K) 0 0 • (1 : Matrix (Fin 2) (Fin 2) K) := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [sub_eq_zero.1 h, h10, h01, Matrix.smul_apply]
      have hmem : M ∈ Subgroup.center (GL (Fin 2) K) := by
        rw [Subgroup.mem_center_iff]
        intro x
        apply Units.ext
        rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, hscal]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply] <;> ring
      rw [← hMs, QuotientGroup.eq_one_iff]
      exact hmem
    · linear_combination h
  -- hence the lift is a nonzero scalar multiple of `diag(1,-1)`
  have h00ne : (M : Matrix (Fin 2) (Fin 2) K) 0 0 ≠ 0 := by
    intro h
    apply hl
    rw [← h00, h]
    ring
  have hMval : (M : Matrix (Fin 2) (Fin 2) K)
      = (M : Matrix (Fin 2) (Fin 2) K) 0 0 • !![(1 : K), 0; 0, -1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [h10, h01, hdiag, Matrix.smul_apply]
  have hdetB : ((M : Matrix (Fin 2) (Fin 2) K) 0 0 • !![(1 : K), 0; 0, -1]).det ≠ 0 := by
    rw [hMval.symm]
    exact Matrix.GeneralLinearGroup.det_ne_zero M
  have hGL : M = Matrix.GeneralLinearGroup.mkOfDetNeZero
      ((M : Matrix (Fin 2) (Fin 2) K) 0 0 • !![(1 : K), 0; 0, -1]) hdetB := by
    apply Units.ext
    show (M : Matrix (Fin 2) (Fin 2) K)
      = ((M : Matrix (Fin 2) (Fin 2) K) 0 0 • !![(1 : K), 0; 0, -1])
    exact hMval
  calc s = (M : PGL2 K) := hMs.symm
    _ = ((Matrix.GeneralLinearGroup.mkOfDetNeZero
          ((M : Matrix (Fin 2) (Fin 2) K) 0 0 • !![(1 : K), 0; 0, -1]) hdetB :
          GL (Fin 2) K) : PGL2 K) :=
        congrArg (fun x : GL (Fin 2) K => (x : PGL2 K)) hGL
    _ = diagInv := by
        rw [class_smul ((M : Matrix (Fin 2) (Fin 2) K) 0 0) h00ne]
        rfl

/-- The affine translation `x ↦ x - c`, which fixes `∞` and sends `c` to `0`. -/
lemma exists_translate (c : K) :
    ∃ h : PGL2 K, h • ptFin c = ptFin 0 ∧ h • (ptInf : P1 K) = ptInf := by
  classical
  have hdet : (!![(1 : K), -c; 0, 1] : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := by
    rw [Matrix.det_fin_two]
    norm_num
  refine ⟨((Matrix.GeneralLinearGroup.mkOfDetNeZero !![(1 : K), -c; 0, 1] hdet :
    GL (Fin 2) K) : PGL2 K), ?_, ?_⟩
  · apply coord_injective
    rw [mk_smul, coord_smul_ptFin, coord_ptFin]
    simp [mobius, mobiusMat, mkOfDetNeZero_val]
  · apply coord_injective
    rw [mk_smul, coord_smul_ptInf, coord_ptInf]
    simp [mobius, mobiusMat, mkOfDetNeZero_val]

/-- **Chunk (1) of Lemma 10, the normal form**: every split involution of `ℙ¹(K)` is conjugate to
`diag(1,-1)`, i.e. to the point `[1 : 0 : 0]` of the involution plane.

The two fixed points of `R` are moved to `0` and `∞` (`exists_smul_eq_ptInf` followed by the
translation `exists_translate`), and a conjugate fixing both is `diag(1,-1)`
(`eq_diagInv_of_fixes`). -/
theorem exists_conj_eq_diag (hodd : Odd (Nat.card K)) {R : PGL2 K} (hR : IsSplit R) :
    ∃ g : PGL2 K, R = g * diagInv * g⁻¹ := by
  classical
  -- the two fixed points of `R`
  have hcard : Nat.card (fixPoints R) = 2 := card_fixPoints_of_isSplit hodd hR
  obtain ⟨x, y, hxy, -⟩ := Nat.card_eq_two_iff.1 hcard
  have hpx : R • (x : P1 K) = x.1 := x.2
  have hqy : R • (y : P1 K) = y.1 := y.2
  have hne : (x : P1 K) ≠ y.1 := fun h => hxy (Subtype.ext h)
  -- move the first fixed point to `∞`
  obtain ⟨g₁, hg₁⟩ := exists_smul_eq_ptInf (y : P1 K)
  -- the other one is then a finite point
  have hg₁x : g₁ • (x : P1 K) ≠ ptInf := by
    intro hh
    apply hne
    have h1 : (x : P1 K) = g₁⁻¹ • (ptInf : P1 K) := by
      have h2 := congrArg (fun z => g₁⁻¹ • z) hh
      rwa [inv_smul_smul] at h2
    rw [h1, ← hg₁, inv_smul_smul]
  obtain ⟨c, hc⟩ : ∃ c : K, g₁ • (x : P1 K) = ptFin c := by
    cases hco : coord (g₁ • (x : P1 K)) with
    | none => exact absurd (by rw [← ptOf_coord (g₁ • (x : P1 K)), hco]; rfl) hg₁x
    | some c => exact ⟨c, by rw [← ptOf_coord (g₁ • (x : P1 K)), hco]; rfl⟩
  -- translate it to `0`
  obtain ⟨h, hh0, hhinf⟩ := exists_translate c
  -- the conjugate fixes `0` and `∞` and is an involution, hence `diag(1,-1)`
  have h0' : (h * g₁)⁻¹ • (ptFin (0 : K) : P1 K) = (x : P1 K) := by
    rw [mul_inv_rev, mul_smul, ← hh0, inv_smul_smul, ← hc, inv_smul_smul]
  have hinf' : (h * g₁)⁻¹ • (ptInf : P1 K) = (y : P1 K) := by
    rw [mul_inv_rev, mul_smul, ← hhinf, inv_smul_smul, ← hg₁, inv_smul_smul]
  have hfix0 : ((h * g₁) * R * (h * g₁)⁻¹) • ptFin (0 : K) = ptFin 0 := by
    rw [conj_smul, h0', hpx, mul_smul, hc, hh0]
  have hfixinf : ((h * g₁) * R * (h * g₁)⁻¹) • (ptInf : P1 K) = ptInf := by
    rw [conj_smul, hinf', hqy, mul_smul, hg₁, hhinf]
  have hinv : IsInvolution ((h * g₁) * R * (h * g₁)⁻¹) :=
    (isInvolution_conj (h * g₁) R).2 hR.1
  have hconj : (h * g₁) * R * (h * g₁)⁻¹ = diagInv := eq_diagInv_of_fixes hinv hfixinf hfix0
  refine ⟨(h * g₁)⁻¹, ?_⟩
  rw [← hconj]
  group

lemma Tmat_zero (A : GL (Fin 2) K) : Tmat A 0 = 0 := by
  funext i
  fin_cases i <;>
    simp [Tmat, Nmat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

/-- **Chunk (1) of Lemma 10, assembled**: the count of `split_off_line` for `(R, v)` is the count
for the normal form `(diag(1,-1), Tmat A v)`, and the two side conditions `v ≠ 0` and
`lineForm v R ≠ 0` correspond. -/
theorem exists_reduce_diag (hodd : Odd (Nat.card K)) (h2 : (2 : K) ≠ 0) {R : PGL2 K}
    (hR : IsSplit R) (v : Fin 3 → K) :
    ∃ (A : GL (Fin 2) K) (w : Fin 3 → K),
      (v ≠ 0 ↔ w ≠ 0) ∧ (lineForm v R ≠ 0 ↔ lineForm w diagInv ≠ 0) ∧
      Nat.card {s : PGL2 K // lineForm v s = 0 ∧ IsInvolution s ∧
          ∀ x : P1 K, (R * s) • x ≠ x}
        = Nat.card {t : PGL2 K // lineForm w t = 0 ∧ IsInvolution t ∧
            ∀ x : P1 K, (diagInv * t) • x ≠ x} := by
  classical
  obtain ⟨g, hg⟩ := exists_conj_eq_diag hodd hR
  -- a lift of `g`
  set A : GL (Fin 2) K := Quotient.out g with hAdef
  have hA : (A : PGL2 K) = g := Quotient.out_eq g
  refine ⟨A, Tmat A v, ?_, ?_, ?_⟩
  · -- `v ≠ 0 ↔ Tmat A v ≠ 0`
    constructor
    · intro hv
      exact Tmat_ne_zero h2 A hv
    · intro hw hv
      rw [hv] at hw
      exact hw (Tmat_zero A)
  · -- `lineForm v R ≠ 0 ↔ lineForm (Tmat A v) diagInv ≠ 0`
    have hR' : (A : PGL2 K) * diagInv * (A : PGL2 K)⁻¹ = R := by rw [hA]; exact hg.symm
    constructor
    · intro hRv hzero
      apply hRv
      rw [← hR']
      exact (lineForm_conj h2 A diagInv v).2 hzero
    · intro hw hzero
      apply hw
      have := (lineForm_conj h2 A diagInv v).1
      rw [hR'] at this
      exact this hzero
  · -- the two counts agree
    have h := card_splitLine_conj h2 A R v
    have hR'' : (A : PGL2 K)⁻¹ * R * (A : PGL2 K) = diagInv := by
      rw [hA, hg]
      group
    rw [hR''] at h
    exact h

/-! #### Chunk (2) of Lemma 10: the line is parametrized by `ℙ¹`

On the involution plane with points `[A : B : C]`, a line `L` is `v₀A + v₁B + v₂C = 0`. When
`[1 : 0 : 0] ∉ L` (`v 0 ≠ 0`, see `lineForm_diagInv_iff`) the projection `[A : B : C] ↦ [B : C]`
is a bijection from the involution points of `L` onto the points of `ℙ¹` whose reconstructed
`A = -(v₁B + v₂C)/v₀` satisfies `A² + BC ≠ 0`:

* `lineForm_coord_ne_zero` : on such a line, `(B, C)` never vanishes, so the projection is defined;
* `invCoord_injOn_involutions` : proportional `invCoord`s give equal involutions (the trace-zero
  lift is determined by `tz`, `tz_injective_on_trace_zero`);
* `exists_involution_on_line` : a point `[B : C]` with `A² + BC ≠ 0` is the projection of the
  involution of the trace-zero matrix `[[A, B], [C, -A]]`, whose square is `(A² + BC) · 1`;
* `line_parametrize` : the three statements together.
-/

/-- The plane point of `diag(1,-1)` is `[1 : 0 : 0]`. -/
lemma invCoord_diagInv : ∃ lam : K, lam ≠ 0 ∧ invCoord diagInv = lam • ![(1 : K), 0, 0] := by
  classical
  have hdet : (!![(1 : K), 0; 0, -1] : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := by
    rw [Matrix.det_fin_two]; norm_num
  obtain ⟨mu, hmu, hcoord⟩ :=
    exists_invCoord_eq_smul_tz (Matrix.GeneralLinearGroup.mkOfDetNeZero !![(1 : K), 0; 0, -1] hdet)
      rfl
  refine ⟨mu, hmu, ?_⟩
  unfold diagInv
  rw [hcoord]
  congr 1
  funext i
  fin_cases i <;>
    simp [tz, mkOfDetNeZero_val, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

/-- `L` does not contain `[1 : 0 : 0]` exactly when `v 0 ≠ 0`, i.e. `lineForm v diagInv ≠ 0`. -/
lemma lineForm_diagInv_iff (v : Fin 3 → K) : lineForm v diagInv = 0 ↔ v 0 = 0 := by
  obtain ⟨lam, hlam, hcoord⟩ := invCoord_diagInv (K := K)
  unfold lineForm
  rw [hcoord, Fin.sum_univ_three]
  simp only [Pi.smul_apply, smul_eq_mul]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  have hval : v 0 * (lam * 1) + v 1 * (lam * 0) + v 2 * (lam * 0) = lam * v 0 := by ring
  rw [hval]
  constructor
  · intro h
    exact (mul_eq_zero.1 h).resolve_left hlam
  · intro h
    rw [h, mul_zero]

/-- `tz` is injective on trace-zero matrices. -/
lemma tz_injective_on_trace_zero {M N : Matrix (Fin 2) (Fin 2) K} (hM : M.trace = 0)
    (hN : N.trace = 0) (h : tz M = tz N) : M = N := by
  have htr : ∀ P : Matrix (Fin 2) (Fin 2) K, P.trace = 0 → P 0 0 + P 1 1 = 0 := by
    intro P hP
    rw [← Matrix.trace_fin_two]
    exact hP
  have e0 : M 0 0 = N 0 0 := by
    have h0 := congrFun h 0
    simp only [tz, Matrix.cons_val_zero] at h0
    rw [htr M hM, htr N hN, zero_div, sub_zero, sub_zero] at h0
    exact h0
  have e1 : M 0 1 = N 0 1 := by
    have h1 := congrFun h 1
    simpa [tz] using h1
  have e2 : M 1 0 = N 1 0 := by
    have h2 := congrFun h 2
    simpa [tz] using h2
  have e3 : M 1 1 = N 1 1 := by
    have h1 : M 0 0 + M 1 1 = 0 := htr M hM
    have h2 : N 0 0 + N 1 1 = 0 := htr N hN
    linear_combination h1 - h2 - e0
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e0, e1, e2, e3]

/-- The involution-plane point of an involution determines the involution: the trace-zero
coordinates are homogeneous coordinates of the class of the trace-zero lift. This is injectivity of
the parametrization `s ↦ [B(s) : C(s)]`. -/
lemma invCoord_injOn_involutions (h2 : (2 : K) ≠ 0) {s t : PGL2 K} (hs : IsInvolution s)
    (ht : IsInvolution t) {mu : K} (hmu : mu ≠ 0) (h : invCoord t = mu • invCoord s) : t = s := by
  classical
  have hMt : ((Quotient.out t : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).trace = 0 :=
    trace_zero_of_isInvolution ht
  have hMs : ((Quotient.out s : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).trace = 0 :=
    trace_zero_of_isInvolution hs
  have hmat : ((Quotient.out t : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = mu • ((Quotient.out s : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
    refine tz_injective_on_trace_zero hMt ?_ ?_
    · rw [Matrix.trace_smul, hMs, smul_zero]
    · rw [tz_smul, ← invCoord_eq_tz, ← invCoord_eq_tz, h]
  -- equal classes, since the lifts differ by a scalar
  have hdet : (mu • ((Quotient.out s : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)).det ≠ 0 := by
    rw [← hmat]
    exact Matrix.GeneralLinearGroup.det_ne_zero (Quotient.out t)
  calc t = ((Quotient.out t : GL (Fin 2) K) : PGL2 K) := (Quotient.out_eq t).symm
    _ = ((Matrix.GeneralLinearGroup.mkOfDetNeZero
          (mu • ((Quotient.out s : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) hdet :
          GL (Fin 2) K) : PGL2 K) := by
        congr 1
        apply Units.ext
        show ((Quotient.out t : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
          = (mu • ((Quotient.out s : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))
        exact hmat
    _ = ((Matrix.GeneralLinearGroup.mkOfDetNeZero
          (((Quotient.out s : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))
          (Matrix.GeneralLinearGroup.det_ne_zero (Quotient.out s)) : GL (Fin 2) K) : PGL2 K) :=
        class_smul mu hmu _ _ _
    _ = s := by
        have hgl : (Matrix.GeneralLinearGroup.mkOfDetNeZero
            ((Quotient.out s : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
            (Matrix.GeneralLinearGroup.det_ne_zero (Quotient.out s)) : GL (Fin 2) K)
            = Quotient.out s := by
          apply Units.ext
          rw [mkOfDetNeZero_val]
        rw [hgl]
        exact Quotient.out_eq s

/-- `invCoord` of the identity is zero (the trace-zero coordinates of a scalar matrix vanish). -/
lemma invCoord_one_eq_zero (h2 : (2 : K) ≠ 0) : invCoord (1 : PGL2 K) = 0 := by
  obtain ⟨mu, hmu, hcoord⟩ :=
    exists_invCoord_eq_smul_tz (1 : GL (Fin 2) K) (g := 1) rfl
  have hz : tz (1 : Matrix (Fin 2) (Fin 2) K) = 0 := by
    funext i
    fin_cases i
    · show (1 : K) - (1 + 1) / 2 = 0
      have hdiv : ((1 : K) + 1) / 2 = 1 := by
        rw [div_eq_iff h2]
        ring
      rw [hdiv, sub_self]
    · show (1 : Matrix (Fin 2) (Fin 2) K) 0 1 = 0
      simp
    · show (1 : Matrix (Fin 2) (Fin 2) K) 1 0 = 0
      simp
  rw [hcoord, show ((1 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 from rfl, hz, smul_zero]

/-- For a line `L` not containing `[1 : 0 : 0]` (`v 0 ≠ 0`), the `(B, C)`-coordinates of an
involution on `L` are not both zero: otherwise the point would be `[1 : 0 : 0]`. -/
lemma lineForm_coord_ne_zero (h2 : (2 : K) ≠ 0) {v : Fin 3 → K} (hv0 : v 0 ≠ 0) {s : PGL2 K}
    (hs : IsInvolution s) (h : lineForm v s = 0) : invCoord s 1 ≠ 0 ∨ invCoord s 2 ≠ 0 := by
  by_contra hb
  push Not at hb
  obtain ⟨hb1, hb2⟩ := hb
  have hnz : invCoord s ≠ 0 := (invCoord_normalized h2 hs).1
  have h0 : invCoord s 0 ≠ 0 := by
    intro hzero
    apply hnz
    funext i
    fin_cases i
    · exact hzero
    · exact hb1
    · exact hb2
  have hv : v 0 * invCoord s 0 = 0 := by
    have hsum : lineForm v s
        = v 0 * invCoord s 0 + v 1 * invCoord s 1 + v 2 * invCoord s 2 := by
      unfold lineForm
      rw [Fin.sum_univ_three]
    rw [hsum, hb1, hb2] at h
    simpa using h
  exact h0 ((mul_eq_zero.1 hv).resolve_left hv0)

/-- **Chunk (2) of Lemma 10, surjectivity**: every point `[B : C]` of `ℙ¹` whose reconstructed
`A = -(v₁B + v₂C)/v₀` satisfies `A² + BC ≠ 0` is the projection of an involution on the line. -/
lemma exists_involution_on_line (h2 : (2 : K) ≠ 0) {v : Fin 3 → K} (hv0 : v 0 ≠ 0) {B C : K}
    (hconic : (-(v 1 * B + v 2 * C) / v 0) ^ 2 + B * C ≠ 0) :
    ∃ (s : PGL2 K) (mu : K), mu ≠ 0 ∧ IsInvolution s ∧ lineForm v s = 0 ∧
      invCoord s = mu • ![-(v 1 * B + v 2 * C) / v 0, B, C] := by
  classical
  set A : K := -(v 1 * B + v 2 * C) / v 0 with hA
  set Z : Matrix (Fin 2) (Fin 2) K := !![A, B; C, -A] with hZ
  have hdet : Z.det ≠ 0 := by
    rw [hZ, Matrix.det_fin_two_of]
    have hval : A * -A - B * C = -(A ^ 2 + B * C) := by ring
    rw [hval]
    exact neg_ne_zero.2 hconic
  -- the class of `Z` is an involution, because `Z * Z` is the scalar `A² + BC`
  have htrZ : Z.trace = 0 := by
    rw [hZ, Matrix.trace, Fin.sum_univ_two]
    show A + -A = 0
    ring
  have hZZ : Z * Z = (A ^ 2 + B * C) • (1 : Matrix (Fin 2) (Fin 2) K) := by
    rw [sq_eq_trace_smul_sub_det, htrZ, zero_smul, zero_sub, hZ, Matrix.det_fin_two_of,
      ← neg_smul]
    congr 1
    ring
  set g : GL (Fin 2) K := Matrix.GeneralLinearGroup.mkOfDetNeZero Z hdet with hg
  have hgval : (g : Matrix (Fin 2) (Fin 2) K) = Z := mkOfDetNeZero_val Z hdet
  have hsqmat : (g : Matrix (Fin 2) (Fin 2) K) * (g : Matrix (Fin 2) (Fin 2) K)
      = (A ^ 2 + B * C) • (1 : Matrix (Fin 2) (Fin 2) K) := by
    rw [hgval, hZZ]
  have hgg : ((g * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = (A ^ 2 + B * C) • (1 : Matrix (Fin 2) (Fin 2) K) := by
    rw [Matrix.GeneralLinearGroup.coe_mul, hsqmat]
  have hmem : g * g ∈ Subgroup.center (GL (Fin 2) K) := by
    rw [Subgroup.mem_center_iff]
    intro x
    apply Units.ext
    show ((x * (g * g) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = ((g * g * x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
    rw [Matrix.GeneralLinearGroup.coe_mul x (g * g),
      Matrix.GeneralLinearGroup.coe_mul (g * g) x, hgg]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, Matrix.one_apply] <;> ring
  have hsq : ((g : PGL2 K) * (g : PGL2 K)) = 1 := by
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
    exact hmem
  -- its coordinates are `[A : B : C]`
  obtain ⟨mu, hmu, hcoord⟩ := exists_invCoord_eq_smul_tz g rfl
  have htz : tz Z = ![A, B, C] := by
    funext i
    fin_cases i <;> simp [tz, hZ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
  have hcoord' : invCoord (g : PGL2 K) = mu • ![A, B, C] := by
    rw [hcoord, hgval, htz]
  -- the point `[A : B : C]` is nonzero, so `g` is not the identity
  have hnz : (![A, B, C] : Fin 3 → K) ≠ 0 := by
    intro hzero
    apply hconic
    have h1 : A = 0 := by
      have := congrFun hzero 0
      simpa using this
    have h2' : B = 0 := by
      have := congrFun hzero 1
      simpa using this
    rw [h1, h2']
    ring
  have hne : (g : PGL2 K) ≠ 1 := by
    intro h1
    rw [h1, invCoord_one_eq_zero h2] at hcoord'
    have : mu • (![A, B, C] : Fin 3 → K) = 0 := hcoord'.symm
    exact hnz ((smul_eq_zero.1 this).resolve_left hmu)
  refine ⟨(g : PGL2 K), mu, hmu, ⟨hne, hsq⟩, ?_, hcoord'⟩
  -- and it lies on the line
  unfold lineForm
  rw [hcoord', Fin.sum_univ_three]
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  have hline : v 0 * A + v 1 * B + v 2 * C = 0 := by
    rw [hA]
    field_simp
    ring
  linear_combination mu * hline

/-- **Chunk (2) of Lemma 10: the line `L` is parametrized by `ℙ¹`.** Assume `[1 : 0 : 0] ∉ L`,
i.e. `v 0 ≠ 0` (`lineForm_diagInv_iff`). Then

* the `(B, C)`-coordinates of an involution on `L` are never both zero, so `s ↦ [B(s) : C(s)]` is
  a map to `ℙ¹`;
* two involutions on `L` with proportional coordinates are equal;
* every `[B : C]` whose reconstructed `A = -(v₁B + v₂C)/v₀` satisfies `A² + BC ≠ 0` is the
  projection of an involution on `L`, and `A` is the unique plane coordinate over `[B : C]`.
-/
theorem line_parametrize (h2 : (2 : K) ≠ 0) {v : Fin 3 → K} (hv0 : v 0 ≠ 0) :
    (∀ s : PGL2 K, IsInvolution s → lineForm v s = 0 → invCoord s 1 ≠ 0 ∨ invCoord s 2 ≠ 0) ∧
    (∀ s t : PGL2 K, IsInvolution s → IsInvolution t → lineForm v s = 0 → lineForm v t = 0 →
        (∃ mu : K, mu ≠ 0 ∧ invCoord t = mu • invCoord s) → t = s) ∧
    (∀ B C : K, (-(v 1 * B + v 2 * C) / v 0) ^ 2 + B * C ≠ 0 →
        ∃ (s : PGL2 K) (mu : K), mu ≠ 0 ∧ IsInvolution s ∧ lineForm v s = 0 ∧
          invCoord s = mu • ![-(v 1 * B + v 2 * C) / v 0, B, C]) :=
  ⟨fun s hs h => lineForm_coord_ne_zero h2 hv0 hs h,
   fun s t hs ht _ _ h => invCoord_injOn_involutions h2 hs ht h.choose_spec.1 h.choose_spec.2,
   fun B C h => exists_involution_on_line h2 hv0 h⟩

/-! #### Chunk (3) of Lemma 10: fixed points of `diag(1,-1) · s` and the discriminant `-4BC`

For an involution `s` with trace-zero lift `P = [[A, B], [C, -A]]`, the lift of `diag(1,-1) · s` is
`D · P = [[A, B], [-C, A]]`, whose characteristic determinant is

`det (D P - a • 1) = (A - a)² + B C`.

Since `K` is a field, this vanishes for some `a` exactly when `-B C` is a square, i.e. exactly
when the discriminant `-4 B C` is a square (`isSquare_four_mul`). Combined with
`exists_fixed_point_iff_eigenvector` — a projectivity has a fixed point exactly when a lift has an
eigenvector — this gives the paper's dictionary (`exists_fixed_point_diag_mul_iff`,
`exists_fixed_point_diag_mul_iff_four`): `diag(1,-1) · s` is fixed-point-free exactly when `-4BC`
is a nonsquare in `K`.
-/

/-- The action of `GL₂` on `K²` is matrix-vector multiplication. -/
lemma gl_smul_eq_mulVec (g : GL (Fin 2) K) (v : Fin 2 → K) :
    g • v = (g : Matrix (Fin 2) (Fin 2) K) *ᵥ v := by
  rw [show g • v
      = (Matrix.GeneralLinearGroup.toLin g : (Fin 2 → K) →ₗ[K] (Fin 2 → K)) v from by
    rw [Matrix.GeneralLinearGroup.coe_toLin]; rfl]
  rw [Matrix.GeneralLinearGroup.coe_toLin]
  rfl

/-- A projective transformation has a fixed point exactly when a lift has an eigenvector. -/
theorem exists_fixed_point_iff_eigenvector (g : GL (Fin 2) K) :
    (∃ x : P1 K, ((g : PGL2 K)) • x = x) ↔
      ∃ (v : Fin 2 → K) (a : K), v ≠ 0 ∧ (g : Matrix (Fin 2) (Fin 2) K) *ᵥ v = a • v := by
  classical
  have h1 : ∀ (v : Fin 2 → K) (hv : v ≠ 0),
      ((g : PGL2 K)) • Projectivization.mk K v hv
        = Projectivization.mk K (g • v) (smul_ne_zero_iff_ne g |>.2 hv) := by
    intro v hv
    rw [mk_smul, Projectivization.smul_mk]
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨v, hv, rfl⟩ : ∃ (v : Fin 2 → K) (hv : v ≠ 0), x = Projectivization.mk K v hv :=
      ⟨x.rep, x.rep_nonzero, (Projectivization.mk_rep x).symm⟩
    rw [h1 v hv] at hx
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' K (g • v) v _ hv).1 hx
    exact ⟨v, a, hv, (gl_smul_eq_mulVec g v).symm.trans ha.symm⟩
  · rintro ⟨v, a, hv, hva⟩
    have hdet : (g : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := Matrix.GeneralLinearGroup.det_ne_zero g
    have ha0 : a ≠ 0 := by
      rintro rfl
      have hz : (g : Matrix (Fin 2) (Fin 2) K) *ᵥ v = 0 := by rw [hva, zero_smul]
      exact hdet ((Matrix.exists_mulVec_eq_zero_iff (M := (g : Matrix (Fin 2) (Fin 2) K))).1
        ⟨v, hv, hz⟩)
    have hva' : a • v = g • v := by
      rw [gl_smul_eq_mulVec]
      exact hva.symm
    refine ⟨Projectivization.mk K v hv, ?_⟩
    rw [h1 v hv]
    exact (Projectivization.mk_eq_mk_iff' K (g • v) v _ hv).2 ⟨a, hva'⟩

/-- The lift `diag(1,-1)` of the normal form `diagInv`. -/
noncomputable def Dmat (K : Type*) [Field K] : GL (Fin 2) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(1 : K), 0; 0, -1] (by
    rw [Matrix.det_fin_two]; norm_num)

lemma diagInv_eq_Dmat : diagInv = (Dmat K : PGL2 K) := rfl

lemma Dmat_val : (Dmat K : Matrix (Fin 2) (Fin 2) K) = !![(1 : K), 0; 0, -1] :=
  mkOfDetNeZero_val _ _

/-- **Chunk (3) of Lemma 10**: for an involution `s` of `ℙ¹` with trace-zero lift `P`, the product
`diagInv * s` has a fixed point on `ℙ¹(K)` exactly when `-P₀₁ P₁₀` is a square in `K`. -/
theorem exists_fixed_point_diag_mul_iff {s : PGL2 K} {P : GL (Fin 2) K}
    (hP : (P : PGL2 K) = s) (htr : ((P : Matrix (Fin 2) (Fin 2) K)).trace = 0) :
    (∃ x : P1 K, (diagInv * s) • x = x) ↔
      IsSquare (-((P : Matrix (Fin 2) (Fin 2) K) 0 1 * (P : Matrix (Fin 2) (Fin 2) K) 1 0)) := by
  classical
  set P' : Matrix (Fin 2) (Fin 2) K := (P : Matrix (Fin 2) (Fin 2) K) with hP'
  set M : Matrix (Fin 2) (Fin 2) K := (Dmat K : Matrix (Fin 2) (Fin 2) K) * P' with hM
  have hP11 : P' 1 1 = -P' 0 0 := by
    have h := htr
    rw [hP', Matrix.trace_fin_two] at h
    linear_combination h
  -- the lift of `diagInv * s` is `D * P = [[P₀₀, P₀₁], [-P₁₀, P₀₀]]`
  have hM00 : M 0 0 = P' 0 0 := by
    rw [hM, Matrix.mul_apply, Fin.sum_univ_two, Dmat_val]
    simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
  have hM01 : M 0 1 = P' 0 1 := by
    rw [hM, Matrix.mul_apply, Fin.sum_univ_two, Dmat_val]
    simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
  have hM10 : M 1 0 = -P' 1 0 := by
    rw [hM, Matrix.mul_apply, Fin.sum_univ_two, Dmat_val]
    simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
  have hM11 : M 1 1 = P' 0 0 := by
    rw [hM, Matrix.mul_apply, Fin.sum_univ_two, Dmat_val]
    simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, hP11]
  have hgs : diagInv * s = ((Dmat K * P : GL (Fin 2) K) : PGL2 K) := by
    rw [diagInv_eq_Dmat, ← hP, ← QuotientGroup.mk_mul]
  have hcoe : ((Dmat K * P : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = M := by
    rw [hM, hP', Matrix.GeneralLinearGroup.coe_mul]
  -- the characteristic determinant of the lift
  have hcompute : ∀ a : K, (M - a • (1 : Matrix (Fin 2) (Fin 2) K)).det
      = (P' 0 0 - a) ^ 2 + P' 0 1 * P' 1 0 := by
    intro a
    have e00 : (M - a • (1 : Matrix (Fin 2) (Fin 2) K)) 0 0 = P' 0 0 - a := by
      rw [Matrix.sub_apply, Matrix.smul_apply, hM00, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    have e01 : (M - a • (1 : Matrix (Fin 2) (Fin 2) K)) 0 1 = P' 0 1 := by
      rw [Matrix.sub_apply, Matrix.smul_apply, hM01, Matrix.one_apply_ne (by decide),
        smul_eq_mul, mul_zero, sub_zero]
    have e10 : (M - a • (1 : Matrix (Fin 2) (Fin 2) K)) 1 0 = -P' 1 0 := by
      rw [Matrix.sub_apply, Matrix.smul_apply, hM10, Matrix.one_apply_ne (by decide),
        smul_eq_mul, mul_zero, sub_zero]
    have e11 : (M - a • (1 : Matrix (Fin 2) (Fin 2) K)) 1 1 = P' 0 0 - a := by
      rw [Matrix.sub_apply, Matrix.smul_apply, hM11, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    rw [Matrix.det_fin_two, e00, e01, e10, e11]
    ring
  rw [hgs, exists_fixed_point_iff_eigenvector]
  constructor
  · -- an eigenvector gives a square root of `-P₀₁P₁₀`
    rintro ⟨v, a, hv, hva⟩
    have hva' : M *ᵥ v = a • v := by rw [hcoe] at hva; exact hva
    have hzero : (M - a • (1 : Matrix (Fin 2) (Fin 2) K)) *ᵥ v = 0 := by
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hva', sub_self]
    have hdet : (M - a • (1 : Matrix (Fin 2) (Fin 2) K)).det = 0 :=
      (Matrix.exists_mulVec_eq_zero_iff (M := M - a • (1 : Matrix (Fin 2) (Fin 2) K))).1
        ⟨v, hv, hzero⟩
    rw [hcompute] at hdet
    exact ⟨P' 0 0 - a, by linear_combination -hdet⟩
  · -- a square root of `-P₀₁P₁₀` gives an eigenvector
    rintro ⟨mu, hmu⟩
    set a : K := P' 0 0 - mu with ha
    have hdet : (M - a • (1 : Matrix (Fin 2) (Fin 2) K)).det = 0 := by
      rw [hcompute]
      have h1 : P' 0 0 - a = mu := by rw [ha]; ring
      rw [h1]
      linear_combination -hmu
    obtain ⟨v, hv, hzero⟩ := (Matrix.exists_mulVec_eq_zero_iff
      (M := M - a • (1 : Matrix (Fin 2) (Fin 2) K))).2 hdet
    refine ⟨v, a, hv, ?_⟩
    have h := hzero
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at h
    rw [hcoe]
    exact sub_eq_zero.1 h

section Four

/-- `4` is a square, so `4 * y` is a square exactly when `y` is (in odd characteristic). -/
lemma isSquare_four_mul (h2 : (2 : K) ≠ 0) {y : K} : IsSquare (4 * y) ↔ IsSquare y := by
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨r / 2, ?_⟩
    have h4 : (4 : K) = 2 * 2 := by norm_num
    rw [h4] at hr
    field_simp
    linear_combination hr
  · rintro ⟨r, rfl⟩
    exact ⟨2 * r, by ring⟩

/-- **Chunk (3) of Lemma 10**, in the paper's form: the discriminant of the characteristic
polynomial of the lift of `diagInv * s` is `-4 P₀₁ P₁₀`. -/
theorem exists_fixed_point_diag_mul_iff_four (h2 : (2 : K) ≠ 0) {s : PGL2 K} {P : GL (Fin 2) K}
    (hP : (P : PGL2 K) = s) (htr : ((P : Matrix (Fin 2) (Fin 2) K)).trace = 0) :
    (∃ x : P1 K, (diagInv * s) • x = x) ↔
      IsSquare (-(4 * ((P : Matrix (Fin 2) (Fin 2) K) 0 1
        * (P : Matrix (Fin 2) (Fin 2) K) 1 0))) := by
  rw [exists_fixed_point_diag_mul_iff hP htr]
  have h4 : (4 : K) * (-((P : Matrix (Fin 2) (Fin 2) K) 0 1
      * (P : Matrix (Fin 2) (Fin 2) K) 1 0))
      = -(4 * ((P : Matrix (Fin 2) (Fin 2) K) 0 1
        * (P : Matrix (Fin 2) (Fin 2) K) 1 0)) := by ring
  rw [← h4]
  exact (isSquare_four_mul (y := -((P : Matrix (Fin 2) (Fin 2) K) 0 1
    * (P : Matrix (Fin 2) (Fin 2) K) 1 0)) h2).symm

end Four

/-! #### Chunk (4) of Lemma 10: the number of points `[B : C]` with `-B*C` a nonsquare

The paper counts the points of `L(𝔽_q)` that represent involutions compatible with `R` by
projecting `[A : B : C] ↦ [B : C]` onto `ℙ¹`, where compatibility is the condition that `-B*C` be
a nonsquare. What is proved here is that count: exactly `(q-1)/2` points of `ℙ¹(K)` have `-B*C`
a nonsquare, and the point `[1 : 0]` (where `-B*C = 0`) is not among them.

The mathematics is the finite-field count `#{t : -t is a nonsquare} = (q-1)/2`: the
nonsquares of `K` are in bijection with the nonzero squares by multiplication by a fixed
nonsquare `n` (using `IsSquare (n*x) ↔ n^(q/2) * x^(q/2) = 1` and `n^(q/2) = -1`), and together
the squares and nonsquares exhaust `K`, with `0` a square.

What is *not* proved here, and is still missing for `split_off_line`, is chunks (1)–(3): the
conjugation of the counted set to `R = [1 : 0 : 0]`, the parametrization `L(K) ≃ ℙ¹(K)`, and the
dictionary "`R·s` fixed-point-free ⟺ the discriminant `-4BC` of the characteristic polynomial of
a lift is a nonsquare". -/

lemma two_ne_zero_of_odd (hodd : Odd (Nat.card K)) : (2 : K) ≠ 0 := by
  have hcard : Fintype.card K % 2 = 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.odd_iff.1 hodd
  have hrc : ringChar K ≠ 2 := fun h => by
    have := (FiniteField.even_card_iff_char_two (F := K)).1 h
    omega
  have hneg : (-1 : K) ≠ 1 := Ring.neg_one_ne_one_of_char_ne_two hrc
  intro h
  apply hneg
  have h1 : (1 : K) + 1 = 0 := by
    rw [← h]
    norm_num
  linear_combination -h1

lemma isSquare_zero' : IsSquare (0 : K) := ⟨0, by simp⟩

lemma card_nonsquare_eq_card_ne_zero_isSquare (hodd : Odd (Nat.card K)) :
    Nat.card {x : K // ¬ IsSquare x} = Nat.card {y : K // y ≠ 0 ∧ IsSquare y} := by
  classical
  have hcard : Fintype.card K % 2 = 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.odd_iff.1 hodd
  have hrc : ringChar K ≠ 2 := fun h => by
    have := (FiniteField.even_card_iff_char_two (F := K)).1 h
    omega
  obtain ⟨n, hn⟩ := FiniteField.exists_nonsquare (F := K) hrc
  have hn0 : n ≠ 0 := by rintro rfl; exact hn isSquare_zero'
  have hnpow : n ^ (Fintype.card K / 2) = -1 := by
    rcases FiniteField.pow_dichotomy hrc hn0 with h | h
    · exact absurd ((FiniteField.isSquare_iff hrc hn0).2 h) hn
    · exact h
  have key : ∀ x : K, x ≠ 0 → (IsSquare (n * x) ↔ ¬ IsSquare x) := by
    intro x hx
    have hnx : n * x ≠ 0 := mul_ne_zero hn0 hx
    rw [FiniteField.isSquare_iff hrc hnx, FiniteField.isSquare_iff hrc hx, mul_pow, hnpow]
    constructor
    · rintro h hx1
      rw [hx1, mul_one] at h
      exact Ring.neg_one_ne_one_of_char_ne_two hrc h
    · intro h
      have hx' : x ^ (Fintype.card K / 2) = -1 := by
        rcases FiniteField.pow_dichotomy hrc hx with h1 | h1
        · exact absurd h1 h
        · exact h1
      rw [hx']
      norm_num
  have hx0ne : ∀ x : {x : K // ¬ IsSquare x}, x.1 ≠ 0 := by
    intro x hx0
    exact x.2 (hx0 ▸ isSquare_zero')
  refine Nat.card_congr
    { toFun := fun x => ⟨n * x.1, mul_ne_zero hn0 (hx0ne x),
        (key x.1 (hx0ne x)).2 x.2⟩
      invFun := fun y => ⟨n⁻¹ * y.1, fun hsq => ?_⟩
      left_inv := fun x => by
        apply Subtype.ext
        show n⁻¹ * (n * x.1) = x.1
        rw [← mul_assoc, inv_mul_cancel₀ hn0, one_mul]
      right_inv := fun y => by
        apply Subtype.ext
        show n * (n⁻¹ * y.1) = y.1
        rw [← mul_assoc, mul_inv_cancel₀ hn0, one_mul] }
  have h1 : IsSquare (n * (n⁻¹ * y.1)) := by
    rw [← mul_assoc, mul_inv_cancel₀ hn0, one_mul]
    exact y.2.2
  exact (key (n⁻¹ * y.1) (by simp [hn0, y.2.1])).1 h1 hsq

theorem card_nonsquare_neg (hodd : Odd (Nat.card K)) :
    2 * Nat.card {x : K // ¬ IsSquare (-x)} = Nat.card K - 1 := by
  classical
  have hbij : Nat.card {x : K // ¬ IsSquare x} = Nat.card {y : K // y ≠ 0 ∧ IsSquare y} :=
    card_nonsquare_eq_card_ne_zero_isSquare hodd
  have hsq : Nat.card {y : K // IsSquare y} = Nat.card {y : K // y ≠ 0 ∧ IsSquare y} + 1 := by
    have e : {y : K // IsSquare y} ≃ {y : K // y ≠ 0 ∧ IsSquare y} ⊕ Unit :=
    { toFun := fun y => if h : y.1 = 0 then Sum.inr () else Sum.inl ⟨y.1, h, y.2⟩
      invFun := fun s => match s with
        | Sum.inl y => ⟨y.1, y.2.2⟩
        | Sum.inr _ => ⟨0, isSquare_zero'⟩
      left_inv := fun y => by
        by_cases h : y.1 = 0
        · simp only [dif_pos h]
          apply Subtype.ext
          exact h.symm
        · simp only [dif_neg h]
      right_inv := fun s => by
        match s with
        | Sum.inl y => simp only [dif_neg y.2.1]
        | Sum.inr _ => simp }
    rw [Nat.card_congr e, Nat.card_sum]
    simp
  have hpart : Nat.card {y : K // IsSquare y} + Nat.card {x : K // ¬ IsSquare x}
      = Nat.card K := by
    have e := Equiv.sumCompl (fun y : K => IsSquare y)
    have h := Nat.card_congr e
    rw [Nat.card_sum] at h
    show Nat.card {y : K // IsSquare y} + Nat.card {y : K // ¬ IsSquare y} = Nat.card K
    exact h
  have hmain : 2 * Nat.card {x : K // ¬ IsSquare x} = Nat.card K - 1 := by
    have h1 : Nat.card {y : K // IsSquare y} = Nat.card {x : K // ¬ IsSquare x} + 1 := by
      rw [hsq, ← hbij]
    omega
  have e2 : {x : K // ¬ IsSquare (-x)} ≃ {x : K // ¬ IsSquare x} :=
  { toFun := fun x => ⟨-x.1, by simpa using x.2⟩
    invFun := fun x => ⟨-x.1, by simpa using x.2⟩
    left_inv := fun x => by apply Subtype.ext; simp
    right_inv := fun x => by apply Subtype.ext; simp }
  rw [Nat.card_congr e2]
  exact hmain

section Proj

/-- The square test on a *ratio*: `none` (the point `[1 : 0]`, where `-B*C = 0`) fails it, and
`some t` passes it exactly when `-t` is a nonsquare. -/
def IsNonsquareOpt : Option K → Prop
  | none => False
  | some t => ¬ IsSquare (-t)

/-- The test "`-B*C` is a nonsquare" for the point `[B : C]` of `ℙ¹(K)`, read through the ratio
`t = B/C`: since `-B*C = -C² t` and `C²` is a square, it is the condition "`-t` is a nonsquare".
The point `[1 : 0]` has `-B*C = 0`, a square, and fails the test. -/
def IsNonsquareBC (P : P1 K) : Prop := IsNonsquareOpt (coord P)

lemma isNonsquareBC_iff (P : P1 K) :
    IsNonsquareBC P ↔ ∃ t : K, coord P = some t ∧ ¬ IsSquare (-t) := by
  cases h : coord P with
  | none => simp [IsNonsquareBC, IsNonsquareOpt, h]
  | some t => simp [IsNonsquareBC, IsNonsquareOpt, h]

lemma not_isNonsquareBC_ptInf : ¬ IsNonsquareBC (ptInf : P1 K) := by
  simp [IsNonsquareBC, IsNonsquareOpt]

lemma isNonsquareBC_ptFin (t : K) : IsNonsquareBC (ptFin t) ↔ ¬ IsSquare (-t) := by
  simp [IsNonsquareBC, IsNonsquareOpt]

/-- **Chunk (4) of Lemma 10, projective form**: exactly `(q-1)/2` points `[B : C]` of `ℙ¹(K)` have
`-B*C` a nonsquare. -/
theorem card_nonsquare_bc (hodd : Odd (Nat.card K)) :
    2 * Nat.card {P : P1 K // IsNonsquareBC P} = Nat.card K - 1 := by
  classical
  -- transport the count to the ratios
  have h1 : Nat.card {P : P1 K // IsNonsquareBC P} = Nat.card {o : Option K // IsNonsquareOpt o} :=
    Nat.card_congr
    { toFun := fun P => ⟨coord P.1, P.2⟩
      invFun := fun o => ⟨ptOf o.1, by rw [IsNonsquareBC, coord_ptOf]; exact o.2⟩
      left_inv := fun P => Subtype.ext (ptOf_coord P.1)
      right_inv := fun o => Subtype.ext (coord_ptOf o.1) }
  -- the ratios that pass the test are the `some t` with `-t` a nonsquare
  have e1 : {t : K // ¬ IsSquare (-t)} ≃ {o : Option K // IsNonsquareOpt o} :=
  { toFun := fun t => ⟨some t.1, t.2⟩
    invFun := fun o => by
      obtain ⟨o1, h⟩ := o
      cases o1 with
      | none => exact False.elim h
      | some t => exact ⟨t, h⟩
    left_inv := fun t => rfl
    right_inv := fun o => by
      obtain ⟨o1, h⟩ := o
      cases o1 with
      | none => exact False.elim h
      | some t => rfl }
  rw [h1, ← Nat.card_congr e1]
  exact card_nonsquare_neg hodd

end Proj


/-! #### Assembling Lemma 10 from the four chunks -/

/-- Multiplying by a nonzero square does not change whether an element is a square. -/
lemma isSquare_sq_mul {mu : K} (hmu : mu ≠ 0) (y : K) :
    IsSquare (mu * mu * y) ↔ IsSquare y := by
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨r / mu, ?_⟩
    field_simp
    linear_combination hr
  · rintro ⟨r, rfl⟩
    exact ⟨mu * r, by ring⟩

/-- The `(1, 0)`-and `(0, 1)`-coordinates of an involution are the off-diagonal entries of its
trace-zero lift. -/
lemma invCoord_one_eq (t : PGL2 K) :
    invCoord t 1 = ((Quotient.out t : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 1 := by
  rw [invCoord_eq_tz]
  rfl

lemma invCoord_two_eq (t : PGL2 K) :
    invCoord t 2 = ((Quotient.out t : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 := by
  rw [invCoord_eq_tz]
  rfl

/-- For a nonzero pair `(b, c)`, the projective point `[b : c]` has `-bc` a nonsquare exactly when
the ratio `b/c` has `-t` a nonsquare — the two agree because `-bc = -c² (b/c)`. -/
lemma isNonsquareBC_mk (b c : K) (hbc : b ≠ 0 ∨ c ≠ 0) :
    IsNonsquareBC (Projectivization.mk K ![b, c] (by
      intro h
      rcases hbc with h1 | h1
      · exact h1 (by simpa using congrFun h 0)
      · exact h1 (by simpa using congrFun h 1))) ↔ ¬ IsSquare (-(b * c)) := by
  have hne : (![b, c] : Fin 2 → K) ≠ 0 := by
    intro h
    rcases hbc with h1 | h1
    · exact h1 (by simpa using congrFun h 0)
    · exact h1 (by simpa using congrFun h 1)
  have hcoord : coord (Projectivization.mk K ![b, c] hne)
      = if c = 0 then none else some (b / c) := by
    rw [coord_mk]
    simp only [coordAux]
    rw [show (![b, c] : Fin 2 → K) 1 = c from rfl, show (![b, c] : Fin 2 → K) 0 = b from rfl]
  rw [IsNonsquareBC, hcoord]
  by_cases hc : c = 0
  · simp [hc, IsNonsquareOpt]
  · rw [if_neg hc]
    simp only [IsNonsquareOpt]
    -- `-b*c = -c²(b/c)`
    have h2 : c * c * (-(b / c)) = -(b * c) := by
      have h3 : c * (b / c) = b := by field_simp
      calc c * c * (-(b / c)) = -(c * (c * (b / c))) := by ring
        _ = -(c * b) := by rw [h3]
        _ = -(b * c) := by ring
    rw [← h2, isSquare_sq_mul hc]

/-- **Assembly of `split_off_line`, normalized case**: for a line `L` through no `[1 : 0 : 0]`
(`w 0 ≠ 0`), the number of involutions `s` on `L` with `diag(1,-1) · s` fixed-point-free is
`(q-1)/2`. -/
theorem split_off_line_normalized (hodd : Odd (Nat.card K)) (hq : 5 ≤ Nat.card K)
    {w : Fin 3 → K} (hw : w ≠ 0) (hw0 : w 0 ≠ 0) :
    2 * Nat.card {t : PGL2 K // lineForm w t = 0 ∧ IsInvolution t ∧
      ∀ x : P1 K, (diagInv * t) • x ≠ x} = Nat.card K - 1 := by
  classical
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd hodd
  -- Step A: the fixed-point-free condition is the condition `-B*C` a nonsquare
  have hA : Nat.card {t : PGL2 K // lineForm w t = 0 ∧ IsInvolution t ∧
        ∀ x : P1 K, (diagInv * t) • x ≠ x}
      = Nat.card {t : PGL2 K // lineForm w t = 0 ∧ IsInvolution t ∧
          ¬ IsSquare (-(invCoord t 1 * invCoord t 2))} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight ?_)
    intro t
    constructor
    · rintro ⟨hl, hi, hf⟩
      have hiff := exists_fixed_point_diag_mul_iff (P := Quotient.out t) (Quotient.out_eq t)
        (trace_zero_of_isInvolution hi)
      rw [invCoord_one_eq, invCoord_two_eq] at *
      exact ⟨hl, hi, fun hsq => by
        obtain ⟨x, hx⟩ := hiff.2 hsq
        exact hf x hx⟩
    · rintro ⟨hl, hi, hsq⟩
      have hiff := exists_fixed_point_diag_mul_iff (P := Quotient.out t) (Quotient.out_eq t)
        (trace_zero_of_isInvolution hi)
      rw [invCoord_one_eq, invCoord_two_eq] at *
      exact ⟨hl, hi, fun x hx => hsq (hiff.1 ⟨x, hx⟩)⟩
  -- Step B: the projection to `ℙ¹` is a bijection onto the nonsquare points
  have hB : Nat.card {t : PGL2 K // lineForm w t = 0 ∧ IsInvolution t ∧
        ¬ IsSquare (-(invCoord t 1 * invCoord t 2))}
      = Nat.card {P : P1 K // IsNonsquareBC P} := by
    -- the projection
    set f : {t : PGL2 K // lineForm w t = 0 ∧ IsInvolution t ∧
          ¬ IsSquare (-(invCoord t 1 * invCoord t 2))} → P1 K :=
      fun t => Projectivization.mk K ![invCoord t.1 1, invCoord t.1 2] (by
        intro hzero
        rcases lineForm_coord_ne_zero h2 hw0 t.2.2.1 t.2.1 with h1 | h1
        · exact h1 (by simpa using congrFun hzero 0)
        · exact h1 (by simpa using congrFun hzero 1)) with hf
    have hinj : Function.Injective f := by
      rintro ⟨t, hl, hi, hsq⟩ ⟨t', hl', hi', hsq'⟩ hff
      have hlt : lineForm w t = 0 := hl
      have hlt' : lineForm w t' = 0 := hl'
      -- proportional `(B, C)`-coordinates
      obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' K
        ![invCoord t 1, invCoord t 2] ![invCoord t' 1, invCoord t' 2] _ _).1 hff
      have hB1 : invCoord t 1 = a * invCoord t' 1 := by
        have := congrFun ha 0
        simpa using this.symm
      have hB2 : invCoord t 2 = a * invCoord t' 2 := by
        have := congrFun ha 1
        simpa using this.symm
      have ha0 : a ≠ 0 := by
        rintro rfl
        rcases lineForm_coord_ne_zero h2 hw0 hi hlt with h1 | h1
        · exact h1 (by rw [hB1]; simp)
        · exact h1 (by rw [hB2]; simp)
      -- the first coordinate follows from the line equation
      have hlin : ∀ s : PGL2 K, lineForm w s = 0 →
          w 0 * invCoord s 0 + w 1 * invCoord s 1 + w 2 * invCoord s 2 = 0 := by
        intro s hs
        have := hs
        unfold lineForm at this
        rwa [Fin.sum_univ_three] at this
      have e1 := hlin t hlt
      have e2 := hlin t' hlt'
      have hB0 : invCoord t 0 = a * invCoord t' 0 := by
        have : w 0 * invCoord t 0
            = a * (w 0 * invCoord t' 0) := by
          rw [hB1, hB2] at e1
          linear_combination e1 - a * e2
        rcases mul_eq_zero.1 (by linear_combination this : w 0 * (invCoord t 0 - a * invCoord t' 0) = 0) with h | h
        · exact absurd h hw0
        · linear_combination h
      apply Subtype.ext
      exact invCoord_injOn_involutions h2 hi' hi ha0 (by
        funext i
        fin_cases i
        · exact hB0
        · exact hB1
        · exact hB2)
    have himg : Set.range f = {P : P1 K | IsNonsquareBC P} := by
      ext P
      constructor
      · rintro ⟨t, rfl⟩
        exact (isNonsquareBC_mk _ _ (lineForm_coord_ne_zero h2 hw0 t.2.2.1 t.2.1)).2 t.2.2.2
      · intro hP
        obtain ⟨u, hcoord, hnsq⟩ := (isNonsquareBC_iff P).1 hP
        -- the reconstructed first coordinate and the conic condition
        have hconic : (-(w 1 * u + w 2 * 1) / w 0) ^ 2 + u * 1 ≠ 0 := by
          intro hzero
          apply hnsq
          exact ⟨-(w 1 * u + w 2 * 1) / w 0, by linear_combination -hzero⟩
        obtain ⟨t, mu, hmu, hinv, hline, hcoordt⟩ :=
          exists_involution_on_line h2 hw0 (v := w) (B := u) (C := 1) hconic
        have hsq : ¬ IsSquare (-(invCoord t 1 * invCoord t 2)) := by
          rw [hcoordt]
          simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
            Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
          have hval : -(mu * u * (mu * 1)) = mu * mu * (-u) := by ring
          rw [hval]
          intro hsq'
          exact hnsq ((isSquare_sq_mul hmu (-u)).1 hsq')
        refine ⟨⟨t, hline, hinv, hsq⟩, ?_⟩
        -- the projected point is `[u : 1] = P`
        have hvec : (![invCoord t 1, invCoord t 2] : Fin 2 → K) = mu • ![u, 1] := by
          rw [hcoordt]
          funext i
          fin_cases i <;> simp
        apply coord_injective
        rw [hcoord]
        show coord (Projectivization.mk K ![invCoord t 1, invCoord t 2] _) = some u
        rw [coord_mk]
        simp only [coordAux]
        have h0 : (![invCoord t 1, invCoord t 2] : Fin 2 → K) 0 = mu * u := by
          rw [hvec]; simp
        have h1 : (![invCoord t 1, invCoord t 2] : Fin 2 → K) 1 = mu := by
          rw [hvec]; simp
        rw [h0, h1, if_neg hmu]
        congr 1
        field_simp
    calc Nat.card {t : PGL2 K // lineForm w t = 0 ∧ IsInvolution t ∧
          ¬ IsSquare (-(invCoord t 1 * invCoord t 2))}
        = Nat.card (Set.univ : Set {t : PGL2 K // lineForm w t = 0 ∧ IsInvolution t ∧
            ¬ IsSquare (-(invCoord t 1 * invCoord t 2))}) := by simp
      _ = Nat.card (f '' (Set.univ : Set {t : PGL2 K // lineForm w t = 0 ∧ IsInvolution t ∧
            ¬ IsSquare (-(invCoord t 1 * invCoord t 2))})) :=
          (Nat.card_image_of_injective hinj Set.univ).symm
      _ = Nat.card (Set.range f) := by
          rw [show f '' (Set.univ : Set {t : PGL2 K // lineForm w t = 0 ∧ IsInvolution t ∧
            ¬ IsSquare (-(invCoord t 1 * invCoord t 2))}) = Set.range f from by
            ext P; simp]
      _ = Nat.card {P : P1 K // IsNonsquareBC P} := by
          rw [himg]
          rfl
  rw [hA, hB]
  exact card_nonsquare_bc hodd

/-- **Lemma 10 of the paper.** Let `R` be a split involution and let `L` be a projective line of
the involution plane with `R ∉ L`. Then exactly `(q-1)/2` points of `L(𝔽_q)` represent
involutions compatible with `R`, i.e. involutions `s` with `R * s` fixed-point-free.

Assembled from the four chunks proved above: conjugate `R` to `diag(1,-1)`
(`exists_reduce_diag`), parametrize the line by `ℙ¹` (`exists_involution_on_line`,
`invCoord_injOn_involutions`, `lineForm_coord_ne_zero`), identify compatibility with `-4BC` a
nonsquare (`exists_fixed_point_diag_mul_iff`), and count the points `[B : C]` with `-BC` a
nonsquare (`card_nonsquare_bc`), all inside `split_off_line_normalized`. -/
theorem split_off_line (hodd : Odd (Nat.card K)) (hq : 5 ≤ Nat.card K)
      {R : PGL2 K} (hR : IsSplit R) {v : Fin 3 → K} (hv : v ≠ 0) (hRv : lineForm v R ≠ 0) :
      2 * Nat.card {s : PGL2 K // lineForm v s = 0 ∧ IsInvolution s ∧
        ∀ x : P1 K, (R * s) • x ≠ x} = Nat.card K - 1 := by

  classical
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd hodd
  obtain ⟨A, w, hvw, hRw, hcount⟩ := exists_reduce_diag hodd h2 hR v
  rw [hcount]
  have hw : w ≠ 0 := hvw.mp hv
  have hw0 : w 0 ≠ 0 := by
    have h : lineForm w diagInv ≠ 0 := hRw.mp hRv
    intro h0
    exact h ((lineForm_diagInv_iff w).2 h0)
  exact split_off_line_normalized hodd hq hw hw0


end PGL2
