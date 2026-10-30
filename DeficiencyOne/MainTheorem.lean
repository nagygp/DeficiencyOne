/-
Copyright (c) 2026 The Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Mathlib Contributors
-/
import Mathlib
import DeficiencyOne.Defs
import DeficiencyOne.Section2FixedPointBound
import DeficiencyOne.Section3PositiveFixedGap
import DeficiencyOne.Section4Rigidity
import DeficiencyOne.AffineModel

/-!
# The main theorems

The three main results of

* G. Korchmáros, G. P. Nagy, T. Szőnyi,
  *Fixed points and rigidity in the deficiency-one case over prime-power fields*,

namely Theorems 1, 2 and 3 of the paper, stated together in this file. Everything else is in
the files of the corresponding section of the paper:

| paper                     | file                              |
| ------------------------- | --------------------------------- |
| §1 Introduction           | `DeficiencyOne/Defs.lean`         |
| §2 The fixed-point bound  | `DeficiencyOne/Section2FixedPointBound.lean` |
| §3 Covering curves …      | `DeficiencyOne/Section3PositiveFixedGap.lean` |
| §4 Rigidity …             | `DeficiencyOne/Section4Rigidity.lean`        |

## The results

* `numFixed_le` (**Theorem 1**) : `f ≤ q - q / p`.
* `card_le_mul_sqrt_add` (**Theorem 2**) : for noncollinear `S` with `f > 0`,
  `q ≤ (f - 1)(4√q + 23)` and `f ≥ 1 + q/(4√q + 23)`.
* `hammingDist_ge` (**Theorem 3**) : for `f ≥ 4`, every split involution `τ` sharing a fixed
  point with `σ` has `d_H(σ, τ) ≥ (q+3)/2`.

## Status

All three theorems are **proved**; this file contains no `sorry`. Two inputs are still unproved
elsewhere and enter as `sorryAx`: Lemma 12 of §3 (used by Theorem 2) and Theorem 17 of §4 (used by
Theorem 3). The proofs are assembled from the chapter files as follows.

* Theorem 1 is `numFixed_le`. Its proof (§2) conjugates `S` so that `σ(∞) = ∞`, writes
  `S = {s_u : X ↦ u + d(u)/(X-u)}`, shows `σ(x) = x - d'(x)` by Lagrange interpolation, and
  concludes `f = 1 + |{x : d'(x) = 0}| ≤ 1 + (q - q/p - 1)` by Lemma 4
  (`Polynomial.card_zeros_derivative_le`), with `d' ≠ 0` from Lemma 5 (`missingPerm_ne_one`).
  The interpolating polynomial and the affine model are not formalized yet.
* Theorem 2 combines the nonsplit cover of Proposition 9 (`exists_nonsplit_cover`: the `f - 1`
  lines `L_c`, `c ∈ E`) with Lemma 12 (`card_lineTrace_le`): the `t = (q + f - 1)/2` nonsplit
  elements of `S` lie on `f - 1` lines carrying at most `2√q + 12` points of `S` each, so
  `(q + f - 1)/2 ≤ (f - 1)(2√q + 12)`, i.e. `q ≤ (f - 1)(4√q + 23)` and the second bound. The
  only unproved input is Lemma 12.
* Theorem 3 is the contrapositive of Theorem 17 (`common_fixed_point_rigidity`) together with
  the counting identity `d_H(σ, τ) + |{x | σ x = τ x}| = q + 1`
  (`card_agreement_add_hammingDist`): agreement in `(q+1)/2` points would force `f = 2`. Its only
  unproved input is Theorem 17, so `#print axioms PGL2.hammingDist_ge` reports `sorryAx` through
  that theorem alone, not through this file.
-/

@[expose] public section

open Classical

namespace PGL2

variable {K : Type*} [Field K] [Fintype K]


/-- Conjugation of a permutation of the projective line by `g ∈ PGL₂(K)`, as a permutation. -/
def conjPermEquiv (g : PGL2 K) (σ : Equiv.Perm (P1 K)) : Equiv.Perm (P1 K) :=
  MulAction.toPerm g * σ * (MulAction.toPerm g)⁻¹

lemma conjPermEquiv_coe (g : PGL2 K) (σ : Equiv.Perm (P1 K)) :
    ⇑(conjPermEquiv g σ) = conjPerm g σ := by
  funext y
  simp [conjPermEquiv, conjPerm, MulAction.toPerm_apply]

/-- **Theorem 1 in the normalization `σ(∞) = ∞`.** This is the content of §2: by
`exists_affineData` the set `S` is `{s_u : u ∈ K}` with `s_u(X) = u + d(u)/(X - u)` and
`σ(x) = x - d'(x)`. Hence the fixed points of `σ` are `∞` and the zeros of `d'`, so
`f = 1 + |{x : d'(x) = 0}|`, and `d' ≠ 0` by Lemma 5 (`missingPerm_ne_one`), since `d' = 0`
would make `σ` the identity. Lemma 4 (`card_zeros_derivative_le`) then gives
`f ≤ 1 + (q - q/p - 1) = q - q/p`. -/
theorem numFixed_le_normalized (hodd : Odd (Nat.card K)) (hq : 5 ≤ Nat.card K)
    {S : Set (PGL2 K)} (hS : IsAdmissible S) (hcard : Nat.card S = Nat.card K)
    {σ : Equiv.Perm (P1 K)} (hσ : IsMissingPerm S σ) (hinf : σ ptInf = ptInf) :
    numFixed σ ≤ Nat.card K - Nat.card K / ringChar K := by
  classical
  have hq3 : 3 ≤ Nat.card K := by omega
  obtain ⟨A⟩ := exists_affineData hodd hq hS hcard hσ hinf
  -- every non-`∞` point is `ptFin u`
  have hcoord : ∀ y : P1 K, y ≠ ptInf → ∃ u : K, y = ptFin u := by
    intro y hy
    have hne : coord y ≠ none := by
      intro h
      apply hy
      have h2 := ptOf_coord y
      rw [h] at h2
      simpa [ptOf] using h2.symm
    cases hc : coord y with
    | none => exact absurd hc hne
    | some u => exact ⟨u, by rw [← ptOf_coord y, hc]; rfl⟩
  -- `d' ≠ 0`, from Lemma 5
  have hd' : Polynomial.derivative A.D ≠ 0 := by
    intro hzero
    have hσ1 : σ = 1 := by
      apply Equiv.ext
      intro y
      by_cases hy : y = ptInf
      · rw [hy]; exact hinf
      · obtain ⟨u, hu⟩ := hcoord y hy
        have h0 : (Polynomial.derivative A.D).eval u = 0 := by simp [hzero]
        have hfin : σ (ptFin u) = ptFin u := by
          rw [A.σ_fin u, A.σ_deriv u, h0, sub_zero]
        rw [hu]; exact hfin
    exact missingPerm_ne_one hodd hq hS hcard hσ hσ1
  -- fixed points of `σ` on the affine line are the zeros of `d'`
  have hfin : ∀ u : K, (σ (ptFin u) = ptFin u) ↔ (Polynomial.derivative A.D).eval u = 0 := by
    intro u
    constructor
    · intro h
      rw [A.σ_fin u] at h
      have hsf : A.sf u = u := ptFin_injective h
      rw [A.σ_deriv u] at hsf
      have h2 : (u - (Polynomial.derivative A.D).eval u) - u = 0 := by rw [hsf, sub_self]
      rw [sub_sub, add_comm ((Polynomial.derivative A.D).eval u) u, sub_add_eq_sub_sub, sub_self,
        zero_sub] at h2
      exact neg_eq_zero.mp h2
    · intro h
      rw [A.σ_fin u, A.σ_deriv u, h, sub_zero]
  -- the count: `f = 1 + |{u : d' u = 0}|`
  have hcard : numFixed σ = 1 + Nat.card {u : K // (Polynomial.derivative A.D).eval u = 0} := by
    unfold numFixed
    have hE1 : {y : P1 K // σ y = y} ≃ {c : Option K // σ (ptOf c) = ptOf c} :=
      equivWithTop.subtypeEquiv (fun y => by
        show (σ y = y) ↔ (σ (ptOf (coord y)) = ptOf (coord y))
        rw [ptOf_coord y])
    have hE2 : {c : Option K // σ (ptOf c) = ptOf c} ≃ Option {u : K // σ (ptFin u) = ptFin u} := by
      refine {
        toFun := fun c => match c with
          | ⟨none, h⟩ => none
          | ⟨some u, h⟩ => some ⟨u, (h : σ (ptFin u) = ptFin u)⟩
        invFun := fun c => match c with
          | none => ⟨none, hinf⟩
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
          | some u => rfl
      }
    have hE3 : {u : K // σ (ptFin u) = ptFin u} ≃ {u : K // (Polynomial.derivative A.D).eval u = 0} :=
      Equiv.subtypeEquiv (Equiv.refl K) hfin
    rw [Nat.card_congr (hE1.trans (hE2.trans (Equiv.optionCongr hE3)))]
    rw [Nat.card_eq_fintype_card, Fintype.card_option, ← Nat.card_eq_fintype_card]
    omega
  -- Lemma 4
  have hKr : ∃ r : ℕ, 1 ≤ r ∧ Nat.card K = ringChar K ^ r := by
    haveI : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K (ringChar K)⟩
    haveI : NeZero (ringChar K) := ⟨(CharP.char_is_prime K (ringChar K)).ne_zero⟩
    letI := ZMod.algebra K (ringChar K)
    have hfin : Module.Finite (ZMod (ringChar K)) K := Module.Finite.of_finite
    have hcard := Module.natCard_eq_pow_finrank (K := ZMod (ringChar K)) (V := K)
    rw [show Nat.card (ZMod (ringChar K)) = ringChar K by
      rw [Nat.card_eq_fintype_card, ZMod.card]] at hcard
    refine ⟨Module.finrank (ZMod (ringChar K)) K, ?_, hcard⟩
    by_contra h
    push_neg at h
    have h0 : Module.finrank (ZMod (ringChar K)) K = 0 := by omega
    rw [h0, pow_zero] at hcard
    have h2 : 1 < Nat.card K := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.one_lt_card
    omega
  obtain ⟨r, hr, hKr⟩ := hKr
  have hbound := Polynomial.card_zeros_derivative_le_pow (K := K) (ringChar K) r hr hKr A.D_deg hd'
  obtain ⟨pp, hpp⟩ : ∃ pp : ℕ, pp = Nat.card K / ringChar K := ⟨_, rfl⟩
  have hp2 : 2 ≤ ringChar K := (CharP.char_is_prime K (ringChar K)).two_le
  have hlt : pp < Nat.card K := by
    rw [hpp]
    exact Nat.div_lt_self (by omega) (by omega)
  rw [← hpp] at hbound ⊢
  rw [hcard]
  omega

/-- **Theorem 1** (fixed-point bound). Let `q = p ^ r ≥ 5` be odd and let `S ⊆ PGL₂(q)` be an
admissible set of size `q`. Then the missing permutation satisfies

`f ≤ q - q / p`,

where `f = |Fix_Ω(σ)|` and `p = ringChar K`. Since `q = p ^ r`, the quotient `q / p` is the
integer `p ^ (r - 1)`. No hypothesis on the degree of a parametrizing polynomial, beyond
taking its reduced representative, is required.

The proof reduces to the normalization `σ(∞) = ∞` by conjugating `S` and `σ` by an element `g`
sending a fixed point of `σ` to `∞`: admissibility, the missing-permutation property and `f` are
all invariant under conjugation (`isAdmissible_conjSet`, `isMissingPerm_conjSet`,
`numFixed_conjPerm`), and every point can be sent to `∞` (`exists_smul_eq_ptInf`). The normalized
case is `numFixed_le_normalized`. -/
theorem numFixed_le (hodd : Odd (Nat.card K)) (hq : 5 ≤ Nat.card K)
    {S : Set (PGL2 K)} (hS : IsAdmissible S) (hcard : Nat.card S = Nat.card K)
    {σ : Equiv.Perm (P1 K)} (hσ : IsMissingPerm S σ) :
    numFixed σ ≤ Nat.card K - Nat.card K / ringChar K := by
  classical
  by_cases hf : numFixed σ = 0
  · omega
  · have hfpos : 0 < numFixed σ := Nat.pos_of_ne_zero hf
    obtain ⟨x, hx⟩ : ∃ x : P1 K, σ x = x := by
      by_contra h
      apply hf
      unfold numFixed
      rw [Nat.card_eq_zero]
      exact Or.inl ⟨fun y => h ⟨y.1, y.2⟩⟩
    obtain ⟨g, hg⟩ := exists_smul_eq_ptInf x
    have hS' : IsAdmissible (conjSet g S) := isAdmissible_conjSet g hS
    have hcard' : Nat.card (conjSet g S) = Nat.card K := by
      rw [card_conjSet, hcard]
    have hσ' : IsMissingPerm (conjSet g S) ⇑(conjPermEquiv g σ) := by
      rw [conjPermEquiv_coe]
      exact isMissingPerm_conjSet g hσ
    have hnum : numFixed ⇑(conjPermEquiv g σ) = numFixed σ := by
      rw [conjPermEquiv_coe]
      exact numFixed_conjPerm g σ
    have hinf : conjPermEquiv g σ ptInf = ptInf := by
      rw [conjPermEquiv_coe]
      have hgx : g⁻¹ • ptInf = x := by rw [← hg]; simp
      simp only [conjPerm, hgx, hx, hg]
    rw [← hnum]
    exact numFixed_le_normalized hodd hq hS' hcard' hσ' hinf

/-- **Theorem 2** (positive fixed-point gap). Let `q = p ^ r ≥ 5` be odd and let `S` be an
admissible set of size `q`. If `S` is noncollinear and `f > 0`, then

`q ≤ (f - 1) (4 √q + 23)`  and  `f ≥ 1 + q / (4 √q + 23)`.

In particular any fixed bound on positive `f` implies collinearity for sufficiently large `q`,
and a sequence with `q → ∞` and `0 < f = o(√q)` must be collinear for all sufficiently large
`q`. -/
theorem card_le_mul_sqrt_add (hodd : Odd (Nat.card K)) (hq : 5 ≤ Nat.card K)
    {S : Set (PGL2 K)} (hS : IsAdmissible S) (hcard : Nat.card S = Nat.card K)
    {σ : Equiv.Perm (P1 K)} (hσ : IsMissingPerm S σ)
    (hnc : ¬ IsCollinear S) (hf : 0 < numFixed σ) :
    (Nat.card K : ℝ) ≤ ((numFixed σ : ℝ) - 1) * (4 * Real.sqrt (Nat.card K) + 23) ∧
      1 + (Nat.card K : ℝ) / (4 * Real.sqrt (Nat.card K) + 23) ≤ (numFixed σ : ℝ) := by
  classical
  -- `σ` is the missing permutation, so it is an involution
  have hσ2 : σ * σ = 1 := by
    obtain ⟨σ₀, hσ₀, hσ₀2⟩ := exists_isMissingPerm hS hcard
    have heq : σ = σ₀ := Equiv.ext (fun x => congrFun (eq_of_isMissingPerm hσ hσ₀) x)
    rw [heq, hσ₀2]
  -- the nonsplit elements of `S` are covered by `f - 1` lines, each carrying at most `2√q + 12`
  -- points of `S` (Lemma 12)
  obtain ⟨V, hVcard, hVcov⟩ := exists_nonsplit_cover hodd hq hS hcard hσ hσ2 hf
  set W : Finset (Fin 3 → K) := V.erase 0 with hW
  have hWcard : W.card ≤ V.card := Finset.card_erase_le
  have hW0 : ∀ v ∈ W, v ≠ 0 := fun v hv => (Finset.mem_erase.1 hv).1
  have hWcov : ∀ s ∈ S, ¬ IsSplit s → ∃ v ∈ W, v ≠ 0 ∧ lineForm v s = 0 := by
    intro s hs hns
    obtain ⟨v, hvV, hv0, hvline⟩ := hVcov s hs hns
    exact ⟨v, Finset.mem_erase.2 ⟨hv0, hvV⟩, hv0, hvline⟩
  have hsub : nonsplitPart S ⊆ ⋃ v ∈ W, lineTrace v S := by
    intro s hs
    obtain ⟨hsS, hns⟩ := hs
    have hnotsplit : ¬ IsSplit s := by
      rintro ⟨-, ⟨x, hx⟩⟩
      exact hns.2 x hx
    obtain ⟨v, hvW, -, hvline⟩ := hWcov s hsS hnotsplit
    exact Set.mem_iUnion.2 ⟨v, Set.mem_iUnion.2 ⟨hvW, hsS, hvline⟩⟩
  have hcount : Nat.card (nonsplitPart S) ≤ ∑ v ∈ W, Nat.card (lineTrace v S) := by
    calc Nat.card (nonsplitPart S) = (nonsplitPart S).ncard := (Nat.card_coe_set_eq _).symm
      _ ≤ (⋃ v ∈ W, lineTrace v S).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ ∑ v ∈ W, (lineTrace v S).ncard := Finset.set_ncard_biUnion_le W _
      _ = ∑ v ∈ W, Nat.card (lineTrace v S) :=
          Finset.sum_congr rfl (fun v _ => (Nat.card_coe_set_eq _).symm)
  -- the `2e + f = q + 1` identity in the form `2 t = q + f - 1`
  have ht : 2 * Nat.card (nonsplitPart S) = Nat.card K + numFixed σ - 1 := by
    have h1 : 2 * Nat.card (splitPart S) + numFixed σ = Nat.card K + 1 :=
      two_mul_card_splitPart_add_numFixed hodd hq hS hcard hσ hσ2
    have h2 : Nat.card (nonsplitPart S) = Nat.card K - Nat.card (splitPart S) :=
      card_nonsplitPart hodd hq hS hcard hσ hσ2
    omega
  have hterm : ∀ v ∈ W, (Nat.card (lineTrace v S) : ℝ)
      ≤ 2 * Real.sqrt (Nat.card K) + 12 :=
    fun v hv => card_lineTrace_le hodd hq hS hcard hσ hnc (hW0 v hv)
  have hs : (0 : ℝ) ≤ Real.sqrt (Nat.card K) := Real.sqrt_nonneg _
  have hbound : (Nat.card (nonsplitPart S) : ℝ)
      ≤ ((numFixed σ : ℝ) - 1) * (2 * Real.sqrt (Nat.card K) + 12) := by
    have h1 : (Nat.card (nonsplitPart S) : ℝ)
        ≤ (W.card : ℝ) * (2 * Real.sqrt (Nat.card K) + 12) := by
      calc (Nat.card (nonsplitPart S) : ℝ)
          ≤ ((∑ v ∈ W, Nat.card (lineTrace v S) : ℕ) : ℝ) := by exact_mod_cast hcount
        _ = ∑ v ∈ W, (Nat.card (lineTrace v S) : ℝ) := by rw [Nat.cast_sum]
        _ ≤ ∑ v ∈ W, (2 * Real.sqrt (Nat.card K) + 12) := Finset.sum_le_sum hterm
        _ = (W.card : ℝ) * (2 * Real.sqrt (Nat.card K) + 12) := by
            rw [Finset.sum_const, nsmul_eq_mul]
    have hWle : (W.card : ℝ) ≤ (numFixed σ : ℝ) - 1 := by
      have h1 : W.card ≤ numFixed σ - 1 := le_trans hWcard hVcard
      have h2 : (W.card : ℝ) ≤ ((numFixed σ - 1 : ℕ) : ℝ) := by exact_mod_cast h1
      have h3 : ((numFixed σ - 1 : ℕ) : ℝ) = (numFixed σ : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ numFixed σ)]
        norm_num
      linarith
    calc (Nat.card (nonsplitPart S) : ℝ)
        ≤ (W.card : ℝ) * (2 * Real.sqrt (Nat.card K) + 12) := h1
      _ ≤ ((numFixed σ : ℝ) - 1) * (2 * Real.sqrt (Nat.card K) + 12) :=
          mul_le_mul_of_nonneg_right hWle (by positivity)
  -- `(q + f - 1)/2 ≤ (f - 1)(2√q + 12)` in `ℝ`
  have hcast : ((Nat.card K + numFixed σ - 1 : ℕ) : ℝ)
      = (Nat.card K : ℝ) + (numFixed σ : ℝ) - 1 := by
    push_cast [show 1 ≤ Nat.card K + numFixed σ by omega]
    ring
  have hmain : ((Nat.card K : ℝ) + (numFixed σ : ℝ) - 1) / 2
      ≤ ((numFixed σ : ℝ) - 1) * (2 * Real.sqrt (Nat.card K) + 12) := by
    have h2t : 2 * (Nat.card (nonsplitPart S) : ℝ)
        = (Nat.card K : ℝ) + (numFixed σ : ℝ) - 1 := by
      rw [← hcast]
      exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) ht
    linarith
  have hq1 : (Nat.card K : ℝ)
      ≤ ((numFixed σ : ℝ) - 1) * (4 * Real.sqrt (Nat.card K) + 23) := by
    nlinarith [hmain]
  refine ⟨hq1, ?_⟩
  have hpos : 0 < 4 * Real.sqrt (Nat.card K) + 23 := by positivity
  have h2 : (Nat.card K : ℝ) / (4 * Real.sqrt (Nat.card K) + 23) ≤ (numFixed σ : ℝ) - 1 := by
    rw [div_le_iff₀ hpos]
    nlinarith [hq1]
  linarith

/-- **Theorem 3** (rigidity next to a split involution). Let `q ≥ 7` be odd and let `S` be an
admissible set of size `q`. If `f ≥ 4`, then every split involution `τ ∈ PGL₂(q)` sharing a
fixed point with `σ` satisfies

`d_H(σ, τ) ≥ (q + 3) / 2`  and  `|{x ∈ Ω : σ x = τ x}| ≤ (q - 1) / 2`.

The hypothesis `q ≥ 7` is essential: there is a noncollinear example at `q = 5`. -/
theorem hammingDist_ge (hodd : Odd (Nat.card K)) (hq : 7 ≤ Nat.card K)
    {S : Set (PGL2 K)} (hS : IsAdmissible S) (hcard : Nat.card S = Nat.card K)
    {σ : Equiv.Perm (P1 K)} (hσ : IsMissingPerm S σ) (hf : 4 ≤ numFixed σ)
    {τ : PGL2 K} (hτ : IsSplit τ) (hcommon : ∃ x : P1 K, σ x = x ∧ τ • x = x) :
    (Nat.card K + 3) / 2 ≤ hammingDist σ (fun x => τ • x) ∧
      Nat.card (agreementSet σ (fun x => τ • x)) ≤ (Nat.card K - 1) / 2 := by
  classical
  -- the contrapositive of Theorem 17: agreement in `(q+1)/2` points forces `σ = τ` and `f = 2`
  have hP1 : Nat.card (P1 K) = Nat.card K + 1 := card_P1
  have hsplit : Nat.card (agreementSet σ (fun x => τ • x))
      + hammingDist σ (fun x => τ • x) = Nat.card K + 1 := by
    have h := card_agreement_add_hammingDist σ (fun x => τ • x)
    rw [hP1] at h
    exact h
  have hagree : Nat.card (agreementSet σ (fun x => τ • x)) ≤ (Nat.card K - 1) / 2 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨-, -, hf2⟩ :=
      common_fixed_point_rigidity hodd hq hS hcard hσ hτ hcommon (by omega)
    omega
  refine ⟨?_, hagree⟩
  omega

end PGL2
