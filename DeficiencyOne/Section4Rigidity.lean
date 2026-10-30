/-
Copyright (c) 2026 The Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Mathlib Contributors
-/
import Mathlib
import DeficiencyOne.Section3PositiveFixedGap

/-!
# §4. Rigidity near a nonidentity projectivity

Statements from Section 4 of the paper. This section controls how closely the missing
permutation `σ` can resemble a nonidentity projectivity `τ ∈ PGL₂(q)`, measured by the Hamming
distance `d_H(σ, τ) = |{x ∈ Ω : σ(x) ≠ τ(x)}|`.

* **Lemma 13** (`rigidity_two_cycle`, not formalized here) : if `σ(0) = ∞` and `σ(∞) = 0`, then
  `S = {s_∞} ∪ {s_u : u ∈ 𝔽_q^×}` with `s_∞(X) = b - X` and `s_u(X) = u + d(u)/(X-u)`, and the
  interpolating polynomial `D` with `D(0) = 0` satisfies `D'(0) = -b`,
  `σ(x) = 2x - b - D'(x)` and `D(σ(x))/σ(x) = D(x)/x` for `x ∈ 𝔽_q^×`.
* **Lemma 14** (`interpolation_rigidity`) : the interpolation lemma with a small exceptional
  set — if `c ∈ 𝔽_q^×`, if `E ⊆ 𝔽_q^×` is invariant under `ι(x) = c/x` with `|E| = k`, and if
  `F ∈ 𝔽_q[X]` satisfies `deg F ≤ q - 2`, `F(0) = 0` and `F(x) + xF'(x) = F(ι(x)) - F(x) = 0`
  for all `x ∈ 𝔽_q^× \ E`, then `q > 3k` forces `F = 0`.
* **Theorem 15** (`hamming_rigidity`) : if `τ ≠ 1` and `q > 3 d_H(σ, τ)`, then `σ = τ`, `S` is
  collinear and `f ∈ {0, 2}`.
* **Corollary 16** (`hammingDist_ge_div_three`) : if `S` is noncollinear or `f ≥ 4`, then
  `d_H(σ, τ) ≥ ⌈q/3⌉` for every `τ ≠ 1`.
* **Theorem 17** (`common_fixed_point_rigidity`) : if `q ≥ 7`, `τ` is a split involution sharing
  a fixed point with `σ`, and `σ` and `τ` agree in at least `(q+1)/2` points, then `σ = τ`, `S`
  is collinear and `f = 2`.

Theorem 3 of the paper (`MainTheorem.lean`) is the contrapositive of Theorem 17 combined with
Corollary 16.

Lemma 13 is not yet formalized: it is stated in the two-cycle normalization of the affine model
`σ(0) = ∞`, `σ(∞) = 0`, which this development does not construct yet.
-/

@[expose] public section

open Polynomial

namespace PGL2

variable {K : Type*} [Field K] [Fintype K]

/-! ### The interpolation lemma with a small exceptional set -/

/-- **Lemma 14 of the paper.** Let `q` be odd, `c ∈ 𝔽_q^×`, and `ι(x) = c/x` on `𝔽_q^×`. Let
`E ⊆ 𝔽_q^×` be `ι`-invariant, with `|E| = k`. If `F ∈ 𝔽_q[X]` satisfies `deg F ≤ q - 2`,
`F(0) = 0`, and `F(x) + x F'(x) = 0` and `F(ι(x)) = F(x)` for every `x ∈ 𝔽_q^× \ E`, then
`q > 3k` implies `F = 0`. -/
theorem interpolation_rigidity (hodd : Odd (Nat.card K)) {c : K} (hc : c ≠ 0) {E : Set K}
    (hE0 : ∀ x ∈ E, x ≠ 0) (hinv : ∀ x ∈ E, c / x ∈ E) {k : ℕ} (hk : Nat.card E = k)
    {F : K[X]} (hdeg : F.natDegree ≤ Nat.card K - 2) (hF0 : F.eval 0 = 0)
    (hderiv : ∀ x : K, x ≠ 0 → x ∉ E → F.eval x + x * (derivative F).eval x = 0)
    (hweight : ∀ x : K, x ≠ 0 → x ∉ E → F.eval (c / x) = F.eval x)
    (hq : 3 * k < Nat.card K) : F = 0 := by
  sorry

/-! ### The counting identity `d_H(α, β) + |{x | α x = β x}| = |Ω|` -/

/-- The points of `Ω` split into the agreement set of `α, β` and its complement. -/
lemma card_agreement_add_hammingDist (α β : P1 K → P1 K) :
    Nat.card (agreementSet α β) + Nat.card {x : P1 K // α x ≠ β x} = Nat.card (P1 K) := by
  classical
  have e := Equiv.sumCompl (fun x : P1 K => α x = β x)
  have h := Nat.card_congr e
  rw [Nat.card_sum] at h
  show Nat.card {x : P1 K // α x = β x} + Nat.card {x : P1 K // ¬ (α x = β x)}
    = Nat.card (P1 K)
  exact h

/-! ### Hamming rigidity for arbitrary `f` -/

/-- **Theorem 15 of the paper.** Let `q ≥ 5` be odd and let `S` be admissible of size `q` with
missing permutation `σ`. Let `τ ∈ PGL₂(q) \ {1}` and put `k = d_H(σ, τ)`. If `q > 3k`, then
`σ = τ`, `S` is collinear and `f ∈ {0, 2}`. -/
theorem hamming_rigidity (hodd : Odd (Nat.card K)) (hq : 5 ≤ Nat.card K)
    {S : Set (PGL2 K)} (hS : IsAdmissible S) (hcard : Nat.card S = Nat.card K)
    {σ : Equiv.Perm (P1 K)} (hσ : IsMissingPerm S σ) {τ : PGL2 K} (hτ : τ ≠ 1)
    (hk : 3 * hammingDist σ (fun x => τ • x) < Nat.card K) :
    (∀ x, σ x = τ • x) ∧ IsCollinear S ∧ (numFixed σ = 0 ∨ numFixed σ = 2) := by
  sorry

/-- **Corollary 16 of the paper.** If `S` is noncollinear, or if `f ≥ 4`, then
`d_H(σ, τ) ≥ ⌈q/3⌉` for every `τ ∈ PGL₂(q) \ {1}`; the ceiling is the natural number
`(q + 2) / 3`. -/
theorem hammingDist_ge_div_three (hodd : Odd (Nat.card K)) (hq : 5 ≤ Nat.card K)
    {S : Set (PGL2 K)} (hS : IsAdmissible S) (hcard : Nat.card S = Nat.card K)
    {σ : Equiv.Perm (P1 K)} (hσ : IsMissingPerm S σ)
    (h : ¬ IsCollinear S ∨ 4 ≤ numFixed σ) {τ : PGL2 K} (hτ : τ ≠ 1) :
    (Nat.card K + 2) / 3 ≤ hammingDist σ (fun x => τ • x) := by
  classical
  -- contrapositive of Theorem 15: `3 d_H(σ, τ) < q` forces `S` collinear and `f ≤ 2`
  have hq3 : Nat.card K ≤ 3 * hammingDist σ (fun x => τ • x) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨-, hcol, hf⟩ := hamming_rigidity hodd hq hS hcard hσ hτ hcon
    rcases h with hnc | hf4
    · exact hnc hcol
    · rcases hf with h0 | h2 <;> omega
  omega

/-! ### A stronger bound from a common fixed point -/

/-- **Theorem 17 of the paper.** Let `q ≥ 7` be odd. Suppose that a split involution
`τ ∈ PGL₂(q)` and the missing permutation `σ` have a common fixed point. If `σ` and `τ` agree in
at least `(q+1)/2` points of `Ω`, then `σ = τ`, the set `S` is collinear and `f = 2`. -/
theorem common_fixed_point_rigidity (hodd : Odd (Nat.card K)) (hq : 7 ≤ Nat.card K)
    {S : Set (PGL2 K)} (hS : IsAdmissible S) (hcard : Nat.card S = Nat.card K)
    {σ : Equiv.Perm (P1 K)} (hσ : IsMissingPerm S σ) {τ : PGL2 K} (hτ : IsSplit τ)
    (hcommon : ∃ x : P1 K, σ x = x ∧ τ • x = x)
    (hagree : (Nat.card K + 1) / 2 ≤ Nat.card (agreementSet σ (fun x => τ • x))) :
    (∀ x, σ x = τ • x) ∧ IsCollinear S ∧ numFixed σ = 2 := by
  sorry

end PGL2
