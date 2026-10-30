/-
Copyright (c) 2026 The Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Mathlib Contributors
-/
import Mathlib
import DeficiencyOne.Defs
import RequestProject.Theorem1

-- `mul_pow_card` below is a statement about cardinalities only, so the field instances of the
-- enclosing section are unused in it; and instances are introduced with `haveI`, which the style
-- linter would prefer as `have`.
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
attribute [local instance] Classical.decEq

/-!
# §2. The fixed-point bound

Formalization of Section 2 of the paper. This section contains

* **Lemma 4** (`Polynomial.card_zeros_derivative_le`): if `q = p ^ r` is a prime power and
  `d ∈ 𝔽_q[X]` has degree at most `q - 1` with `d' ≠ 0`, then `d'` has at most `q - q / p - 1`
  zeros in `𝔽_q`. **Proved here**, with no `sorry`.
* **Lemma 5** (`missingPerm_ne_one`): under the hypotheses of Theorem 1, the missing permutation
  is not the identity. Stated only; its proof uses Eberhard's sharply transitive set theorem,
  which is available in the repository as `eberhard_theorem1` (Project: `RequestProject/`).

The proof of Theorem 1 itself (the interpolating polynomial `d`, the derivative identity
`σ(x) = x - d'(x)`, and the final count) is set up in `MainTheorem.lean`.

## Lemma 4

For `r = 1` the bound is `q - q / p - 1 = q - 2`, so in that case the statement is exactly the
root bound; the content is in the prime-power case `r ≥ 2`. The proof follows the paper but
works over the support of `g = d'` rather than over digit pairs: with `q = p ^ (k + 1)` and
`h = p ^ k = q / p`, the substitution `j ↦ j / p + (j % p) * h` sends `j` to an exponent `Φ j`
with `x ^ (j * h) = x ^ (Φ j)` for every `x` in the field, so that

`g(x) ^ h = ∑_{j ∈ supp g} (g.coeff j) ^ h * x ^ (Φ j) = R(x)`

for an explicit polynomial `R`. On the support of `g` the map `Φ` is injective (so `R ≠ 0`) and
`Φ j + h + 1 ≤ q` (so `deg R ≤ q - h - 1`), and `g` and `R` have the same zero set; the root
bound for `R` gives the claim.
-/

@[expose] public section

open Polynomial

namespace FiniteField

variable {K : Type*} [Field K] [Fintype K]

/-- In a finite field, `x ^ |K| = x`. -/
lemma pow_natCard (x : K) : x ^ Nat.card K = x := by
  rw [Nat.card_eq_fintype_card]
  exact FiniteField.pow_card x

end FiniteField

namespace Polynomial

variable {K : Type*} [Field K] [Fintype K]

/-- The exponent map of the proof of Lemma 4. For `j = p * (j / p) + j % p` it is the exponent
congruent to `j * p ^ k` modulo `|K| - 1` that lies in `[0, |K| - 1]`, when `|K| = p ^ (k + 1)`. -/
def digitExp (p k j : ℕ) : ℕ := j / p + (j % p) * p ^ k

section Lemma4

variable (p k : ℕ) [CharP K p]

/-- With `|K| = p ^ (k + 1)` one has `p * p ^ k = |K|`. -/
lemma mul_pow_card (hk : Nat.card K = p ^ (k + 1)) : p * p ^ k = Nat.card K := by
  rw [hk, pow_succ, Nat.mul_comm]

/-- The Frobenius power of a finite sum: `(∑ f i) ^ (p ^ k) = ∑ (f i) ^ (p ^ k)`. -/
lemma sum_pow_pow {ι : Type*} (s : Finset ι) (f : ι → K) :
    (∑ i ∈ s, f i) ^ p ^ k = ∑ i ∈ s, (f i) ^ p ^ k := by
  classical
  haveI : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
  induction s using Finset.induction with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    exact zero_pow (pow_ne_zero k (CharP.char_is_prime K p).pos.ne')
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      add_pow_char_pow (f a) (∑ i ∈ s, f i) p k, ih]

/-- The key exponent identity: for `|K| = p ^ (k + 1)` and every `x : K`,
`x ^ (j * p ^ k) = x ^ (digitExp p k j)`. -/
lemma pow_mul_digitExp (hk : Nat.card K = p ^ (k + 1)) (x : K) (j : ℕ) :
    x ^ (j * p ^ k) = x ^ digitExp p k j := by
  have hq : p * p ^ k = Nat.card K := mul_pow_card p k hk
  calc x ^ (j * p ^ k)
      = x ^ ((p * (j / p) + j % p) * p ^ k) := by rw [Nat.div_add_mod j p]
    _ = x ^ ((p * p ^ k) * (j / p) + (j % p) * p ^ k) := by rw [add_mul]; ring_nf
    _ = x ^ ((p * p ^ k) * (j / p)) * x ^ ((j % p) * p ^ k) := pow_add ..
    _ = (x ^ (p * p ^ k)) ^ (j / p) * x ^ ((j % p) * p ^ k) := by rw [pow_mul]
    _ = (x ^ Nat.card K) ^ (j / p) * x ^ ((j % p) * p ^ k) := by rw [hq]
    _ = x ^ (j / p) * x ^ ((j % p) * p ^ k) := by rw [FiniteField.pow_natCard]
    _ = x ^ (j / p + (j % p) * p ^ k) := (pow_add _ _ _).symm
    _ = x ^ digitExp p k j := by rw [digitExp]

/-- The exponent map is bounded: for `j` with `j + 2 ≤ |K|` and `j % p ≤ p - 2` (the conditions
satisfied on the support of a derivative), `digitExp p k j + p ^ k + 1 ≤ |K|`. -/
lemma digitExp_add_le (hk : Nat.card K = p ^ (k + 1)) {j : ℕ} (hj : j + 2 ≤ Nat.card K)
    (hjm : j % p ≤ p - 2) : digitExp p k j + p ^ k + 1 ≤ Nat.card K := by
  have hpp : p.Prime := CharP.char_is_prime K p
  have hq : p * p ^ k = Nat.card K := mul_pow_card p k hk
  have hp2 : 2 ≤ p := hpp.two_le
  have hp : 0 < p := hpp.pos
  have hdiv : j / p < p ^ k := by
    rw [Nat.div_lt_iff_lt_mul hp, Nat.mul_comm (p ^ k) p]
    omega
  have h1 : j / p + 1 ≤ p ^ k := hdiv
  have h2 : j % p + 1 ≤ p - 1 := by omega
  calc digitExp p k j + p ^ k + 1
      = (j / p + 1) + ((j % p) + 1) * p ^ k := by
        rw [digitExp, Nat.add_mul, Nat.one_mul]; ring
    _ ≤ p ^ k + (p - 1) * p ^ k := Nat.add_le_add h1 (Nat.mul_le_mul_right _ h2)
    _ = p * p ^ k := by
        have h3 : p ^ k + (p - 1) * p ^ k = (1 + (p - 1)) * p ^ k := by
          rw [Nat.add_mul, Nat.one_mul]
        rw [h3, show 1 + (p - 1) = p by omega]
    _ = Nat.card K := hq

/-- The exponent map is injective on the support of a derivative. -/
lemma digitExp_injOn (hk : Nat.card K = p ^ (k + 1)) {j j' : ℕ} (hj : j + 2 ≤ Nat.card K)
    (hj' : j' + 2 ≤ Nat.card K) (heq : digitExp p k j = digitExp p k j') : j = j' := by
  have hpp : p.Prime := CharP.char_is_prime K p
  have hq : p * p ^ k = Nat.card K := mul_pow_card p k hk
  have hp : 0 < p := hpp.pos
  have hA : 0 < p ^ k := pow_pos hp k
  have hjq : j / p < p ^ k := by
    rw [Nat.div_lt_iff_lt_mul hp, Nat.mul_comm (p ^ k) p]
    omega
  have hjq' : j' / p < p ^ k := by
    rw [Nat.div_lt_iff_lt_mul hp, Nat.mul_comm (p ^ k) p]
    omega
  have e1 : digitExp p k j % p ^ k = j / p := by
    rw [digitExp, Nat.mul_comm (j % p) (p ^ k), Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt hjq]
  have e2 : digitExp p k j' % p ^ k = j' / p := by
    rw [digitExp, Nat.mul_comm (j' % p) (p ^ k), Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt hjq']
  have hdiv_eq : j / p = j' / p := by rw [← e1, ← e2, heq]
  have hmul_eq : (j % p) * p ^ k = (j' % p) * p ^ k := by
    rw [digitExp, digitExp, hdiv_eq] at heq
    exact Nat.add_left_cancel heq
  have hmod_eq : j % p = j' % p := Nat.mul_right_cancel hA hmul_eq
  calc j = p * (j / p) + j % p := (Nat.div_add_mod j p).symm
    _ = p * (j' / p) + j' % p := by rw [hdiv_eq, hmod_eq]
    _ = j' := Nat.div_add_mod j' p

/-- A derivative has zero coefficient at every exponent `j` with `j ≡ p - 1 (mod p)`. -/
lemma coeff_derivative_eq_zero {d : K[X]} {j : ℕ} (hj : j % p = p - 1) :
    (derivative d).coeff j = 0 := by
  have hpp : p.Prime := CharP.char_is_prime K p
  have hp : 0 < p := hpp.pos
  rw [coeff_derivative]
  have hdvd : p ∣ j + 1 := by
    refine ⟨j / p + 1, ?_⟩
    rw [Nat.mul_succ]
    have h := Nat.div_add_mod j p
    omega
  have hzero : ((j + 1 : ℕ) : K) = 0 := (CharP.cast_eq_zero_iff K p (j + 1)).mpr hdvd
  push_cast at hzero
  rw [hzero, mul_zero]

/-- **Lemma 4 of the paper.** Let `q = p ^ (k + 1)` be a prime power, let `d ∈ 𝔽_q[X]` have
degree at most `q - 1`, and suppose that `d' ≠ 0`. Then `d'` has at most `q - q / p - 1` zeros
in `𝔽_q`. -/
theorem card_zeros_derivative_le (hk : Nat.card K = p ^ (k + 1)) {d : K[X]}
    (hd : d.natDegree ≤ Nat.card K - 1) (hd' : derivative d ≠ 0) :
    Nat.card {x : K // (derivative d).eval x = 0} ≤ Nat.card K - Nat.card K / p - 1 := by
  classical
  have hpp : p.Prime := CharP.char_is_prime K p
  have hp : 0 < p := hpp.pos
  have hq : p * p ^ k = Nat.card K := mul_pow_card p k hk
  set g : K[X] := derivative d with hg
  -- degree bound for `g`
  have hgdeg : g.natDegree + 2 ≤ Nat.card K := by
    have h1 : g.natDegree ≤ d.natDegree - 1 := hg ▸ natDegree_derivative_le d
    have hq2 : 2 ≤ Nat.card K := by
      rw [← hq]
      have hk1 : 1 ≤ p ^ k := by have := pow_pos hp k; omega
      calc 2 = 2 * 1 := by ring
        _ ≤ p * p ^ k := Nat.mul_le_mul hpp.two_le hk1
    omega
  -- two consequences of membership in the support of `g`
  have hsupp_le : ∀ j ∈ g.support, j + 2 ≤ Nat.card K := by
    intro j hj
    have := le_natDegree_of_mem_supp j hj
    omega
  have hsupp_mod : ∀ j ∈ g.support, j % p ≤ p - 2 := by
    intro j hj
    have hne : j % p ≠ p - 1 := by
      intro hcon
      exact (mem_support_iff.mp hj) (hg ▸ coeff_derivative_eq_zero p (d := d) (j := j) hcon)
    have := Nat.mod_lt j hp
    omega
  -- `g` as a sum over its support
  have hgsum : g = ∑ j ∈ g.support, C (g.coeff j) * X ^ j := by
    have h := as_sum_support (derivative d)
    have h' : ∑ i ∈ (derivative d).support, monomial i ((derivative d).coeff i)
        = ∑ i ∈ (derivative d).support, C ((derivative d).coeff i) * X ^ i :=
      Finset.sum_congr rfl fun i _ => C_mul_X_pow_eq_monomial.symm
    rw [hg]
    exact h.trans h'
  -- the covering polynomial `R`
  set R : K[X] := ∑ j ∈ g.support, C ((g.coeff j) ^ p ^ k) * X ^ digitExp p k j with hR
  -- its values are the `p ^ k`-th powers of the values of `g`
  have hRval : ∀ x : K, R.eval x = (g.eval x) ^ p ^ k := by
    intro x
    have hgval : g.eval x = ∑ j ∈ g.support, g.coeff j * x ^ j := by
      conv_lhs => rw [hgsum]
      simp [eval_finsetSum, eval_mul, eval_pow]
    have hRval' : R.eval x = ∑ j ∈ g.support, (g.coeff j) ^ p ^ k * x ^ digitExp p k j := by
      rw [hR]
      simp [eval_finsetSum, eval_mul, eval_pow]
    rw [hRval', hgval, sum_pow_pow]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_pow, ← pow_mul, pow_mul_digitExp p k hk]
  -- `R` is nonzero: its coefficient at `digitExp j₀` is the nonzero `(g.coeff j₀) ^ (p ^ k)`
  have hRne : R ≠ 0 := by
    have hne : g.support.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty, Ne, support_eq_empty]
      exact hd'
    obtain ⟨j₀, hj₀⟩ := hne
    have hcoe : R.coeff (digitExp p k j₀) = (g.coeff j₀) ^ p ^ k := by
      rw [hR, finsetSum_coeff, Finset.sum_eq_single j₀]
      · rw [coeff_C_mul_X_pow]; simp
      · intro j hj hne'
        rw [coeff_C_mul_X_pow]
        have hdj : digitExp p k j₀ ≠ digitExp p k j := by
          intro hcon
          exact hne' (digitExp_injOn p k hk (hsupp_le j hj) (hsupp_le j₀ hj₀) hcon.symm)
        simp [hdj]
      · intro hnot
        exact absurd hj₀ hnot
    intro hR0
    rw [hR0, coeff_zero] at hcoe
    exact pow_ne_zero _ (mem_support_iff.mp hj₀) hcoe.symm
  -- degree bound for `R`
  have hRdeg : R.natDegree ≤ Nat.card K - p ^ k - 1 := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [hR, finsetSum_coeff]
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [coeff_C_mul_X_pow]
    have hle : digitExp p k j + p ^ k + 1 ≤ Nat.card K :=
      digitExp_add_le p k hk (hsupp_le j hj) (hsupp_mod j hj)
    have hNj : N ≠ digitExp p k j := by omega
    simp [hNj]
  -- the zero sets of `g` and of `R` coincide, and the root bound applies to `R`
  have hzero : ∀ x : K, g.eval x = 0 ↔ R.eval x = 0 := by
    intro x
    rw [hRval x, pow_eq_zero_iff (pow_ne_zero k (ne_of_gt hp))]
  have hcard : Nat.card {x : K // g.eval x = 0} =
      (Finset.univ.filter fun x => g.eval x = 0).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hcard]
  have hsub : (Finset.univ.filter fun x => g.eval x = 0).val ⊆ R.roots := by
    intro x hx
    simp only [Finset.mem_val, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    rw [mem_roots hRne, IsRoot, (hzero x).mp hx]
  have hfin := card_le_degree_of_subset_roots hsub
  have hdiv : Nat.card K / p = p ^ k := by
    rw [hk, pow_succ, Nat.mul_div_cancel _ hp]
  rw [hdiv]
  omega

/-- **Lemma 4 of the paper**, in the paper's own notation: for `q = p ^ r` with `r ≥ 1`, a
polynomial `d` of degree at most `q - 1` with `d' ≠ 0` has at most `q - q / p - 1` zeros of its
derivative. -/
theorem card_zeros_derivative_le_pow (p r : ℕ) [CharP K p] (hr : 1 ≤ r)
    (hk : Nat.card K = p ^ r) {d : K[X]} (hd : d.natDegree ≤ Nat.card K - 1)
    (hd' : derivative d ≠ 0) :
    Nat.card {x : K // (derivative d).eval x = 0} ≤ Nat.card K - Nat.card K / p - 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  exact card_zeros_derivative_le p k hk hd hd'

end Lemma4

/-- **Lemma 4 over a prime field.** For `d ∈ 𝔽_p[X]` of degree at most `p - 1` with `d' ≠ 0`,
the derivative has at most `p - 2` zeros in `𝔽_p`; this is the root bound, since `d'` has degree
at most `p - 2`. -/
theorem card_zeros_derivative_le_zmod (p : ℕ) [Fact p.Prime] {d : (ZMod p)[X]}
    (hd : d.natDegree ≤ p - 1) (hd' : derivative d ≠ 0) :
    Nat.card {x : ZMod p // (derivative d).eval x = 0} ≤ p - 2 := by
  have hcard : Nat.card (ZMod p) = p := by simp
  have h := card_zeros_derivative_le (K := ZMod p) p 0 (by rw [hcard]; ring) (by rwa [hcard]) hd'
  rw [hcard] at h
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hdiv : p / p = 1 := Nat.div_self hp
  rw [hdiv] at h
  omega


/-- In a finite field of odd order the sum of all elements is zero. -/
lemma sum_univ_eq_zero (hq : 3 ≤ Nat.card K) : ∑ x : K, x = 0 := by
  classical
  have hcard : Fintype.card K = Nat.card K := (Nat.card_eq_fintype_card).symm
  have h := FiniteField.sum_pow_lt_card_sub_one (K := K) 1 (by rw [hcard]; omega)
  simpa using h

-- interpolation identity, step by step
/-- The interpolation identity behind the Lagrange formula: a polynomial of degree at most
`q - 1` is determined by its values on `𝔽_q`, and
`d(X) = ∑_{u ∈ 𝔽_q} d(u) (1 - (X - u)^{q-1})`. -/
private lemma interp_aux (hq3 : 3 ≤ Nat.card K) {d : K[X]}
    (hd : d.natDegree ≤ Nat.card K - 1) :
    d = ∑ u : K, C (d.eval u) * (1 - (X - C u) ^ (Nat.card K - 1)) := by
  classical
  set R : K[X] := ∑ u : K, C (d.eval u) * (1 - (X - C u) ^ (Nat.card K - 1)) with hR
  have hterm : ∀ u : K, (C (d.eval u) * (1 - (X - C u) ^ (Nat.card K - 1))).natDegree ≤
      Nat.card K - 1 := by
    intro u
    refine le_trans Polynomial.natDegree_mul_le ?_
    have hsub : ((1 : K[X]) - (X - C u) ^ (Nat.card K - 1)).natDegree ≤ Nat.card K - 1 := by
      refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
      rw [max_le_iff]
      refine ⟨by simp, ?_⟩
      rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C]
      simp
    have hC : (Polynomial.C (d.eval u)).natDegree ≤ 0 := by simp
    omega
  have hRdeg : R.natDegree ≤ Nat.card K - 1 := by
    rw [hR]
    exact Polynomial.natDegree_sum_le_of_forall_le (Finset.univ)
      (fun u => C (d.eval u) * (1 - (X - C u) ^ (Nat.card K - 1))) (fun u _ => hterm u)
  have heval : ∀ v : K, d.eval v = R.eval v := by
    intro v
    rw [hR, Polynomial.eval_finsetSum]
    have hsplit : ∀ u : K, d.eval u * (1 - (X - C u) ^ (Nat.card K - 1)).eval v
        = d.eval u - d.eval u * (v - u) ^ (Nat.card K - 1) := by
      intro u
      simp only [Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_C]
      ring
    simp only [Polynomial.eval_mul, Polynomial.eval_C, hsplit]
    rw [Finset.sum_sub_distrib]
    have hsecond : ∑ u : K, d.eval u * (v - u) ^ (Nat.card K - 1) =
        ∑ u ∈ Finset.univ.erase v, d.eval u := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ v)]
      rw [show (v - v) = (0 : K) by ring, zero_pow (by omega : Nat.card K - 1 ≠ 0), mul_zero,
        add_zero]
      refine Finset.sum_congr rfl fun u hu => ?_
      rw [Finset.mem_erase] at hu
      have hvu : v - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu.1)
      rw [show Nat.card K - 1 = Fintype.card K - 1 from by rw [Nat.card_eq_fintype_card]]
      rw [FiniteField.pow_card_sub_one_eq_one (v - u) hvu, mul_one]
    rw [hsecond]
    have hsum := Finset.sum_erase_add (Finset.univ : Finset K) (fun u => d.eval u)
      (Finset.mem_univ v)
    rw [← hsum]
    ring
  refine Polynomial.eq_of_natDegree_lt_card_of_eval_eq' d R Finset.univ ?_ ?_
  · intro v _
    exact heval v
  · rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
    omega


theorem deriv_eq_sum (hq3 : 3 ≤ Nat.card K) {d : K[X]}
    (hd : d.natDegree ≤ Nat.card K - 1) (x : K) :
    (derivative d).eval x = ∑ u ∈ Finset.univ.erase x, d.eval u / (x - u) := by
  classical
  have hid := interp_aux (K := K) hq3 (d := d) hd
  have hderiv : derivative d =
      ∑ u : K, C (d.eval u) *
        (-(C ((Nat.card K - 1 : ℕ) : K) * (X - C u) ^ (Nat.card K - 2))) := by
    conv_lhs => rw [hid]
    rw [Polynomial.derivative_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Polynomial.derivative_C_mul, Polynomial.derivative_sub, Polynomial.derivative_one,
      Polynomial.derivative_X_sub_C_pow]
    rw [show Nat.card K - 1 - 1 = Nat.card K - 2 by omega]
    ring
  have hc1 : ((Nat.card K - 1 : ℕ) : K) = -1 := by
    have h0 : ((Nat.card K : ℕ) : K) = 0 := by
      rw [Nat.card_eq_fintype_card]
      exact Nat.cast_card_eq_zero K
    rw [Nat.cast_sub (by omega : 1 ≤ Nat.card K), Nat.cast_one, h0, zero_sub]
  rw [hderiv, Polynomial.eval_finsetSum]
  have hterm : ∀ u : K, u ≠ x →
      (C (d.eval u) * (-(C ((Nat.card K - 1 : ℕ) : K) * (X - C u) ^ (Nat.card K - 2)))).eval x
        = d.eval u / (x - u) := by
    intro u hux
    have hxu : x - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hux)
    have hpow : (x - u) ^ (Nat.card K - 2) = (x - u)⁻¹ := by
      have h1 : (x - u) ^ (Nat.card K - 1) = 1 := by
        rw [show Nat.card K - 1 = Fintype.card K - 1 from by rw [Nat.card_eq_fintype_card]]
        exact FiniteField.pow_card_sub_one_eq_one (x - u) hxu
      have h2 : (x - u) ^ (Nat.card K - 1) = (x - u) ^ (Nat.card K - 2) * (x - u) := by
        rw [← pow_succ, show Nat.card K - 2 + 1 = Nat.card K - 1 by omega]
      rw [h1] at h2
      exact eq_inv_of_mul_eq_one_left h2.symm
    simp only [Polynomial.eval_mul, Polynomial.eval_neg, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_sub, hc1, hpow]
    rw [div_eq_mul_inv]
    ring
  have htermx :
      (C (d.eval x) * (-(C ((Nat.card K - 1 : ℕ) : K) * (X - C x) ^ (Nat.card K - 2)))).eval x = 0 := by
    simp only [Polynomial.eval_mul, Polynomial.eval_neg, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_sub, sub_self]
    rw [zero_pow (by omega : Nat.card K - 2 ≠ 0)]
    ring
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ x), htermx, add_zero]
  refine Finset.sum_congr rfl fun u hu => hterm u ?_
  rw [Finset.mem_erase] at hu
  exact hu.1


/-- The interpolating polynomial of a function `f : K → K`: the sum
`∑ u, C (f u) * (1 - (X - C u)^(|K| - 1))`. -/
noncomputable def interpPoly (f : K → K) : K[X] :=
  ∑ u : K, C (f u) * (1 - (X - C u) ^ (Nat.card K - 1))

/-- The interpolating polynomial has degree at most `|K| - 1`. -/
lemma interpPoly_natDegree_le (f : K → K) : (interpPoly f).natDegree ≤ Nat.card K - 1 := by
  unfold interpPoly
  refine Polynomial.natDegree_sum_le_of_forall_le (Finset.univ) _ ?_
  intro u _
  refine le_trans Polynomial.natDegree_mul_le ?_
  have hsub : ((1 : K[X]) - (X - C u) ^ (Nat.card K - 1)).natDegree ≤ Nat.card K - 1 := by
    refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
    rw [max_le_iff]
    refine ⟨by simp, ?_⟩
    rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C]; simp
  have hC : (Polynomial.C (f u)).natDegree ≤ 0 := by simp
  omega

/-- The interpolating polynomial evaluates to `f` at every point of `K`. -/
lemma interpPoly_eval (hq2 : 2 ≤ Nat.card K) (f : K → K) (v : K) :
    (interpPoly f).eval v = f v := by
  classical
  unfold interpPoly
  rw [Polynomial.eval_finsetSum]
  have hsplit : ∀ u : K, f u * (1 - (X - C u) ^ (Nat.card K - 1)).eval v
      = f u - f u * (v - u) ^ (Nat.card K - 1) := by
    intro u
    simp only [Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C]
    ring
  simp only [Polynomial.eval_mul, Polynomial.eval_C, hsplit]
  rw [Finset.sum_sub_distrib]
  have hsecond : ∑ u : K, f u * (v - u) ^ (Nat.card K - 1) = ∑ u ∈ Finset.univ.erase v, f u := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ v)]
    rw [show (v - v) = (0 : K) by ring, zero_pow (by omega : Nat.card K - 1 ≠ 0), mul_zero,
      add_zero]
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [Finset.mem_erase] at hu
    have hvu : v - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu.1)
    rw [show Nat.card K - 1 = Fintype.card K - 1 from by rw [Nat.card_eq_fintype_card]]
    rw [FiniteField.pow_card_sub_one_eq_one (v - u) hvu, mul_one]
  rw [hsecond]
  have hsum := Finset.sum_erase_add (Finset.univ : Finset K) (fun u => f u) (Finset.mem_univ v)
  rw [← hsum]
  ring

end Polynomial

namespace PGL2

open Polynomial

variable {K : Type*} [Field K] [Fintype K]

/-- For trace-zero `2 × 2` matrices, `M * N + N * M = tr(M * N) • 1`. -/
lemma anticommutator_of_trace_zero (M N : Matrix (Fin 2) (Fin 2) K)
    (hM : M.trace = 0) (hN : N.trace = 0) :
    M * N + N * M = (M * N).trace • (1 : Matrix (Fin 2) (Fin 2) K) := by
  have hM' : M 1 1 = -M 0 0 := by
    have h := hM; rw [Matrix.trace_fin_two] at h; exact eq_neg_of_add_eq_zero_right h
  have hN' : N 1 1 = -N 0 0 := by
    have h := hN; rw [Matrix.trace_fin_two] at h; exact eq_neg_of_add_eq_zero_right h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.add_apply, Matrix.trace_fin_two,
      Matrix.one_apply, Matrix.smul_apply] <;> rw [hM', hN'] <;> ring

/-- In a finite field of odd order, `2 ≠ 0`. -/
lemma two_ne_zero_of_odd_card (hodd : Odd (Nat.card K)) : (2 : K) ≠ 0 := by
  classical
  haveI : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K (ringChar K)⟩
  haveI : NeZero (ringChar K) := ⟨(CharP.char_is_prime K (ringChar K)).ne_zero⟩
  letI := ZMod.algebra K (ringChar K)
  have hfin : Module.Finite (ZMod (ringChar K)) K := Module.Finite.of_finite
  have hcard := Module.natCard_eq_pow_finrank (K := ZMod (ringChar K)) (V := K)
  have hcardZ : Nat.card (ZMod (ringChar K)) = ringChar K := by
    rw [Nat.card_eq_fintype_card, ZMod.card]
  obtain ⟨r, hr⟩ : ∃ r : ℕ, r = Module.finrank (ZMod (ringChar K)) K := ⟨_, rfl⟩
  have hcard' : Nat.card K = ringChar K ^ r := by
    rw [hcard, hcardZ, ← hr]
  intro h2z
  have hdvd : ringChar K ∣ 2 := (CharP.cast_eq_zero_iff K (ringChar K) 2).mp h2z
  have hpeq : ringChar K = 2 := by
    rcases Nat.prime_two.eq_one_or_self_of_dvd (ringChar K) hdvd with h | h
    · exact absurd h (CharP.char_is_prime K (ringChar K)).ne_one
    · exact h
  have hcard2 : Nat.card K = 2 ^ r := by rw [hcard', hpeq]
  have hfr : 1 ≤ r := by
    by_contra h
    push_neg at h
    have h0 : r = 0 := by omega
    rw [h0, pow_zero] at hcard2
    have h1 : 1 < Nat.card K := by rw [Nat.card_eq_fintype_card]; exact Fintype.one_lt_card
    omega
  rcases hodd with ⟨n, hn⟩
  rw [hcard2] at hn
  have h2dvd : 2 ∣ 2 ^ r := Nat.pow_dvd_pow 2 hfr
  rw [hn] at h2dvd
  omega

/-- A nonidentity involution's lift squares to a nonzero scalar matrix. -/
lemma sq_smul_of_isInvolution {h : PGL2 K} (hh : IsInvolution h) :
    ∃ l : K, l ≠ 0 ∧ (((Quotient.out h : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * ((Quotient.out h : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
        l • (1 : Matrix (Fin 2) (Fin 2) K)) := by
  classical
  set g : GL (Fin 2) K := Quotient.out h with hg
  set M : Matrix (Fin 2) (Fin 2) K := (g : Matrix (Fin 2) (Fin 2) K) with hM
  have hmem : g * g ∈ Subgroup.center (GL (Fin 2) K) := by
    have h1 : (g : PGL2 K) = h := Quotient.out_eq h
    have h2 : ((g * g : GL (Fin 2) K) : PGL2 K) = 1 := by
      rw [QuotientGroup.mk_mul, h1]
      exact hh.2
    rw [← QuotientGroup.eq_one_iff]
    exact h2
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hmem
  obtain ⟨u, hu⟩ := hmem
  have hval : ((Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) = Matrix.scalar (Fin 2) (u : K) := rfl
  have hsq : M * M = (u : K) • (1 : Matrix (Fin 2) (Fin 2) K) := by
    have h3 : ((g * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
        ((Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K) := by rw [← hu]
    calc M * M = ((g * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
          rw [hM, Matrix.GeneralLinearGroup.coe_mul]
      _ = ((Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) K) :
            Matrix (Fin 2) (Fin 2) K) := h3
      _ = Matrix.scalar (Fin 2) (u : K) := hval
      _ = (u : K) • (1 : Matrix (Fin 2) (Fin 2) K) := by
        ext i j
        simp [Matrix.scalar, Matrix.diagonal, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  have hune : (u : K) ≠ 0 := by
    have hMdet : M.det ≠ 0 := Matrix.GeneralLinearGroup.det_ne_zero g
    have hdet2 : M.det * M.det = (u : K) ^ 2 := by
      rw [← Matrix.det_mul, hsq, Matrix.det_smul, Fintype.card_fin, Matrix.det_one, mul_one]
    intro huz
    rw [huz, zero_pow (by norm_num : 2 ≠ 0)] at hdet2
    exact hMdet ((mul_eq_zero.mp hdet2).elim id id)
  exact ⟨(u : K), hune, hsq⟩

/-- If the lifts of `h₁, h₂` differ by a nonzero scalar, then `h₁ = h₂`. -/
lemma eq_of_lift_eq_smul {h₁ h₂ : PGL2 K} {c : K} (hc : c ≠ 0)
    (h : ((Quotient.out h₂ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      c • ((Quotient.out h₁ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) : h₂ = h₁ := by
  classical
  rw [← Quotient.out_eq h₂, ← Quotient.out_eq h₁, QuotientGroup.eq_iff_div_mem]
  have hval : ((Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 c hc) : GL (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) = Matrix.scalar (Fin 2) c := rfl
  have hGL : Quotient.out h₂ = Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 c hc) *
      (Quotient.out h₁ : GL (Fin 2) K) := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    rw [Matrix.GeneralLinearGroup.coe_mul, hval, h]
    simp [Matrix.scalar, Matrix.diagonal, Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two,
      smul_eq_mul]
  rw [hGL, mul_div_cancel_right]
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
  exact ⟨Units.mk0 c hc, rfl⟩

/-- Distinct commuting involutions of `PGL₂(K)` have anticommuting trace-zero lifts. -/
lemma anticommute_lifts_of_commute {h₁ h₂ : PGL2 K} (hh₁ : IsInvolution h₁)
    (hh₂ : IsInvolution h₂) (hne : h₁ ≠ h₂) (hcomm : h₁ * h₂ = h₂ * h₁) :
    ((Quotient.out h₁ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
      ((Quotient.out h₂ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
    -(((Quotient.out h₂ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
      ((Quotient.out h₁ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) := by
  classical
  set g₁ : GL (Fin 2) K := Quotient.out h₁ with hg₁
  set g₂ : GL (Fin 2) K := Quotient.out h₂ with hg₂
  set M₁ : Matrix (Fin 2) (Fin 2) K := (g₁ : Matrix (Fin 2) (Fin 2) K) with hM₁
  set M₂ : Matrix (Fin 2) (Fin 2) K := (g₂ : Matrix (Fin 2) (Fin 2) K) with hM₂
  have htr₁ := trace_zero_of_isInvolution hh₁
  have htr₂ := trace_zero_of_isInvolution hh₂
  obtain ⟨l₁, hl₁, hsq₁⟩ := sq_smul_of_isInvolution hh₁
  -- projective commutation: `M₁ * M₂ = c • (M₂ * M₁)` for some `c ≠ 0`
  have hproj : ∃ c : K, c ≠ 0 ∧ M₁ * M₂ = c • (M₂ * M₁) := by
    have e1 : (g₁ : PGL2 K) = h₁ := Quotient.out_eq h₁
    have e2 : (g₂ : PGL2 K) = h₂ := Quotient.out_eq h₂
    have hcomm'' : ((g₁ * g₂ : GL (Fin 2) K) : PGL2 K) = ((g₂ * g₁ : GL (Fin 2) K) : PGL2 K) :=
      calc ((g₁ * g₂ : GL (Fin 2) K) : PGL2 K)
          = (g₁ : PGL2 K) * (g₂ : PGL2 K) := by rw [QuotientGroup.mk_mul]
        _ = h₁ * h₂ := by rw [e1, e2]
        _ = h₂ * h₁ := hcomm
        _ = (g₂ : PGL2 K) * (g₁ : PGL2 K) := by rw [e2, e1]
        _ = ((g₂ * g₁ : GL (Fin 2) K) : PGL2 K) := by rw [← QuotientGroup.mk_mul]
    have hmem : g₁ * g₂ / (g₂ * g₁) ∈ Subgroup.center (GL (Fin 2) K) :=
      QuotientGroup.eq_iff_div_mem.mp hcomm''
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hmem
    obtain ⟨u, hu⟩ := hmem
    have hval : ((Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) = Matrix.scalar (Fin 2) (u : K) := rfl
    have hGL : g₁ * g₂ = Matrix.GeneralLinearGroup.scalar (Fin 2) u * (g₂ * g₁) := by
      calc g₁ * g₂ = (g₁ * g₂ / (g₂ * g₁)) * (g₂ * g₁) := (div_mul_cancel (g₁ * g₂) (g₂ * g₁)).symm
        _ = Matrix.GeneralLinearGroup.scalar (Fin 2) u * (g₂ * g₁) := by rw [← hu]
    have hM : M₁ * M₂ = (u : K) • (M₂ * M₁) := by
      have hM' := congrArg (fun x : GL (Fin 2) K => (x : Matrix (Fin 2) (Fin 2) K)) hGL
      rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, ← hM₁, ← hM₂] at hM'
      rw [hval] at hM'
      rw [hM']
      ext i j
      simp [Matrix.scalar, Matrix.diagonal, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply,
        smul_eq_mul, hM₁, hM₂]
    exact ⟨(u : K), by simp, hM⟩
  obtain ⟨c, hc, hrel⟩ := hproj
  have hanti := anticommutator_of_trace_zero M₁ M₂ htr₁ htr₂
  have hsum0 : M₁ * M₂ + M₂ * M₁ = c • (M₂ * M₁) + M₂ * M₁ := by rw [hrel]
  rw [hsum0] at hanti
  have hsum : c • (M₂ * M₁) + M₂ * M₁ = (c + 1) • (M₂ * M₁) := by
    rw [add_smul, one_smul]
  rw [hsum] at hanti
  by_cases hc1 : c = -1
  · rw [hc1] at hrel
    simpa using hrel
  · -- `c ≠ -1`: `M₂ * M₁` is scalar, so `M₂` is a scalar multiple of `M₁`, contradiction
    have hc1' : c + 1 ≠ 0 := fun h => hc1 (eq_neg_of_add_eq_zero_left h)
    have hmu : M₂ * M₁ = ((M₁ * M₂).trace / (c + 1)) • (1 : Matrix (Fin 2) (Fin 2) K) := by
      have h5 := congrArg (fun X => ((c + 1)⁻¹) • X) hanti
      rw [smul_smul, inv_mul_cancel₀ hc1', one_smul] at h5
      rw [smul_smul, mul_comm ((c + 1)⁻¹) ((M₁ * M₂).trace), ← div_eq_mul_inv] at h5
      exact h5
    -- `M₂ * M₁ = μ • 1` and `M₁ * M₁ = l₁ • 1` give `l₁ • M₂ = μ • M₁`
    have hM₂ : M₂ = (((M₁ * M₂).trace / (c + 1)) / l₁) • M₁ := by
      have h6 : M₂ * (M₁ * M₁) = (M₂ * M₁) * M₁ := by rw [Matrix.mul_assoc]
      rw [hsq₁, hmu] at h6
      rw [mul_smul_comm, smul_mul_assoc, Matrix.mul_one, Matrix.one_mul] at h6
      calc M₂ = l₁⁻¹ • (l₁ • M₂) := by rw [smul_smul, inv_mul_cancel₀ hl₁, one_smul]
        _ = l₁⁻¹ • (((M₁ * M₂).trace / (c + 1)) • M₁) := by rw [h6]
        _ = (((M₁ * M₂).trace / (c + 1)) / l₁) • M₁ := by
          rw [smul_smul, mul_comm l₁⁻¹ ((M₁ * M₂).trace / (c + 1)), ← div_eq_mul_inv]
    have hM₂det : M₂.det ≠ 0 := Matrix.GeneralLinearGroup.det_ne_zero (Quotient.out h₂)
    have hcz' : ((M₁ * M₂).trace / (c + 1)) / l₁ ≠ 0 := by
      intro hcz
      rw [hM₂, hcz, zero_smul, Matrix.det_zero] at hM₂det
      exact hM₂det rfl
    exact absurd (eq_of_lift_eq_smul hcz' hM₂) hne.symm

/-- Four pairwise anticommuting invertible trace-zero `2 × 2` matrices cannot exist when
`2 ≠ 0` in `K`: trace-zero matrices form a 3-dimensional space, so four of them are linearly
dependent, but anticommutation forces every coefficient of a dependence to vanish. -/
lemma not_four_anticommute (h2 : (2 : K) ≠ 0) (M : Fin 4 → Matrix (Fin 2) (Fin 2) K)
    (htr : ∀ i, (M i).trace = 0) (hdet : ∀ i, (M i).det ≠ 0)
    (hanti : ∀ i j, i ≠ j → M i * M j = -(M j * M i)) : False := by
  classical
  -- Step 1: the coordinate vectors `w i` in the 3-dimensional space `Fin 3 → K` are
  -- linearly dependent.
  set w : Fin 4 → (Fin 3 → K) := fun i => ![M i 0 0, M i 0 1, M i 1 0] with hw
  have hNL : ¬ LinearIndependent K w := by
    intro hLI
    have hle := hLI.fintype_card_le_finrank
    rw [Fintype.card_fin, Module.finrank_fin_fun] at hle
    exact absurd hle (by decide)
  obtain ⟨c, hsum, j, hj⟩ := Fintype.not_linearIndependent_iff.mp hNL
  -- Step 2: coordinate-wise dependence of the matrices themselves (the `(1,1)` entry is
  -- `-M i 0 0` since the trace vanishes).
  have hcoord : ∀ a : Fin 3, ∑ i, c i * w i a = 0 := by
    intro a
    have h := congrFun hsum a
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using h
  have hc0 : ∑ i, c i * M i 0 0 = 0 := by
    have h := hcoord 0
    rw [hw] at h
    simpa using h
  have hc1 : ∑ i, c i * M i 0 1 = 0 := by
    have h := hcoord 1
    rw [hw] at h
    simpa using h
  have hc2 : ∑ i, c i * M i 1 0 = 0 := by
    have h := hcoord 2
    rw [hw] at h
    simpa using h
  have hc3 : ∑ i, c i * M i 1 1 = 0 := by
    have hneg : ∀ i, M i 1 1 = -M i 0 0 := fun i => by
      have h := htr i
      rw [Matrix.trace_fin_two] at h
      exact eq_neg_of_add_eq_zero_right h
    simp_rw [hneg, mul_neg, Finset.sum_neg_distrib, hc0, neg_zero]
  have hM : ∑ i, c i • M i = 0 := by
    ext a b
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]
    fin_cases a <;> fin_cases b
    · exact hc0
    · exact hc1
    · exact hc2
    · exact hc3
  -- Step 3: anticommutation forces every coefficient of the dependence to vanish.
  have hcz : ∀ j, c j = 0 := by
    intro j
    have hsqj : M j * M j = -((M j).det • (1 : Matrix (Fin 2) (Fin 2) K)) := by
      have h := sq_eq_trace_smul_sub_det (M j)
      rw [htr j, zero_smul, zero_sub] at h
      exact h
    have hl : M j * (∑ i, c i • M i) = ∑ i, c i • (M j * M i) := by
      simp [Finset.mul_sum]
    have hr : (∑ i, c i • M i) * M j = ∑ i, c i • (M i * M j) := by
      simp [Finset.sum_mul]
    have h12 : ∑ i, c i • (M j * M i + M i * M j) = 0 := by
      have h := congrArg (fun X => M j * X + X * M j) hM
      rw [hl, hr, mul_zero, zero_mul, add_zero, ← Finset.sum_add_distrib] at h
      simp_rw [← smul_add] at h
      exact h
    have hsingle : ∑ i, c i • (M j * M i + M i * M j) = c j • (M j * M j + M j * M j) := by
      refine Finset.sum_eq_single j (fun b _ hb => ?_)
        (fun hcon => absurd (Finset.mem_univ j) hcon)
      rw [hanti j b (Ne.symm hb), neg_add_cancel, smul_zero]
    rw [hsingle, hsqj] at h12
    -- `h12 : c j • (-(d • 1) + -(d • 1)) = 0` with `d = (M j).det`; evaluate at `(0,0)`.
    have h00 := congrFun (congrFun h12 0) 0
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.neg_apply, smul_eq_mul,
      Matrix.one_apply_eq, Matrix.zero_apply, mul_one] at h00
    have hscalar : c j * (-(2 * (M j).det)) = 0 := by linear_combination h00
    rcases mul_eq_zero.mp hscalar with h | h
    · exact h
    · have h2d : 2 * (M j).det = 0 := neg_eq_zero.mp h
      rcases mul_eq_zero.mp h2d with h2z | hdetz
      · exact absurd h2z h2
      · exact absurd hdetz (hdet j)
  exact hj (hcz j)

theorem card_le_four_of_forall_sq (hodd : Odd (Nat.card K)) (_hq : 5 ≤ Nat.card K)
    (H : Subgroup (PGL2 K)) (hsq : ∀ h ∈ H, h * h = 1) : Nat.card H ≤ 4 := by
  classical
  by_contra hcon
  have hcard5 : 4 < Nat.card H := by omega
  -- `H` is abelian: every element is its own inverse.
  have hab : ∀ h₁ h₂ : PGL2 K, h₁ ∈ H → h₂ ∈ H → h₁ * h₂ = h₂ * h₁ := by
    intro h₁ h₂ h₁H h₂H
    have hinv1 : h₁⁻¹ = h₁ := (eq_inv_of_mul_eq_one_left (hsq h₁ h₁H)).symm
    have hinv2 : h₂⁻¹ = h₂ := (eq_inv_of_mul_eq_one_left (hsq h₂ h₂H)).symm
    have h12 : h₁ * h₂ = (h₁ * h₂)⁻¹ :=
      eq_inv_of_mul_eq_one_left (hsq (h₁ * h₂) (H.mul_mem h₁H h₂H))
    rw [h12, mul_inv_rev, hinv1, hinv2]
  -- four distinct nonidentity elements of `H`
  have hfc : Fintype.card ↥H = Nat.card H := (Nat.card_eq_fintype_card).symm
  have hne : 4 ≤ (Finset.univ.erase (1 : ↥H)).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hfc]
    omega
  obtain ⟨t, htsub, htcard⟩ := Finset.exists_subset_card_eq hne
  let e := t.equivFin
  let f : Fin 4 → ↥H := fun i => (e.symm (Fin.cast htcard.symm i)).1
  have hf_inj : Function.Injective f := by
    intro i j hij
    have hij' : (e.symm (Fin.cast htcard.symm i)).1 = (e.symm (Fin.cast htcard.symm j)).1 := hij
    refine Fin.cast_injective htcard.symm (e.symm.injective ?_)
    exact Subtype.val_injective hij'
  have hf_ne : ∀ i, (f i : PGL2 K) ≠ 1 := by
    intro i
    have hmem : f i ∈ Finset.univ.erase (1 : ↥H) :=
      htsub (e.symm (Fin.cast htcard.symm i)).2
    rw [Finset.mem_erase] at hmem
    intro heq
    exact hmem.1 (Subtype.ext (heq.trans (Subgroup.coe_one H).symm))
  -- the lifts form four pairwise anticommuting invertible trace-zero matrices
  set M : Fin 4 → Matrix (Fin 2) (Fin 2) K :=
    fun i => ((Quotient.out (f i : PGL2 K) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
  have hinv : ∀ i, IsInvolution (f i : PGL2 K) := fun i => ⟨hf_ne i, hsq _ (f i).2⟩
  have htr : ∀ i, (M i).trace = 0 := fun i => trace_zero_of_isInvolution (hinv i)
  have hdet : ∀ i, (M i).det ≠ 0 :=
    fun i => Matrix.GeneralLinearGroup.det_ne_zero (Quotient.out (f i : PGL2 K))
  have hanti : ∀ i j, i ≠ j → M i * M j = -(M j * M i) := by
    intro i j hij
    exact anticommute_lifts_of_commute (hinv i) (hinv j)
      (fun h => hij (hf_inj (Subtype.ext h))) (hab _ _ (f i).2 (f j).2)
  exact not_four_anticommute (two_ne_zero_of_odd_card hodd) M htr hdet hanti

/-- **Lemma 5 of the paper.** Under the hypotheses of Theorem 1 the missing permutation is not
the identity. If `σ = 1`, then `S ∪ {1}` is sharply transitive (equation (1)), so by Eberhard's
sharply transitive set theorem (`eberhard_theorem1`) it is a subgroup `H` of order `q + 1`, all of
whose nonidentity elements are involutions; hence `H` is elementary abelian of order `q + 1`,
contradicting `card_le_four_of_forall_sq` since `q ≥ 5`. -/
theorem missingPerm_ne_one (hodd : Odd (Nat.card K)) (hq : 5 ≤ Nat.card K)
    {S : Set (PGL2 K)} (hS : IsAdmissible S) (hcard : Nat.card S = Nat.card K)
    {σ : Equiv.Perm (P1 K)} (hσ : IsMissingPerm S σ) : σ ≠ 1 := by
  classical
  intro hσ1
  -- two elements of `S` agreeing at a point are equal
  have hinj : ∀ (x : P1 K) (s : PGL2 K), s ∈ S → ∀ (s' : PGL2 K), s' ∈ S →
      s • x = s' • x → s = s' := by
    intro x s hs s' hs' h
    by_contra hne
    have hcon := hS.2 s' hs' s hs (Ne.symm hne) x
    have hs'2 := (hS.1 s' hs').2
    have hfix : (s' * s) • x = x := by
      calc (s' * s) • x = s' • (s • x) := by rw [mul_smul]
        _ = s' • (s' • x) := by rw [h]
        _ = (s' * s') • x := by rw [← mul_smul]
        _ = (1 : PGL2 K) • x := by rw [hs'2]
        _ = x := one_smul _ _
    exact hcon hfix
  -- Step 1: `S ∪ {1}` is sharply transitive
  have hST : IsSharplyTransitive (X := P1 K) (insert 1 S) := by
    intro x y
    by_cases hxy : x = y
    · refine ⟨1, ⟨Set.mem_insert 1 S, by rw [one_smul]; exact hxy⟩, ?_⟩
      intro g ⟨hg, hgx⟩
      rw [Set.mem_insert_iff] at hg
      rcases hg with rfl | hgS
      · rfl
      · rw [← hxy] at hgx
        have hne : x ≠ σ x := (hσ x x).1 ⟨g, hgS, hgx⟩
        have hx : σ x = x := by rw [hσ1]; rfl
        exact absurd hx.symm hne
    · have hne : y ≠ σ x := by
        rw [hσ1]; exact Ne.symm hxy
      obtain ⟨s, hs, hsx⟩ := (hσ x y).2 hne
      refine ⟨s, ⟨Set.mem_insert_of_mem 1 hs, hsx⟩, ?_⟩
      intro g ⟨hg, hgx⟩
      rw [Set.mem_insert_iff] at hg
      rcases hg with rfl | hgS
      · rw [one_smul] at hgx
        exact absurd hgx hxy
      · exact hinj x g hgS s hs (hgx.trans hsx.symm)
  -- Eberhard's theorem
  have h1 : (1 : PGL2 K) ∈ insert 1 S := Set.mem_insert 1 S
  obtain ⟨H, hH⟩ := eberhard_theorem1 (insert 1 S) hST h1
  -- `|H| = |S| + 1 = q + 1`
  have h1not : (1 : PGL2 K) ∉ S := fun h1S => (hS.1 1 h1S).1 rfl
  have hcard' : Nat.card (insert 1 S : Set (PGL2 K)) = Nat.card S + 1 := by
    rw [Nat.card_coe_set_eq, Set.ncard_insert_of_notMem h1not, Nat.card_coe_set_eq]
  have hcardH : Nat.card H = Nat.card K + 1 := by
    have h1' : Nat.card H = Nat.card (insert 1 S : Set (PGL2 K)) :=
      Nat.card_congr (Equiv.cast (congrArg (fun T : Set (PGL2 K) => ↥T) hH))
    rw [h1', hcard', hcard]
  -- every element of `H` squares to `1`
  have hsq : ∀ h ∈ H, h * h = 1 := by
    intro h hh
    have hh' : h ∈ insert 1 S := by rw [← hH]; exact hh
    rw [Set.mem_insert_iff] at hh'
    rcases hh' with rfl | hhS
    · simp
    · exact (hS.1 h hhS).2
  -- the elementary abelian bound contradicts `q ≥ 5`
  have hle4 : Nat.card H ≤ 4 := card_le_four_of_forall_sq hodd hq H hsq
  rw [hcardH] at hle4
  omega

end PGL2
