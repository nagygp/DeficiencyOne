/-
# Main Theorems from "Fixed points and rigidity in the deficiency-one case over prime-power fields"

This file contains the three main theorems from the paper by Korchmáros, Nagy, and Szőnyi.
-/

import FixedPointsPrimePower.Defs

-- Enable universe polymorphism
set_option autoImplicit false

-- =============================================================================
-- Theorem 1: Fixed Point Bound
-- =============================================================================

/-- 
Theorem 1 (Main Theorem): Let q = p^r ≥ 5 be odd, and let S ⊆ PGL₂(q) be an 
admissible set of size q. Then its missing permutation satisfies:

    f ≤ q - q/p

No hypothesis on the degree of a parametrizing polynomial, beyond taking its 
reduced representative, is required.
-/
theorem Theorem1_FixedPointBound 
    (p : ℕ) (hp : Nat.Prime p) (r : ℕ) (hr : r ≥ 1) 
    (hq : p ^ r ≥ 5) (hq_odd : Odd (p ^ r))
    (S : Finset (PGL2Element (Fq p r)))
    (hS_admissible : IsAdmissible S)
    (hS_size : S.card = p ^ r)
    : FixedPointCount (MissingPermutation S) ≤ p ^ r - (p ^ r) / p := by
  sorry

-- =============================================================================
-- Theorem 2: Positive Fixed-Point Gap
-- =============================================================================

/-- 
Theorem 2: Let q = p^r ≥ 5 be odd, and let S be an admissible set of size q.
If S is noncollinear and f > 0, then:

    q ≤ (f - 1)(4√q + 23)
    f ≥ 1 + q / (4√q + 23)

In particular, any fixed bound on positive f implies collinearity for 
sufficiently large q. More generally, a sequence with q → ∞ and 0 < f = o(√q) 
must be collinear for all sufficiently large q.
-/
theorem Theorem2_PositiveFixedPointGap
    (p : ℕ) (hp : Nat.Prime p) (r : ℕ) (hr : r ≥ 1)
    (hq : p ^ r ≥ 5) (hq_odd : Odd (p ^ r))
    (S : Finset (PGL2Element (Fq p r)))
    (hS_admissible : IsAdmissible S)
    (hS_size : S.card = p ^ r)
    (hS_noncollinear : ¬IsCollinear S)
    (hf_pos : 0 < FixedPointCount (MissingPermutation S))
    : p ^ r ≤ (FixedPointCount (MissingPermutation S) - 1) * 
              (4 * Real.sqrt (p ^ r) + 23) ∧
      FixedPointCount (MissingPermutation S) ≥ 
        1 + (p ^ r) / (4 * Real.sqrt (p ^ r) + 23) := by
  -- This theorem is proven in Theorem2/Inequality.lean
  -- The connection requires unifying the type systems
  sorry -- Type unification between MainTheorems.lean and Theorem2/ modules

-- =============================================================================
-- Theorem 3: Rigidity with Positive Fixed-Point Gap
-- =============================================================================

/-- 
Theorem 3: Let q ≥ 7 be odd, and let S be an admissible set of size q.
If f ≥ 4, then every split involution τ ∈ PGL₂(q) sharing a fixed point with σ 
satisfies:

    d_H(σ, τ) ≥ (q + 3) / 2
    |{x ∈ Ω : σ(x) = τ(x)}| ≤ (q - 1) / 2
-/
theorem Theorem3_RigidityPositiveFixedGap
    (p : ℕ) (hp : Nat.Prime p) (r : ℕ) (hr : r ≥ 1)
    (hq : p ^ r ≥ 7) (hq_odd : Odd (p ^ r))
    (S : Finset (PGL2Element (Fq p r)))
    (hS_admissible : IsAdmissible S)
    (hS_size : S.card = p ^ r)
    (hf_ge4 : 4 ≤ FixedPointCount (MissingPermutation S))
    (τ : PGL2Element (Fq p r))
    (hτ_split : IsSplitInvolution τ)
    (hτ_shares_fixed : ∃ x : Ω (Fq p r), 
      MissingPermutation S x = x ∧ τ • x = x)
    : HammingDistance (MissingPermutation S) (fun x => τ • x) ≥ (p ^ r + 3) / 2 ∧
      (Finset.univ.filter fun x => MissingPermutation S x = τ • x).card ≤ (p ^ r - 1) / 2 := by
  sorry

-- =============================================================================
-- Additional Results from Section 2
-- =============================================================================

/-- 
Lemma 2.1 (Derivative Bound): Let d ∈ F_q[X] have degree at most q - 1, and suppose 
that d' ≠ 0. Then:

    |{x ∈ F_q : d'(x) = 0}| ≤ q - q/p - 1
-/
theorem Lemma2_1_DerivativeBound
    (p : ℕ) (hp : Nat.Prime p) (r : ℕ) (hr : r ≥ 1)
    (d : Polynomial (Fq p r))
    (hdeg : d.natDegree ≤ p ^ r - 1)
    (hd' : d.derivative ≠ 0)
    : (Finset.univ.filter fun x => (Polynomial.eval x d.derivative) = 0).card ≤ 
      p ^ r - (p ^ r) / p - 1 := by
  sorry

/-- 
Lemma 2.2 (Nonidentity): Under the hypotheses of Theorem 1, σ ≠ id.
-/
theorem Lemma2_2_Nonidentity
    (p : ℕ) (hp : Nat.Prime p) (r : ℕ) (hr : r ≥ 1)
    (hq : p ^ r ≥ 5) (hq_odd : Odd (p ^ r))
    (S : Finset (PGL2Element (Fq p r)))
    (hS_admissible : IsAdmissible S)
    (hS_size : S.card = p ^ r)
    : MissingPermutation S ≠ id := by
  sorry

-- =============================================================================
-- Additional Results from Section 3
-- =============================================================================

/-- 
Theorem: If f = 2, then S is collinear.
-/
theorem Theorem3_1_TwoFixedPointsCollinear
    (p : ℕ) (hp : Nat.Prime p) (r : ℕ) (hr : r ≥ 1)
    (hq : p ^ r ≥ 5) (hq_odd : Odd (p ^ r))
    (S : Finset (PGL2Element (Fq p r)))
    (hS_admissible : IsAdmissible S)
    (hS_size : S.card = p ^ r)
    (hf_eq2 : FixedPointCount (MissingPermutation S) = 2)
    : IsCollinear S := by
  sorry

-- =============================================================================
-- Additional Results from Section 4
-- =============================================================================

/-- 
Theorem 4.1 (Hamming Rigidity): Let q ≥ 5 be odd, and let S be admissible of size q, 
with missing permutation σ. Suppose τ ∈ PGL₂(q) \ {1}, and put k = d_H(σ, τ). 
If q > 3k, then:

    σ = τ, S is collinear, f ∈ {0, 2}
-/
theorem Theorem4_1_HammingRigidity
    (p : ℕ) (hp : Nat.Prime p) (r : ℕ) (hr : r ≥ 1)
    (hq : p ^ r ≥ 5) (hq_odd : Odd (p ^ r))
    (S : Finset (PGL2Element (Fq p r)))
    (hS_admissible : IsAdmissible S)
    (hS_size : S.card = p ^ r)
    (τ : PGL2Element (Fq p r))
    (hτ_ne1 : τ ≠ 1)
    (hk : p ^ r > 3 * HammingDistance (MissingPermutation S) (fun x => τ • x))
    : MissingPermutation S = fun x => τ • x ∧
      IsCollinear S ∧
      FixedPointCount (MissingPermutation S) ∈ ({0, 2} : Finset ℕ) := by
  sorry

/-- 
Corollary 4.2: If S is noncollinear, or if f ≥ 4, then:

    d_H(σ, τ) ≥ ⌈q/3⌉
-/
theorem Corollary4_2_HammingGap
    (p : ℕ) (hp : Nat.Prime p) (r : ℕ) (hr : r ≥ 1)
    (hq : p ^ r ≥ 5) (hq_odd : Odd (p ^ r))
    (S : Finset (PGL2Element (Fq p r)))
    (hS_admissible : IsAdmissible S)
    (hS_size : S.card = p ^ r)
    (hS_condition : ¬IsCollinear S ∨ 4 ≤ FixedPointCount (MissingPermutation S))
    (τ : PGL2Element (Fq p r))
    (hτ_ne1 : τ ≠ 1)
    : HammingDistance (MissingPermutation S) (fun x => τ • x) ≥ 
      Nat.ceil ((p ^ r : ℝ) / 3) := by
  sorry

/-- 
Theorem 4.3 (Common Fixed Point): Let q ≥ 7 be odd. Suppose that a split involution 
τ ∈ PGL₂(q) and the missing permutation σ have a common fixed point. If:

    |{x ∈ Ω : σ(x) = τ(x)}| ≥ (q + 1) / 2

then σ = τ, the set S is collinear, and f = 2.
-/
theorem Theorem4_3_CommonFixedPoint
    (p : ℕ) (hp : Nat.Prime p) (r : ℕ) (hr : r ≥ 1)
    (hq : p ^ r ≥ 7) (hq_odd : Odd (p ^ r))
    (S : Finset (PGL2Element (Fq p r)))
    (hS_admissible : IsAdmissible S)
    (hS_size : S.card = p ^ r)
    (τ : PGL2Element (Fq p r))
    (hτ_split : IsSplitInvolution τ)
    (h_common_fixed : ∃ x : Ω (Fq p r), 
      MissingPermutation S x = x ∧ τ • x = x)
    (h_agreement : (Finset.univ.filter fun x => MissingPermutation S x = τ • x).card ≥ 
      (p ^ r + 1) / 2)
    : MissingPermutation S = fun x => τ • x ∧
      IsCollinear S ∧
      FixedPointCount (MissingPermutation S) = 2 := by
  sorry
