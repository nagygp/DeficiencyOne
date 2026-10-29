/-
# Section 4: Rigidity Near a Nonidentity Projectivity

This file contains the proofs from Section 4 of the paper, which proves rigidity near 
a projectivity and then the stronger shared-fixed-point bound of Theorem 3.
-/

import FixedPointsPrimePower.Defs
import FixedPointsPrimePower.MainTheorems
import FixedPointsPrimePower.Section2
import FixedPointsPrimePower.Section3

-- Enable universe polymorphism
set_option autoImplicit false

-- =============================================================================
-- Section 4.1: Normalization at a Two-Cycle
-- =============================================================================

/-- 
Lemma 4.1 (Two-Cycle Normalization): Suppose that σ(0) = ∞ and σ(∞) = 0.
There are b ∈ F_q and nonzero values d(u), u ∈ F_q^×, such that:

    S = {s_∞} ∪ {s_u : u ∈ F_q^×}
    s_∞(X) = b - X
    s_u(X) = u + d(u) / (X - u)

Let D ∈ F_q[X], deg D ≤ q - 1, interpolate these values with the additional value D(0) = 0.
Then:

    D'(0) = -b
    σ(x) = 2x - b - D'(x) for x ∈ F_q^×
    D(σ(x)) / σ(x) = D(x) / x for x ∈ F_q^×
-/
theorem Lemma4_1_RigidityTwoCycle
    (p : ℕ) (hp : Nat.Prime p) (r : ℕ) (hr : r ≥ 1)
    (S : Finset (PGL2Element (Fq p r)))
    (hS_admissible : IsAdmissible S)
    (hS_size : S.card = p ^ r)
    (hσ_two_cycle : NormalizedTwoCycle (MissingPermutation S))
    : ∃ (b : Fq p r) (d : Fq p r → Fq p r) (D : Polynomial (Fq p r)),
        (∀ u ∈ (Finset.univ : Finset (Fq p r)).filter (· ≠ 0), d u ≠ 0) ∧
        D.natDegree ≤ p ^ r - 1 ∧
        Polynomial.eval 0 D = 0 ∧
        Polynomial.eval 0 D.derivative = -b ∧
        (∀ x ∈ (Finset.univ : Finset (Fq p r)).filter (· ≠ 0),
          MissingPermutation S x = 2 * x - b - Polynomial.eval x D.derivative) ∧
        (∀ x ∈ (Finset.univ : Finset (Fq p r)).filter (· ≠ 0),
          Polynomial.eval (MissingPermutation S x) D / MissingPermutation S x = 
          Polynomial.eval x D / x) := by
  sorry

-- =============================================================================
-- Section 4.2: Interpolation Lemma with Small Exceptional Set
-- =============================================================================

/-- 
Lemma 4.2 (Interpolation): Let q be odd, c ∈ F_q^×, and ι(x) = c/x on F_q^×.
Let E ⊆ F_q^× be ι-invariant, with |E| = k. Suppose that F ∈ F_q[X] satisfies:

    deg F ≤ q - 2
    F(0) = 0

and, for every x ∈ F_q^× \ E:

    F(x) + x F'(x) = 0
    F(ι(x)) = F(x)

If q > 3k, then F = 0.
-/
theorem Lemma4_2_RigidityInterpolation
    (p : ℕ) (hp : Nat.Prime p) (r : ℕ) (hr : r ≥ 1)
    (c : Fq p r) (hc : c ≠ 0)
    (E : Finset (Fq p r))
    (hE_invariant : ∀ x, x ∈ E ↔ c / x ∈ E)
    (F : Polynomial (Fq p r))
    (hF_deg : F.natDegree ≤ p ^ r - 2)
    (hF_zero : Polynomial.eval 0 F = 0)
    (hF_diff : ∀ x ∈ (Finset.univ : Finset (Fq p r)).filter (· ≠ 0), x ∉ E →
      Polynomial.eval x F + x * Polynomial.eval x F.derivative = 0)
    (hF_invariant : ∀ x ∈ (Finset.univ : Finset (Fq p r)).filter (· ≠ 0), x ∉ E →
      Polynomial.eval (c / x) F = Polynomial.eval x F)
    (hq_gt : p ^ r > 3 * E.card)
    : F = 0 := by
  sorry

-- =============================================================================
-- Section 4.3: Hamming Rigidity
-- =============================================================================

/-- 
Proof of Theorem 4.1: Hamming Rigidity

Let q ≥ 5 be odd, and let S be admissible of size q, with missing permutation σ.
Suppose τ ∈ PGL₂(q) \ {1}, and put k = d_H(σ, τ). If q > 3k, then:

    σ = τ, S is collinear, f ∈ {0, 2}
-/
theorem Theorem4_1_HammingRigidity_Proof
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
  -- If k = 0, then τ = σ is already a nonidentity involution
  by_cases hk_zero : HammingDistance (MissingPermutation S) (fun x => τ • x) = 0
  · -- In this case, τ = σ
    have hτ_eq_σ : ∀ x, τ • x = MissingPermutation S x := by
      sorry
    -- Since τ is a nonidentity element of PGL₂, it's an involution
    -- A nonidentity projective involution has zero or two fixed points
    sorry
  
  -- If k ≥ 1, at least q + 1 - 2k ≥ 3 points x are agreement points
  -- for which τ(x) is also an agreement point
  
  -- At each of them, τ²(x) = σ(τ(x)) = σ²(x) = x
  -- A nonidentity projectivity has at most two fixed points, so τ² = 1
  
  -- There are more than two agreement points, while τ ≠ 1 has at most two fixed points
  -- Hence σ and τ share a nontrivial two-cycle
  
  -- Conjugate it to {0, ∞}, so that τ(X) = c/X, c ≠ 0
  -- Use Lemma 4.1
  
  -- The disagreement set E is contained in F_q^× and is τ-invariant
  
  -- Define D₀ = X² - bX + cX^{q-1}, F = (D - D₀) / X
  -- The origin identities give deg F ≤ q - 2, F(0) = 0
  
  -- On F_q^×, the function D₀(x)/x = x - b + c/x is τ-invariant
  -- Equation (4.3), applied at agreement points, therefore gives F(c/x) = F(x) outside E
  
  -- Lemma 4.2 implies F = 0
  
  -- Consequently D = D₀, and the points of S are:
  -- [u : -bu + c : 1] for u ≠ 0, [1 : -b : 0]
  -- They all lie on the line V + bU - cW = 0
  
  -- Equation (4.2) gives σ(x) = c/x for x ≠ 0, and the normalized two-cycle gives equality at 0, ∞
  -- Thus σ = τ
  
  -- Finally, a nonidentity projective involution has zero or two fixed points
  
  sorry

-- =============================================================================
-- Section 4.4: Corollary 4.2
-- =============================================================================

/-- 
Proof of Corollary 4.2: Hamming Gap

If S is noncollinear, or if f ≥ 4, then:

    d_H(σ, τ) ≥ ⌈q/3⌉
-/
theorem Corollary4_2_HammingGap_Proof
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
  -- If d_H(σ, τ) < ⌈q/3⌉, then q > 3 d_H(σ, τ)
  -- By Theorem 4.1, this would imply S is collinear and f ∈ {0, 2}
  -- But this contradicts hS_condition
  
  sorry

-- =============================================================================
-- Section 4.5: Stronger Bound from Common Fixed Point
-- =============================================================================

/-- 
Proof of Theorem 4.3: Common Fixed Point

Let q ≥ 7 be odd. Suppose that a split involution τ ∈ PGL₂(q) and the missing 
permutation σ have a common fixed point. If:

    |{x ∈ Ω : σ(x) = τ(x)}| ≥ (q + 1) / 2

then σ = τ, the set S is collinear, and f = 2.
-/
theorem Theorem4_3_CommonFixedPoint_Proof
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
  -- Normalize the common fixed point to ∞, and the other fixed point of τ to 0
  -- Then τ(X) = -X, σ(∞) = ∞
  
  -- Use the covering normalization, and denote its reduced interpolating polynomial by D
  -- Thus σ(x) = x - D'(x), D(σ(x)) = D(x) for x ∈ F_q
  
  -- Let E be the disagreement set and k = |E|
  -- Since ∞ is an agreement point, E ⊆ F_q
  -- Also E = -E, since σ and τ are involutions
  -- The hypothesis gives k ≤ (q + 1) / 2
  
  -- The odd part O(X) = D(X) - D(-X) has degree at most q - 2
  -- For x ∉ E, both x and -x are agreement points, so D(x) = D(-x), D'(x) = 2x, D'(-x) = -2x
  -- Hence O(x) = O'(x) = 0
  -- There are q - k such distinct double roots, and 2(q - k) ≥ q - 1 > q - 2
  -- Thus O = 0: the polynomial D is even
  
  -- Represent s_u by P_u = [u : D(u) - u² : 1], and represent τ by T = [1 : 0 : 0]
  -- For u ≠ 0, evenness of D gives:
  -- Δ(P_u, P_{-u}) = 16u²(u² - D(u)), Δ(T, P_u) = 4(u² - D(u))
  -- Their ratio is the nonzero square 4u²
  -- Since s_u and s_{-u} are distinct compatible members of S, the involution τ is compatible
  -- with every s_u, u ≠ 0
  
  -- If σ(x) ≠ τ(x), the value τ(x) is attained by a member of S
  -- That member can only be s_0
  -- Conversely, s_0(x) = τ(x) forces disagreement
  -- Thus E = {x : s_0(x) = τ(x)} = {x ∈ F_q : x² = -d(0)}
  -- As d(0) ≠ 0, this set has size zero or two
  
  -- We now have q > 3k, since q ≥ 7
  -- Theorem 4.1 completes the proof
  
  sorry

-- =============================================================================
-- Section 4.6: Proof of Theorem 3
-- =============================================================================

/-- 
Proof of Theorem 3: Rigidity with Positive Fixed-Point Gap

Let q ≥ 7 be odd, and let S be an admissible set of size q.
If f ≥ 4, then every split involution τ ∈ PGL₂(q) sharing a fixed point with σ satisfies:

    d_H(σ, τ) ≥ (q + 3) / 2
    |{x ∈ Ω : σ(x) = τ(x)}| ≤ (q - 1) / 2
-/
theorem Theorem3_RigidityPositiveFixedGap_Proof
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
  -- If σ and τ agreed on at least (q + 1) / 2 points, then by Theorem 4.3,
  -- we would have f = 2, contrary to f ≥ 4
  
  -- Thus they agree on at most (q - 1) / 2 points
  
  -- Since |Ω| = q + 1, their Hamming distance is at least (q + 3) / 2
  
  sorry

-- =============================================================================
-- Section 4.7: Remarks
-- =============================================================================

/-- 
Remark: A genuine exception at q = 5

Over F₅, take D(X) = X⁴ + 3X² + 4, with (d(0), d(1), d(2), d(3), d(4)) = (4, 3, 2, 2, 3).
The corresponding five involutions are admissible. Their missing permutation fixes 0, 1, -1, ∞,
and interchanges 2, -2. It therefore has f = 4 and distance two from τ(X) = -X, which shares
the fixed points 0, ∞. The set is noncollinear.

Thus the small-field restriction in Theorem 4.3 cannot simply be omitted.
-/

/-- 
Remark: Scope and the identity comparator

Theorem 4.1 compares σ with a nonidentity projectivity and applies for arbitrary f.
Its normalization needs a common nontrivial two-cycle, which is guaranteed by its agreement
hypothesis. The identity projectivity supplies no such cycle.

In particular, comparison with the identity, whose Hamming distance from σ is q + 1 - f,
is not covered by that theorem. The results in this section do not by themselves improve the
unconditional upper bound (1.1), and do not establish an unconditional bounded-degree cover
for f = 0.
-/
