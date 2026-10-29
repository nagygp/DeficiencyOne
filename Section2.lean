/-
# Section 2: The Fixed-Point Bound

This file contains the proofs from Section 2 of the paper, which derives the fixed-point 
bound from an interpolating polynomial and its derivative.
-/

import Defs
import MainTheorems

-- Enable universe polymorphism
set_option autoImplicit false

-- =============================================================================
-- Section 2.1: Derivative Bound Lemma
-- =============================================================================

/-- 
Proof of Lemma 2.1: Derivative Bound

Let d ∈ F_q[X] have degree at most q - 1, and suppose that d' ≠ 0. Then:
    |{x ∈ F_q : d'(x) = 0}| ≤ q - q/p - 1

The proof uses Frobenius maps and root bounds for polynomials.
-/
theorem Lemma2_1_DerivativeBound_Proof
    (p : ℕ) (hp : Nat.Prime p) (r : ℕ) (hr : r ≥ 1)
    (d : Polynomial (Fq p r))
    (hdeg : d.natDegree ≤ p ^ r - 1)
    (hd' : d.derivative ≠ 0)
    : (Finset.univ.filter fun x => (Polynomial.eval x d.derivative) = 0).card ≤ 
      p ^ r - (p ^ r) / p - 1 := by
  -- Put h = q/p = p^(r-1) and g = d'
  let h := p ^ (r - 1)
  let g := d.derivative
  
  -- A derivative has zero coefficient at every exponent congruent to p-1 mod p
  -- Since deg g ≤ q-2, we may write:
  -- g(X) = Σ_{a=0}^{h-1} Σ_{b=0}^{p-2} c_{ab} X^{ap+b}
  
  -- Raising to the h-th power is a Frobenius map
  -- For x ∈ F_q, g(x)^h = Σ_{a,b} c_{ab}^h x^{a+bh} =: R(x)
  
  -- The integers a+bh in the indicated ranges are pairwise distinct
  -- Therefore g ≠ 0 implies R ≠ 0
  
  -- deg R ≤ (h-1) + (p-2)h = q - h - 1
  -- The functions g and R have the same zero set in F_q
  -- The usual root bound for the nonzero polynomial R proves the claim
  
  sorry

-- =============================================================================
-- Section 2.2: Nonidentity Lemma
-- =============================================================================

/-- 
Proof of Lemma 2.2: Nonidentity

Under the hypotheses of Theorem 1, σ ≠ id.

The proof uses Eberhard's theorem on sharply transitive sets.
-/
theorem Lemma2_2_Nonidentity_Proof
    (p : ℕ) (hp : Nat.Prime p) (r : ℕ) (hr : r ≥ 1)
    (hq : p ^ r ≥ 5) (hq_odd : Odd (p ^ r))
    (S : Finset (PGL2Element (Fq p r)))
    (hS_admissible : IsAdmissible S)
    (hS_size : S.card = p ^ r)
    : MissingPermutation S ≠ id := by
  -- Suppose σ = id
  by_contra hσ_id
  
  -- Equation (1) shows that S ∪ {1} is sharply transitive on Ω
  -- By Eberhard's theorem, H = S ∪ {1} is a subgroup of PGL₂(q)
  
  -- All nonidentity elements of H have order 2, so H is an elementary abelian 2-group
  -- of order q + 1
  
  -- An elementary abelian 2-subgroup of PGL₂(q) has order at most 4 when q is odd
  -- This gives q + 1 ≤ 4, contrary to q ≥ 5
  
  sorry

-- =============================================================================
-- Section 2.3: Proof of Theorem 1 (Main Theorem)
-- =============================================================================

/-- 
Proof of Theorem 1: Fixed Point Bound

Let q = p^r ≥ 5 be odd, and let S ⊆ PGL₂(q) be an admissible set of size q. 
Then its missing permutation satisfies f ≤ q - q/p.

The proof uses the interpolating polynomial and its derivative.
-/
theorem Theorem1_FixedPointBound_Proof
    (p : ℕ) (hp : Nat.Prime p) (r : ℕ) (hr : r ≥ 1)
    (hq : p ^ r ≥ 5) (hq_odd : Odd (p ^ r))
    (S : Finset (PGL2Element (Fq p r)))
    (hS_admissible : IsAdmissible S)
    (hS_size : S.card = p ^ r)
    : FixedPointCount (MissingPermutation S) ≤ p ^ r - (p ^ r) / p := by
  -- If f = 0, the result is immediate
  by_cases hf_zero : FixedPointCount (MissingPermutation S) = 0
  · simp [hf_zero]
    omega
  
  -- Otherwise, conjugate S in PGL₂(q) so that one fixed point of σ becomes ∞
  -- We may assume σ(∞) = ∞
  
  -- By equation (1), the values s(∞), s ∈ S, run through F_q
  -- Label the corresponding involutions by s_u, where s_u(∞) = u
  
  -- Since s_u does not fix ∞, its matrix can be normalized to have lower-left entry one
  -- In odd characteristic, a matrix representing a nonidentity projective involution has trace zero
  -- Consequently:
  -- s_u = [[u, d(u) - u²], [1, -u]]
  -- s_u(X) = u + d(u) / (X - u), d(u) ≠ 0
  
  -- Let d(X) be the unique polynomial of degree at most q - 1 interpolating these values
  let d_poly : Polynomial (Fq p r) := sorry
  
  -- We verify the derivative identity: σ(x) = x - d'(x) for x ∈ F_q
  -- This follows from Lagrange interpolation and differentiation
  
  -- Lemma 2.2 implies that d' ≠ 0
  -- We may therefore apply Lemma 2.1
  
  -- There is one fixed point at infinity, and the finite fixed points are exactly the zeros of d'
  -- Hence f = 1 + |{x ∈ F_q : d'(x) = 0}| ≤ 1 + (q - q/p - 1) = q - q/p
  
  sorry

-- =============================================================================
-- Section 2.4: Remarks
-- =============================================================================

/-- 
Remark: For prime q, the bound is f ≤ q - 1. For a proper prime power it is strictly stronger.
The proof does not require a low-degree hypothesis such as deg d ≤ (q-1)/2.
-/

/-- 
Remark: The restriction q ≥ 5 is necessary. In its natural action on four points,
PGL₂(3) ≅ S₄ contains a regular Klein four subgroup. Its three nonidentity elements are
involutions, and the product of any two distinct ones is the third, which is fixed-point-free.
They form an admissible set of size three whose missing permutation is the identity.
Thus f = 4, whereas q - q/p = 2.
-/
