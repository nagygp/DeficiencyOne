/-
# Theorem 3: Rigidity with Positive Fixed-Point Gap - Definitions

This file contains the definitions needed for proving Theorem 3 from the paper.

**Theorem 3**: Let q ≥ 7 be odd, and let S be an admissible set of size q.
If f ≥ 4, then every split involution τ ∈ PGL₂(q) sharing a fixed point with σ satisfies:
    d_H(σ, τ) ≥ (q + 3) / 2
    |{x ∈ Ω : σ(x) = τ(x)}| ≤ (q - 1) / 2

This theorem strengthens the rigidity results from Section 4.
-/

import Theorem2.Inequality
import Mathlib.Data.Finset.Card

-- Enable universe polymorphism
set_option autoImplicit false

-- =============================================================================
-- Part 1: Hamming Distance
-- =============================================================================

variable {F : Type*} [Field F] [Fintype F]

/-- 
Hamming distance between two functions on Ω.
-/
def HammingDistance (f g : Ω F → Ω F) : ℕ :=
  (Finset.univ.filter fun x => f x ≠ g x).card

/-- 
Hamming distance notation.
-/
notation "d_H" => HammingDistance

/-- 
Lemma: d_H(f, g) = d_H(g, f).
-/
theorem HammingDistance_symm (f g : Ω F → Ω F) :
    HammingDistance f g = HammingDistance g f := by
  simp [HammingDistance]
  apply Finset.card_congr
  intro x
  simp
  tauto

/-- 
Lemma: d_H(f, f) = 0.
-/
theorem HammingDistance_self (f : Ω F → Ω F) :
    HammingDistance f f = 0 := by
  simp [HammingDistance]

/-- 
Lemma: d_H(f, g) ≤ |Ω| = q + 1.
-/
theorem HammingDistance_bound (f g : Ω F → Ω F) :
    HammingDistance f g ≤ Fintype.card (Ω F) := by
  simp [HammingDistance]
  apply Finset.card_le_card
  exact Finset.filter_subset _ _

-- =============================================================================
-- Part 2: Split Involutions Sharing Fixed Points
-- =============================================================================

variable {S : AdmissibleSet F} {σ : Ω F → Ω F}

/-- 
Definition: A split involution τ shares a fixed point with σ.
-/
def SharesFixedPoint (τ : PGL2Element F) (σ : Ω F → Ω F) : Prop :=
  ∃ x : Ω F, σ x = x ∧ τ ⬬ x = x

/-- 
Definition: The set of split involutions sharing a fixed point with σ.
-/
def SplitInvolutionsSharingFixedPoint (S : AdmissibleSet F) (σ : Ω F → Ω F) :
    Finset (PGL2Element F) :=
  (Finset.univ : Finset (PGL2Element F)).filter (fun τ =>
    IsSplitInvolution τ ∧ SharesFixedPoint τ σ)

-- =============================================================================
-- Part 3: Agreement Set
-- =============================================================================

/-- 
Definition: The agreement set {x ∈ Ω : σ(x) = τ(x)}.
-/
def AgreementSet (σ τ : Ω F → Ω F) : Finset (Ω F) :=
  Finset.univ.filter (fun x => σ x = τ x)

/-- 
Lemma: |AgreementSet σ τ| + d_H(σ, τ) = |Ω| = q + 1.
-/
theorem AgreementSet_card_add_HammingDistance
    (σ τ : Ω F → Ω F) :
    (AgreementSet σ τ).card + HammingDistance σ τ = Fintype.card (Ω F) := by
  
  have : (AgreementSet σ τ) ∪ (Finset.univ.filter fun x => σ x ≠ τ x) = Finset.univ := by
    ext x
    simp [AgreementSet, HammingDistance]
    by_cases h : σ x = τ x
    · left; exact h
    · right; exact h
  
  have h_disjoint : Disjoint (AgreementSet σ τ) 
                                  (Finset.univ.filter fun x => σ x ≠ τ x) := by
    apply Finset.disjoint_filter_filter_neg
    intro x _ h_eq h_ne
    exact h_ne h_eq
  
  have : (AgreementSet σ τ).card + 
         (Finset.univ.filter fun x => σ x ≠ τ x).card = 
         ((AgreementSet σ τ) ∪ (Finset.univ.filter fun x => σ x ≠ τ x)).card := by
    rw [Finset.card_union_of_disjoint h_disjoint]
  
  rw [this, this]
  simp [HammingDistance]

-- =============================================================================
-- Part 4: Theorem 3 Assumptions
-- =============================================================================

/-- 
Structure containing all assumptions for Theorem 3.
-/
structure Theorem3Assumptions where
  -- Field properties
  p : ℕ
  hp : Fact (Nat.Prime p)
  r : ℕ
  hr : Fact (r ≥ 1)
  hF : Fintype.card F = p ^ r
  hF_odd : Characteristic.char F ≠ 2
  hq_ge_7 : p ^ r ≥ 7
  -- Admissible set
  S : AdmissibleSet F
  σ : Ω F → Ω F
  hσ : σ = MissingPermutation S
  -- Fixed point condition
  hf_ge_4 : 4 ≤ FixedPointCount σ

-- =============================================================================
-- Part 5: Two-Cycle Normalization
-- =============================================================================

/-- 
Definition: A two-cycle normalization where σ(0) = ∞ and σ(∞) = 0.

This is used in the proof of Theorem 3.
-/
structure TwoCycleNormalization (S : AdmissibleSet F) (σ : Ω F → Ω F) where
  -- σ(0) = ∞
  σ_0 : σ (Ω.finite 0) = Ω.infinity
  -- σ(∞) = 0
  σ_infty : σ Ω.infinity = Ω.finite 0
  -- σ is the missing permutation
  hσ : σ = MissingPermutation S

/-- 
Lemma: If σ and τ share a fixed point, we can normalize so that
σ(0) = ∞, σ(∞) = 0, and τ(0) = 0, τ(∞) = ∞.

This is used in the proof of Lemma 4.1.
-/
theorem TwoCycleNormalization_exists
    (S : AdmissibleSet F)
    (σ : Ω F → Ω F)
    (τ : PGL2Element F)
    (hτ_split : IsSplitInvolution τ)
    (h_shares : SharesFixedPoint τ σ)
    : ∃ (N : TwoCycleNormalization S σ), 
        τ (Ω.finite 0) = Ω.finite 0 ∧ τ Ω.infinity = Ω.infinity := by
  
  -- The proof involves conjugating σ and τ so that their common fixed point
  -- becomes 0 and ∞ appropriately
  
  -- From h_shares, there exists x such that σ(x) = x and τ(x) = x
  obtain ⟨x, hσ_x, hτ_x⟩ := h_shares
  
  -- We need to conjugate so that x becomes 0 or ∞
  -- and the other fixed point of τ becomes the other point
  
  -- For a split involution τ, there are exactly two fixed points
  -- We can normalize so that these are 0 and ∞
  
  -- Then σ fixes one of these points
  
  -- The normalization gives us σ(0) = ∞, σ(∞) = 0
  -- and τ(0) = 0, τ(∞) = ∞ (or vice versa)
  
  sorry -- This requires PGL₂ conjugation theory

-- =============================================================================
-- Part 6: Summary
-- =============================================================================

/-- 
Phase 12 Summary:

This file provides the definitions needed for Theorem 3:

1. **Hamming Distance**: d_H(f, g) = |{x : f(x) ≠ g(x)}|
   - Symmetric: d_H(f, g) = d_H(g, f)
   - Self: d_H(f, f) = 0
   - Bound: d_H(f, g) ≤ |Ω| = q + 1

2. **Sharing Fixed Points**: SharesFixedPoint τ σ

3. **Agreement Set**: AgreementSet σ τ = {x : σ(x) = τ(x)}
   - |AgreementSet σ τ| + d_H(σ, τ) = q + 1

4. **Two-Cycle Normalization**: σ(0) = ∞, σ(∞) = 0

Next: Phase 13 (Theorem 3 proof implementation)
-/
