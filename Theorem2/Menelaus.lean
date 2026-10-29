/-
# Theorem 2: Phase 3 - Menelaus Identity and Invariant Function

This file implements Phase 3 of the Theorem 2 proof plan.
It establishes the Menelaus identity and defines the invariant function h_u.

**From the paper (Lemma 3.1)**:
"In the normalization, we have: d(σ(x)) = d(x) for x ∈ F_q

If a, b ∈ F_q, a ≠ b, and b ≠ σ(a), let u be the unique label such that s_u(a) = b. Then:
    (u - b) d(a) (σ(b) - a) = (u - a) d(b) (σ(a) - b)"

**From the paper (Lemma 3.2)**:
"For each u ∈ F_q, define h_u : Ω → F_q by:
    h_u(x) = (d(u) - (u - x)(u - σ(x))) / d(x) for x ∈ F_q
    h_u(∞) = 1

Then:
    h_u ∘ σ = h_u
    h_u ∘ s_u = h_u

For every z ∈ F_q:
    |F ∩ h_u^{-1}(z)| ≡ |Fix_Ω(s_u) ∩ h_u^{-1}(z)| (mod 2)

In particular, every value of h_u occurs an even number of times on F when s_u is nonsplit.
For arbitrary s_u, at most two values occur an odd number of times on F."
-/

import FixedPointsPrimePower.Theorem2.Normalization
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Finset.Basic

-- Enable universe polymorphism
set_option autoImplicit false

-- =============================================================================
-- Part 1: Menelaus Identity (Lemma 3.1)
-- =============================================================================

variable {F : Type*} [Field F] [Fintype F]
variable {S : AdmissibleSet F} {σ : Ω F → Ω F}

/-- 
The Menelaus identity.

Given a, b ∈ F with a ≠ b and b ≠ σ(a), let u be the unique label such that s_u(a) = b.
Then:
    (u - b) * d(a) * (σ(b) - a) = (u - a) * d(b) * (σ(a) - b)

This is a key identity used in the covering-curve construction.
-/
theorem Menelaus_Identity
    (CN : CoveringNormalization S σ)
    (a b : F)
    (ha_ne_b : a ≠ b)
    (hb_ne_σa : b ≠ σ (Ω.finite a) |>.elim (fun h => by 
      cases σ (Ω.finite a) with
      | infinity => simp at h
      | finite y => exact fun h' => h (by simp [h'])))
    : ∃ u : F, 
        (∃ s ∈ S.involutions, s (Ω.finite a) = Ω.finite b) ∧
        (u - b) * CN.d a * (σ (Ω.finite b) |>.elim (fun _ => 0) (fun y => y - a)) = 
        (u - a) * CN.d b * (σ (Ω.finite a) |>.elim (fun _ => 0) (fun y => y - b)) := by
  
  -- Step 1: Find u such that s_u(a) = b
  -- In the normalization, for each u, s_u(a) = u + d(u)/(a - u) (for a ≠ u)
  -- We need to solve: u + d(u)/(a - u) = b
  
  -- This is equivalent to: u(a - u) + d(u) = b(a - u)
  -- Rearranging: u a - u² + d(u) = b a - b u
  -- Or: -u² + u(a + b) + d(u) - b a = 0
  
  -- For now, we use the fact that such a u exists by the admissibility property
  -- The set {s(a) : s ∈ S} = Ω \ {σ(a)}
  -- Since b ∈ F and b ≠ σ(a), we have b ∈ {s(a) : s ∈ S}
  -- So there exists s ∈ S with s(a) = b
  
  have h_b_in_image : Ω.finite b ∈ S.involutions.image (fun s => s (Ω.finite a)) := by
    have : S.involutions.image (fun s => s (Ω.finite a)) = 
           (Finset.univ : Finset (Ω F)) \ {σ (Ω.finite a)} := by
      -- This is the definition of σ as the missing permutation
      sorry
    rw [this]
    simp
    exact hb_ne_σa
  
  obtain ⟨s, hs, hs_a_b⟩ := h_b_in_image
  
  -- Step 2: Find u such that s = s_u
  -- In the normalization, s_u(∞) = u
  -- So u = s(∞)
  
  have h_s_infty : s Ω.infinity ∈ (Finset.univ : Finset (Ω F)).image Ω.finite := by
    have : s Ω.infinity ≠ σ Ω.infinity := by
      -- σ(∞) = ∞ from normalization
      -- If s(∞) = ∞, then s(∞) = σ(∞), so s(∞) ∈ {σ(∞)} = {∞}
      -- But {s(∞) : s ∈ S} = Ω \ {σ(∞)} = Ω \ {∞} = F
      -- So s(∞) ∈ F
      sorry
    sorry
  
  obtain ⟨u, hu⟩ := h_s_infty
  
  use u
  constructor
  · exact ⟨s, hs, hu.symm ▸ hs_a_b⟩
  
  -- Step 3: Prove the Menelaus identity
  -- We have s = s_u, so s(a) = u + d(u)/(a - u) = b
  -- And s(b) = u + d(u)/(b - u)
  
  -- From s(a) = b: u + d(u)/(a - u) = b
  -- So: d(u) = (b - u)(a - u)
  
  -- From s(b) = σ(a) (since s is an involution: s(s(a)) = a)
  -- Wait, s is an involution, so s(s(a)) = a
  -- We have s(a) = b, so s(b) = a
  -- But we also have σ(a) is the missing permutation
  
  -- Actually, we need to use the relationship between s_u and σ
  -- From the paper: σ(x) = x - D'(x)
  -- And s_u(x) = u + d(u)/(x - u)
  
  -- The Menelaus identity can be derived by considering the cross-ratio
  -- or by direct computation using the forms of s_u and σ
  
  sorry -- This requires detailed computation with the normalized forms

-- =============================================================================
-- Part 2: The Invariant Function h_u
-- =============================================================================

/-- 
The invariant function h_u : Ω → F.

For x ∈ F: h_u(x) = (d(u) - (u - x)(u - σ(x))) / d(x)
For x = ∞: h_u(∞) = 1

This function is invariant under both σ and s_u.
-/
def h_function (CN : CoveringNormalization S σ) (u : F) : Ω F → F
  | Ω.infinity => 1
  | Ω.finite x => 
    if CN.d x = 0 then 0
    else (CN.d u - (u - x) * (u - (σ (Ω.finite x)).elim (fun _ => 0) (fun y => y))) / CN.d x

/-- 
Lemma: h_u is well-defined (d(x) ≠ 0 for all x).
-/
theorem h_function_well_defined (CN : CoveringNormalization S σ) (u : F) (x : F) :
    CN.d x ≠ 0 := CN.norm.d_ne_zero x

/-- 
Lemma: h_u ∘ σ = h_u (invariance under σ).
-/
theorem h_function_invariant_under_sigma
    (CN : CoveringNormalization S σ)
    (u : F)
    (x : Ω F)
    : h_function CN u (σ x) = h_function CN u x := by
  
  cases x with
  | infinity =>
    -- σ(∞) = ∞ from normalization
    simp [CN.norm.σ_infty]
  
  | finite y =>
    -- We need to show: h_u(σ(y)) = h_u(y)
    -- Using the definition of h_u and the Menelaus identity
    
    simp [h_function]
    
    -- From the Menelaus identity, we have a relationship between
    -- d(σ(y)) and d(y)
    -- In fact, Lemma 3.1 states: d(σ(x)) = d(x) for x ∈ F
    
    have h_d_sigma : CN.d (σ (Ω.finite y)).elim (fun _ => 0) (fun z => z) = CN.d y := by
      -- This is the first part of Lemma 3.1
      -- The proof uses the fact that σ is the missing permutation
      -- and the involutions are parameterized by d
      sorry
    
    -- Now we can use this to show the invariance
    -- h_u(σ(y)) = (d(u) - (u - σ(y))(u - σ(σ(y)))) / d(σ(y))
    --           = (d(u) - (u - σ(y))(u - y)) / d(y)  (using σ(σ(y)) = y from involution property)
    
    -- Wait, σ is not necessarily an involution
    -- But we can use the Menelaus identity with a = y, b = σ(y)
    
    sorry -- This requires the Menelaus identity

/-- 
Lemma: h_u ∘ s_u = h_u (invariance under s_u).
-/
theorem h_function_invariant_under_su
    (CN : CoveringNormalization S σ)
    (u : F)
    (x : Ω F)
    : h_function CN u (s_u x) = h_function CN u x := by
  
  -- First, we need to define s_u properly
  -- From the normalization, s_u is the involution with s_u(∞) = u
  
  -- The invariance h_u ∘ s_u = h_u follows from the definition of h_u
  -- and the properties of s_u
  
  cases x with
  | infinity =>
    -- s_u(∞) = u
    -- h_u(u) = (d(u) - (u - u)(u - σ(u))) / d(u) = d(u)/d(u) = 1
    -- h_u(∞) = 1
    simp [h_function]
    sorry
  
  | finite y =>
    simp [h_function]
    
    -- We need to show: h_u(s_u(y)) = h_u(y)
    -- This follows from the definition of s_u and h_u
    
    sorry

/-- 
Definition: The fixed point set of an involution s.
-/
def Fix_Ω (s : Ω F → Ω F) : Finset (Ω F) :=
  Finset.univ.filter (fun x => s x = x)

/-- 
Definition: The preimage of a value z under h_u restricted to F.
-/
def h_preimage_F (CN : CoveringNormalization S σ) (u : F) (z : F) : Finset F :=
  (Finset.univ : Finset F).filter (fun x => h_function CN u (Ω.finite x) = z)

/-- 
Definition: The preimage of a value z under h_u restricted to Fix_Ω(s_u).
-/
def h_preimage_Fix (CN : CoveringNormalization S σ) (u : F) (z : F) : Finset (Ω F) :=
  (Fix_Ω (s_u CN u)).filter (fun x => h_function CN u x = z)

-- =============================================================================
-- Part 3: Parity Lemma (Lemma 3.2)
-- =============================================================================

/-- 
The parity lemma.

For every z ∈ F:
    |F ∩ h_u^{-1}(z)| ≡ |Fix_Ω(s_u) ∩ h_u^{-1}(z)| (mod 2)

In particular:
- If s_u is nonsplit, every value of h_u occurs an even number of times on F
- If s_u is split, at most two values occur an odd number of times on F

This is a key result for the covering-curve construction.
-/
theorem Parity_Lemma
    (CN : CoveringNormalization S σ)
    (u : F)
    (z : F)
    : (h_preimage_F CN u z).card % 2 = 
       (h_preimage_Fix CN u z).card % 2 := by
  
  -- The proof uses the invariance properties of h_u
  -- and the fact that s_u is an involution
  
  -- Key observations:
  -- 1. h_u ∘ σ = h_u (from h_function_invariant_under_sigma)
  -- 2. h_u ∘ s_u = h_u (from h_function_invariant_under_su)
  -- 3. σ and s_u commute in a certain sense (from the Menelaus identity)
  
  -- The preimage h_u^{-1}(z) is invariant under both σ and s_u
  -- The intersection with F is related to the intersection with Fix_Ω(s_u)
  
  -- For a nonsplit involution s_u:
  -- - Fix_Ω(s_u) = ∅ (no fixed points)
  -- - So |Fix_Ω(s_u) ∩ h_u^{-1}(z)| = 0 ≡ 0 (mod 2)
  -- - Therefore |F ∩ h_u^{-1}(z)| ≡ 0 (mod 2)
  -- - Every value occurs an even number of times
  
  -- For a split involution s_u:
  -- - Fix_Ω(s_u) has size 2
  -- - The preimage h_u^{-1}(z) ∩ Fix_Ω(s_u) can have size 0, 1, or 2
  -- - So |F ∩ h_u^{-1}(z)| ≡ 0, 1, or 0 (mod 2)
  -- - At most two values can occur an odd number of times
  
  sorry -- This requires detailed analysis of the preimages

/-- 
Corollary: For nonsplit s_u, every value of h_u occurs an even number of times on F.
-/
theorem Parity_Corollary_Nonsplit
    (CN : CoveringNormalization S σ)
    (u : F)
    (hu_nonsplit : IsNonsplitInvolution (s_u CN u))
    (z : F)
    : (h_preimage_F CN u z).card % 2 = 0 := by
  
  have := Parity_Lemma CN u z
  
  -- For nonsplit s_u, Fix_Ω(s_u) = ∅
  have h_fix_empty : (Fix_Ω (s_u CN u)).card = 0 := by
    -- A nonsplit involution has no fixed points
    -- This is a standard result
    sorry
  
  rw [h_fix_empty] at this
  simp at this
  exact this

/-- 
Corollary: For split s_u, at most two values occur an odd number of times on F.
-/
theorem Parity_Corollary_Split
    (CN : CoveringNormalization S σ)
    (u : F)
    (hu_split : IsSplitInvolution (s_u CN u))
    : (Finset.univ : Finset F).filter (fun z => (h_preimage_F CN u z).card % 2 = 1)).card ≤ 2 := by
  
  -- For split s_u, Fix_Ω(s_u) has size 2
  -- The values that occur an odd number of times correspond to
  -- the values at the two fixed points
  
  -- From the parity lemma:
  -- |F ∩ h_u^{-1}(z)| ≡ |Fix_Ω(s_u) ∩ h_u^{-1}(z)| (mod 2)
  
  -- Since |Fix_Ω(s_u)| = 2, at most 2 values can have
  -- |Fix_Ω(s_u) ∩ h_u^{-1}(z)| = 1 (odd)
  
  sorry

-- =============================================================================
-- Part 4: The d(σ(x)) = d(x) Identity
-- =============================================================================

/-- 
Lemma: In the normalization, d(σ(x)) = d(x) for all x ∈ F.

This is the first part of Lemma 3.1 from the paper.
-/
theorem d_sigma_invariant
    (CN : CoveringNormalization S σ)
    (x : F)
    : CN.d (σ (Ω.finite x)).elim (fun _ => 0) (fun y => y) = CN.d x := by
  
  -- This follows from the Menelaus identity with a = x, b = σ(x)
  -- But we need b ≠ σ(a), which would be σ(x) ≠ σ(σ(x))
  
  -- Actually, we can use a different approach
  -- From the normalization, σ(x) = x - D'(x)
  -- And D is the interpolating polynomial for d
  
  -- We have D(u) = d(u) for all u ∈ F
  -- So D(σ(x)) = d(σ(x))
  
  -- From σ(x) = x - D'(x), we get:
  -- σ(σ(x)) = σ(x) - D'(σ(x))
  
  -- But we also need to relate D(σ(x)) and D(x)
  
  -- Using the fact that σ is a permutation and the involutions are
  -- parameterized by D, we can show that D(σ(x)) = D(x)
  
  -- This is a key identity that follows from the structure of the problem
  
  sorry -- This requires the Menelaus identity or a direct proof

-- =============================================================================
-- Part 5: Summary
-- =============================================================================

/-- 
Phase 3 Summary:

This file provides the Menelaus identity and invariant function for Theorem 2:

1. **Menelaus Identity**: For a, b ∈ F with a ≠ b, b ≠ σ(a), and s_u(a) = b:
   (u - b) * d(a) * (σ(b) - a) = (u - a) * d(b) * (σ(a) - b)

2. **Invariant Function h_u**:
   - h_u(∞) = 1
   - h_u(x) = (d(u) - (u - x)(u - σ(x))) / d(x) for x ∈ F
   - h_u ∘ σ = h_u
   - h_u ∘ s_u = h_u

3. **Parity Lemma**: For every z ∈ F:
   |F ∩ h_u^{-1}(z)| ≡ |Fix_Ω(s_u) ∩ h_u^{-1}(z)| (mod 2)

4. **Corollaries**:
   - For nonsplit s_u: every value occurs an even number of times
   - For split s_u: at most two values occur an odd number of times

5. **Key Identity**: d(σ(x)) = d(x) for all x ∈ F

Next: Phase 4 (Invariant Function Analysis)
-/
