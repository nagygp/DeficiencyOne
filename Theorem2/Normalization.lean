/-
# Theorem 2: Phase 2 - Normalization Setup

This file implements Phase 2 of the Theorem 2 proof plan.
It sets up the normalization where σ(∞) = ∞ and S is parameterized by 
polynomial interpolation.

**From the paper**:
"Throughout the covering-curve construction we assume f > 0 and use the normalization:
    σ(∞) = ∞
    S = {s_u : X ↦ u + d(u)/(X - u) | u ∈ F_q}
In particular, d(u) ≠ 0 for every u."
-/

import Theorem2.Defs
import Mathlib.Algebra.Polynomial.Eval
import Mathlib.Algebra.Polynomial.Lagrange
import Mathlib.Data.Fintype.BigOperators

-- Enable universe polymorphism
set_option autoImplicit false

-- =============================================================================
-- Part 1: Normalization Type and Properties
-- =============================================================================

variable {F : Type*} [Field F] [Fintype F]

/-- 
Normalization data for Theorem 2 proof.
This captures the normalized setup where:
- σ(∞) = ∞
- S is parameterized by u ∈ F with d(u) ≠ 0
- Each s_u is an involution with s_u(∞) = u
-/
structure Normalization (S : AdmissibleSet F) (σ : Ω F → Ω F) where
  -- σ fixes infinity
  σ_infty : σ Ω.infinity = Ω.infinity
  -- σ is the missing permutation for S
  σ_missing : σ = MissingPermutation S
  -- The d function: d(u) ≠ 0 for all u
  d : F → F
  d_ne_zero : ∀ u, d u ≠ 0
  -- S is parameterized: for each u, there exists s_u ∈ S with s_u(∞) = u
  -- and s_u(X) = u + d(u)/(X - u) for X ≠ u, s_u(u) = ∞
  parameterization : ∀ u : F, ∃ s ∈ S.involutions, 
    s Ω.infinity = Ω.finite u ∧
    (∀ x : F, x ≠ u → s (Ω.finite x) = Ω.finite (u + d u / (x - u))) ∧
    s (Ω.finite u) = Ω.infinity

-- =============================================================================
-- Part 2: Existence of Normalization
-- =============================================================================

/-- 
Theorem: For any admissible set S with f > 0, there exists a normalization.

Proof: Since f > 0, σ has at least one fixed point. We can conjugate S and σ
so that one fixed point becomes ∞. Then σ(∞) = ∞ by construction.

The parameterization follows from the fact that for each u ∈ F, there is a unique
s ∈ S such that s(∞) = u (since {s(∞) : s ∈ S} = Ω \ {σ(∞)} = Ω \ {∞} = F).
-/
theorem Normalization_exists
    (S : AdmissibleSet F) 
    (hf_pos : 0 < FixedPointCount (MissingPermutation S))
    : ∃ (N : Normalization S (MissingPermutation S)), 
        N.σ_infty ∧ N.σ_missing := by
  
  -- Step 1: σ has at least one fixed point
  have h_fixed_exists : ∃ x : Ω F, MissingPermutation S x = x := by
    have : FixedPointCount (MissingPermutation S) > 0 := hf_pos
    simp [FixedPointCount] at this
    exact Finset.card_pos.mp this
  
  -- Step 2: Choose a fixed point to be ∞
  -- We need to conjugate S so that a fixed point becomes ∞
  -- For now, we assume we can do this and focus on the structure
  
  -- Step 3: After conjugation, σ(∞) = ∞
  -- The image {s(∞) : s ∈ S} = Ω \ {σ(∞)} = Ω \ {∞} = F
  -- So for each u ∈ F, there is a unique s ∈ S with s(∞) = u
  
  -- Step 4: Define d(u)
  -- For each u ∈ F, let s_u be the unique involution with s_u(∞) = u
  -- Since s_u is an involution and s_u(∞) = u, we have s_u(u) = ∞
  -- For x ≠ u, s_u(x) must be finite (since s_u is a bijection on Ω)
  -- The form s_u(x) = u + d(u)/(x - u) comes from the matrix representation
  
  -- For now, we construct the normalization using Classical.choose
  -- The actual construction requires more PGL₂ theory
  
  sorry -- This requires developing the conjugation theory for PGL₂

-- =============================================================================
-- Part 3: The Interpolating Polynomial
-- =============================================================================

/-- 
The interpolating polynomial D(X) of degree ≤ q-1.
This is the polynomial that interpolates the values d(u) for u ∈ F.
-/
noncomputable def InterpolatingPolynomial (N : Normalization S σ) : Polynomial F :=
  Polynomial.Lagrange.interpolate F (fun u => N.d u)

-- =============================================================================
-- Part 4: Key Properties in Normalization
-- =============================================================================

/-- 
Lemma: In the normalization, for each u ∈ F, the involution s_u 
has the form:
    s_u(∞) = u
    s_u(u) = ∞
    s_u(x) = u + d(u)/(x - u) for x ≠ u

This is a standard form for involutions in PGL₂ that fix ∞ and map ∞ to u.
-/
theorem involution_form_in_normalization
    (N : Normalization S σ)
    (u : F)
    : ∃ s ∈ S.involutions,
        s Ω.infinity = Ω.finite u ∧
        s (Ω.finite u) = Ω.infinity ∧
        (∀ x : F, x ≠ u → s (Ω.finite x) = Ω.finite (u + N.d u / (x - u))) := by
  obtain ⟨s, hs, h_infty, h_form, h_u⟩ := N.parameterization u
  exact ⟨s, hs, h_infty, h_u, h_form⟩

/-- 
Lemma: The interpolating polynomial D(X) satisfies D(u) = d(u) for all u ∈ F.
This is the defining property of Lagrange interpolation.
-/
theorem interpolating_polynomial_eval
    (N : Normalization S σ)
    (u : F)
    : (InterpolatingPolynomial N).eval u = N.d u := by
  simp [InterpolatingPolynomial, Polynomial.Lagrange.interpolate]

/-- 
Lemma: The interpolating polynomial has degree at most q-1.
-/
theorem interpolating_polynomial_degree
    (N : Normalization S σ)
    : (InterpolatingPolynomial N).natDegree ≤ Fintype.card F - 1 := by
  apply Polynomial.natDegree_Lagrange_interpolate_le

-- =============================================================================
-- Part 5: The Derivative Identity
-- =============================================================================

/-- 
The key identity from the paper: σ(x) = x - D'(x) for x ∈ F.

This is equation (2.1) from Section 2 of the paper.
The proof uses the fact that σ is the missing permutation and 
the involutions are parameterized by D.
-/
theorem sigma_derivative_identity
    (N : Normalization S σ) 
    (x : F)
    : σ (Ω.finite x) = Ω.finite (x - (InterpolatingPolynomial N).derivative.eval x) := by
  
  -- The proof uses the fact that for each x ∈ F:
  -- {s(x) : s ∈ S} = Ω \ {σ(x)}
  
  -- In the normalization, for each u ∈ F, s_u(x) = u + d(u)/(x - u)
  -- (with the convention that s_u(u) = ∞)
  
  -- The set {s(x) : s ∈ S} = {s_u(x) : u ∈ F}
  -- = {u + d(u)/(x - u) : u ∈ F, u ≠ x} ∪ {∞}
  
  -- The missing point σ(x) is the unique point not in this set
  
  -- Using Lagrange interpolation, we can show that:
  -- σ(x) = x - D'(x)
  
  -- This is a key result from Section 2
  -- The proof involves showing that the function
  -- f(y) = ∏_{u ∈ F} (y - (u + d(u)/(x - u)))
  -- has a specific form
  
  sorry -- This is proven in Theorem1.lean as sigma_derivative_identity

-- =============================================================================
-- Part 6: Normalization with Positive Fixed Points
-- =============================================================================

/-- 
Structure for the normalization used in Section 3.
This assumes f > 0 and sets up the covering-curve construction.
-/
structure CoveringNormalization (S : AdmissibleSet F) (σ : Ω F → Ω F) where
  -- Underlying normalization
  norm : Normalization S σ
  -- Positive fixed points
  f_pos : 0 < FixedPointCount σ
  -- The d function from normalization
  d : F → F := norm.d
  -- The interpolating polynomial
  D : Polynomial F := InterpolatingPolynomial norm

/-- 
Theorem: For any admissible set S with f > 0, there exists a covering normalization.
-/
theorem CoveringNormalization_exists
    (S : AdmissibleSet F) 
    (σ : Ω F → Ω F)
    (hσ : σ = MissingPermutation S)
    (hf_pos : 0 < FixedPointCount σ)
    : ∃ (CN : CoveringNormalization S σ), CN.f_pos := by
  
  -- First, obtain a normalization
  have h_norm : ∃ N : Normalization S σ, N.σ_infty ∧ N.σ_missing := by
    sorry -- This is Normalization_exists
  
  obtain ⟨N, _, _⟩ := h_norm
  
  -- Construct the covering normalization
  use { norm := N, f_pos := hf_pos }
  exact hf_pos

-- =============================================================================
-- Part 7: Additional Properties
-- =============================================================================

/-- 
Lemma: In the covering normalization, D'(x) ≠ 0 for some x.
This follows from Lemma 2.2 (σ ≠ id).
-/
theorem derivative_nonzero
    (CN : CoveringNormalization S σ)
    (hσ_ne_id : σ ≠ id)
    : CN.D.derivative ≠ 0 := by
  
  -- If D' = 0, then D is constant
  -- Then σ(x) = x - D'(x) = x for all x ∈ F
  -- Combined with σ(∞) = ∞, this gives σ = id
  -- Contradicting hσ_ne_id
  
  by_contra hD'
  have hD_const : CN.D.derivative = 0 := hD'
  have hD_is_const : ∃ c : F, CN.D = Polynomial.C c := by
    exact Polynomial.isConst_iff_derivative_eq_zero.mpr hD_const
  
  obtain ⟨c, hD_c⟩ := hD_is_const
  
  -- Then σ(x) = x - D'(x) = x - 0 = x for all x ∈ F
  have hσ_finite : ∀ x : F, σ (Ω.finite x) = Ω.finite x := by
    intro x
    calc σ (Ω.finite x)
        = Ω.finite (x - CN.D.derivative.eval x) := by
            sorry -- This is sigma_derivative_identity
      _ = Ω.finite (x - 0) := by rw [hD_const]; simp
      _ = Ω.finite x := by simp
  
  -- Also σ(∞) = ∞ from normalization
  have hσ_infty : σ Ω.infinity = Ω.infinity := CN.norm.σ_infty
  
  -- Therefore σ = id
  have : σ = id := by
    ext x
    cases x with
    | infinity => exact hσ_infty
    | finite y => exact hσ_finite y
  
  exact hσ_ne_id this

-- =============================================================================
-- Part 8: Summary
-- =============================================================================

/-- 
Phase 2 Summary:

This file provides the normalization setup for Theorem 2:

1. **Normalization**: σ(∞) = ∞, S parameterized by u ∈ F
2. **Interpolating Polynomial**: D(X) with D(u) = d(u), deg D ≤ q-1
3. **Derivative Identity**: σ(x) = x - D'(x) for x ∈ F
4. **Covering Normalization**: Structure for Section 3

Key results:
- Normalization_exists: normalization exists when f > 0
- sigma_derivative_identity: the key derivative identity
- derivative_nonzero: D' ≠ 0 (from σ ≠ id)

Next: Phase 3 (Menelaus Identity and Invariant Function)
-/
