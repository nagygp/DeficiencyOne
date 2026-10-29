/-
# Theorem 2: Phase 1 - Basic Definitions

This file contains the basic definitions for proving Theorem 2 from the paper.
It implements Phase 1 of the comprehensive plan.

**Theorem 2**: Let q = p^r ≥ 5 be odd, and let S be an admissible set of size q.
If S is noncollinear and f > 0, then:
    q ≤ (f - 1)(4√q + 23)
    f ≥ 1 + q / (4√q + 23)

Phase 1 focuses on the basic geometric and algebraic structures needed.
-/

import FixedPointsPrimePower.Defs
import Mathlib.LinearAlgebra.ProjectiveSpace.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Notation

-- Enable universe polymorphism
set_option autoImplicit false

-- =============================================================================
-- Part 1: Finite Field and Projective Line Setup
-- =============================================================================

variable {p : ℕ} [Fact (Nat.Prime p)] {r : ℕ} [Fact (r ≥ 1)]

-- Finite field with q = p^r elements
abbrev Fq : Type := FiniteField.ofPrimePower p r

-- The projective line P¹(F) = F ∪ {∞}
abbrev Ω (F : Type*) [Field F] : Type := ProjectiveLine F

-- Notation for infinity
notation "∞" => ProjectiveLine.infinity

-- =============================================================================
-- Part 2: PGL₂ Elements and Involutions
-- =============================================================================

/-- 
PGL₂(F) elements represented as Möbius transformations.
In PGL₂, elements are equivalence classes of 2×2 invertible matrices.
-/
structure PGL2Element (F : Type*) [Field F] where
  -- Represent as a Möbius transformation: f(x) = (a*x + b) / (c*x + d)
  a b c d : F
  -- The matrix [a b; c d] is invertible (ad - bc ≠ 0)
  det_ne_zero : a * d - b * c ≠ 0

-- Coercion to function on projective line
instance : CoeFun (PGL2Element F) (fun _ => Ω F → Ω F) where
  coe g := fun x => match x with
    | Ω.finite y => 
      if g.c = 0 ∨ g.d + g.c * y = 0 then Ω.infinity
      else Ω.finite ((g.a * y + g.b) / (g.c * y + g.d))
    | Ω.infinity => 
      if g.c = 0 then Ω.infinity
      else Ω.finite (g.a / g.c)

/-- 
An involution in PGL₂(F) is an element g such that g² = id.
For Möbius transformations, this means g(g(x)) = x for all x.
-/
def IsInvolution (g : PGL2Element F) : Prop :=
  ∀ x : Ω F, g (g x) = x

/-- 
Split involutions: those with two fixed points in Ω(F).
In PGL₂, an involution is split if its matrix has trace ≠ 0 (over F).
-/
def IsSplitInvolution (g : PGL2Element F) : Prop :=
  g.a + g.d ≠ 0

/-- 
Nonsplit involutions: those with no fixed points in Ω(F).
In PGL₂, an involution is nonsplit if its matrix has trace = 0.
-/
def IsNonsplitInvolution (g : PGL2Element F) : Prop :=
  g.a + g.d = 0

-- =============================================================================
-- Part 3: Trace-Zero Matrices and Involution Plane
-- =============================================================================

/-- 
Trace-zero 2×2 matrices over F.
These correspond to nonsplit involutions in PGL₂(F).
-/
def TraceZeroMatrix (F : Type*) [Field F] : Type :=
  {M : Matrix (Fin 2) (Fin 2) F // M.trace = 0}

-- Projective space of trace-zero matrices
-- This is the "involution plane" where involutions are represented as points
abbrev InvolutionPlane (F : Type*) [Field F] : Type :=
  ProjectiveSpace (TraceZeroMatrix F)

/-- 
Map a PGL₂ involution to a point in the involution plane.
For a nonsplit involution with trace zero, we map it to its matrix.
For a split involution, we need a different representation.
-/
noncomputable def involutionToPlanePoint 
    (g : PGL2Element F) (h : IsInvolution g) : InvolutionPlane F := by
  -- For now, we construct a default point
  -- The actual construction requires more development
  -- A nonsplit involution g corresponds to a matrix with trace 0
  -- We would construct the matrix from g's coefficients
  
  -- Placeholder: return a default projective point
  -- This will be properly implemented when we have the full PGL₂ theory
  sorry

-- =============================================================================
-- Part 4: Collinearity
-- =============================================================================

/-- 
A set of involutions is collinear if all corresponding points in the involution plane
lie on a single projective line.
-/
def IsCollinear (S : Finset (PGL2Element F)) : Prop :=
  ∃ (L : ProjectiveLine (InvolutionPlane F)),
    ∀ s ∈ S, ∃ (h : IsInvolution s), 
      involutionToPlanePoint s h ∈ L

-- =============================================================================
-- Part 5: Admissible Sets
-- =============================================================================

/-- 
An admissible set of involutions.
This is the key structure from the paper: a set S of |F| = q involutions
such that the product of any two distinct elements has no fixed points.
-/
structure AdmissibleSet (F : Type*) [Field F] [Fintype F] where
  -- The set of involutions
  involutions : Finset (PGL2Element F)
  -- Each element is an involution
  is_involution : ∀ s ∈ involutions, IsInvolution s
  -- Admissibility: product of any two distinct involutions has no fixed points
  admissible : ∀ s ∈ involutions, ∀ t ∈ involutions, s ≠ t → 
    ∀ x : Ω F, (g (g x) = x) → (g x ≠ x)  -- Need to properly define composition
  -- Size: |S| = q = |F|
  card_eq : involutions.card = Fintype.card F

-- =============================================================================
-- Part 6: Missing Permutation
-- =============================================================================

/-- 
The missing permutation σ associated with an admissible set S.
For each x ∈ Ω, σ(x) is the unique point not in {s(x) : s ∈ S}.
-/
noncomputable def MissingPermutation (S : AdmissibleSet F) : Ω F → Ω F := fun x =>
  Classical.choose (by
    -- For each x, {s(x) : s ∈ S} has cardinality |S| = q
    -- The projective line has cardinality q + 1
    -- So there is exactly one point missing
    
    have h_image_card : (S.involutions.image fun s => s x).card = S.involutions.card := by
      apply Finset.card_image_of_injective
      intro s hs t ht hst
      -- Need: if s(x) = t(x) for s, t ∈ S, then s = t
      -- This follows from admissibility
      sorry
    
    have h_Ω_card : Fintype.card (Ω F) = Fintype.card F + 1 := by
      simp [Fintype.card_option]
    
    have h_missing : (Finset.univ : Finset (Ω F)) \ (S.involutions.image fun s => s x)).card = 1 := by
      rw [Finset.card_sdiff (by simp), h_Ω_card, S.card_eq]
      omega
    
    exact Finset.card_pos.mp (by omega : 0 < (Finset.univ : Finset (Ω F)) \ 
      (S.involutions.image fun s => s x)).card))

/-- 
Fixed point count: number of x such that σ(x) = x.
-/
def FixedPointCount (σ : Ω F → Ω F) : ℕ :=
  (Finset.univ.filter fun x => σ x = x).card

-- =============================================================================
-- Part 7: Split and Nonsplit Counts
-- =============================================================================

/-- 
Count of split involutions in S.
-/
noncomputable def SplitCount (S : AdmissibleSet F) : ℕ :=
  (S.involutions.filter IsSplitInvolution).card

/-- 
Count of nonsplit involutions in S.
-/
noncomputable def NonsplitCount (S : AdmissibleSet F) : ℕ :=
  (S.involutions.filter IsNonsplitInvolution).card

-- =============================================================================
-- Part 8: The Fundamental Counting Lemma
-- =============================================================================

/-- 
Theorem: Relationship between split, nonsplit, and fixed points.

From the paper: 2e + f = q + 1, where:
- e = number of split involutions
- t = number of nonsplit involutions  
- f = number of fixed points of σ
- q = |F| = |S|

Each split involution fixes exactly 2 points in Ω.
Each nonsplit involution fixes exactly 0 points in Ω.
The missing permutation σ has f fixed points.

Total: 2e + f = |Ω| = q + 1
Also: e + t = |S| = q
Therefore: t = q - e = (q + f - 1) / 2
-/
theorem SplitNonsplitCount (S : AdmissibleSet F) :
    2 * SplitCount S + FixedPointCount (MissingPermutation S) = Fintype.card F + 1 ∧
    NonsplitCount S = (Fintype.card F + FixedPointCount (MissingPermutation S) - 1) / 2 := by
  
  -- Let e = SplitCount S, t = NonsplitCount S, f = FixedPointCount (MissingPermutation S)
  -- Let q = Fintype.card F
  
  -- First, we show that e + t = q
  have h_total : SplitCount S + NonsplitCount S = Fintype.card F := by
    have : S.involutions = (S.involutions.filter IsSplitInvolution) ∪ 
                          (S.involutions.filter IsNonsplitInvolution) := by
      ext s
      simp
      by_cases h : IsSplitInvolution s
      · left; exact h
      · right
        -- If not split, then nonsplit (since every involution is either split or nonsplit)
        -- For a proper involution in PGL₂, trace is either 0 or non-zero
        -- If trace ≠ 0, it's split; if trace = 0, it's nonsplit
        -- But we need to verify that every involution in S is either split or nonsplit
        -- This is true for PGL₂ involutions
        sorry
    
    have : (S.involutions.filter IsSplitInvolution).card + 
           (S.involutions.filter IsNonsplitInvolution).card = 
           ((S.involutions.filter IsSplitInvolution) ∪ 
            (S.involutions.filter IsNonsplitInvolution)).card := by
      rw [Finset.card_union_of_disjoint]
      apply Finset.disjoint_filter_filter_neg
      intro s hs h_split h_nonsplit
      simp [IsSplitInvolution, IsNonsplitInvolution] at h_split h_nonsplit
      omega
    
    rw [this, this]
    simp [SplitCount, NonsplitCount]
    exact S.card_eq
  
  -- Now, we count fixed points
  -- Each split involution s fixes exactly 2 points
  -- Each nonsplit involution fixes exactly 0 points
  -- The set S acts on Ω, and for each x ∈ Ω, {s(x) : s ∈ S} = Ω \ {σ(x)}
  
  -- We need to count: for each x, how many s ∈ S fix x?
  -- If s fixes x, then s(x) = x
  -- But {s(x) : s ∈ S} = Ω \ {σ(x)}
  -- So s(x) = x means x ≠ σ(x), i.e., x is NOT a fixed point of σ
  
  -- Actually, we need a different approach
  -- Let's use the fact that involutions have specific fixed point structures
  
  -- For a split involution s: Fix_Ω(s) has size 2
  -- For a nonsplit involution s: Fix_Ω(s) has size 0
  
  -- The total number of pairs (s, x) where s ∈ S and s(x) = x is:
  -- ∑_{s ∈ S} |Fix_Ω(s)| = ∑_{s ∈ S, split} 2 + ∑_{s ∈ S, nonsplit} 0 = 2e
  
  -- On the other hand, for each x ∈ Ω:
  -- - If σ(x) = x, then {s(x) : s ∈ S} = Ω \ {x}, so no s fixes x
  -- - If σ(x) ≠ x, then {s(x) : s ∈ S} = Ω \ {σ(x)}, and exactly one s satisfies s(x) = x
  --   (because x ∈ Ω \ {σ(x)} = {s(x) : s ∈ S})
  
  -- Therefore: ∑_{x ∈ Ω} |{s ∈ S : s(x) = x}| = |{x : σ(x) ≠ x}| = (q + 1) - f
  
  -- But also: ∑_{x ∈ Ω} |{s ∈ S : s(x) = x}| = ∑_{s ∈ S} |Fix_Ω(s)| = 2e
  
  -- Therefore: 2e = (q + 1) - f
  -- Rearranging: 2e + f = q + 1
  
  have h_fixed_points : 2 * SplitCount S + FixedPointCount (MissingPermutation S) = 
      Fintype.card F + 1 := by
    
    -- Count the total number of fixed point pairs
    let total_fixed_pairs : ℕ := 
      (Finset.univ : Finset (Ω F)).sum fun x => 
        (S.involutions.filter fun s => s x = x).card
    
    -- This equals the sum over S of the number of fixed points of each involution
    have h_double_count : total_fixed_pairs = 
        S.involutions.sum fun s => (Finset.univ : Finset (Ω F)).filter (fun x => s x = x)).card := by
      rw [Finset.sum_comm]
      congr 1
      ext s
      simp
    
    -- For split involutions, there are 2 fixed points; for nonsplit, 0
    have h_sum_fixed : S.involutions.sum fun s => 
        (Finset.univ : Finset (Ω F)).filter (fun x => s x = x)).card = 
        2 * SplitCount S := by
      
      -- Split S into split and nonsplit involutions
      have h_partition : S.involutions = (S.involutions.filter IsSplitInvolution) ∪ 
                                        (S.involutions.filter IsNonsplitInvolution) := by
        ext s
        simp
        by_cases h : IsSplitInvolution s
        · left; exact h
        · right
          -- Every involution in PGL₂ is either split or nonsplit
          -- This is a standard fact
          sorry
      
      rw [h_partition, Finset.sum_union]
      · have h_disjoint : Disjoint (S.involutions.filter IsSplitInvolution) 
                                       (S.involutions.filter IsNonsplitInvolution) := by
          apply Finset.disjoint_filter_filter_neg
          intro s _ h_split h_nonsplit
          simp [IsSplitInvolution, IsNonsplitInvolution] at h_split h_nonsplit
          omega
        rw [Finset.sum_disjoint h_disjoint]
        
        -- For split involutions: each has exactly 2 fixed points
        -- For nonsplit involutions: each has exactly 0 fixed points
        
        congr 1
        · -- Sum over split involutions
          apply Finset.sum_congr rfl
          intro s hs
          -- A split involution in PGL₂ has exactly 2 fixed points
          -- This is a standard result
          sorry
        
        · -- Sum over nonsplit involutions
          apply Finset.sum_eq_zero
          intro s hs
          -- A nonsplit involution in PGL₂ has exactly 0 fixed points
          -- This is a standard result
          sorry
      
      · -- Disjointness (already shown above)
        apply Finset.disjoint_filter_filter_neg
        intro s _ h_split h_nonsplit
        simp [IsSplitInvolution, IsNonsplitInvolution] at h_split h_nonsplit
        omega
    
    -- On the other hand, for each x, count how many s fix x
    have h_count_by_point : total_fixed_pairs = 
        (Finset.univ : Finset (Ω F)).sum fun x => 
          (S.involutions.filter fun s => s x = x).card := by
      rfl
    
    -- For each x:
    -- - If σ(x) = x, then {s(x) : s ∈ S} = Ω \ {x}, so no s fixes x
    -- - If σ(x) ≠ x, then exactly one s satisfies s(x) = x
    
    have h_fixed_by_point : total_fixed_pairs = 
        (Fintype.card F + 1) - FixedPointCount (MissingPermutation S) := by
      
      rw [h_count_by_point]
      
      -- Split Ω into fixed and non-fixed points of σ
      have h_partition_Ω : (Finset.univ : Finset (Ω F)) = 
          (Finset.univ.filter fun x => MissingPermutation S x = x) ∪
          (Finset.univ.filter fun x => MissingPermutation S x ≠ x) := by
        ext x
        simp
        by_cases h : MissingPermutation S x = x
        · left; exact h
        · right; exact h
      
      rw [h_partition_Ω, Finset.sum_union]
      · have h_disjoint : Disjoint 
            (Finset.univ.filter fun x => MissingPermutation S x = x)
            (Finset.univ.filter fun x => MissingPermutation S x ≠ x) := by
          apply Finset.disjoint_filter_filter_neg
          intro x _ h_eq h_ne
          exact h_ne h_eq
        rw [Finset.sum_disjoint h_disjoint]
        
        congr 1
        · -- For fixed points of σ: no s fixes x
          apply Finset.sum_eq_zero
          intro x hx
          simp [FixedPointCount] at hx
          -- If σ(x) = x, then {s(x) : s ∈ S} = Ω \ {x}
          -- So for all s ∈ S, s(x) ≠ x
          have h_image : ∀ s ∈ S.involutions, s x ≠ x := by
            intro s hs
            -- By definition of σ, {s(x) : s ∈ S} = Ω \ {σ(x)}
            -- If σ(x) = x, then {s(x) : s ∈ S} = Ω \ {x}
            -- So s(x) ∈ Ω \ {x}, meaning s(x) ≠ x
            sorry
          
          simp [h_image]
        
        · -- For non-fixed points of σ: exactly one s fixes x
          have : (Finset.univ.filter fun x => MissingPermutation S x ≠ x).sum 
                   (fun x => (S.involutions.filter fun s => s x = x).card) = 
                 (Finset.univ.filter fun x => MissingPermutation S x ≠ x).card := by
            apply Finset.sum_congr rfl
            intro x hx
            simp at hx
            -- For x with σ(x) ≠ x, we have {s(x) : s ∈ S} = Ω \ {σ(x)}
            -- Since σ(x) ≠ x, we have x ∈ Ω \ {σ(x)} = {s(x) : s ∈ S}
            -- So there exists exactly one s ∈ S such that s(x) = x
            have : (S.involutions.filter fun s => s x = x).card = 1 := by
              -- x ∈ {s(x) : s ∈ S}
              have h_x_in_image : x ∈ S.involutions.image (fun s => s x) := by
                have : S.involutions.image (fun s => s x) = 
                       (Finset.univ : Finset (Ω F)) \ {MissingPermutation S x} := by
                  -- This is the definition of σ
                  sorry
                rw [this]
                simp [hx]
              
              -- So there exists s ∈ S such that s(x) = x
              -- And it's unique because... (need to show injectivity)
              sorry
            
            exact this
          
          rw [this]
          simp [FixedPointCount]
          
          -- The number of non-fixed points is |Ω| - f = (q + 1) - f
          have : (Finset.univ.filter fun x => MissingPermutation S x ≠ x).card = 
                 Fintype.card (Ω F) - FixedPointCount (MissingPermutation S) := by
            have : (Finset.univ : Finset (Ω F)) = 
                   (Finset.univ.filter fun x => MissingPermutation S x = x) ∪
                   (Finset.univ.filter fun x => MissingPermutation S x ≠ x) := by
              ext x; simp
              by_cases h : MissingPermutation S x = x
              · left; exact h
              · right; exact h
            
            have h_disjoint : Disjoint 
                (Finset.univ.filter fun x => MissingPermutation S x = x)
                (Finset.univ.filter fun x => MissingPermutation S x ≠ x) := by
              apply Finset.disjoint_filter_filter_neg
              intro x _ h_eq h_ne
              exact h_ne h_eq
            
            have : (Finset.univ : Finset (Ω F)).card = 
                   (Finset.univ.filter fun x => MissingPermutation S x = x).card +
                   (Finset.univ.filter fun x => MissingPermutation S x ≠ x).card := by
              rw [← Finset.card_union_of_disjoint h_disjoint, this]
            
            simp [FixedPointCount] at this
            omega
          
          rw [this]
          have : Fintype.card (Ω F) = Fintype.card F + 1 := by
            simp [Fintype.card_option]
          rw [this]
          omega
      
      · -- Disjointness
        apply Finset.disjoint_filter_filter_neg
        intro x _ h_eq h_ne
        exact h_ne h_eq
    
    rw [h_double_count, h_sum_fixed, h_fixed_by_point] at h_double_count
    omega
  
  -- Now we can prove both parts
  constructor
  · exact h_fixed_points
  
  · -- For the second part: t = (q + f - 1) / 2
    have : NonsplitCount S = Fintype.card F - SplitCount S := by
      have := h_total
      simp [NonsplitCount, SplitCount]
      omega
    
    rw [this]
    have : 2 * SplitCount S = Fintype.card F + 1 - FixedPointCount (MissingPermutation S) := by
      have := h_fixed_points
      omega
    
    omega
