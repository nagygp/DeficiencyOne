/-
# Section 3: Covering Curves and the Positive Fixed-Point Gap

This file contains the proofs from Section 3 of the paper, which uses fixed points of σ 
to cover the nonsplit members of S by lines and prove Theorem 2.
-/

import FixedPointsPrimePower.Defs
import FixedPointsPrimePower.MainTheorems
import FixedPointsPrimePower.Section2

-- Enable universe polymorphism
set_option autoImplicit false

-- =============================================================================
-- Section 3.1: Split and Nonsplit Count
-- =============================================================================

/-- 
The relationship between split, nonsplit, and fixed points:

    2e + f = q + 1
    t = q - e = (q + f - 1) / 2

where e = number of split involutions, t = number of nonsplit involutions, f = fixed points
-/
theorem SplitNonsplitCount
    (p : ℕ) (hp : Nat.Prime p) (r : ℕ) (hr : r ≥ 1)
    (S : Finset (PGL2Element (Fq p r)))
    (hS_admissible : IsAdmissible S)
    (hS_size : S.card = p ^ r)
    : 2 * SplitCount S + FixedPointCount (MissingPermutation S) = p ^ r + 1 ∧
      NonsplitCount S = p ^ r - SplitCount S ∧
      NonsplitCount S = (p ^ r + FixedPointCount (MissingPermutation S) - 1) / 2 := by
  sorry

-- =============================================================================
-- Section 3.2: Normalization for Covering
-- =============================================================================

/-- 
Throughout the covering-curve construction we assume f > 0 and use the normalization:

    σ(∞) = ∞
    S = {s_u : X ↦ u + d(u) / (X - u) | u ∈ F_q}

In particular, d(u) ≠ 0 for every u.
-/
def CoveringNormalization
    (p : ℕ) (hp : Nat.Prime p) (r : ℕ) (hr : r ≥ 1)
    (S : Finset (PGL2Element (Fq p r)))
    (hS_admissible : IsAdmissible S)
    (hS_size : S.card = p ^ r)
    (hf_pos : 0 < FixedPointCount (MissingPermutation S))
    : Prop := 
  NormalizedAtInfinity (MissingPermutation S) ∧
  ∃ (d : Fq p r → Fq p r), 
    (∀ u, d u ≠ 0) ∧
    S = Finset.image (fun u => sorry) Finset.univ

-- =============================================================================
-- Section 3.3: Menelaus Identity and Invariant Function
-- =============================================================================

/-- 
Lemma 3.1 (Menelaus Identity): In the normalization, we have:

    d(σ(x)) = d(x) for x ∈ F_q

If a, b ∈ F_q, a ≠ b, and b ≠ σ(a), let u be the unique label such that s_u(a) = b. Then:

    (u - b) d(a) (σ(b) - a) = (u - a) d(b) (σ(a) - b)
-/
theorem Lemma3_1_CoverMenelaus
    (p : ℕ) (hp : Nat.Prime p) (r : ℕ) (hr : r ≥ 1)
    (S : Finset (PGL2Element (Fq p r)))
    (hS_admissible : IsAdmissible S)
    (hS_size : S.card = p ^ r)
    (hf_pos : 0 < FixedPointCount (MissingPermutation S))
    (h_norm : CoveringNormalization p hp r hr S hS_admissible hS_size hf_pos)
    : ∃ (d : Fq p r → Fq p r),
        (∀ x, d (MissingPermutation S x) = d x) ∧
        (∀ a b u, a ≠ b → b ≠ MissingPermutation S a → 
          (s_u : PGL2Element (Fq p r)) • a = b →
          (u - b) * d a * (MissingPermutation S b - a) = 
          (u - a) * d b * (MissingPermutation S a - b)) := by
  sorry

/-- 
Lemma 3.2 (Parity): For each u ∈ F_q, define h_u : Ω → F_q by:

    h_u(x) = (d(u) - (u - x)(u - σ(x))) / d(x) for x ∈ F_q
    h_u(∞) = 1

Then:

    h_u ∘ σ = h_u
    h_u ∘ s_u = h_u

For every z ∈ F_q:

    |F ∩ h_u⁻¹(z)| ≡ |Fix_Ω(s_u) ∩ h_u⁻¹(z)| (mod 2)

In particular, every value of h_u occurs an even number of times on F when s_u is nonsplit.
For arbitrary s_u, at most two values occur an odd number of times on F.
-/
theorem Lemma3_2_CoverParity
    (p : ℕ) (hp : Nat.Prime p) (r : ℕ) (hr : r ≥ 1)
    (S : Finset (PGL2Element (Fq p r)))
    (hS_admissible : IsAdmissible S)
    (hS_size : S.card = p ^ r)
    (hf_pos : 0 < FixedPointCount (MissingPermutation S))
    (h_norm : CoveringNormalization p hp r hr S hS_admissible hS_size hf_pos)
    : ∃ (d : Fq p r → Fq p r), ∀ u,
        (∀ x, h_function d (MissingPermutation S) u (MissingPermutation S x) = 
               h_function d (MissingPermutation S) u x) ∧
        (∀ x, h_function d (MissingPermutation S) u (s_u • x) = 
               h_function d (MissingPermutation S) u x) ∧
        (∀ z, (Fix_Ω (MissingPermutation S)).filter (fun x => h_function d (MissingPermutation S) u x = z)).card % 2 =
               ((Fix_Ω (s_u)).filter (fun x => h_function d (MissingPermutation S) u x = z)).card % 2) := by
  sorry

-- =============================================================================
-- Section 3.4: Rich Lines and Covering
-- =============================================================================

/-- 
Definition: A line L in the involution plane is rich if it contains at least one split involution
or at least two nonsplit involutions.
-/
def IsRichLine (L : ProjectiveLine (InvolutionPlane (Fq p r))) : Prop := 
  ∃ s ∈ S, IsSplitInvolution s ∧ InvolutionToPlanePoint s sorry ∈ L ∨
  ∃ s t ∈ S, s ≠ t ∧ IsNonsplitInvolution s ∧ IsNonsplitInvolution t ∧
    InvolutionToPlanePoint s sorry ∈ L ∧ InvolutionToPlanePoint t sorry ∈ L

/-- 
Lemma 3.3: Every nonsplit involution lies on at most two rich lines.
-/
theorem Lemma3_3_NonsplitRichLines
    (p : ℕ) (hp : Nat.Prime p) (r : ℕ) (hr : r ≥ 1)
    (S : Finset (PGL2Element (Fq p r)))
    (hS_admissible : IsAdmissible S)
    (hS_size : S.card = p ^ r)
    (hf_pos : 0 < FixedPointCount (MissingPermutation S))
    : ∀ s ∈ S, IsNonsplitInvolution s → 
      (Finset.filter (fun L => IsRichLine L ∧ InvolutionToPlanePoint s sorry ∈ L) 
        (Finset.univ : Finset (ProjectiveLine (InvolutionPlane (Fq p r))))).card ≤ 2 := by
  sorry

/-- 
Lemma 3.4: The number of rich lines is at most f - 1.
-/
theorem Lemma3_4_RichLinesBound
    (p : ℕ) (hp : Nat.Prime p) (r : ℕ) (hr : r ≥ 1)
    (S : Finset (PGL2Element (Fq p r)))
    (hS_admissible : IsAdmissible S)
    (hS_size : S.card = p ^ r)
    (hf_pos : 0 < FixedPointCount (MissingPermutation S))
    : (Finset.filter IsRichLine (Finset.univ : Finset (ProjectiveLine (InvolutionPlane (Fq p r))))).card ≤
      FixedPointCount (MissingPermutation S) - 1 := by
  sorry

/-- 
Lemma 3.5: Every rich line contains at most 2√q + 12 nonsplit involutions.
-/
theorem Lemma3_5_RichLineNonsplitBound
    (p : ℕ) (hp : Nat.Prime p) (r : ℕ) (hr : r ≥ 1)
    (S : Finset (PGL2Element (Fq p r)))
    (hS_admissible : IsAdmissible S)
    (hS_size : S.card = p ^ r)
    (hf_pos : 0 < FixedPointCount (MissingPermutation S))
    (L : ProjectiveLine (InvolutionPlane (Fq p r)))
    (hL_rich : IsRichLine L)
    : (S.filter (fun s => IsNonsplitInvolution s ∧ InvolutionToPlanePoint s sorry ∈ L)).card ≤
      2 * Real.sqrt (p ^ r) + 12 := by
  sorry

/-- 
Lemma 3.6: The nonsplit involutions can be covered by f - 1 lines.
-/
theorem Lemma3_6_NonsplitCover
    (p : ℕ) (hp : Nat.Prime p) (r : ℕ) (hr : r ≥ 1)
    (S : Finset (PGL2Element (Fq p r)))
    (hS_admissible : IsAdmissible S)
    (hS_size : S.card = p ^ r)
    (hf_pos : 0 < FixedPointCount (MissingPermutation S))
    : ∃ (Lines : Finset (ProjectiveLine (InvolutionPlane (Fq p r)))),
        Lines.card ≤ FixedPointCount (MissingPermutation S) - 1 ∧
        ∀ s ∈ S, IsNonsplitInvolution s → 
          ∃ L ∈ Lines, InvolutionToPlanePoint s sorry ∈ L := by
  sorry

-- =============================================================================
-- Section 3.5: Proof of Theorem 2
-- =============================================================================

/-- 
Proof of Theorem 2: Positive Fixed-Point Gap

Let q = p^r ≥ 5 be odd, and let S be an admissible set of size q.
If S is noncollinear and f > 0, then:

    q ≤ (f - 1)(4√q + 23)
    f ≥ 1 + q / (4√q + 23)
-/
theorem Theorem2_PositiveFixedPointGap_Proof
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
  -- The t = (q + f - 1) / 2 nonsplit elements are covered by the f - 1 lines
  -- Applying Lemma 3.5 to each line gives:
  -- (q + f - 1) / 2 ≤ (f - 1)(2√q + 12)
  
  -- Rearranging gives the desired inequality
  
  sorry

-- =============================================================================
-- Section 3.6: Remarks
-- =============================================================================

/-- 
Remark: The polynomial (2.3) covers the whole graph for f ≥ 4, and Theorem 3.1 
supplies a quadratic cover when f = 2. Its degree is controlled by f, not by an 
absolute constant. In the involution plane the cover is a union of lines, which 
yields the stronger threshold q of order f² in Theorem 2.

An unconditional upper bound excluding positive f of order √q or larger is not 
established here. The case f = 0 requires a different normalization.
-/
