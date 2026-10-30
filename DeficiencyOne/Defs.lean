/-
Copyright (c) 2026 The Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Mathlib Contributors
-/
import Mathlib
import RequestProject.Defs

/-!
# §1. Introduction: the deficiency-one setting

Formalization of Section 1 of

* G. Korchmáros, G. P. Nagy, T. Szőnyi,
  *Fixed points and rigidity in the deficiency-one case over prime-power fields*.

This file sets up the ambient objects and records the definitions of the paper.

`K` is a finite field of odd order `q = Nat.card K = p ^ r`, where `p = ringChar K`. The
projective line is

`P1 K = ℙ K (Fin 2 → K)`, the projectivization of `Fin 2 → K`, which has `q + 1` points
(`card_P1`), and `PGL2 K = GL₂(K) / Z(GL₂(K))` acts on it by fractional linear maps.

## Main definitions

* `IsAdmissible S` : `S ⊆ PGL₂(K)` consists of involutions and the product of two distinct
  elements of `S` is fixed-point-free (the paper's "admissible").
* `IsMissingPerm S σ` : equation (1) of the paper, `{s(x) : s ∈ S} = Ω \ {σ(x)}` for every `x`.
* `numFixed σ` : `f = |Fix_Ω(σ)|`, the number of fixed points of the missing permutation.
* `IsSplit` / `IsNonsplit` : an involution with two fixed points on `Ω`, respectively none.
* `IsCollinear S` : the elements of `S`, viewed in the involution plane of trace-zero matrices
  as `[A : B : C]`, lie on one projective line.
* `lineForm v`, `lineTrace v S` : the linear form of a line of the involution plane, and the
  points of `S` lying on it (used by §3).
* `hammingDist α β`, `agreementSet α β` : the paper's `d_H(α, β)` and the set it measures.

## Basic facts recorded here

* `card_P1` (proved) : `|Ω| = q + 1`.
* `exists_isMissingPerm` (proved) : the missing permutation `σ` exists and is an involution.
* `even_numFixed` (proved) : `|Ω| - f` is even.
* `invCoord_normalized` (proved) : the coordinates `[A : B : C]` of an involution satisfy `A² + BC ≠ 0`,
  i.e. lie off the conic `Q = 0` of the involution plane. Its ingredients
  (`sq_eq_trace_smul_sub_det`, `trace_zero_of_isInvolution`) are proved here, before the
  coordinates are defined.
-/

@[expose] public section

open scoped LinearAlgebra.Projectivization
open Classical

universe u

/-- The projective line `ℙ¹(K)` over `K`, as the projectivization of `K²`. -/
abbrev P1 (K : Type u) [Field K] : Type u := ℙ K (Fin 2 → K)

namespace PGL2

variable {K : Type u} [Field K]

/-! ### Definitions of the paper -/

/-- An element of `PGL₂(K)` is an *involution* if it is nontrivial and its square is the
identity; this is the projective class of a matrix with minimal polynomial `X² - λ`. -/
def IsInvolution (g : PGL2 K) : Prop := g ≠ 1 ∧ g * g = 1

/-- The set of fixed points of `g` on `ℙ¹(K)`. -/
def fixPoints (g : PGL2 K) : Set (P1 K) := {x | g • x = x}

/-- A *split* involution: a nontrivial involution with a fixed point on `ℙ¹(K)`. In odd
characteristic a nontrivial projective involution has either no or exactly two fixed points,
so this is the paper's "split involution" (`Fix` has two elements). -/
def IsSplit (g : PGL2 K) : Prop := IsInvolution g ∧ (fixPoints g).Nonempty

/-- A *nonsplit* involution: a nontrivial involution without fixed points on `ℙ¹(K)`. -/
def IsNonsplit (g : PGL2 K) : Prop := IsInvolution g ∧ ∀ x : P1 K, g • x ≠ x

/-- `S ⊆ PGL₂(K)` is *admissible* if all its elements are involutions and the product of two
distinct elements of `S` is fixed-point-free on `ℙ¹(K)` (definition of the introduction). -/
def IsAdmissible (S : Set (PGL2 K)) : Prop :=
  (∀ s ∈ S, IsInvolution s) ∧ ∀ s ∈ S, ∀ t ∈ S, s ≠ t → ∀ x : P1 K, (s * t) • x ≠ x

/-- `σ` is the *missing permutation* of `S`: for every point `x` the images `s • x`, `s ∈ S`,
are exactly the points other than `σ x` (equation (1) of the paper). -/
def IsMissingPerm (S : Set (PGL2 K)) (σ : P1 K → P1 K) : Prop :=
  ∀ x y : P1 K, (∃ s ∈ S, s • x = y) ↔ y ≠ σ x

/-- The number `f = |Fix_Ω(σ)|` of fixed points of a permutation `σ` of the projective
line. -/
noncomputable def numFixed (σ : P1 K → P1 K) : ℕ := Nat.card {x : P1 K // σ x = x}

/-- The *Hamming distance* of two permutations of the projective line,
`d_H(α, β) = |{x | α x ≠ β x}|`. -/
noncomputable def hammingDist (α β : P1 K → P1 K) : ℕ := Nat.card {x : P1 K // α x ≠ β x}

/-- The set of points on which `α` and `β` agree. -/
def agreementSet (α β : P1 K → P1 K) : Set (P1 K) := {x | α x = β x}

/-- The coordinates `[A : B : C]` of the point of the *involution plane* attached to `g`:
the trace-zero part of a matrix representative of `g`, read in the basis
`[[A, B], [C, -A]]`. For an involution every representative has trace zero and `A² + BC ≠ 0`,
and multiplying the representative by `λ ≠ 0` scales all three coordinates by `λ`, so the
projective point does not depend on the chosen lift. -/
noncomputable def invCoord (g : PGL2 K) : Fin 3 → K :=
  let M : Matrix (Fin 2) (Fin 2) K := (Quotient.out g : GL (Fin 2) K)
  let t := (M 0 0 + M 1 1) / 2
  ![M 0 0 - t, M 0 1, M 1 0]

/-- The linear form on the involution plane vanishing on the point attached to `g` — in other
words, the value at `invCoord g` of the form with coefficient vector `v`. -/
noncomputable def lineForm (v : Fin 3 → K) (g : PGL2 K) : K := ∑ i, v i * invCoord g i

/-- The points of `S` lying on the projective line `{P | ⟨v, P⟩ = 0}` of the involution
plane. -/
noncomputable def lineTrace (v : Fin 3 → K) (S : Set (PGL2 K)) : Set (PGL2 K) :=
  {s ∈ S | lineForm v s = 0}

/-- `S` is *collinear* if its elements, viewed as points of the projective plane of trace-zero
`2 × 2` matrices, lie on one projective line: there is a nonzero linear form `v` on the
coordinates `[A : B : C]` vanishing on all of them. -/
def IsCollinear (S : Set (PGL2 K)) : Prop :=
  ∃ v : Fin 3 → K, v ≠ 0 ∧ ∀ s ∈ S, lineForm v s = 0

/-- Cayley–Hamilton for `2 × 2` matrices: `M² = tr(M) • M − det(M) • 1`. -/
lemma sq_eq_trace_smul_sub_det (M : Matrix (Fin 2) (Fin 2) K) :
    M * M = M.trace • M - M.det • (1 : Matrix (Fin 2) (Fin 2) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two,
      Matrix.one_apply, Matrix.smul_apply, Matrix.sub_apply] <;> ring

/-- A nonidentity involution of `PGL₂(K)` has trace-zero matrix representative `Quotient.out h`:
its square is a nonzero scalar, and Cayley–Hamilton forces the trace to vanish. -/
lemma trace_zero_of_isInvolution {h : PGL2 K} (hh : IsInvolution h) :
    ((Quotient.out h : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).trace = 0 := by
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
  have hMdet : M.det ≠ 0 := Matrix.GeneralLinearGroup.det_ne_zero g
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
  have hCH := sq_eq_trace_smul_sub_det M
  rw [hsq] at hCH
  have hkey : M.trace • M = ((u : K) + M.det) • (1 : Matrix (Fin 2) (Fin 2) K) := by
    have h4 : M.trace • M = (u : K) • (1 : Matrix (Fin 2) (Fin 2) K) +
        M.det • (1 : Matrix (Fin 2) (Fin 2) K) := by
      calc M.trace • M = (M.trace • M - M.det • (1 : Matrix (Fin 2) (Fin 2) K)) +
          M.det • (1 : Matrix (Fin 2) (Fin 2) K) := (sub_add_cancel _ _).symm
        _ = (u : K) • (1 : Matrix (Fin 2) (Fin 2) K) +
            M.det • (1 : Matrix (Fin 2) (Fin 2) K) := by rw [← hCH]
    rw [h4, ← add_smul]
  by_contra htr
  have hMscalar : M = (((u : K) + M.det) / M.trace) • (1 : Matrix (Fin 2) (Fin 2) K) := by
    calc M = M.trace⁻¹ • (M.trace • M) := by rw [smul_smul, inv_mul_cancel₀ htr, one_smul]
      _ = M.trace⁻¹ • (((u : K) + M.det) • (1 : Matrix (Fin 2) (Fin 2) K)) := by rw [hkey]
      _ = (((u : K) + M.det) / M.trace) • (1 : Matrix (Fin 2) (Fin 2) K) := by
        rw [smul_smul, mul_comm (M.trace⁻¹) (↑u + M.det), ← div_eq_mul_inv]
  have hc : ((u : K) + M.det) / M.trace ≠ 0 := by
    intro hcz
    apply hMdet
    rw [hMscalar, hcz, zero_smul]
    simp
  have hcomm : ∀ x : GL (Fin 2) K, (g : Matrix (Fin 2) (Fin 2) K) * (x : Matrix (Fin 2) (Fin 2) K) =
      (x : Matrix (Fin 2) (Fin 2) K) * (g : Matrix (Fin 2) (Fin 2) K) := by
    intro x
    rw [← hM, hMscalar]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, Fin.sum_univ_two, smul_eq_mul] <;>
      ring
  have hgcenter : g ∈ Subgroup.center (GL (Fin 2) K) := by
    rw [Subgroup.mem_center_iff]
    intro x
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul]
    exact (hcomm x).symm
  have hh1 : h = 1 := by
    rw [← Quotient.out_eq h, QuotientGroup.eq_one_iff]
    exact hgcenter
  exact hh.1 hh1

/-- For a nonidentity projective involution the coordinates `invCoord` are the paper's
`[A : B : C]`: a nonzero vector with `A² + BC ≠ 0`, i.e. a point off the conic `Q = 0` of the
involution plane `Q(U, V, W) = U² + VW`. (The condition `A² + BC = -det M ≠ 0` is exactly
invertibility of the matrix.) -/
lemma invCoord_normalized (h2 : (2 : K) ≠ 0) {s : PGL2 K} (hs : IsInvolution s) :
    invCoord s ≠ 0 ∧ (invCoord s 0) ^ 2 + (invCoord s 1) * (invCoord s 2) ≠ 0 := by
  classical
  set M : Matrix (Fin 2) (Fin 2) K := ((Quotient.out s : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
    with hM
  have htr : M.trace = 0 := trace_zero_of_isInvolution hs
  have hdet : M.det ≠ 0 := Matrix.GeneralLinearGroup.det_ne_zero (Quotient.out s)
  have htr' : M 0 0 + M 1 1 = 0 := by
    rw [← Matrix.trace_fin_two]
    exact htr
  have h11 : M 1 1 = -M 0 0 := by linear_combination htr'
  have hcoord : invCoord s = ![M 0 0 - (M 0 0 + M 1 1) / 2, M 0 1, M 1 0] := rfl
  rw [hcoord]
  have ht : (M 0 0 + M 1 1) / 2 = 0 := by rw [htr', zero_div]
  rw [ht, sub_zero]
  constructor
  · intro hzero
    have h00 : M 0 0 = 0 := by
      have := congrArg (fun v : Fin 3 → K => v 0) hzero
      simpa using this
    have h01 : M 0 1 = 0 := by
      have := congrArg (fun v : Fin 3 → K => v 1) hzero
      simpa using this
    have h10 : M 1 0 = 0 := by
      have := congrArg (fun v : Fin 3 → K => v 2) hzero
      simpa using this
    have hMzero : M = 0 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h11]
    rw [hMzero, Matrix.det_zero] at hdet
    exact hdet rfl
  · intro hQ
    have hsq : M 0 0 ^ 2 + M 0 1 * M 1 0 = 0 := by
      simpa using hQ
    have hdet0 : M.det = 0 := by
      rw [Matrix.det_fin_two, h11]
      linear_combination -hsq
    exact hdet hdet0

/-! ### Counting the projective line -/

variable [Fintype K]

noncomputable instance : Fintype (P1 K) := Fintype.ofFinite _

/-- The projective line over a field with `q` elements has `q + 1` points. -/
lemma card_P1 : Nat.card (P1 K) = Nat.card K + 1 := by
  rw [Nat.card_eq_fintype_card (α := K)]
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  have hq1 : 1 ≤ Fintype.card K := by omega
  have hV : Nat.card (Fin 2 → K) = Fintype.card K ^ 2 := by
    rw [Nat.card_pi]; simp
  have h := Projectivization.card' (k := K) (V := Fin 2 → K)
  rw [hV] at h
  have hKc : Nat.card K = Fintype.card K := Nat.card_eq_fintype_card
  rw [hKc] at h
  -- `h : Fintype.card K ^ 2 = Nat.card (ℙ K (Fin 2 → K)) * (Fintype.card K - 1) + 1`
  have hZ : (Fintype.card K : ℤ) ^ 2 =
      (Nat.card (P1 K) : ℤ) * ((Fintype.card K : ℤ) - 1) + 1 := by
    have hcast := congrArg (Nat.cast : ℕ → ℤ) h
    push_cast at hcast
    rw [Nat.cast_sub hq1] at hcast
    exact hcast
  have keyZ : (Fintype.card K : ℤ) ^ 2 =
      ((Fintype.card K : ℤ) + 1) * ((Fintype.card K : ℤ) - 1) + 1 := by ring
  have hmul : (Nat.card (P1 K) : ℤ) * ((Fintype.card K : ℤ) - 1) =
      ((Fintype.card K : ℤ) + 1) * ((Fintype.card K : ℤ) - 1) := by
    linarith
  have hpos : (Fintype.card K : ℤ) - 1 ≠ 0 := by
    have h2 : (2 : ℤ) ≤ Fintype.card K := by exact_mod_cast hq
    linarith
  have hc : (Nat.card (P1 K) : ℤ) = (Fintype.card K : ℤ) + 1 :=
    mul_right_cancel₀ hpos hmul
  exact_mod_cast hc

/-- The point `σ x` is determined by `S` and `x`: for an admissible `S` of size `q` there is a
permutation `σ` playing the role of the missing permutation, and it is an involution (the
paragraph following (1) in the paper). -/
private lemma hinj_smul {S : Set (PGL2 K)} (hS : IsAdmissible S) (x : P1 K) :
    ∀ s ∈ S, ∀ t ∈ S, s • x = t • x → s = t := by
  intro s hs t ht heq
  by_contra hne
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right (hS.1 t ht).2
  have h1 : (t⁻¹ * s) • x = x := by
    rw [mul_smul, heq, ← mul_smul, inv_mul_cancel, one_smul]
  rw [htinv] at h1
  exact hS.2 t ht s hs (fun h => hne h.symm) x h1

lemma exists_isMissingPerm {S : Set (PGL2 K)} (hS : IsAdmissible S)
    (hcard : Nat.card S = Nat.card K) :
    ∃ σ : Equiv.Perm (P1 K), IsMissingPerm S σ ∧ σ * σ = 1 := by
  classical
  have huniq : ∀ x : P1 K, ∃! y : P1 K, ¬ ∃ s ∈ S, s • x = y := by
    intro x
    have himg : Nat.card ((fun s : PGL2 K => s • x) '' S) = Nat.card S := by
      refine Nat.card_image_of_injOn ?_
      intro a ha b hb hab
      exact hinj_smul hS x a ha b hb hab
    have hcompl : Nat.card {y : P1 K // ¬ ∃ s ∈ S, s • x = y} = 1 := by
      have e := Equiv.sumCompl (fun y : P1 K => ∃ s ∈ S, s • x = y)
      have h := Nat.card_congr e
      rw [Nat.card_sum] at h
      have hsub : Nat.card {y : P1 K // ∃ s ∈ S, s • x = y}
          = Nat.card ((fun s : PGL2 K => s • x) '' S) := rfl
      have h1 : Nat.card {y : P1 K // ∃ s ∈ S, s • x = y} = Nat.card K := by
        rw [hsub, himg, hcard]
      rw [h1, card_P1] at h
      omega
    obtain ⟨y₀, hy₀⟩ := Nat.card_eq_one_iff_exists.1 hcompl
    exact ⟨y₀.1, y₀.2, fun b hb => congrArg Subtype.val (hy₀ ⟨b, hb⟩)⟩
  set φ : P1 K → P1 K := fun x => (huniq x).choose with hφ
  have hφspec : ∀ x, ¬ ∃ s ∈ S, s • x = φ x := fun x => (huniq x).choose_spec.1
  have hφuniq : ∀ x y, (¬ ∃ s ∈ S, s • x = y) → y = φ x :=
    fun x y hy => (huniq x).unique hy (hφspec x)
  have hinvol : Function.Involutive φ := by
    intro x
    have hx : ¬ ∃ s ∈ S, s • (φ x) = x := by
      rintro ⟨s, hs, hsm⟩
      have h3 : s • (s • (φ x)) = s • x := by rw [hsm]
      rw [← mul_smul, (hS.1 s hs).2, one_smul] at h3
      exact hφspec x ⟨s, hs, h3.symm⟩
    exact (hφuniq (φ x) x hx).symm
  have hbij : Function.Bijective φ := ⟨hinvol.injective, hinvol.surjective⟩
  refine ⟨Equiv.ofBijective φ hbij, ?_, ?_⟩
  · intro x y
    constructor
    · rintro ⟨s, hs, hxy⟩ h
      exact hφspec x ⟨s, hs, hxy.trans h⟩
    · intro hne
      by_contra hcon
      exact hne (hφuniq x y hcon)
  · ext x
    exact hinvol x


/-- An involution without fixed points on a finite type has an even number of elements,
since `x ↦ {x, g x}` partitions the type into two-element blocks. -/
lemma even_card_of_involutive_no_fixed {X : Type*} [Fintype X] (g : X → X)
      (hg : Function.Involutive g) (hnf : ∀ x, g x ≠ x) : Even (Fintype.card X) := by
  classical
  set f : X → Finset X := fun x => {x, g x} with hf
  have hfiber : ∀ x : X, Finset.univ.filter (fun y => f y = f x) = {x, g x} := by
      intro x
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hf]
      constructor
      · intro h
        have hx : x ∈ ({y, g y} : Finset X) := by rw [h]; simp
        rw [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with h1 | h1
        · rw [← h1]; simp
        · have h2 : y = g x := by
            rw [← hg y]
            exact congrArg g h1.symm
          rw [h2]; simp
      · intro h
        rw [Finset.mem_insert, Finset.mem_singleton] at h
        rcases h with rfl | rfl
        · rfl
        · show ({g x, g (g x)} : Finset X) = {x, g x}
          rw [hg x, Finset.pair_comm]
  have hfib2 : ∀ b ∈ Finset.univ.image f, (Finset.univ.filter (fun y => f y = b)).card = 2 := by
      intro b hb
      obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hb
      rw [hfiber x, Finset.card_pair (hnf x).symm]
  have hmain := Finset.card_eq_sum_card_fiberwise (f := f) (s := (Finset.univ : Finset X))
      (t := Finset.univ.image f) (fun a _ => Finset.mem_image_of_mem f (Finset.mem_univ a))
  rw [Finset.sum_congr rfl hfib2, Finset.sum_const, Nat.nsmul_eq_mul] at hmain
  rw [← Finset.card_univ, hmain]
  exact ⟨_, by rw [mul_comm, two_mul]⟩

/-- The missing permutation is unique: if `σ` and `τ` both satisfy (1), they agree everywhere,
since `σ x` (respectively `τ x`) is the unique point not of the form `s • x`, `s ∈ S`. -/
lemma eq_of_isMissingPerm {S : Set (PGL2 K)} {σ τ : P1 K → P1 K}
    (hσ : IsMissingPerm S σ) (hτ : IsMissingPerm S τ) : σ = τ := by
  funext x
  have h1 : ¬ ∃ s ∈ S, s • x = σ x := by
    intro h
    rw [hσ x (σ x)] at h
    exact h rfl
  have h2 : τ x = σ x := by
    by_contra hneq
    exact h1 ((hτ x (σ x)).2 (fun h => hneq h.symm))
  exact h2.symm

/-- The number of fixed points of the missing permutation is even: an involution of the
`q + 1` points of `ℙ¹(K)` fixes `f` points, and `q + 1 - f` is even. -/
lemma even_numFixed {σ : Equiv.Perm (P1 K)} (hσ : σ * σ = 1) :
    Even (Nat.card (P1 K) - numFixed σ) := by
  classical
  have hsq : ∀ y : P1 K, σ (σ y) = y := by
    intro y
    have h := congrFun (congrArg (fun e : Equiv.Perm (P1 K) => (⇑e : P1 K → P1 K)) hσ) y
    simpa using h
  -- `ℙ¹` splits into the fixed points of `σ` and the rest, on which `σ` is a fixed-point-free
  -- involution
  have hsplit : Nat.card (P1 K) = numFixed σ + Nat.card {x : P1 K // σ x ≠ x} := by
    have e := Equiv.sumCompl (fun x : P1 K => σ x = x)
    have h := Nat.card_congr e
    rw [Nat.card_sum] at h
    show Nat.card (P1 K) = Nat.card {x : P1 K // σ x = x} + Nat.card {x : P1 K // ¬ (σ x = x)}
    exact h.symm
  have hcomp : ∀ y : {x : P1 K // σ x ≠ x}, σ (σ y.1) ≠ σ y.1 := by
    intro y h
    have h1 : y.1 = σ y.1 := by
      rw [hsq y.1] at h
      exact h
    exact y.2 h1.symm
  let g : {x : P1 K // σ x ≠ x} → {x : P1 K // σ x ≠ x} :=
    fun y => ⟨σ y.1, hcomp y⟩
  have hinv : Function.Involutive g := by
    intro y
    apply Subtype.ext
    exact hsq y.1
  have hnf : ∀ y, g y ≠ y := fun y h => y.2 (congrArg Subtype.val h)
  have heven : Even (Nat.card {x : P1 K // σ x ≠ x}) := by
    rw [Nat.card_eq_fintype_card]
    exact even_card_of_involutive_no_fixed g hinv hnf
  obtain ⟨k, hk⟩ := heven
  have hsub : Nat.card (P1 K) - numFixed σ = Nat.card {x : P1 K // σ x ≠ x} := by
    omega
  rw [hsub, hk]
  exact ⟨k, rfl⟩

end PGL2
