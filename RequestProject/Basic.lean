module

public import RequestProject.Defs

/-! Auxiliary facts about the projective line, `PGL₂(K)` and sharply transitive sets. -/

@[expose] public section

open scoped LinearAlgebra.Projectivization

namespace PGL2

variable {K : Type*} [Field K]

/-- The point `(x : y)` of the projective line (junk value `(1 : 0)` if `x = y = 0`). -/
noncomputable def pt (x y : K) : ℙ K (Fin 2 → K) := by
  classical
  exact if h : ![x, y] ≠ 0 then Projectivization.mk K ![x, y] h
    else Projectivization.mk K ![1, 0] (by simp)

lemma vec_ne_zero {x y : K} (h : x ≠ 0 ∨ y ≠ 0) : (![x, y] : Fin 2 → K) ≠ 0 := by
  intro h0
  have h0' := congrFun h0 0
  have h1' := congrFun h0 1
  simp at h0' h1'
  tauto

lemma pt_eq_mk {x y : K} (h : (![x, y] : Fin 2 → K) ≠ 0) :
    pt x y = Projectivization.mk K ![x, y] h := by
  simp [pt, h]

lemma pt_eq_pt_iff {a b c d : K} (h1 : a ≠ 0 ∨ b ≠ 0) (h2 : c ≠ 0 ∨ d ≠ 0) :
    pt a b = pt c d ↔ a * d = b * c := by
  rw [pt_eq_mk (vec_ne_zero h1), pt_eq_mk (vec_ne_zero h2), Projectivization.mk_eq_mk_iff]
  constructor
  · rintro ⟨u, hu⟩
    have e0 := congrFun hu 0
    have e1 := congrFun hu 1
    simp [Units.smul_def] at e0 e1
    rw [← e0, ← e1]; ring
  · intro h
    rcases h2 with hc | hd
    · have hu : a / c ≠ 0 := by
        intro h0
        rw [div_eq_zero_iff] at h0
        rcases h0 with h0 | h0
        · subst h0; rcases h1 with h1 | h1
          · exact h1 rfl
          · exact h1 (by simpa [hc] using h.symm)
        · exact hc h0
      refine ⟨Units.mk0 _ hu, ?_⟩
      ext i; fin_cases i <;> simp [Units.smul_def] <;> field_simp; linear_combination h
    · have hu : b / d ≠ 0 := by
        intro h0
        rw [div_eq_zero_iff] at h0
        rcases h0 with h0 | h0
        · subst h0; rcases h1 with h1 | h1
          · exact h1 (by simpa [hd] using h)
          · exact h1 rfl
        · exact hd h0
      refine ⟨Units.mk0 _ hu, ?_⟩
      ext i; fin_cases i <;> simp [Units.smul_def] <;> field_simp; linear_combination -h

lemma smul_pt (g : GL (Fin 2) K) {x y : K} (h : x ≠ 0 ∨ y ≠ 0) :
    g • pt x y = pt (g 0 0 * x + g 0 1 * y) (g 1 0 * x + g 1 1 * y) := by
  have hv : (![g 0 0 * x + g 0 1 * y, g 1 0 * x + g 1 1 * y] : Fin 2 → K) ≠ 0 := by
    have := (smul_ne_zero_iff_ne g).mpr (vec_ne_zero h)
    convert this using 1
    ext i; fin_cases i <;> simp [Units.smul_def, Fin.sum_univ_two]
  rw [pt_eq_mk (vec_ne_zero h), pt_eq_mk hv, Projectivization.smul_mk]
  congr 1
  ext i; fin_cases i <;> simp [Units.smul_def, Fin.sum_univ_two]

lemma pt_surj (p : ℙ K (Fin 2 → K)) : ∃ x y : K, (x ≠ 0 ∨ y ≠ 0) ∧ p = pt x y := by
  induction p using Projectivization.ind with
  | h v hv =>
    have hxy : v 0 ≠ 0 ∨ v 1 ≠ 0 := by
      by_contra hc; push_neg at hc
      exact hv (by ext i; fin_cases i <;> simp [hc])
    refine ⟨v 0, v 1, hxy, ?_⟩
    rw [pt_eq_mk (vec_ne_zero hxy)]
    congr 1
    ext i; fin_cases i <;> simp

lemma det_ne_zero (g : GL (Fin 2) K) : g 0 0 * g 1 1 - g 0 1 * g 1 0 ≠ 0 := by
  rw [← Matrix.det_fin_two]
  exact (Matrix.GeneralLinearGroup.det g).ne_zero

/-- Equality in `PGL₂` of images of elements of `GL₂`. -/
lemma mk_eq_mk_iff (g g' : GL (Fin 2) K) :
    (g : PGL2 K) = (g' : PGL2 K) ↔ ∃ c : Kˣ, ∀ i j, g' i j = c * g i j := by
  rw [QuotientGroup.eq, Matrix.GeneralLinearGroup.center_eq_range_scalar]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, fun i j => ?_⟩
    have : g' = g * Matrix.GeneralLinearGroup.scalar (Fin 2) c := by rw [hc]; group
    rw [this]
    simp [Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply, Matrix.diagonal_apply, mul_comm]
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    rw [eq_inv_mul_iff_mul_eq]
    ext i j
    rw [hc]
    simp [Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply, Matrix.diagonal_apply, mul_comm]

end PGL2

namespace IsSharplyTransitive

variable {G X : Type*} [Group G] [MulAction G X] {S : Set G}

lemma unique (hS : IsSharplyTransitive (X := X) S) {g g' : G} (hg : g ∈ S) (hg' : g' ∈ S)
    {x : X} (h : g • x = g' • x) : g = g' :=
  (hS x (g' • x)).unique ⟨hg, h⟩ ⟨hg', rfl⟩

lemma exists_smul (hS : IsSharplyTransitive (X := X) S) (x y : X) : ∃ g ∈ S, g • x = y :=
  (hS x y).exists

/-- A nonidentity element of a regular set containing `1` has no fixed points. -/
lemma eq_one_of_smul_eq (hS : IsSharplyTransitive (X := X) S) (h1 : (1 : G) ∈ S) {g : G}
    (hg : g ∈ S) {x : X} (h : g • x = x) : g = 1 :=
  hS.unique hg h1 (by simpa using h)

/-- Two-sided translates of regular sets are regular. -/
lemma translate (hS : IsSharplyTransitive (X := X) S) (a b : G) :
    IsSharplyTransitive (X := X) ((fun s => a * s * b) '' S) := by
  intro x y
  obtain ⟨s, hs, hsx⟩ := hS.exists_smul (b • x) (a⁻¹ • y)
  refine ⟨a * s * b, ⟨⟨s, hs, rfl⟩, ?_⟩, ?_⟩
  · simp [mul_smul, hsx]
  · rintro _ ⟨⟨t, ht, rfl⟩, htx⟩
    have : t • (b • x) = s • (b • x) := by
      rw [hsx]; rw [← htx]; simp [mul_smul]
    rw [hS.unique ht hs this]

lemma card_eq [Nonempty X] (hS : IsSharplyTransitive (X := X) S) :
    Nat.card S = Nat.card X := by
  obtain ⟨x0⟩ := ‹Nonempty X›
  refine Nat.card_eq_of_bijective (fun s : S => (s : G) • x0) ⟨?_, ?_⟩
  · rintro ⟨s, hs⟩ ⟨t, ht⟩ h
    exact Subtype.ext (hS.unique hs ht h)
  · intro y
    obtain ⟨s, hs, h⟩ := hS.exists_smul x0 y
    exact ⟨⟨s, hs⟩, h⟩

end IsSharplyTransitive
