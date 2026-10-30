module

public import RequestProject.Basic

/-!
# Lemma 2 of Eberhard, *Sharply transitive sets in PGL₂(K)*

A version of Segre's "lemma of the tangents": if a sharply transitive subset `S` of
`PGL₂(K)` contains elements of the shapes
`g₁ = [[0, b₁], [c₁, d₁]]`, `g₂ = [[a₂, 0], [c₂, d₂]]`, `g₃ = [[a₃, b₃], [0, d₃]]`,
`g₄ = [[a₄, b₄], [c₄, 0]]`, then `b₁ d₂ a₃ c₄ = c₁ a₂ d₃ b₄`.
-/

@[expose] public section

open scoped LinearAlgebra.Projectivization
open Classical

namespace PGL2

variable {K : Type*} [Field K]

/-- The image of a nonzero vector under an element of `GL₂` is nonzero. -/
lemma smul_vec_ne_zero (g : GL (Fin 2) K) {x y : K} (h : x ≠ 0 ∨ y ≠ 0) :
    g 0 0 * x + g 0 1 * y ≠ 0 ∨ g 1 0 * x + g 1 1 * y ≠ 0 := by
  by_contra hc
  push_neg at hc
  have hd := det_ne_zero g
  rcases h with h | h
  · apply h
    have : (g 0 0 * g 1 1 - g 0 1 * g 1 0) * x = 0 := by
      linear_combination g 1 1 * hc.1 - g 0 1 * hc.2
    simpa [hd] using this
  · apply h
    have : (g 0 0 * g 1 1 - g 0 1 * g 1 0) * y = 0 := by
      linear_combination - g 1 0 * hc.1 + g 0 0 * hc.2
    simpa [hd] using this

/-- `g • (x : y) = (x' : y')` in terms of matrix entries. -/
lemma smul_pt_eq_pt_iff (g : GL (Fin 2) K) {x y x' y' : K} (h : x ≠ 0 ∨ y ≠ 0)
    (h' : x' ≠ 0 ∨ y' ≠ 0) :
    g • pt x y = pt x' y' ↔
      (g 0 0 * x + g 0 1 * y) * y' = (g 1 0 * x + g 1 1 * y) * x' := by
  rw [smul_pt g h, pt_eq_pt_iff (smul_vec_ne_zero g h) h']

/-- A chosen representative in `GL₂(K)` of an element of `PGL₂(K)`. -/
noncomputable def rep (s : PGL2 K) : GL (Fin 2) K := Quotient.out s

@[simp] lemma mk_rep (s : PGL2 K) : ((rep s : GL (Fin 2) K) : PGL2 K) = s :=
  QuotientGroup.out_eq' s

lemma smul_eq_rep_smul (s : PGL2 K) (x : ℙ K (Fin 2 → K)) : s • x = rep s • x := by
  conv_lhs => rw [← mk_rep s]
  rfl

/-- Wilson's theorem for finite fields, in the form of a product over a set in bijection with
the nonzero elements. -/
lemma prod_eq_neg_one_of_bij [Fintype K] {ι : Type*} (F : Finset ι) (φ : ι → K)
    (hinj : Set.InjOn φ F) (hne : ∀ i ∈ F, φ i ≠ 0) (hsurj : ∀ t ≠ 0, ∃ i ∈ F, φ i = t) :
    ∏ i ∈ F, φ i = -1 := by
  have h := Finset.prod_image (f := fun x : K => x) hinj
  rw [← h]
  have himg : F.image φ = Finset.univ.map ⟨((↑) : Kˣ → K), Units.val_injective⟩ := by
    ext t
    simp only [Finset.mem_image, Finset.mem_map, Finset.mem_univ, true_and,
      Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨Units.mk0 _ (hne i hi), rfl⟩
    · rintro ⟨u, rfl⟩
      exact hsurj u u.ne_zero
  rw [himg, Finset.prod_map]
  have := congrArg Units.val (FiniteField.prod_univ_units_id_eq_neg_one (K := K))
  simpa using this

/-- The pointwise algebraic identity behind Lemma 2. -/
lemma pointwise_identity (a b c d : K) (hdet : a * d - b * c ≠ 0) :
    ((if a ≠ 0 ∧ b ≠ 0 then a / b else 1) * (if b ≠ 0 ∧ d ≠ 0 then b / d else 1) *
      (if c ≠ 0 ∧ d ≠ 0 then d / c else 1) * (if a ≠ 0 ∧ c ≠ 0 then c / a else 1)) =
    (if a = 0 then b / c else 1) * (if b = 0 then d / a else 1) *
      (if c = 0 then a / d else 1) * (if d = 0 then c / b else 1) := by
  by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> by_cases hc : c = 0 <;> by_cases hd : d = 0 <;>
    simp_all <;> field_simp

variable [Fintype K]

/-- The product of the "slopes" `φ s` over those `s ∈ S` satisfying `cond`, where `φ`
is characterized by the action, equals `-1`. -/
lemma prod_slopes (S : Set (PGL2 K)) (hS : IsSharplyTransitive (X := ℙ K (Fin 2 → K)) S)
    (cond : PGL2 K → Prop) [DecidablePred cond] (φ : PGL2 K → K)
    (P Q : K → ℙ K (Fin 2 → K)) (hφ : ∀ s, cond s → φ s ≠ 0)
    (hchar : ∀ s ∈ S, ∀ t ≠ 0, (cond s ∧ φ s = t) ↔ s • P t = Q t) :
    ∏ s ∈ S.toFinset.filter cond, φ s = -1 := by
  apply prod_eq_neg_one_of_bij
  · intro s hs s' hs' h
    simp only [Finset.coe_filter, Set.mem_toFinset, Set.mem_setOf_eq] at hs hs'
    have h1 := (hchar s hs.1 (φ s) (hφ s hs.2)).1 ⟨hs.2, rfl⟩
    have h2 := (hchar s' hs'.1 (φ s) (hφ s hs.2)).1 ⟨hs'.2, h.symm⟩
    exact hS.unique hs.1 hs'.1 (h1.trans h2.symm)
  · intro s hs
    simp only [Finset.mem_filter, Set.mem_toFinset] at hs
    exact hφ s hs.2
  · intro t ht
    obtain ⟨s, hs, h⟩ := hS.exists_smul (P t) (Q t)
    have := (hchar s hs t ht).2 h
    exact ⟨s, Finset.mem_filter.2 ⟨by simpa using hs, this.1⟩, this.2⟩

/-- A product over a regular set of a function which is trivial away from one element. -/
lemma prod_single (S : Set (PGL2 K)) (Z : PGL2 K → Prop) [DecidablePred Z] (ψ : PGL2 K → K)
    (s₀ : PGL2 K) (hs₀ : s₀ ∈ S) (hZ : ∀ s ∈ S, Z s ↔ s = s₀) :
    ∏ s ∈ S.toFinset, (if Z s then ψ s else 1) = ψ s₀ := by
  rw [Finset.prod_eq_single s₀]
  · simp [(hZ s₀ hs₀).2 rfl]
  · intro s hs hne
    simp only [Set.mem_toFinset] at hs
    simp [show ¬ Z s from fun h => hne ((hZ s hs).1 h)]
  · intro h; exact absurd (by simpa using hs₀) h

end PGL2

open PGL2

/-- **Lemma 2** (Eberhard). Suppose `S` is a sharply transitive subset of `PGL₂(K)`
containing (the images of) the matrices
`g₁ = [[0, b₁], [c₁, d₁]]`, `g₂ = [[a₂, 0], [c₂, d₂]]`, `g₃ = [[a₃, b₃], [0, d₃]]`,
`g₄ = [[a₄, b₄], [c₄, 0]]`. Then `b₁ d₂ a₃ c₄ = c₁ a₂ d₃ b₄`. -/
theorem eberhard_lemma2 {K : Type*} [Field K] [Fintype K] (S : Set (PGL2 K))
    (hS : IsSharplyTransitive (X := ℙ K (Fin 2 → K)) S)
    (g₁ g₂ g₃ g₄ : GL (Fin 2) K)
    (hg₁S : (g₁ : PGL2 K) ∈ S) (hg₂S : (g₂ : PGL2 K) ∈ S)
    (hg₃S : (g₃ : PGL2 K) ∈ S) (hg₄S : (g₄ : PGL2 K) ∈ S)
    (hg₁ : g₁ 0 0 = 0) (hg₂ : g₂ 0 1 = 0) (hg₃ : g₃ 1 0 = 0) (hg₄ : g₄ 1 1 = 0) :
    g₁ 0 1 * g₂ 1 1 * g₃ 0 0 * g₄ 1 0 = g₁ 1 0 * g₂ 0 0 * g₃ 1 1 * g₄ 0 1 := by
  set A : PGL2 K → K := fun s => rep s 0 0 with hA
  set B : PGL2 K → K := fun s => rep s 0 1 with hB
  set C : PGL2 K → K := fun s => rep s 1 0 with hC
  set D : PGL2 K → K := fun s => rep s 1 1 with hD
  have hdet : ∀ s, A s * D s - B s * C s ≠ 0 := fun s => det_ne_zero (rep s)
  have act : ∀ s : PGL2 K, ∀ {x y x' y' : K}, (x ≠ 0 ∨ y ≠ 0) → (x' ≠ 0 ∨ y' ≠ 0) →
      (s • pt x y = pt x' y' ↔ (A s * x + B s * y) * y' = (C s * x + D s * y) * x') := by
    intro s x y x' y' h h'
    rw [smul_eq_rep_smul]
    exact smul_pt_eq_pt_iff _ h h'
  have one0 : (1 : K) ≠ 0 ∨ (0 : K) ≠ 0 := Or.inl one_ne_zero
  have zero1 : (0 : K) ≠ 0 ∨ (1 : K) ≠ 0 := Or.inr one_ne_zero
  -- the four Wilson products
  have P1 := prod_slopes S hS (fun s => A s ≠ 0 ∧ B s ≠ 0) (fun s => A s / B s)
    (fun t => pt 1 (-t)) (fun _ => pt 0 1) (fun s h => div_ne_zero h.1 h.2) (by
      intro s hs t ht
      beta_reduce
      rw [act s (Or.inl one_ne_zero) (Or.inr one_ne_zero)]
      constructor
      · rintro ⟨⟨ha, hb⟩, rfl⟩; field_simp; ring
      · intro h
        have h' : A s = B s * t := by linear_combination h
        have hb : B s ≠ 0 := by
          intro hb; apply hdet s; simp [h', hb]
        refine ⟨⟨by rw [h']; exact mul_ne_zero hb ht, hb⟩, ?_⟩
        beta_reduce; rw [h']; field_simp)
  have P2 := prod_slopes S hS (fun s => B s ≠ 0 ∧ D s ≠ 0) (fun s => B s / D s)
    (fun _ => pt 0 1) (fun t => pt t 1) (fun s h => div_ne_zero h.1 h.2) (by
      intro s hs t ht
      beta_reduce
      rw [act s zero1 (Or.inr one_ne_zero)]
      constructor
      · rintro ⟨⟨ha, hb⟩, rfl⟩; field_simp; ring
      · intro h
        have h' : B s = D s * t := by linear_combination h
        have hd : D s ≠ 0 := by
          intro hd; apply hdet s; simp [h', hd]
        refine ⟨⟨by rw [h']; exact mul_ne_zero hd ht, hd⟩, ?_⟩
        beta_reduce; rw [h']; field_simp)
  have P3 := prod_slopes S hS (fun s => C s ≠ 0 ∧ D s ≠ 0) (fun s => D s / C s)
    (fun t => pt t (-1)) (fun _ => pt 1 0) (fun s h => div_ne_zero h.2 h.1) (by
      intro s hs t ht
      beta_reduce
      rw [act s (Or.inr (neg_ne_zero.2 one_ne_zero)) one0]
      constructor
      · rintro ⟨⟨ha, hb⟩, rfl⟩; field_simp; ring
      · intro h
        have h' : D s = C s * t := by linear_combination h
        have hc : C s ≠ 0 := by
          intro hc; apply hdet s; simp [h', hc]
        refine ⟨⟨hc, by rw [h']; exact mul_ne_zero hc ht⟩, ?_⟩
        beta_reduce; rw [h']; field_simp)
  have P4 := prod_slopes S hS (fun s => A s ≠ 0 ∧ C s ≠ 0) (fun s => C s / A s)
    (fun _ => pt 1 0) (fun t => pt 1 t) (fun s h => div_ne_zero h.2 h.1) (by
      intro s hs t ht
      beta_reduce
      rw [act s one0 (Or.inl one_ne_zero)]
      constructor
      · rintro ⟨⟨ha, hb⟩, rfl⟩; field_simp; ring
      · intro h
        have h' : C s = A s * t := by linear_combination -h
        have ha : A s ≠ 0 := by
          intro ha; apply hdet s; simp [h', ha]
        refine ⟨⟨ha, by rw [h']; exact mul_ne_zero ha ht⟩, ?_⟩
        beta_reduce; rw [h']; field_simp)
  rw [Finset.prod_filter] at P1 P2 P3 P4
  have hall := congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg₂ (· * ·) P1 P2) P3) P4
  norm_num at hall
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib] at hall
  rw [Finset.prod_congr rfl (fun s _ => pointwise_identity (A s) (B s) (C s) (D s) (hdet s))]
    at hall
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib] at hall
  have key : ∀ (Z : PGL2 K → Prop) (p q : ℙ K (Fin 2 → K)) (s₀ : PGL2 K), s₀ ∈ S →
      (∀ s, Z s ↔ s • p = q) → s₀ • p = q → ∀ s ∈ S, Z s ↔ s = s₀ := by
    intro Z p q s₀ hs₀ hZ hq s hs
    rw [hZ]
    constructor
    · intro h; exact hS.unique hs hs₀ (h.trans hq.symm)
    · rintro rfl; exact hq
  have Za := key (fun s => A s = 0) (pt 1 0) (pt 0 1) _ hg₁S
    (fun s => by rw [act s one0 zero1]; simp)
    (by rw [PGL2.mk_smul, smul_pt_eq_pt_iff _ one0 zero1]; simp [hg₁])
  have Zb := key (fun s => B s = 0) (pt 0 1) (pt 0 1) _ hg₂S
    (fun s => by rw [act s zero1 zero1]; simp)
    (by rw [PGL2.mk_smul, smul_pt_eq_pt_iff _ zero1 zero1]; simp [hg₂])
  have Zc := key (fun s => C s = 0) (pt 1 0) (pt 1 0) _ hg₃S
    (fun s => by rw [act s one0 one0]; simp [eq_comm])
    (by rw [PGL2.mk_smul, smul_pt_eq_pt_iff _ one0 one0]; simp [hg₃])
  have Zd := key (fun s => D s = 0) (pt 0 1) (pt 1 0) _ hg₄S
    (fun s => by rw [act s zero1 one0]; simp [eq_comm])
    (by rw [PGL2.mk_smul, smul_pt_eq_pt_iff _ zero1 one0]; simp [hg₄])
  rw [prod_single S _ _ _ hg₁S Za, prod_single S _ _ _ hg₂S Zb, prod_single S _ _ _ hg₃S Zc,
    prod_single S _ _ _ hg₄S Zd] at hall
  obtain ⟨c₁, hc₁⟩ := (mk_eq_mk_iff (rep (g₁ : PGL2 K)) g₁).1 (mk_rep _)
  obtain ⟨c₂, hc₂⟩ := (mk_eq_mk_iff (rep (g₂ : PGL2 K)) g₂).1 (mk_rep _)
  obtain ⟨c₃, hc₃⟩ := (mk_eq_mk_iff (rep (g₃ : PGL2 K)) g₃).1 (mk_rep _)
  obtain ⟨c₄, hc₄⟩ := (mk_eq_mk_iff (rep (g₄ : PGL2 K)) g₄).1 (mk_rep _)
  have e₁ := hdet (g₁ : PGL2 K)
  have e₂ := hdet (g₂ : PGL2 K)
  have e₃ := hdet (g₃ : PGL2 K)
  have e₄ := hdet (g₄ : PGL2 K)
  simp only [hA, hB, hC, hD] at hall e₁ e₂ e₃ e₄
  simp only [hc₁, hc₂, hc₃, hc₄, mul_eq_zero, Units.ne_zero, false_or] at hg₁ hg₂ hg₃ hg₄
  rw [hg₁] at e₁
  rw [hg₂] at e₂
  rw [hg₃] at e₃
  rw [hg₄] at e₄
  have n₁ : rep (g₁ : PGL2 K) 1 0 ≠ 0 := by intro h; apply e₁; simp [h]
  have n₂ : rep (g₂ : PGL2 K) 0 0 ≠ 0 := by intro h; apply e₂; simp [h]
  have n₃ : rep (g₃ : PGL2 K) 1 1 ≠ 0 := by intro h; apply e₃; simp [h]
  have n₄ : rep (g₄ : PGL2 K) 0 1 ≠ 0 := by intro h; apply e₄; simp [h]
  simp only [hc₁, hc₂, hc₃, hc₄]
  field_simp at hall
  linear_combination (↑c₁ * ↑c₂ * ↑c₃ * ↑c₄ : K) * hall
