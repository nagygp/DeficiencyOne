module

public import RequestProject.Theorem1

/-!
# Stability conjecture for sharply transitive sets in `PGL₂(K)`

We study the following stability version of Eberhard's theorem
(*Sharply transitive sets in PGL₂(K)*, arXiv:2105.02760).

Let `K` be a finite field of order `q` and let `S ⊆ PGL₂(K)` have `q` elements, contain `1`,
and have all ratios `a * b⁻¹` (for distinct `a, b ∈ S`) fixed-point-free on the projective
line `ℙ¹(K)`.  The **stability conjecture** asserts that (for `q` large enough) `S` is
contained in a subgroup of `PGL₂(K)` of order `q + 1`.

We prove the key reduction: the conclusion is equivalent to the existence of a
"missing" element `g ∈ PGL₂(K)` with `g • x ∉ {s • x | s ∈ S}` for all `x` (equivalently,
the completion `S ∪ {g}` is sharply transitive, hence a subgroup by `eberhard_theorem1`).
-/

@[expose] public section

open scoped LinearAlgebra.Projectivization
open Classical

namespace PGL2

variable {K : Type*} [Field K] [Fintype K]

/-- The hypothesis of the stability conjecture: `S` has `q` elements, contains `1`, and all
ratios of distinct elements are fixed-point-free on the projective line. -/
def IsStableSet (S : Set (PGL2 K)) : Prop :=
  (1 : PGL2 K) ∈ S ∧ Nat.card S = Fintype.card K ∧
    ∀ a ∈ S, ∀ b ∈ S, a ≠ b → ∀ x : ℙ K (Fin 2 → K), (a * b⁻¹) • x ≠ x

/-- The conclusion of the stability conjecture: `S` is contained in a subgroup of order `q+1`. -/
def IsStableConclusion (S : Set (PGL2 K)) : Prop :=
  ∃ H : Subgroup (PGL2 K), S ⊆ H ∧ Nat.card H = Fintype.card K + 1

/-- The projective line over a field of order `q` has `q + 1` points. -/
lemma card_projectiveLine : Nat.card (ℙ K (Fin 2 → K)) = Fintype.card K + 1 := by
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  have hq1 : 1 ≤ Fintype.card K := by omega
  have hV : Nat.card (Fin 2 → K) = Fintype.card K ^ 2 := by
    rw [Nat.card_pi]; simp
  have h := Projectivization.card' (k := K) (V := Fin 2 → K)
  rw [hV] at h
  have hKc : Nat.card K = Fintype.card K := Nat.card_eq_fintype_card
  rw [hKc] at h
  -- h : Fintype.card K ^ 2 = Nat.card (ℙ K (Fin 2 → K)) * (Fintype.card K - 1) + 1
  have hZ : (Fintype.card K : ℤ) ^ 2 =
      (Nat.card (ℙ K (Fin 2 → K)) : ℤ) * ((Fintype.card K : ℤ) - 1) + 1 := by
    have hcast := congrArg (Nat.cast : ℕ → ℤ) h
    push_cast at hcast
    rw [Nat.cast_sub hq1] at hcast
    exact hcast
  have keyZ : (Fintype.card K : ℤ) ^ 2 =
      ((Fintype.card K : ℤ) + 1) * ((Fintype.card K : ℤ) - 1) + 1 := by ring
  have hmul : (Nat.card (ℙ K (Fin 2 → K)) : ℤ) * ((Fintype.card K : ℤ) - 1) =
      ((Fintype.card K : ℤ) + 1) * ((Fintype.card K : ℤ) - 1) := by
    linarith
  have hpos : (Fintype.card K : ℤ) - 1 ≠ 0 := by
    have h2 : (2 : ℤ) ≤ Fintype.card K := by exact_mod_cast hq
    linarith
  have hc : (Nat.card (ℙ K (Fin 2 → K)) : ℤ) = (Fintype.card K : ℤ) + 1 :=
    mul_right_cancel₀ hpos hmul
  exact_mod_cast hc

/-- Key injectivity: under the stability hypothesis, two elements of `S` agreeing at a point
are equal. (If `a • x = b • x` with `a ≠ b`, then `a * b⁻¹` fixes `b • x`.) -/
lemma stable_inj {S : Set (PGL2 K)} (hS : IsStableSet S) {x : ℙ K (Fin 2 → K)}
    {a b : PGL2 K} (ha : a ∈ S) (hb : b ∈ S) (h : a • x = b • x) : a = b := by
  by_contra hne
  have h2 := hS.2.2 a ha b hb hne (b • x)
  rw [mul_smul, inv_smul_smul, h] at h2
  exact h2 rfl

/-- A `Fintype` instance for the projective line over a finite field. -/
noncomputable instance : Fintype (ℙ K (Fin 2 → K)) := Fintype.ofFinite _

/-- If there is a "missing" element `g ∈ PGL₂(K)` avoiding `S • x` at every `x`, then the
completion `S ∪ {g}` is sharply transitive, hence a subgroup by `eberhard_theorem1`,
and `S` is contained in a subgroup of order `q+1`. -/
lemma stable_conclusion_of_missing {S : Set (PGL2 K)} (hS : IsStableSet S)
    {g : PGL2 K} (hg : ∀ x : ℙ K (Fin 2 → K), ∀ s ∈ S, g • x ≠ s • x) :
    IsStableConclusion S := by
  have h1 : (1 : PGL2 K) ∈ S := hS.1
  have hcardS : Nat.card S = Fintype.card K := hS.2.1
  have hgS : g ∉ S := by
    intro hgS
    exact hg (pt 1 0) g hgS rfl
  set T := insert g S with hTdef
  have hcardT : Nat.card T = Fintype.card K + 1 := by
    rw [hTdef, Nat.card_coe_set_eq, Set.ncard_insert_of_notMem hgS,
      ← Nat.card_coe_set_eq, hcardS]
  have h1T : (1 : PGL2 K) ∈ T := by rw [hTdef]; exact Set.mem_insert_of_mem _ h1
  have hT : IsSharplyTransitive (X := ℙ K (Fin 2 → K)) T := by
    have hcardT' : Fintype.card ↥T = Fintype.card (ℙ K (Fin 2 → K)) := by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcardT, card_projectiveLine]
    have mem_T : ∀ t : ↥T, t.val = g ∨ t.val ∈ S := by
      intro t
      have ht : t.val ∈ insert g S := by
        rw [← hTdef]
        exact t.2
      exact Set.mem_insert_iff.mp ht
    intro x y
    let φ : ↥T → ℙ K (Fin 2 → K) := fun t => t.val • x
    have hφinj : Function.Injective φ := by
      intro t₁ t₂ h
      have h' : t₁.val • x = t₂.val • x := h
      apply Subtype.ext
      obtain h1 | h1 := mem_T t₁
      · obtain h2 | h2 := mem_T t₂
        · rw [h1, h2]
        · rw [h1] at h'; exact absurd h' (hg x t₂.val h2)
      · obtain h2 | h2 := mem_T t₂
        · rw [h2] at h'; exact absurd h'.symm (hg x t₁.val h1)
        · exact stable_inj hS h1 h2 h'
    have hbij : Function.Bijective φ :=
      (Fintype.bijective_iff_injective_and_card φ).2 ⟨hφinj, hcardT'⟩
    obtain ⟨t, ht⟩ := hbij.surjective y
    have ht' : t.val • x = y := ht
    refine ⟨t.val, ⟨t.property, ht'⟩, ?_⟩
    intro t' ⟨ht'T, ht'x⟩
    have heq : (⟨t', ht'T⟩ : ↥T) = t := hφinj (ht'x.trans ht'.symm)
    exact congrArg Subtype.val heq
  obtain ⟨H, hH⟩ := eberhard_theorem1 T hT h1T
  refine ⟨H, ?_, ?_⟩
  · intro s hs
    have hsT : s ∈ T := Set.mem_insert_of_mem _ hs
    rw [← hH] at hsT
    exact hsT
  · have hcardH : Nat.card H = Nat.card T :=
      Nat.card_congr (Equiv.cast (congrArg (fun s : Set (PGL2 K) => ↥s) hH))
    rw [hcardH, hcardT]

/-- If `S` is contained in a subgroup `H` of order `q+1`, then some `t ∈ H` is "missing":
`t • x ≠ s • x` for all `x` and all `s ∈ S`. (The subgroup `H` acts regularly on `ℙ¹`,
and the element of `H \ S` is missing.) -/
lemma stable_missing_of_conclusion {S : Set (PGL2 K)} (hS : IsStableSet S)
    {H : Subgroup (PGL2 K)} (hSH : S ⊆ H) (hcardH : Nat.card H = Fintype.card K + 1) :
    ∃ t ∈ H, ∀ x : ℙ K (Fin 2 → K), ∀ s ∈ S, t • x ≠ s • x := by
  have hcardS : Nat.card S = Fintype.card K := hS.2.1
  have hq2 : 2 ≤ Fintype.card K := by
    have := Fintype.one_lt_card (α := K)
    omega
  have hcardHq : Fintype.card ↥H = Fintype.card K + 1 := by
    rw [← Nat.card_eq_fintype_card, hcardH]
  -- freeness: the stabilizer of each point is trivial (H acts regularly), via orbit-stabilizer
  have hfree : ∀ x : ℙ K (Fin 2 → K), ∀ h : ↥H, h • x = x → h = 1 := by
    intro x h hh
    have hos := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (G := ↥H) x
    have hinj : Set.InjOn (fun s => s • x) S := by
      intro a ha b hb hab
      exact stable_inj hS ha hb hab
    have himage : Nat.card ↑((fun s => s • x) '' S) = Fintype.card K := by
      rw [Nat.card_image_of_injOn hinj, hcardS]
    have horbit_ge : Fintype.card K ≤ Fintype.card (MulAction.orbit ↥H x) := by
      have hsub : (fun s => s • x) '' S ⊆ MulAction.orbit ↥H x := by
        intro y hy
        obtain ⟨s, hs, rfl⟩ := hy
        exact MulAction.mem_orbit_iff.mpr ⟨⟨s, hSH hs⟩, rfl⟩
      have hfin : (MulAction.orbit ↥H x).Finite :=
        Set.Finite.subset Set.finite_univ (Set.subset_univ _)
      have hle := Set.ncard_le_ncard hsub hfin
      rw [← Nat.card_coe_set_eq ((fun s => s • x) '' S),
        ← Nat.card_coe_set_eq (MulAction.orbit ↥H x)] at hle
      rw [himage, Nat.card_eq_fintype_card] at hle
      exact hle
    have horbit_le : Fintype.card (MulAction.orbit ↥H x) ≤ Fintype.card K + 1 := by
      have hinj' : Function.Injective
          (fun y : ↥(MulAction.orbit ↥H x) => (y : ℙ K (Fin 2 → K))) :=
        Subtype.val_injective
      have hle := Fintype.card_le_of_injective _ hinj'
      have hcardP : Fintype.card (ℙ K (Fin 2 → K)) = Fintype.card K + 1 := by
        rw [← Nat.card_eq_fintype_card, card_projectiveLine]
      rw [hcardP] at hle
      exact hle
    have horbit_eq : Fintype.card (MulAction.orbit ↥H x) = Fintype.card K + 1 := by
      have hdvd : Fintype.card (MulAction.orbit ↥H x) ∣ Fintype.card K + 1 := by
        rw [← hcardHq, ← hos]
        exact Nat.dvd_mul_right _ _
      rcases Nat.lt_or_eq_of_le horbit_ge with hlt | heq
      · omega
      · exfalso
        rw [← heq] at hdvd
        have hdvd1 : Fintype.card K ∣ 1 := (Nat.dvd_add_right (Nat.dvd_refl _)).mp hdvd
        have hle1 := Nat.le_of_dvd (by norm_num) hdvd1
        omega
    have hstab : Fintype.card (MulAction.stabilizer ↥H x) = 1 := by
      rw [hcardHq, horbit_eq] at hos
      have hos' : (Fintype.card K + 1) * Fintype.card (MulAction.stabilizer ↥H x) =
          (Fintype.card K + 1) * 1 := by rw [mul_one]; exact hos
      exact Nat.eq_of_mul_eq_mul_left (by omega) hos'
    have hmem : h ∈ MulAction.stabilizer ↥H x := by
      rw [MulAction.mem_stabilizer_iff]
      exact hh
    obtain ⟨a, ha⟩ := Fintype.card_eq_one_iff.mp hstab
    have hk : (⟨h, hmem⟩ : ↥(MulAction.stabilizer ↥H x)) = 1 := by
      calc (⟨h, hmem⟩ : ↥(MulAction.stabilizer ↥H x)) = a := ha _
        _ = 1 := (ha 1).symm
    exact Subtype.ext_iff.mp hk
  -- pick t ∈ H \ S (proper subset since |S| = q < q+1 = |H|)
  have hne : S ≠ ↑H := by
    intro heq
    have h1 : Nat.card S = Nat.card H := by
      rw [heq]
      rfl
    rw [hcardS, hcardH] at h1
    omega
  obtain ⟨t, htH, htS⟩ := Set.exists_of_ssubset (Set.ssubset_iff_subset_ne.mpr ⟨hSH, hne⟩)
  refine ⟨t, htH, ?_⟩
  intro x s hs hEq
  have hfix : (s⁻¹ * t) • x = x := by
    rw [mul_smul, hEq, inv_smul_smul]
  have hmem : (s⁻¹ * t : PGL2 K) ∈ H := H.mul_mem (H.inv_mem (hSH hs)) htH
  have hfree' := hfree x ⟨s⁻¹ * t, hmem⟩ (by simpa using hfix)
  have hst1 : s⁻¹ * t = 1 := Subtype.ext_iff.mp hfree'
  have hst : t = s := by
    have h2 : s * (s⁻¹ * t) = t := by group
    rw [hst1, mul_one] at h2
    exact h2.symm
  exact htS (hst ▸ hs)

/-- **Equivalence.** Under the stability hypothesis, the conclusion is equivalent to the
existence of a "missing" element of `PGL₂(K)` (an element avoiding `S • x` at every `x`). -/
theorem stable_conclusion_iff_missing {S : Set (PGL2 K)} (hS : IsStableSet S) :
    IsStableConclusion S ↔ ∃ g : PGL2 K, ∀ x : ℙ K (Fin 2 → K), ∀ s ∈ S, g • x ≠ s • x := by
  constructor
  · intro h
    obtain ⟨H, hSH, hcardH⟩ := h
    obtain ⟨t, _htH, ht⟩ := stable_missing_of_conclusion hS hSH hcardH
    exact ⟨t, ht⟩
  · intro h
    obtain ⟨g, hg⟩ := h
    exact stable_conclusion_of_missing hS hg

/-- **Stability conjecture.** For `q > 10`, every stable set `S ⊆ PGL₂(K)` is contained in a
subgroup of order `q+1`. (By `stable_conclusion_iff_missing`, equivalent to the existence of a
"missing" element.) -/
theorem stability_conjecture (hq : 10 < Fintype.card K) (S : Set (PGL2 K))
    (hS : IsStableSet S) : IsStableConclusion S := by
  rw [stable_conclusion_iff_missing hS]
  -- The remaining goal — producing a "missing" element — is the hard part of the conjecture.
  sorry

end PGL2
