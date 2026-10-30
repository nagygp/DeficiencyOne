module

public import RequestProject.Lemma2

/-!
# Theorem 1 of Eberhard, *Sharply transitive sets in PGL₂(K)*

If `K` is a finite field and `S ⊆ PGL₂(K)` is sharply transitive on the projective line
`ℙ¹(K)` with `1 ∈ S`, then `S` is a subgroup.
-/

@[expose] public section

open scoped LinearAlgebra.Projectivization

namespace PGL2

variable {K : Type*} [Field K]

lemma inv_apply_00 (g : GL (Fin 2) K) :
    (g⁻¹ : GL (Fin 2) K) 0 0 = g 1 1 / (g 0 0 * g 1 1 - g 0 1 * g 1 0) := by
  rw [Matrix.coe_units_inv, Matrix.inv_def, Matrix.adjugate_fin_two, ← Matrix.det_fin_two]
  simp [Ring.inverse_eq_inv', div_eq_inv_mul]

lemma inv_apply_01 (g : GL (Fin 2) K) :
    (g⁻¹ : GL (Fin 2) K) 0 1 = - g 0 1 / (g 0 0 * g 1 1 - g 0 1 * g 1 0) := by
  rw [Matrix.coe_units_inv, Matrix.inv_def, Matrix.adjugate_fin_two, ← Matrix.det_fin_two]
  simp [Ring.inverse_eq_inv', div_eq_inv_mul]

lemma inv_apply_10 (g : GL (Fin 2) K) :
    (g⁻¹ : GL (Fin 2) K) 1 0 = - g 1 0 / (g 0 0 * g 1 1 - g 0 1 * g 1 0) := by
  rw [Matrix.coe_units_inv, Matrix.inv_def, Matrix.adjugate_fin_two, ← Matrix.det_fin_two]
  simp [Ring.inverse_eq_inv', div_eq_inv_mul]

lemma inv_apply_11 (g : GL (Fin 2) K) :
    (g⁻¹ : GL (Fin 2) K) 1 1 = g 0 0 / (g 0 0 * g 1 1 - g 0 1 * g 1 0) := by
  rw [Matrix.coe_units_inv, Matrix.inv_def, Matrix.adjugate_fin_two, ← Matrix.det_fin_two]
  simp [Ring.inverse_eq_inv', div_eq_inv_mul]

/-- Change of coordinates: any two distinct points can be moved to `(1 : 0)` and `(0 : 1)`. -/
lemma exists_GL_of_ne {p q : ℙ K (Fin 2 → K)} (hpq : p ≠ q) :
    ∃ P : GL (Fin 2) K, P • pt 1 0 = p ∧ P • pt 0 1 = q := by
  obtain ⟨x0, x1, hx, rfl⟩ := pt_surj p
  obtain ⟨w0, w1, hw, rfl⟩ := pt_surj q
  have hdet : (!![x0, w0; x1, w1] : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := by
    rw [Matrix.det_fin_two_of]
    intro h
    exact hpq ((pt_eq_pt_iff hx hw).2 (by linear_combination h))
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet, ?_, ?_⟩
  · rw [smul_pt _ (Or.inl one_ne_zero)]
    congr 1 <;> simp [Matrix.GeneralLinearGroup.mkOfDetNeZero]
  · rw [smul_pt _ (Or.inr one_ne_zero)]
    congr 1 <;> simp [Matrix.GeneralLinearGroup.mkOfDetNeZero]

/-- The unipotent matrix `[[1, t], [0, 1]]`. -/
noncomputable def unip (t : K) : GL (Fin 2) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, t; 0, 1] (by simp)

@[simp] lemma unip_00 (t : K) : unip t 0 0 = 1 := rfl
@[simp] lemma unip_01 (t : K) : unip t 0 1 = t := rfl
@[simp] lemma unip_10 (t : K) : unip t 1 0 = 0 := rfl
@[simp] lemma unip_11 (t : K) : unip t 1 1 = 1 := rfl

lemma exists_unip_smul {p : ℙ K (Fin 2 → K)} (hp : p ≠ pt 1 0) :
    ∃ t : K, unip t • pt 0 1 = p := by
  obtain ⟨z0, z1, hz, rfl⟩ := pt_surj p
  have hz1 : z1 ≠ 0 := by
    rintro rfl
    apply hp
    rw [pt_eq_pt_iff hz (Or.inl one_ne_zero)]
    simp
  refine ⟨z0 / z1, ?_⟩
  rw [smul_pt _ (Or.inr one_ne_zero), pt_eq_pt_iff (by simp) hz]
  simp
  field_simp

/-- An upper triangular matrix with equal diagonal entries fixing a point other than `(1 : 0)`
is trivial in `PGL₂`. -/
lemma mk_eq_one_of_fixes (M : GL (Fin 2) K) (h10 : M 1 0 = 0) (hdiag : M 0 0 = M 1 1)
    {p : ℙ K (Fin 2 → K)} (hp : p ≠ pt 1 0) (hMp : M • p = p) : (M : PGL2 K) = 1 := by
  obtain ⟨z0, z1, hz, rfl⟩ := pt_surj p
  have hz1 : z1 ≠ 0 := by
    rintro rfl
    apply hp
    rw [pt_eq_pt_iff hz (Or.inl one_ne_zero)]
    simp
  have hd := det_ne_zero M
  rw [h10, hdiag] at hd
  have ha : M 1 1 ≠ 0 := by intro h; apply hd; simp [h]
  rw [smul_pt _ hz, pt_eq_pt_iff (smul_vec_ne_zero M hz) hz, h10, hdiag] at hMp
  have h01 : M 0 1 = 0 := by
    have : M 0 1 * (z1 * z1) = 0 := by linear_combination hMp
    simpa [hz1] using this
  rw [← QuotientGroup.mk_one, mk_eq_mk_iff]
  refine ⟨Units.mk0 _ (inv_ne_zero ha), fun i j => ?_⟩
  fin_cases i <;> fin_cases j <;> simp [h01, h10, hdiag, ha]

/-- The matrix computation `(hu)(ku)⁻¹(gu)u⁻¹ = [[a, *], [0, bc]]` from the paper. -/
lemma triangular_of_shape (G1 G2 G4 : GL (Fin 2) K) (t : K) (c1 : G1 0 0 = 0)
    (c2 : G2 0 1 = 0) (c4 : G4 1 1 = 0)
    (L : G1 0 1 * G2 1 1 * G4 1 0 = G1 1 0 * G2 0 0 * G4 0 1) :
    (G4 * G2⁻¹ * G1 * (unip t)⁻¹) 1 0 = 0 ∧
      (G4 * G2⁻¹ * G1 * (unip t)⁻¹) 0 0 = (G4 * G2⁻¹ * G1 * (unip t)⁻¹) 1 1 := by
  have d2 := det_ne_zero G2
  rw [c2, zero_mul, sub_zero] at d2
  have n00 : G2 0 0 ≠ 0 := left_ne_zero_of_mul d2
  have n11 : G2 1 1 ≠ 0 := right_ne_zero_of_mul d2
  constructor
  · simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, inv_apply_00, inv_apply_01,
      inv_apply_10, inv_apply_11, unip_00, unip_01, unip_10, unip_11, c1, c2, c4]
    ring
  · simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, inv_apply_00, inv_apply_01,
      inv_apply_10, inv_apply_11, unip_00, unip_01, unip_10, unip_11, c1, c2, c4]
    field_simp
    linear_combination -L

/-- Expanding the action of a conjugate. -/
lemma smul_five {G X : Type*} [Group G] [MulAction G X] (P H Kk A : G) (z : X) :
    (P⁻¹ * H * Kk⁻¹ * A * P) • z = P⁻¹ • H • Kk⁻¹ • A • P • z := by
  simp only [mul_smul]



variable [Fintype K]

/-- The coordinate computation in the proof of Theorem 1. -/
lemma key_step (S : Set (PGL2 K))
    (hS : IsSharplyTransitive (X := ℙ K (Fin 2 → K)) S) (h1 : (1 : PGL2 K) ∈ S)
    (G H Kk : GL (Fin 2) K) (hg : (G : PGL2 K) ∈ S) (hh : (H : PGL2 K) ∈ S)
    (hkS' : (Kk : PGL2 K) ∈ S)
    (hfg : ∀ x : ℙ K (Fin 2 → K), (G : PGL2 K) • x ≠ x)
    (hfh : ∀ x : ℙ K (Fin 2 → K), (H : PGL2 K) • x ≠ x)
    (x y : ℙ K (Fin 2 → K)) (hxy : x ≠ y)
    (hx : Kk • H⁻¹ • x = G • x) (hy : Kk • H⁻¹ • y = G • y) :
    (G : PGL2 K) * H = Kk := by
  have hGx : x ≠ G • x := fun e => hfg x (by rw [mk_smul]; exact e.symm)
  have hHx : H⁻¹ • x ≠ x := by
    intro e
    apply hfh x
    rw [mk_smul]
    conv_lhs => rw [← e]
    rw [smul_inv_smul]
  obtain ⟨P, hP0, hP1⟩ := exists_GL_of_ne hGx
  have hz : P⁻¹ • H⁻¹ • x ≠ pt 1 0 := by
    intro e
    apply hHx
    calc H⁻¹ • x = P • (P⁻¹ • H⁻¹ • x) := (smul_inv_smul _ _).symm
      _ = P • pt 1 0 := by rw [e]
      _ = x := hP0
  obtain ⟨t, ht⟩ := exists_unip_smul hz
  obtain ⟨U, hU⟩ : ∃ U, U = unip t := ⟨_, rfl⟩
  rw [← hU] at ht
  have hS' := hS.translate ((P : PGL2 K)⁻¹) ((P : PGL2 K) * (U : PGL2 K))
  have mem : ∀ A : GL (Fin 2) K, (A : PGL2 K) ∈ S →
      ((P⁻¹ * A * (P * U) : GL (Fin 2) K) : PGL2 K) ∈
        (fun s => (P : PGL2 K)⁻¹ * s * ((P : PGL2 K) * (U : PGL2 K))) '' S := by
    intro A hA
    exact ⟨_, hA, by simp [QuotientGroup.mk_mul, QuotientGroup.mk_inv]⟩
  have memU : (U : PGL2 K) ∈
      (fun s => (P : PGL2 K)⁻¹ * s * ((P : PGL2 K) * (U : PGL2 K))) '' S :=
    ⟨1, h1, by simp⟩
  have one0 : (1 : K) ≠ 0 ∨ (0 : K) ≠ 0 := Or.inl one_ne_zero
  have zero1 : (0 : K) ≠ 0 ∨ (1 : K) ≠ 0 := Or.inr one_ne_zero
  have hUe0 : U • pt (1 : K) 0 = pt 1 0 := by rw [smul_pt _ one0]; simp [hU]
  obtain ⟨G1, hG1⟩ : ∃ G1, G1 = P⁻¹ * G * (P * U) := ⟨_, rfl⟩
  obtain ⟨G2, hG2⟩ : ∃ G2, G2 = P⁻¹ * Kk * (P * U) := ⟨_, rfl⟩
  obtain ⟨G4, hG4⟩ : ∃ G4, G4 = P⁻¹ * H * (P * U) := ⟨_, rfl⟩
  have e1 : G1 • pt (1 : K) 0 = pt 0 1 := by
    rw [hG1, mul_smul, mul_smul, mul_smul, hUe0, hP0, ← hP1, inv_smul_smul]
  have e2 : G2 • pt (0 : K) 1 = pt 0 1 := by
    rw [hG2, mul_smul, mul_smul, mul_smul, ht, smul_inv_smul, hx, ← hP1, inv_smul_smul]
  have e4 : G4 • pt (0 : K) 1 = pt 1 0 := by
    rw [hG4, mul_smul, mul_smul, mul_smul, ht, smul_inv_smul, smul_inv_smul, ← hP0,
      inv_smul_smul]
  have c1 : G1 0 0 = 0 := by
    have := (smul_pt_eq_pt_iff _ one0 zero1).1 e1; simpa using this
  have c2 : G2 0 1 = 0 := by
    have := (smul_pt_eq_pt_iff _ zero1 zero1).1 e2; simpa using this
  have c4 : G4 1 1 = 0 := by
    have := (smul_pt_eq_pt_iff _ zero1 one0).1 e4; simpa [eq_comm] using this
  have L := eberhard_lemma2 _ hS' G1 G2 U G4 (hG1 ▸ mem G hg) (hG2 ▸ mem Kk hkS') memU
    (hG4 ▸ mem H hh) c1 c2 (by simp [hU]) c4
  rw [hU] at L
  simp only [unip_00, unip_11, mul_one] at L
  obtain ⟨M, hM⟩ : ∃ M, M = P⁻¹ * H * Kk⁻¹ * G * P := ⟨_, rfl⟩
  have hM' : M = G4 * G2⁻¹ * G1 * U⁻¹ := by rw [hM, hG1, hG2, hG4]; group
  obtain ⟨m10, mdiag⟩ := triangular_of_shape G1 G2 G4 t c1 c2 c4 L
  rw [← hU, ← hM'] at m10 mdiag
  have hfix : (M • (P⁻¹ • y) : ℙ K (Fin 2 → K)) = P⁻¹ • y := by
    have e := smul_five (X := ℙ K (Fin 2 → K)) P H Kk G (P⁻¹ • y)
    rw [← hM] at e
    rw [e, smul_inv_smul P y, ← hy, inv_smul_smul Kk, smul_inv_smul H]
  have hne : P⁻¹ • y ≠ pt 1 0 := by
    intro e
    apply hxy
    rw [← hP0, ← e, smul_inv_smul P y]
  have hM1 := mk_eq_one_of_fixes M m10 mdiag hne hfix
  rw [hM] at hM1
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at hM1
  have h2 : (H : PGL2 K) * (Kk : PGL2 K)⁻¹ * (G : PGL2 K) = 1 := by
    have := congrArg (fun z => (P : PGL2 K) * z * (P : PGL2 K)⁻¹) hM1
    simpa [mul_assoc] using this
  have h3 := eq_inv_of_mul_eq_one_right h2
  have h4 : (G : PGL2 K) * (H : PGL2 K) = Kk := by
    rw [h3]; group
  exact h4

/-- The key step: a regular set containing `1` is closed under multiplication. -/
lemma mul_mem_of_isSharplyTransitive (S : Set (PGL2 K))
    (hS : IsSharplyTransitive (X := ℙ K (Fin 2 → K)) S) (h1 : (1 : PGL2 K) ∈ S)
    {g h : PGL2 K} (hg : g ∈ S) (hh : h ∈ S) : g * h ∈ S := by
  by_cases hg1 : g = 1
  · simpa [hg1] using hh
  by_cases hh1 : h = 1
  · simpa [hh1] using hg
  have fpf : ∀ s ∈ S, s ≠ 1 → ∀ x : ℙ K (Fin 2 → K), s • x ≠ x :=
    fun s hs hs1 x hx => hs1 (hS.eq_one_of_smul_eq h1 hs hx)
  have hk : ∀ x : ℙ K (Fin 2 → K), ∃ k ∈ S, k • (h⁻¹ • x) = g • x :=
    fun x => hS.exists_smul _ _
  choose k hkS hkx using hk
  have hkh : ∀ x, k x ≠ h := by
    intro x hx
    have := hkx x
    rw [hx, smul_inv_smul] at this
    exact fpf g hg hg1 x this.symm
  haveI : Nonempty (ℙ K (Fin 2 → K)) := ⟨pt 1 0⟩
  obtain ⟨x, y, hxy, hk_eq⟩ : ∃ x y, x ≠ y ∧ k x = k y := by
    by_contra hcon
    push_neg at hcon
    let f : ℙ K (Fin 2 → K) → ↥(S \ {h}) := fun x => ⟨k x, hkS x, hkh x⟩
    have hf : Function.Injective f := fun x y hfxy => by
      by_contra hne
      exact hcon x y hne (congrArg Subtype.val hfxy)
    have c1 := Nat.card_le_card_of_injective f hf
    have c2 : Nat.card ↥(S \ {h}) < Nat.card S := by
      rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq]
      exact Set.ncard_diff_singleton_lt_of_mem hh (Set.toFinite S)
    have c3 := hS.card_eq
    omega
  have hx := hkx x
  have hy := hkx y
  rw [hk_eq] at hx
  have hkS' := hkS y
  have hfg := fpf g hg hg1
  have hfh := fpf h hh hh1
  obtain ⟨G, rfl⟩ := QuotientGroup.mk_surjective g
  obtain ⟨H, rfl⟩ := QuotientGroup.mk_surjective h
  obtain ⟨Kk, hKk⟩ := QuotientGroup.mk_surjective (k y)
  rw [← hKk] at hx hy hkS'
  rw [← QuotientGroup.mk_inv, mk_smul, mk_smul, mk_smul] at hx hy
  rw [key_step S hS h1 G H Kk hg hh hkS' hfg hfh x y hxy hx hy]
  exact hkS'

end PGL2

open PGL2

/-- **Theorem 1** (Bader–Lunardon, Thas, Bonisoli–Korchmáros; proof of Eberhard).
If `K` is a finite field and `S ⊆ PGL₂(K)` is sharply transitive on the projective line
`ℙ¹(K)` and contains `1`, then `S` is a subgroup of `PGL₂(K)`. -/
theorem eberhard_theorem1 {K : Type*} [Field K] [Fintype K] (S : Set (PGL2 K))
    (hS : IsSharplyTransitive (X := ℙ K (Fin 2 → K)) S) (h1 : (1 : PGL2 K) ∈ S) :
    ∃ H : Subgroup (PGL2 K), (H : Set (PGL2 K)) = S := by
  have hmul : ∀ a b : PGL2 K, a ∈ S → b ∈ S → a * b ∈ S :=
    fun a b ha hb => mul_mem_of_isSharplyTransitive S hS h1 ha hb
  have hpow : ∀ a ∈ S, ∀ n : ℕ, a ^ n ∈ S := by
    intro a ha n
    induction n with
    | zero => simpa using h1
    | succ n ih => rw [pow_succ]; exact hmul _ _ ih ha
  refine ⟨⟨⟨⟨S, fun ha hb => hmul _ _ ha hb⟩, h1⟩, fun {a} ha => ?_⟩, rfl⟩
  have hpos := orderOf_pos a
  have key : a ^ (orderOf a - 1) * a = 1 := by
    rw [← pow_succ, Nat.sub_add_cancel hpos, pow_orderOf_eq_one]
  rw [← eq_inv_of_mul_eq_one_left key]
  exact hpow a ha _
