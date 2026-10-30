import Mathlib
import DeficiencyOne.Defs
import DeficiencyOne.Section2FixedPointBound
open scoped LinearAlgebra.Projectivization
open Classical
open Polynomial

namespace PGL2
variable {K : Type*} [Field K]
attribute [local instance] Classical.propDecidable

def ptFin (x : K) : P1 K :=
  Projectivization.mk K ![x, 1] (by intro h; have := congrFun h 1; simp at this)

def ptInf : P1 K :=
  Projectivization.mk K ![1, 0] (by intro h; have := congrFun h 0; simp at this)

lemma ptFin_injective : Function.Injective (ptFin (K := K)) := by
  intro x y h
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' K _ _ (by simp) (by simp)).1 h
  have h0 : a * y = x := by have := congrFun ha 0; simpa using this
  have h1 : a * 1 = 1 := by have := congrFun ha 1; simpa using this
  rw [mul_one] at h1
  rw [← h0, h1, one_mul]

lemma ptFin_ne_ptInf (x : K) : ptFin x ≠ ptInf := by
  intro h
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' K _ _ (by simp) (by simp)).1 h
  have h1 : a * 0 = 1 := by have := congrFun ha 1; simpa using this
  simp at h1

noncomputable def coordAux (v : { v : Fin 2 → K // v ≠ 0 }) : Option K :=
  if (v : Fin 2 → K) 1 = 0 then none
  else some ((v : Fin 2 → K) 0 / (v : Fin 2 → K) 1)

lemma coordAux_scale (a b : { v : Fin 2 → K // v ≠ 0 }) (t : K)
    (h : (a : Fin 2 → K) = t • (b : Fin 2 → K)) : coordAux a = coordAux b := by
  have ht : t ≠ 0 := by
    rintro rfl
    rw [zero_smul] at h
    exact a.2 h
  have h0 : (a : Fin 2 → K) 0 = t * (b : Fin 2 → K) 0 := by rw [h]; simp
  have h1 : (a : Fin 2 → K) 1 = t * (b : Fin 2 → K) 1 := by rw [h]; simp
  simp only [coordAux]
  by_cases hb : (b : Fin 2 → K) 1 = 0
  · have ha : (a : Fin 2 → K) 1 = 0 := by rw [h1, hb, mul_zero]
    rw [if_pos ha, if_pos hb]
  · have ha : (a : Fin 2 → K) 1 ≠ 0 := by rw [h1]; exact mul_ne_zero ht hb
    rw [if_neg ha, if_neg hb, h0, h1, mul_div_mul_left _ _ ht]

noncomputable def coord (x : P1 K) : Option K :=
  Projectivization.lift coordAux coordAux_scale x

@[simp] lemma coord_mk (v : Fin 2 → K) (hv : v ≠ 0) :
    coord (Projectivization.mk K v hv) = coordAux ⟨v, hv⟩ := rfl

@[simp] lemma coord_ptFin (x : K) : coord (ptFin x) = some x := by
  simp only [ptFin, coord_mk, coordAux]
  rw [if_neg (by simp)]
  simp

@[simp] lemma coord_ptInf : coord (ptInf (K := K)) = none := by
  simp only [ptInf, coord_mk, coordAux]
  rw [if_pos (show (![1, 0] : Fin 2 → K) 1 = 0 by simp)]

noncomputable def ptOf : Option K → P1 K
  | none => ptInf
  | some x => ptFin x

@[simp] lemma coord_ptOf : ∀ y : Option K, coord (ptOf y) = y
  | none => coord_ptInf
  | some x => coord_ptFin x

lemma ptOf_coord (x : P1 K) : ptOf (coord x) = x := by
  induction x using Projectivization.ind with
  | h v hv =>
    rw [coord_mk]
    simp only [coordAux]
    by_cases h : v 1 = 0
    · rw [if_pos h]
      have hv0 : v 0 ≠ 0 := by
        intro h0
        exact hv (by funext i; fin_cases i <;> simp [h, h0])
      refine (Projectivization.mk_eq_mk_iff' K _ _ (by simp) hv).2 ⟨(v 0)⁻¹, ?_⟩
      funext i
      fin_cases i <;> simp [h, inv_mul_cancel₀ hv0]
    · rw [if_neg h]
      refine (Projectivization.mk_eq_mk_iff' K _ _ (by simp) hv).2 ⟨(v 1)⁻¹, ?_⟩
      funext i
      fin_cases i <;> simp [h, inv_mul_cancel₀ h, div_eq_inv_mul]

noncomputable def equivWithTop : P1 K ≃ Option K where
  toFun := coord
  invFun := ptOf
  left_inv := ptOf_coord
  right_inv := coord_ptOf

noncomputable def mobiusMat (M : Matrix (Fin 2) (Fin 2) K) (x : Option K) : Option K :=
  match x with
  | none => if M 1 0 = 0 then none else some (M 0 0 / M 1 0)
  | some y =>
    if M 1 0 * y + M 1 1 = 0 then none
    else some ((M 0 0 * y + M 0 1) / (M 1 0 * y + M 1 1))

noncomputable def mobius (g : GL (Fin 2) K) (x : Option K) : Option K :=
  mobiusMat (g : Matrix (Fin 2) (Fin 2) K) x

lemma coord_smul_ptInf (g : GL (Fin 2) K) :
    coord (g • ptInf) = mobius g none := by
  have hne : (g • (![1, 0] : Fin 2 → K)) ≠ 0 := by
    intro hz
    have h2 := congrArg (fun w => (g⁻¹ : GL (Fin 2) K) • w) hz
    rw [← mul_smul, inv_mul_cancel, one_smul, smul_zero] at h2
    exact (by simp : (![1, 0] : Fin 2 → K) ≠ 0) h2
  have e0 : (g • (![1, 0] : Fin 2 → K)) 0 = (g : Matrix (Fin 2) (Fin 2) K) 0 0 := by
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have e1 : (g • (![1, 0] : Fin 2 → K)) 1 = (g : Matrix (Fin 2) (Fin 2) K) 1 0 := by
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [ptInf, Projectivization.smul_mk, coord_mk]
  simp only [coordAux, mobius, mobiusMat]
  by_cases h : (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0
  · rw [if_pos (by rw [e1]; exact h), if_pos h]
  · rw [if_neg (by rw [e1]; exact h), if_neg h, e0, e1]

lemma coord_smul_ptFin (g : GL (Fin 2) K) (y : K) :
    coord (g • ptFin y) = mobius g (some y) := by
  have hne : (g • (![y, 1] : Fin 2 → K)) ≠ 0 := by
    intro hz
    have h2 := congrArg (fun w => (g⁻¹ : GL (Fin 2) K) • w) hz
    rw [← mul_smul, inv_mul_cancel, one_smul, smul_zero] at h2
    exact (by simp : (![y, 1] : Fin 2 → K) ≠ 0) h2
  have e0 : (g • (![y, 1] : Fin 2 → K)) 0 =
      (g : Matrix (Fin 2) (Fin 2) K) 0 0 * y + (g : Matrix (Fin 2) (Fin 2) K) 0 1 := by
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have e1 : (g • (![y, 1] : Fin 2 → K)) 1 =
      (g : Matrix (Fin 2) (Fin 2) K) 1 0 * y + (g : Matrix (Fin 2) (Fin 2) K) 1 1 := by
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [ptFin, Projectivization.smul_mk, coord_mk]
  simp only [coordAux, mobius, mobiusMat]
  by_cases h : (g : Matrix (Fin 2) (Fin 2) K) 1 0 * y + (g : Matrix (Fin 2) (Fin 2) K) 1 1 = 0
  · rw [if_pos (by rw [e1]; exact h), if_pos h]
  · rw [if_neg (by rw [e1]; exact h), if_neg h, e0, e1]

/-- Equivariance of the affine coordinate with respect to the action of `GL₂(K)`. -/
lemma coord_smul_GL (g : GL (Fin 2) K) (x : P1 K) : coord (g • x) = mobius g (coord x) := by
  rw [show x = ptOf (coord x) from (ptOf_coord x).symm]
  cases h : coord x with
  | none => simpa [ptOf] using coord_smul_ptInf g
  | some y => simpa [ptOf] using coord_smul_ptFin g y

lemma coord_smul_class (g : GL (Fin 2) K) (x : P1 K) :
    coord ((g : PGL2 K) • x) = mobius g (coord x) := by
  rw [mk_smul]
  exact coord_smul_GL g x

/-- Equivariance of the affine coordinate with respect to the action of `PGL₂(K)`. -/
lemma coord_smul (s : PGL2 K) (x : P1 K) :
    coord (s • x) = mobius (Quotient.out s) (coord x) := by
  conv_lhs => rw [← Quotient.out_eq s]
  exact coord_smul_class _ x

def invMat (u c : K) : Matrix (Fin 2) (Fin 2) K := !![u, c - u ^ 2; 1, -u]

lemma invMat_det (u c : K) : (invMat u c).det = -c := by
  rw [invMat, Matrix.det_fin_two_of]; ring

lemma invMat_sq (u c : K) : invMat u c * invMat u c = c • (1 : Matrix (Fin 2) (Fin 2) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [invMat, Matrix.mul_apply, Fin.sum_univ_two] <;> ring


/-! ### The involutions `s_u(X) = u + c/(X - u)` -/

/-- The matrix `[[u, c - u²], [1, -u]]` as an element of `GL₂(K)`, when `c ≠ 0`. -/
noncomputable def invGL (u c : K) (hc : c ≠ 0) : GL (Fin 2) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (invMat u c) (by rw [invMat_det]; exact neg_ne_zero.mpr hc)

/-- The involution `s_u = [[u, c - u²], [1, -u]]` of `PGL₂(K)`, with `c ≠ 0`. -/
noncomputable def invClass (u c : K) (hc : c ≠ 0) : PGL2 K := (invGL u c hc : PGL2 K)

@[simp] lemma invGL_coe (u c : K) (hc : c ≠ 0) :
    (invGL u c hc : Matrix (Fin 2) (Fin 2) K) = invMat u c := rfl

/-- `s_u` acts on `∞` by `∞ ↦ u`. -/
@[simp] lemma mobius_invGL_inf (u c : K) (hc : c ≠ 0) :
    mobius (invGL u c hc) none = some u := by
  simp [mobius, mobiusMat, invGL, invMat]

/-- `s_u` acts on its own label `u` by `u ↦ ∞`. -/
@[simp] lemma mobius_invGL_at (u c : K) (hc : c ≠ 0) :
    mobius (invGL u c hc) (some u) = none := by
  simp [mobius, mobiusMat, invGL, invMat]

/-- `s_u` acts on `x ≠ u` by `x ↦ u + c/(x - u)`. -/
lemma mobius_invGL_fin (u c x : K) (hc : c ≠ 0) (hx : x ≠ u) :
    mobius (invGL u c hc) (some x) = some (u + c / (x - u)) := by
  have hcond : (1 : K) * x + -u ≠ 0 := by
    rw [one_mul, ← sub_eq_add_neg]
    exact sub_ne_zero.mpr hx
  have h00 : (invMat u c) 0 0 = u := rfl
  have h01 : (invMat u c) 0 1 = c - u ^ 2 := rfl
  have h10 : (invMat u c) 1 0 = 1 := rfl
  have h11 : (invMat u c) 1 1 = -u := rfl
  simp only [mobius, mobiusMat, invGL_coe, h00, h01, h10, h11]
  rw [if_neg hcond, one_mul]
  congr 1
  have hsub : x - u = x + -u := sub_eq_add_neg x u
  have hx' : x + -u ≠ 0 := by simpa using hcond
  rw [hsub, div_eq_iff hx', add_mul, div_mul_cancel₀ _ hx']
  ring

/-- The action of `s_u` on the affine line, as a map `K → Option K`. -/
lemma coord_smul_invClass (u c x : K) (hc : c ≠ 0) :
    coord (invClass u c hc • ptFin x) = mobius (invGL u c hc) (some x) := by
  have h : invClass u c hc = ((invGL u c hc : GL (Fin 2) K) : PGL2 K) := rfl
  rw [h, coord_smul_class]
  simp

/-! ### The normalization `σ(∞) = ∞` -/

/-- The data attached to an admissible set `S` of size `q` in the normalization `σ(∞) = ∞`:
`S = {s_u : u ∈ K}` with `s_u(X) = u + d(u)/(X - u)` and `d(u) ≠ 0`, and `σ` fixes `∞` and maps
`u ∈ K` to `sf u ∈ K`. -/
structure AffineData (S : Set (PGL2 K)) (σ : Equiv.Perm (P1 K)) where
  /-- the interpolating values `d(u)`, all nonzero -/
  d : K → K
  d_ne : ∀ u, d u ≠ 0
  /-- `S` is exactly the set of involutions `s_u` -/
  isNormal : ∀ s, s ∈ S ↔ ∃ u, s = invClass u (d u) (d_ne u)
  /-- `σ` fixes the point at infinity -/
  σ_inf : σ ptInf = ptInf
  /-- the induced map on the affine line -/
  sf : K → K
  /-- `σ` acts on finite points by `sf` -/
  σ_fin : ∀ u, σ (ptFin u) = ptFin (sf u)
  /-- the polynomial `d`, of degree at most `q - 1`, interpolating the values `d(u)` -/
  D : K[X]
  D_deg : D.natDegree ≤ Nat.card K - 1
  D_eval : ∀ u, D.eval u = d u
  /-- the derivative identity `σ(x) = x - d'(x)` of §2 -/
  σ_deriv : ∀ u, sf u = u - (derivative D).eval u

/-- The normal form of `AffineData` does **not** by itself force `d ∘ σ = d`: the structure only
records that `d` is nowhere zero and interpolated by a polynomial of degree `≤ q - 1`, and
`sf u = u - d'(u)`. The implication `d(σ u) = d(u)` of Lemma 6 needs the incidence
identity (1) relating `S` and `σ`, so the statements of Lemmas 6, 7 and Theorem 8 below carry
`IsAdmissible S`, `IsMissingPerm S σ` and `σ * σ = 1` as explicit hypotheses. -/


lemma mkOfDetNeZero_val (A : Matrix (Fin 2) (Fin 2) K) (h : A.det ≠ 0) :
    ((Matrix.GeneralLinearGroup.mkOfDetNeZero A h : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = A :=
  rfl

lemma scalar_val (u : Kˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) = Matrix.scalar (Fin 2) (u : K) := rfl

/-- In `PGL₂(K)`, invertible matrices differing by a nonzero scalar have the same class. -/
lemma class_smul (lam : K) (hlam : lam ≠ 0) (A : Matrix (Fin 2) (Fin 2) K) (hA : A.det ≠ 0)
    (hA' : (lam • A).det ≠ 0) :
    ((Matrix.GeneralLinearGroup.mkOfDetNeZero (lam • A) hA' : GL (Fin 2) K) : PGL2 K)
      = ((Matrix.GeneralLinearGroup.mkOfDetNeZero A hA : GL (Fin 2) K) : PGL2 K) := by
  classical
  have hscalar : ((Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 lam hlam) : GL (Fin 2) K) :
      PGL2 K) = 1 := by
    rw [QuotientGroup.eq_one_iff, Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨Units.mk0 lam hlam, rfl⟩
  have hBC : Matrix.GeneralLinearGroup.mkOfDetNeZero (lam • A) hA' =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 lam hlam) *
        Matrix.GeneralLinearGroup.mkOfDetNeZero A hA := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    rw [Matrix.GeneralLinearGroup.coe_mul, mkOfDetNeZero_val, mkOfDetNeZero_val, scalar_val]
    simp [Matrix.smul_apply, smul_eq_mul, Matrix.scalar, Matrix.diagonal_apply, apply_ite]
  rw [hBC]
  simp only [QuotientGroup.mk_mul, hscalar, one_mul]

lemma invMat_00 (u c : K) : invMat u c 0 0 = u := rfl
lemma invMat_01 (u c : K) : invMat u c 0 1 = c - u ^ 2 := rfl
lemma invMat_10 (u c : K) : invMat u c 1 0 = 1 := rfl
lemma invMat_11 (u c : K) : invMat u c 1 1 = -u := rfl

/-- An involution of `PGL₂(K)` sending `∞` to `u` is `s_u = [[u, c-u²],[1,-u]]` for some
`c ≠ 0`. -/
lemma exists_invClass_of_smul_ptInf {s : PGL2 K} (hs : IsInvolution s)
    {u : K} (hu : s • ptInf = ptFin u) : ∃ c : K, ∃ hc : c ≠ 0, s = invClass u c hc := by
  classical
  set M : Matrix (Fin 2) (Fin 2) K := ((Quotient.out s : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
    with hM
  have hMd : M.det ≠ 0 := Matrix.GeneralLinearGroup.det_ne_zero (Quotient.out s)
  have h1 : mobius (Quotient.out s) none = some u := by
    have h := coord_smul s ptInf
    rw [hu, coord_ptFin, coord_ptInf] at h
    exact h.symm
  have hsu : s • ptFin u = ptInf := by
    conv_lhs => rw [← hu]
    rw [← mul_smul, hs.2, one_smul]
  have h2 : mobius (Quotient.out s) (some u) = none := by
    have h := coord_smul s (ptFin u)
    rw [hsu, coord_ptInf, coord_ptFin] at h
    exact h.symm
  simp only [mobius, mobiusMat, hM] at h1 h2
  by_cases h10 : M 1 0 = 0
  · rw [if_pos h10] at h1
    exact absurd h1 (by simp)
  · rw [if_neg h10] at h1
    have h00 : M 0 0 / M 1 0 = u := by simpa using h1
    have hcond : M 1 0 * u + M 1 1 = 0 := by
      by_contra hc
      rw [if_neg hc] at h2
      exact absurd h2 (by simp)
    have h00' : M 0 0 = u * M 1 0 := by
      rw [← h00]; field_simp
    have h11' : M 1 1 = -(M 1 0 * u) := by linear_combination hcond
    set c : K := M 0 1 / M 1 0 + u ^ 2 with hcdef
    have hN : (M 1 0)⁻¹ • M = invMat u c := by
      ext i j
      fin_cases i <;> fin_cases j
      · show (M 1 0)⁻¹ * M 0 0 = u
        rw [h00', mul_comm u (M 1 0), ← mul_assoc, inv_mul_cancel₀ h10, one_mul]
      · show (M 1 0)⁻¹ * M 0 1 = c - u ^ 2
        rw [hcdef, div_eq_inv_mul]; ring
      · show (M 1 0)⁻¹ * M 1 0 = 1
        exact inv_mul_cancel₀ h10
      · show (M 1 0)⁻¹ * M 1 1 = -u
        rw [h11', mul_neg, ← mul_assoc, inv_mul_cancel₀ h10, one_mul]
    have hdetN : ((M 1 0)⁻¹ • M).det ≠ 0 := by
      rw [Matrix.det_smul, Fintype.card_fin]
      exact mul_ne_zero (pow_ne_zero 2 (inv_ne_zero h10)) hMd
    have hc : c ≠ 0 := by
      intro hc0
      apply hdetN
      rw [hN, invMat_det, hc0, neg_zero]
    refine ⟨c, hc, ?_⟩
    have hMeq : (Matrix.GeneralLinearGroup.mkOfDetNeZero M hMd : GL (Fin 2) K) = Quotient.out s := by
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      rfl
    calc s = ((Quotient.out s : GL (Fin 2) K) : PGL2 K) := (Quotient.out_eq s).symm
      _ = ((Matrix.GeneralLinearGroup.mkOfDetNeZero M hMd : GL (Fin 2) K) : PGL2 K) := by
            rw [hMeq]
      _ = ((Matrix.GeneralLinearGroup.mkOfDetNeZero ((M 1 0)⁻¹ • M) hdetN : GL (Fin 2) K) :
            PGL2 K) := (class_smul _ (inv_ne_zero h10) M hMd hdetN).symm
      _ = invClass u c hc := by
            have hgl : (Matrix.GeneralLinearGroup.mkOfDetNeZero ((M 1 0)⁻¹ • M) hdetN :
                GL (Fin 2) K) = invGL u c hc := by
              apply Matrix.GeneralLinearGroup.ext
              intro i j
              rw [mkOfDetNeZero_val, invGL_coe, hN]
            show ((Matrix.GeneralLinearGroup.mkOfDetNeZero ((M 1 0)⁻¹ • M) hdetN :
                GL (Fin 2) K) : PGL2 K) = ((invGL u c hc : GL (Fin 2) K) : PGL2 K)
            rw [hgl]

section Labelling

variable [Fintype K]

/-! ### The labelling bijection `S ≃ K` -/

/-- Under `σ(∞) = ∞`, no element of `S` fixes `∞`. -/
lemma smul_ptInf_ne_ptInf {S : Set (PGL2 K)} (hS : IsAdmissible S) {σ : Equiv.Perm (P1 K)}
    (hσ : IsMissingPerm S σ) (hinf : σ (ptInf : P1 K) = ptInf) {s : PGL2 K} (hs : s ∈ S) :
    s • (ptInf : P1 K) ≠ ptInf := by
  have h := (hσ (ptInf : P1 K) (s • ptInf)).1 ⟨s, hs, rfl⟩
  rw [hinf] at h
  exact h

/-- Every element of `S` sends `∞` to a finite point `[u : 1]`. -/
lemma exists_ptFin_smul_ptInf {S : Set (PGL2 K)} (hS : IsAdmissible S)
    {σ : Equiv.Perm (P1 K)} (hσ : IsMissingPerm S σ) (hinf : σ (ptInf : P1 K) = ptInf)
    {s : PGL2 K} (hs : s ∈ S) : ∃ u : K, s • (ptInf : P1 K) = ptFin u := by
  have hne := smul_ptInf_ne_ptInf hS hσ hinf hs
  have hcoord : coord (s • (ptInf : P1 K)) ≠ none := by
    intro h
    apply hne
    have h2 := ptOf_coord (s • (ptInf : P1 K))
    rw [h] at h2
    simpa [ptOf] using h2.symm
  cases hc : coord (s • (ptInf : P1 K)) with
  | none => exact absurd hc hcoord
  | some u => exact ⟨u, by rw [← ptOf_coord (s • (ptInf : P1 K)), hc]; rfl⟩

/-- The label of `s ∈ S`: the unique `u` with `s • ∞ = [u : 1]`. -/
noncomputable def labelOf {S : Set (PGL2 K)} {σ : Equiv.Perm (P1 K)} (hS : IsAdmissible S)
    (hσ : IsMissingPerm S σ)
    (hinf : σ (ptInf : P1 K) = ptInf) {s : PGL2 K} (hs : s ∈ S) : K :=
  (exists_ptFin_smul_ptInf hS hσ hinf hs).choose

lemma labelOf_smul {S : Set (PGL2 K)} {σ : Equiv.Perm (P1 K)} (hS : IsAdmissible S)
    (hσ : IsMissingPerm S σ)
    (hinf : σ (ptInf : P1 K) = ptInf) {s : PGL2 K} (hs : s ∈ S) :
    s • (ptInf : P1 K) = ptFin (labelOf hS hσ hinf hs) :=
  (exists_ptFin_smul_ptInf hS hσ hinf hs).choose_spec

/-- Injectivity of the labelling. -/
lemma label_injective {S : Set (PGL2 K)} (hS : IsAdmissible S) {s t : PGL2 K} (hs : s ∈ S)
    (ht : t ∈ S) (h : s • (ptInf : P1 K) = t • ptInf) : s = t := by
  by_contra hne
  have hcon := hS.2 t ht s hs (Ne.symm hne) (ptInf : P1 K)
  have hfix : (t * s) • (ptInf : P1 K) = ptInf := by
    have ht2 := (hS.1 t ht).2
    calc (t * s) • (ptInf : P1 K) = t • (s • (ptInf : P1 K)) := by rw [mul_smul]
      _ = t • (t • (ptInf : P1 K)) := by rw [h]
      _ = (t * t) • (ptInf : P1 K) := by rw [← mul_smul]
      _ = (1 : PGL2 K) • (ptInf : P1 K) := by rw [ht2]
      _ = ptInf := one_smul _ _
  exact hcon hfix

/-- Surjectivity of the labelling, from `|S| = q = |K|`. -/
lemma label_surjective {S : Set (PGL2 K)} {σ : Equiv.Perm (P1 K)} (hS : IsAdmissible S)
    (hcard : Nat.card S = Nat.card K)
    (hσ : IsMissingPerm S σ) (hinf : σ (ptInf : P1 K) = ptInf) :
    ∀ u : K, ∃ s : PGL2 K, s ∈ S ∧ s • (ptInf : P1 K) = ptFin u := by
  classical
  have hφ_inj : Function.Injective
      (fun s : {s : PGL2 K // s ∈ S} => labelOf hS hσ hinf s.2) := by
    intro a b hab
    apply Subtype.ext
    apply label_injective hS a.2 b.2
    rw [labelOf_smul hS hσ hinf a.2, labelOf_smul hS hσ hinf b.2]
    exact congrArg ptFin hab
  have hcard_eq : Fintype.card {s : PGL2 K // s ∈ S} = Fintype.card K := by
    have h1 : Nat.card {s : PGL2 K // s ∈ S} = Nat.card S := rfl
    rw [← Nat.card_eq_fintype_card, h1, hcard, Nat.card_eq_fintype_card]
  have hbij : Function.Bijective
      (fun s : {s : PGL2 K // s ∈ S} => labelOf hS hσ hinf s.2) :=
    (Fintype.bijective_iff_injective_and_card _).2 ⟨hφ_inj, hcard_eq⟩
  intro u
  obtain ⟨s, hs⟩ := hbij.2 u
  refine ⟨s.1, s.2, ?_⟩
  rw [labelOf_smul hS hσ hinf s.2]
  exact congrArg ptFin hs

/-- The labelling bijection `S ≃ K`: `s ↦ u` where `s • ∞ = [u : 1]`. -/
noncomputable def labelEquiv {S : Set (PGL2 K)} {σ : Equiv.Perm (P1 K)} (hS : IsAdmissible S)
    (hcard : Nat.card S = Nat.card K) (hσ : IsMissingPerm S σ)
    (hinf : σ (ptInf : P1 K) = ptInf) : {s : PGL2 K // s ∈ S} ≃ K :=
  Equiv.ofBijective (fun s => labelOf hS hσ hinf s.2) (by
    constructor
    · intro a b hab
      apply Subtype.ext
      apply label_injective hS a.2 b.2
      rw [labelOf_smul hS hσ hinf a.2, labelOf_smul hS hσ hinf b.2]
      exact congrArg ptFin hab
    · intro u
      obtain ⟨s, hs, hs'⟩ := label_surjective hS hcard hσ hinf u
      refine ⟨⟨s, hs⟩, ptFin_injective ?_⟩
      rw [← labelOf_smul hS hσ hinf hs]
      exact hs')

end Labelling


/-! ### The induced map on the affine line -/

/-- A permutation `σ` fixing `∞` sends the finite point `[u : 1]` to a finite point. -/
lemma exists_sf (σ : Equiv.Perm (P1 K)) (hinf : σ (ptInf : P1 K) = ptInf) (u : K) :
    ∃ w : K, σ (ptFin u) = ptFin w := by
  have hne : σ (ptFin u) ≠ ptInf := by
    intro h
    exact ptFin_ne_ptInf u (σ.injective (h.trans hinf.symm))
  have hcoord : coord (σ (ptFin u)) ≠ none := by
    intro h
    apply hne
    have h2 := ptOf_coord (σ (ptFin u))
    rw [h] at h2
    simpa [ptOf] using h2.symm
  cases hc : coord (σ (ptFin u)) with
  | none => exact absurd hc hcoord
  | some w => exact ⟨w, by rw [← ptOf_coord (σ (ptFin u)), hc]; rfl⟩

/-- The map induced on the affine line by a permutation `σ` fixing `∞`. -/
noncomputable def sfOf (σ : Equiv.Perm (P1 K)) (hinf : σ (ptInf : P1 K) = ptInf) (u : K) : K :=
  (exists_sf σ hinf u).choose

lemma sfOf_spec (σ : Equiv.Perm (P1 K)) (hinf : σ (ptInf : P1 K) = ptInf) (u : K) :
    σ (ptFin u) = ptFin (sfOf σ hinf u) :=
  (exists_sf σ hinf u).choose_spec

/-! ### Reduction to the normalization -/

/-- The conjugate of a permutation of the projective line by `g ∈ PGL₂(K)`. -/
def conjPerm (g : PGL2 K) (σ : P1 K → P1 K) : P1 K → P1 K := fun y => g • σ (g⁻¹ • y)

/-- The conjugate of a set of projective transformations. -/
def conjSet (g : PGL2 K) (S : Set (PGL2 K)) : Set (PGL2 K) := {t | ∃ s ∈ S, t = g * s * g⁻¹}

/-- Conjugation turns fixed points into fixed points: `f` is unchanged. -/
lemma numFixed_conjPerm (g : PGL2 K) (σ : P1 K → P1 K) :
    numFixed (conjPerm g σ) = numFixed σ := by
  unfold numFixed conjPerm
  refine Nat.card_congr (Equiv.subtypeEquiv (MulAction.toPerm g⁻¹) ?_)
  intro y
  simp only [MulAction.toPerm_apply, Equiv.Perm.coe_inv]
  constructor
  · intro h
    have := congrArg (fun z => g⁻¹ • z) h
    simpa using this
  · intro h
    rw [h]
    simp

lemma conj_smul (g s : PGL2 K) (x : P1 K) : ((g * s * g⁻¹) • x) = g • (s • (g⁻¹ • x)) := by
  rw [mul_smul, mul_smul]

/-- Admissibility is invariant under conjugation: `t ∈ conjSet g S` are the conjugates
`g s g⁻¹` of the elements of `S`. -/
lemma isAdmissible_conjSet (g : PGL2 K) {S : Set (PGL2 K)} (hS : IsAdmissible S) :
    IsAdmissible (conjSet g S) := by
  constructor
  · rintro t ⟨s, hs, rfl⟩
    obtain ⟨hne, hsq⟩ := hS.1 s hs
    refine ⟨?_, ?_⟩
    · intro h
      apply hne
      have h2 := congrArg (fun z => g⁻¹ * z * g) h
      rw [mul_one] at h2
      calc s = g⁻¹ * (g * s * g⁻¹) * g := by group
        _ = g⁻¹ * g := h2
        _ = 1 := inv_mul_cancel g
    · have h2 : (g * s * g⁻¹) * (g * s * g⁻¹) = g * (s * s) * g⁻¹ := by group
      rw [h2, hsq]; group
  · rintro t ⟨s, hs, rfl⟩ t' ⟨s', hs', rfl⟩ hne x hx
    have hss' : s ≠ s' := by
      intro h
      exact hne (by rw [h])
    have h2 : ((g * s * g⁻¹) * (g * s' * g⁻¹)) = g * (s * s') * g⁻¹ := by group
    rw [h2, conj_smul] at hx
    have h3 : (s * s') • (g⁻¹ • x) = g⁻¹ • x := by
      have := congrArg (fun z => g⁻¹ • z) hx
      simpa using this
    exact hS.2 s hs s' hs' hss' (g⁻¹ • x) h3

/-- The missing-permutation property is invariant under conjugation. -/
lemma isMissingPerm_conjSet (g : PGL2 K) {S : Set (PGL2 K)} {σ : P1 K → P1 K}
    (hσ : IsMissingPerm S σ) : IsMissingPerm (conjSet g S) (conjPerm g σ) := by
  intro x y
  have key : (∃ t ∈ conjSet g S, t • x = y) ↔ ∃ s ∈ S, s • (g⁻¹ • x) = g⁻¹ • y := by
    constructor
    · rintro ⟨t, ⟨s, hs, rfl⟩, hxy⟩
      refine ⟨s, hs, ?_⟩
      have h2 : (g * s * g⁻¹) • x = g • (s • (g⁻¹ • x)) := by
        rw [mul_smul, mul_smul]
      rw [h2] at hxy
      have := congrArg (fun z => g⁻¹ • z) hxy
      simpa using this
    · rintro ⟨s, hs, hsy⟩
      exact ⟨g * s * g⁻¹, ⟨s, hs, rfl⟩, by rw [mul_smul, mul_smul, hsy, smul_inv_smul]⟩
  rw [key, hσ (g⁻¹ • x) (g⁻¹ • y)]
  constructor
  · rintro h hc
    apply h
    rw [hc]
    simp [conjPerm]
  · rintro h hc
    apply h
    calc y = g • (g⁻¹ • y) := by simp
      _ = g • σ (g⁻¹ • x) := by rw [hc]
      _ = conjPerm g σ x := rfl

/-- A matrix sending a given finite point to `∞`. -/
def toInfMat (y : K) : Matrix (Fin 2) (Fin 2) K := !![0, 1; 1, -y]

lemma toInfMat_det (y : K) : (toInfMat y).det = -1 := by
  rw [toInfMat, Matrix.det_fin_two_of]; ring

/-- Every point of the projective line can be sent to `∞` by a projective transformation. -/
lemma exists_smul_eq_ptInf (x : P1 K) : ∃ g : PGL2 K, g • x = ptInf := by
  cases h : coord x with
  | none => exact ⟨1, by rw [one_smul, ← ptOf_coord x, h]; rfl⟩
  | some y =>
    let g : GL (Fin 2) K :=
      Matrix.GeneralLinearGroup.mkOfDetNeZero (toInfMat y) (by rw [toInfMat_det]; norm_num)
    refine ⟨(g : PGL2 K), ?_⟩
    have hc : coord ((g : PGL2 K) • x) = none := by
      rw [coord_smul_class g, h]
      simp [g, mobius, mobiusMat, toInfMat]
    calc (g : PGL2 K) • x = ptOf (coord ((g : PGL2 K) • x)) := (ptOf_coord _).symm
      _ = ptOf none := by rw [hc]
      _ = ptInf := rfl

/-- Two elements of an admissible set agreeing at a point are equal. -/
lemma eq_of_smul_eq {S : Set (PGL2 K)} (hS : IsAdmissible S) {s t : PGL2 K} (hs : s ∈ S)
    (ht : t ∈ S) {y : P1 K} (h : s • y = t • y) : s = t := by
  by_contra hne
  have hcon := hS.2 t ht s hs (Ne.symm hne) y
  have hfix : (t * s) • y = y := by
    have ht2 := (hS.1 t ht).2
    calc (t * s) • y = t • (s • y) := by rw [mul_smul]
      _ = t • (t • y) := by rw [h]
      _ = (t * t) • y := by rw [← mul_smul]
      _ = (1 : PGL2 K) • y := by rw [ht2]
      _ = y := one_smul _ _
  exact hcon hfix

/-- **The derivative identity of §2**: `σ(x) = x - d'(x)` on the affine line. -/
lemma sigma_deriv [Fintype K] (hodd : Odd (Nat.card K)) (hq : 5 ≤ Nat.card K)
    {S : Set (PGL2 K)} (hS : IsAdmissible S) (hcard : Nat.card S = Nat.card K)
    {σ : Equiv.Perm (P1 K)} (hσ : IsMissingPerm S σ) (hinf : σ (ptInf : P1 K) = ptInf)
    {d : K → K} (hd : ∀ u, d u ≠ 0)
    (isNormal : ∀ s, s ∈ S ↔ ∃ u, s = invClass u (d u) (hd u)) (x : K) :
    sfOf σ hinf x = x - (Polynomial.derivative (Polynomial.interpPoly d)).eval x := by
  classical
  have hq3 : 3 ≤ Nat.card K := by omega
  have hq2 : 2 ≤ Nat.card K := by omega
  set sOf : K → PGL2 K := fun u => invClass u (d u) (hd u) with hsOf
  have hsOf_mem : ∀ u, sOf u ∈ S := fun u => (isNormal _).2 ⟨u, rfl⟩
  have hsOf_inf : ∀ u, sOf u • (ptInf : P1 K) = ptFin u := by
    intro u
    have hcoord : coord (sOf u • (ptInf : P1 K)) = some u := by
      have h1 : sOf u = ((invGL u (d u) (hd u) : GL (Fin 2) K) : PGL2 K) := rfl
      rw [h1, coord_smul_class, coord_ptInf]
      exact mobius_invGL_inf u (d u) (hd u)
    rw [← ptOf_coord (sOf u • (ptInf : P1 K)), hcoord]
    rfl
  have hsOf_fin : ∀ u y, y ≠ u → sOf u • ptFin y = ptFin (u + d u / (y - u)) := by
    intro u y hy
    have hcoord : coord (sOf u • ptFin y) = some (u + d u / (y - u)) := by
      have h1 : sOf u = ((invGL u (d u) (hd u) : GL (Fin 2) K) : PGL2 K) := rfl
      rw [h1, coord_smul_class, coord_ptFin]
      exact mobius_invGL_fin u (d u) y (hd u) hy
    rw [← ptOf_coord (sOf u • ptFin y), hcoord]
    rfl
  have hsOf_at : ∀ u, sOf u • ptFin u = ptInf := by
    intro u
    have hcoord : coord (sOf u • ptFin u) = none := by
      have h1 : sOf u = ((invGL u (d u) (hd u) : GL (Fin 2) K) : PGL2 K) := rfl
      rw [h1, coord_smul_class, coord_ptFin]
      exact mobius_invGL_at u (d u) (hd u)
    rw [← ptOf_coord (sOf u • ptFin u), hcoord]
    rfl
  -- the sum bijection `{u ≠ x} → {v ≠ sf}`
  have hsum : ∑ u ∈ Finset.univ.erase x, (u + d u / (x - u)) = ∑ v ∈ Finset.univ.erase (sfOf σ hinf x), v := by
    refine Finset.sum_bij (fun u _ => u + d u / (x - u)) ?_ ?_ ?_ ?_
    · intro u hu
      rw [Finset.mem_erase] at hu ⊢
      refine ⟨?_, Finset.mem_univ _⟩
      intro hEq
      have h1 : sOf u • ptFin x = ptFin (u + d u / (x - u)) := hsOf_fin u x (Ne.symm hu.1)
      rw [hEq] at h1
      have h2 : σ (ptFin x) = ptFin (sfOf σ hinf x) := sfOf_spec σ hinf x
      have h3 : ¬ ∃ s ∈ S, s • ptFin x = σ (ptFin x) := by
        rw [hσ (ptFin x) (σ (ptFin x))]
        simp
      apply h3
      exact ⟨sOf u, hsOf_mem u, by rw [h1, h2]⟩
    · intro u₁ hu₁ u₂ hu₂ hEq
      rw [Finset.mem_erase] at hu₁ hu₂
      have h1 : sOf u₁ • ptFin x = ptFin (u₁ + d u₁ / (x - u₁)) := hsOf_fin u₁ x (Ne.symm hu₁.1)
      have h2 : sOf u₂ • ptFin x = ptFin (u₂ + d u₂ / (x - u₂)) := hsOf_fin u₂ x (Ne.symm hu₂.1)
      have h4 : sOf u₁ = sOf u₂ := eq_of_smul_eq hS (hsOf_mem u₁) (hsOf_mem u₂) (by
        rw [h1, h2, hEq])
      have h5 : ptFin u₁ = ptFin u₂ := by rw [← hsOf_inf u₁, ← hsOf_inf u₂, h4]
      exact ptFin_injective h5
    · intro v hv
      rw [Finset.mem_erase] at hv
      have hne : ptFin v ≠ σ (ptFin x) := by
        rw [sfOf_spec σ hinf x]
        intro h
        exact hv.1 (ptFin_injective h)
      obtain ⟨s, hs, hsx⟩ := (hσ (ptFin x) (ptFin v)).2 hne
      obtain ⟨u, hu⟩ := (isNormal s).1 hs
      have hsu : s = sOf u := hu
      rw [hsu] at hsx
      have hux : u ≠ x := by
        intro h
        rw [h] at hsx
        rw [hsOf_at x] at hsx
        exact ptFin_ne_ptInf v hsx.symm
      rw [hsOf_fin u x (Ne.symm hux)] at hsx
      exact ⟨u, by rw [Finset.mem_erase]; exact ⟨hux, Finset.mem_univ _⟩, ptFin_injective hsx⟩
    · intro u hu
      rfl

  -- split and evaluate the sums
  rw [Finset.sum_add_distrib] at hsum
  have hsumU : ∑ u ∈ Finset.univ.erase x, u = -x := by
    have h0 := Polynomial.sum_univ_eq_zero (K := K) hq3
    have hsplit := Finset.sum_erase_add (Finset.univ : Finset K) (fun u => u) (Finset.mem_univ x)
    rw [h0] at hsplit
    exact eq_neg_of_add_eq_zero_left hsplit
  have hsumD : ∑ u ∈ Finset.univ.erase x, d u / (x - u)
      = (Polynomial.derivative (Polynomial.interpPoly d)).eval x := by
    rw [Polynomial.deriv_eq_sum hq3 (Polynomial.interpPoly_natDegree_le d) x]
    exact Finset.sum_congr rfl fun u _ => by
      rw [Polynomial.interpPoly_eval hq2 d u]
  have hsumV : ∑ v ∈ Finset.univ.erase (sfOf σ hinf x), v = -(sfOf σ hinf x) := by
    have h0 := Polynomial.sum_univ_eq_zero (K := K) hq3
    have hsplit := Finset.sum_erase_add (Finset.univ : Finset K) (fun v => v) (Finset.mem_univ (sfOf σ hinf x))
    rw [h0] at hsplit
    exact eq_neg_of_add_eq_zero_left hsplit
  rw [hsumU, hsumD, hsumV] at hsum
  linear_combination hsum

/-- **The normalization step of §2.** Let `q ≥ 5` be odd, `S ⊆ PGL₂(q)` admissible of size `q`,
and let `σ` be the missing permutation, normalized so that `σ(∞) = ∞`. Then `S` is exactly the
set of involutions `s_u(X) = u + d(u)/(X - u)` for `u ∈ K`, with `d(u) ≠ 0`, and there is a
polynomial `D` of degree at most `q - 1` interpolating `d` and satisfying `σ(x) = x - d'(x)`.

The labelling is the one of the paper: `s_u` is the unique element of `S` with `s_u(∞) = u`, and
`d(u)` is read off its matrix representative `[[u, d(u) - u²], [1, -u]]` (every involution has
trace zero in odd characteristic). The derivative identity is proved by Lagrange interpolation
(`deriv_eq_sum`) together with `∑ u = 0`. -/
theorem exists_affineData [Fintype K] (hodd : Odd (Nat.card K)) (hq : 5 ≤ Nat.card K)
    {S : Set (PGL2 K)} (hS : IsAdmissible S) (hcard : Nat.card S = Nat.card K)
    {σ : Equiv.Perm (P1 K)} (hσ : IsMissingPerm S σ) (hinf : σ ptInf = ptInf) :
    Nonempty (AffineData S σ) := by
  classical
  have hq2 : 2 ≤ Nat.card K := by omega
  have hchoice : ∀ u : K, ∃ c : K, ∃ hc : c ≠ 0, ∃ s : PGL2 K, s ∈ S ∧
      s • (ptInf : P1 K) = ptFin u ∧ s = invClass u c hc := by
    intro u
    obtain ⟨s, hs, hsu⟩ := label_surjective hS hcard hσ hinf u
    obtain ⟨c, hc, hsc⟩ := exists_invClass_of_smul_ptInf (hS.1 s hs) hsu
    exact ⟨c, hc, s, hs, hsu, hsc⟩
  choose d hd s hrest using hchoice
  have hsS : ∀ u, s u ∈ S := fun u => (hrest u).1
  have hsu : ∀ u, s u • (ptInf : P1 K) = ptFin u := fun u => (hrest u).2.1
  have hsc : ∀ u, s u = invClass u (d u) (hd u) := fun u => (hrest u).2.2
  have isNormal : ∀ t, t ∈ S ↔ ∃ u, t = invClass u (d u) (hd u) := by
    intro t
    constructor
    · intro ht
      refine ⟨labelOf hS hσ hinf ht, ?_⟩
      have hEq : t • (ptInf : P1 K) = s (labelOf hS hσ hinf ht) • (ptInf : P1 K) := by
        rw [labelOf_smul hS hσ hinf ht, hsu (labelOf hS hσ hinf ht)]
      have h1 : t = s (labelOf hS hσ hinf ht) := label_injective hS ht (hsS _) hEq
      exact h1.trans (hsc (labelOf hS hσ hinf ht))
    · intro ⟨u, hu⟩
      rw [hu, ← hsc u]
      exact hsS u
  exact ⟨{
    d := d
    d_ne := hd
    isNormal := isNormal
    σ_inf := hinf
    sf := sfOf σ hinf
    σ_fin := sfOf_spec σ hinf
    D := Polynomial.interpPoly d
    D_deg := Polynomial.interpPoly_natDegree_le d
    D_eval := fun u => Polynomial.interpPoly_eval hq2 d u
    σ_deriv := fun u => sigma_deriv hodd hq hS hcard hσ hinf hd isNormal u
  }⟩


end PGL2
