module

public import Mathlib

/-!
# Sharply transitive sets in `PGL₂(K)`: basic definitions

Formalization of the setting of S. Eberhard, *Sharply transitive sets in PGL₂(K)*
(arXiv:2105.02760v2).

* `PGL2 K` is the projective general linear group `GL₂(K) / Z(GL₂(K))`.
* `PGL2 K` acts on the projective line `ℙ K (Fin 2 → K)`.
* `IsSharplyTransitive S` says that a subset `S` of a group acting on a set is sharply
  transitive (regular): for all `x y` there is a unique `g ∈ S` with `g • x = y`.
-/

@[expose] public section

open scoped LinearAlgebra.Projectivization

/-- A subset `S` of a group `G` acting on `X` is *sharply transitive* (or *regular*) if for
all `x y : X` there is a unique `g ∈ S` with `g • x = y`. -/
def IsSharplyTransitive {G X : Type*} [Group G] [MulAction G X] (S : Set G) : Prop :=
  ∀ x y : X, ∃! g : G, g ∈ S ∧ g • x = y

/-- The projective general linear group `PGL₂(K) = GL₂(K) / Z(GL₂(K))`. -/
abbrev PGL2 (K : Type*) [Field K] : Type _ :=
  GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K)

namespace PGL2

variable {K : Type*} [Field K]

/-- Shortcut instance for the action of `GL₂(K)` on the projective line (speeds up
instance search). -/
instance instMulActionGL : MulAction (GL (Fin 2) K) (ℙ K (Fin 2 → K)) := inferInstance

/-- Shortcut instance for the scalar action of `GL₂(K)` on the projective line. -/
instance (priority := high) instSMulGL : SMul (GL (Fin 2) K) (ℙ K (Fin 2 → K)) :=
  instMulActionGL.toSMul

lemma center_le_ker_toPerm :
    Subgroup.center (GL (Fin 2) K) ≤
      (MulAction.toPermHom (GL (Fin 2) K) (ℙ K (Fin 2 → K))).ker := by
  intro g hg
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hg
  obtain ⟨c, rfl⟩ := hg
  rw [MonoidHom.mem_ker]
  ext x
  induction x using Projectivization.ind with
  | h v hv =>
    simp only [MulAction.toPermHom_apply, MulAction.toPerm_apply, Equiv.Perm.coe_one, id_eq,
      Projectivization.smul_mk]
    rw [Projectivization.mk_eq_mk_iff]
    refine ⟨c, ?_⟩
    ext i
    simp [Units.smul_def, Matrix.GeneralLinearGroup.scalar, Matrix.diagonal_apply]

/-- The action of `PGL₂(K)` on the projective line, as a homomorphism into permutations. -/
def toPerm : PGL2 K →* Equiv.Perm (ℙ K (Fin 2 → K)) :=
  QuotientGroup.lift _ (MulAction.toPermHom _ _) center_le_ker_toPerm

/-- `PGL₂(K)` acts on the projective line `ℙ¹(K) = ℙ K (Fin 2 → K)`. -/
instance : MulAction (PGL2 K) (ℙ K (Fin 2 → K)) :=
  MulAction.compHom _ toPerm

@[simp]
lemma mk_smul (g : GL (Fin 2) K) (x : ℙ K (Fin 2 → K)) :
    ((g : PGL2 K)) • x = g • x := rfl

end PGL2
