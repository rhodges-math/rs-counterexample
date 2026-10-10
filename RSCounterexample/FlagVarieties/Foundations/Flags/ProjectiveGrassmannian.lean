import Mathlib.LinearAlgebra.Projectivization.Basic
import RSCounterexample.FlagVarieties.Foundations.Flags.GrassmannianTransport

/-!
The line convention for projective points agrees with the quotient convention
of the existing Grassmannian: a line in `K^(r+1)` has quotient rank `r`.
These are equivalences of field-valued objects, not scheme isomorphisms.
-/

noncomputable section
namespace FlagVarieties.Foundations
set_option backward.isDefEq.respectTransparency false
open Module
variable {K : Type*} [Field K] {r : ℕ}

/-- A Grassmannian point of quotient rank `r` in `K^(r+1)` is a line. -/
theorem grassmannian_line_finrank
    (P : Module.Grassmannian K (Fin (r+1) → K) r) :
    finrank K P.toSubmodule = 1 := by
  have hq := P.rankAtStalk_eq (⟨⊥, inferInstance⟩ : PrimeSpectrum K)
  rw [Module.rankAtStalk_eq_finrank_of_free] at hq
  change finrank K ((Fin (r+1) → K) ⧸ P.toSubmodule) = r at hq
  have hd := P.toSubmodule.finrank_quotient_add_finrank
  simp only [Module.finrank_pi, Fintype.card_fin] at hd
  change finrank K ((Fin (r+1) → K) ⧸ P.toSubmodule) +
    finrank K P.toSubmodule = r+1 at hd
  omega

/-- The quotient represented by a projective line. -/
def projectiveGrassmannian (p : Projectivization K (Fin (r+1) → K)) :
    Module.Grassmannian K (Fin (r+1) → K) r where
  toSubmodule := p.submodule
  finite_quotient := inferInstance
  projective_quotient := inferInstance
  rankAtStalk_eq q := by
    rw [Module.rankAtStalk_eq_finrank_of_free, Submodule.finrank_quotient,
      p.finrank_submodule]
    simp

@[simp] theorem projectiveGrassmannian_submodule
    (p : Projectivization K (Fin (r+1) → K)) :
    (projectiveGrassmannian p).toSubmodule = p.submodule := rfl

/-- The exact equivalence with the existing quotient Grassmannian. -/
def projectiveGrassmannianEquiv :
    Projectivization K (Fin (r+1) → K) ≃
      Module.Grassmannian K (Fin (r+1) → K) r where
  toFun := projectiveGrassmannian
  invFun P := Projectivization.mk'' P.toSubmodule (grassmannian_line_finrank P)
  left_inv p := by
    apply Projectivization.submodule_injective
    simp
  right_inv P := by
    apply Module.Grassmannian.ext
    simp

/-- Projective transport maps the line submodule. -/
theorem projectivization_map_submodule
    (p : Projectivization K (Fin (r+1) → K))
    (g : (Fin (r+1) → K) ≃ₗ[K] (Fin (r+1) → K)) :
    (Projectivization.map g.toLinearMap g.injective p).submodule =
      p.submodule.map g.toLinearMap := by
  induction p using Projectivization.ind with
  | h v hv =>
    simp only [Projectivization.map_mk, Projectivization.submodule_mk,
      Submodule.map_span, Set.image_singleton]

/-- The equivalence preserves the linear change of coordinates. -/
theorem projectiveGrassmannian_transport
    (p : Projectivization K (Fin (r+1) → K))
    (g : (Fin (r+1) → K) ≃ₗ[K] (Fin (r+1) → K)) :
    projectiveGrassmannian (Projectivization.map g.toLinearMap g.injective p) =
      grassmannianTransport (projectiveGrassmannian p) g := by
  apply Module.Grassmannian.ext
  exact projectivization_map_submodule p g

end FlagVarieties.Foundations
