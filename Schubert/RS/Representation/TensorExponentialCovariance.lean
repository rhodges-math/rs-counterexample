import Schubert.RS.Representation.RankOneTensorAdjunction
import Mathlib.RingTheory.Nilpotent.Exp

namespace Schubert.RS.Representation
noncomputable section
open TensorProduct Module.End

variable {R X : Type*} [AddCommGroup R] [Module ℂ R] [Module ℚ R]
  [AddCommGroup X] [Module ℂ X] [Module ℚ X]

/-- Exponentiating two nilpotent tensor operators exponentiates each
factor. This is a finite algebraic exponential identity. -/
theorem tensor_sum_exp (D : Module.End ℂ R) (E : Module.End ℂ X)
    (hD : IsNilpotent D) (hE : IsNilpotent E) (r : R) (x : X) :
    IsNilpotent.exp (D.rTensor X + E.lTensor R) (r ⊗ₜ[ℂ] x) =
      IsNilpotent.exp D r ⊗ₜ[ℂ] IsNilpotent.exp E x := by
  have hDr : IsNilpotent (D.rTensor X) := hD.map (rTensorAlgHom ℂ R X)
  have hEl : IsNilpotent (E.lTensor R) := hE.map (lTensorAlgHom ℂ X R)
  have hc : Commute (D.rTensor X) (E.lTensor R) := by ext; simp
  have hr : IsNilpotent.exp (D.rTensor X) = (IsNilpotent.exp D).rTensor X :=
    (hD.map_exp (rTensorAlgHom ℂ R X)).symm
  have hl : IsNilpotent.exp (E.lTensor R) = (IsNilpotent.exp E).lTensor R :=
    (hE.map_exp (lTensorAlgHom ℂ X R)).symm
  rw [IsNilpotent.exp_add_of_commute hc hDr hEl,hr,hl]
  rfl

/-- A bilinear action satisfying the derivation equation respects the
algebraic exponentials of its actual nilpotent source and target operators. -/
theorem tensor_action_exp (D : Module.End ℂ R) (E : Module.End ℂ X)
    (hD : IsNilpotent D) (hE : IsNilpotent E) (ρ : R ⊗[ℂ] X →ₗ[ℂ] X)
    (hρ : E.comp ρ = ρ.comp (D.rTensor X + E.lTensor R)) (r : R) (x : X) :
    IsNilpotent.exp E (ρ (r ⊗ₜ[ℂ] x)) =
      ρ (IsNilpotent.exp D r ⊗ₜ[ℂ] IsNilpotent.exp E x) := by
  have hDr : IsNilpotent (D.rTensor X) := hD.map (rTensorAlgHom ℂ R X)
  have hEl : IsNilpotent (E.lTensor R) := hE.map (lTensorAlgHom ℂ X R)
  have hc : Commute (D.rTensor X) (E.lTensor R) := by ext; simp
  have hh := Module.End.commute_exp_left_of_commute (hc.isNilpotent_add hDr hEl) hE hρ
  exact (LinearMap.congr_fun hh (r ⊗ₜ[ℂ] x)).trans
    (congrArg ρ (tensor_sum_exp D E hD hE r x))

end
end Schubert.RS.Representation
