import Schubert.RS.TorusEigenbasisCharacter

namespace Schubert.RS.Representation
noncomputable section

variable {n : ℕ} {I X : Type*} [AddCommGroup X] [Module ℂ X]
  (b : Module.Basis I ℂ X) (w : I → Weight n)

def basisWeightOperator (t : DiagonalTorus n) : Module.End ℂ X :=
  b.constr ℂ (fun j => integerWeightScalar (w j) t • b j)

theorem basisWeightOperator_basis (t : DiagonalTorus n) (j : I) :
    basisWeightOperator b w t (b j)=integerWeightScalar (w j) t • b j :=
  b.constr_basis ℂ _ j

/-- The torus representation of a weight-labelled basis, with both group
laws verified. Comparison with another torus action requires an intertwining map. -/
def basisWeightTorus : DiagonalTorus n →* Module.End ℂ X where
  toFun := basisWeightOperator b w
  map_one' := by
    apply b.ext
    intro j
    rw [basisWeightOperator_basis]
    simp [integerWeightScalar]
  map_mul' s t := by
    apply b.ext
    intro j
    change basisWeightOperator b w (s*t) (b j)=
      basisWeightOperator b w s (basisWeightOperator b w t (b j))
    rw [basisWeightOperator_basis,basisWeightOperator_basis,map_smul,
      basisWeightOperator_basis,smul_smul,integerWeightScalar_mul]
    rw [mul_comm]

theorem basisWeightTorus_basis (t : DiagonalTorus n) (j : I) :
    basisWeightTorus b w t (b j)=integerWeightScalar (w j) t • b j :=
  basisWeightOperator_basis b w t j

theorem basisWeightTorus_character [Fintype I] [FiniteDimensional ℂ X]
    (label : I → Fin n →₀ ℕ) :
    HasTorusCharacter (basisWeightTorus b (fun j => exponentWeight (label j)))
      (labelledCharacter label) :=
  hasTorusCharacter_of_eigenbasis _ b label (basisWeightTorus_basis b _)

theorem basisWeightTorus_intertwines {J Y : Type*} [AddCommGroup Y] [Module ℂ Y]
    (b' : Module.Basis J ℂ Y) (w' : J → Weight n) (f : X →ₗ[ℂ] Y) (σ : I → J)
    (hf : ∀ j, f (b j)=b' (σ j)) (hw : ∀ j, w j=w' (σ j))
    (t : DiagonalTorus n) (x : X) :
    f (basisWeightTorus b w t x)=basisWeightTorus b' w' t (f x) := by
  have hh : f.comp (basisWeightTorus b w t)=(basisWeightTorus b' w' t).comp f := by
    apply b.ext
    intro j
    change f (basisWeightTorus b w t (b j))=basisWeightTorus b' w' t (f (b j))
    rw [basisWeightTorus_basis,map_smul,hf,basisWeightTorus_basis,hw]
  exact LinearMap.congr_fun hh x

end
end Schubert.RS.Representation
