import Schubert.RS.Representation.RankOneActionExtension

namespace Schubert.RS.Representation
noncomputable section
universe u v
open LieModule Module TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

variable {L : Type v} [LieRing L] [LieAlgebra ℂ L]
  {R X : Type u} [LieRing R] [LieAlgebra ℂ R]
  [LieRingModule L R] [LieModule ℂ L R]
  [AddCommGroup X] [Module ℂ X] [LieRingModule L X] [LieModule ℂ L X]

/-- A derivation action makes the radical bracket an actual equivariant
bilinear map. The compatibility is explicit and later verified on roots. -/
def lieEquivariantBracket
    (hder : ∀ (a : L) (r s : R), ⁅a,⁅r,s⁆⁆ = ⁅⁅a,r⁆,s⁆ + ⁅r,⁅a,s⁆⁆) :
    (R ⊗[ℂ] R) →ₗ⁅ℂ,L⁆ R where
  toLinearMap := TensorProduct.lift (LieModule.toEnd ℂ R R).toLinearMap
  map_lie' := by
    intro a z
    change (TensorProduct.lift (LieModule.toEnd ℂ R R).toLinearMap) ⁅a,z⁆ =
      ⁅a,(TensorProduct.lift (LieModule.toEnd ℂ R R).toLinearMap) z⁆
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul r s =>
        rw [TensorProduct.LieModule.lie_tmul_right,map_add]
        exact (hder a r s).symm
    | add z w hz hw => simp only [lie_add,map_add,hz,hw]

@[simp] theorem lieEquivariantBracket_tmul
    (hder : ∀ (a : L) (r s : R), ⁅a,⁅r,s⁆⁆ = ⁅⁅a,r⁆,s⁆ + ⁅r,⁅a,s⁆⁆) (r s : R) :
    lieEquivariantBracket hder (r ⊗ₜ[ℂ] s) = ⁅r,s⁆ := rfl

def bracketAction
    (hder : ∀ (a : L) (r s : R), ⁅a,⁅r,s⁆⁆ = ⁅⁅a,r⁆,s⁆ + ⁅r,⁅a,s⁆⁆)
    (A : (R ⊗[ℂ] X) →ₗ⁅ℂ,L⁆ X) : (R ⊗[ℂ] (R ⊗[ℂ] X)) →ₗ⁅ℂ,L⁆ X :=
  A.comp ((TensorProduct.LieModule.map (lieEquivariantBracket hder)
    (LieModuleHom.id : X →ₗ⁅ℂ,L⁆ X)).comp
    (lieTensorAssoc (L := L) R R X).symm.toLieModuleHom)

@[simp] theorem bracketAction_tmul
    (hder : ∀ (a : L) (r s : R), ⁅a,⁅r,s⁆⁆ = ⁅⁅a,r⁆,s⁆ + ⁅r,⁅a,s⁆⁆)
    (A : (R ⊗[ℂ] X) →ₗ⁅ℂ,L⁆ X) (r s : R) (x : X) :
    bracketAction hder A (r ⊗ₜ[ℂ] (s ⊗ₜ[ℂ] x)) = A (⁅r,s⁆ ⊗ₜ[ℂ] x) := rfl

def iteratedAction (A : (R ⊗[ℂ] X) →ₗ⁅ℂ,L⁆ X) :
    (R ⊗[ℂ] (R ⊗[ℂ] X)) →ₗ⁅ℂ,L⁆ X :=
  A.comp (TensorProduct.LieModule.map (LieModuleHom.id : R →ₗ⁅ℂ,L⁆ R) A)

@[simp] theorem iteratedAction_tmul (A : (R ⊗[ℂ] X) →ₗ⁅ℂ,L⁆ X) (r s : R) (x : X) :
    iteratedAction A (r ⊗ₜ[ℂ] (s ⊗ₜ[ℂ] x)) = A (r ⊗ₜ[ℂ] A (s ⊗ₜ[ℂ] x)) := rfl

variable {M : Type u} [AddCommGroup M] [Module ℂ M] [Module.Finite ℂ X]
  [Module.Finite ℂ R] {e h : L} {E H : Module.End ℂ M} {ι : M →ₗ[ℂ] X}

/-- The Lie-action identity is forced by agreement on the actual source,
using uniqueness on the twice-tensored completion. -/
theorem IsRankOneCompletion.action_jacobi
    (C : IsRankOneCompletion e h E H ι)
    (hder : ∀ (a : L) (r s : R), ⁅a,⁅r,s⁆⁆ = ⁅⁅a,r⁆,s⁆ + ⁅r,⁅a,s⁆⁆)
    (ρ : (R ⊗[ℂ] M) →ₗ[ℂ] M) (A : (R ⊗[ℂ] X) →ₗ⁅ℂ,L⁆ X)
    (hA : ∀ r m, A (r ⊗ₜ[ℂ] ι m) = ι (ρ (r ⊗ₜ[ℂ] m)))
    (hρ : ∀ r s m, ρ (⁅r,s⁆ ⊗ₜ[ℂ] m) =
      ρ (r ⊗ₜ[ℂ] ρ (s ⊗ₜ[ℂ] m)) - ρ (s ⊗ₜ[ℂ] ρ (r ⊗ₜ[ℂ] m)))
    (r s : R) (x : X) :
    A (⁅r,s⁆ ⊗ₜ[ℂ] x) =
      A (r ⊗ₜ[ℂ] A (s ⊗ₜ[ℂ] x)) - A (s ⊗ₜ[ℂ] A (r ⊗ₜ[ℂ] x)) := by
  have hj : bracketAction hder A = iteratedAction A -
      (iteratedAction A).comp (lieTensorSwapFirst (L := L) R R X) := by
    apply ((C.tensor R).tensor R).hom_ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul r z =>
        induction z using TensorProduct.induction_on with
        | zero => simp
        | tmul s m =>
            change A (⁅r,s⁆ ⊗ₜ[ℂ] ι m) =
              A (r ⊗ₜ[ℂ] A (s ⊗ₜ[ℂ] ι m)) - A (s ⊗ₜ[ℂ] A (r ⊗ₜ[ℂ] ι m))
            simp only [hA]
            rw [hρ,map_sub]
        | add z w hz hw => simp only [TensorProduct.tmul_add,map_add,hz,hw]
    | add z w hz hw => simp only [map_add,hz,hw]
  exact LieModuleHom.congr_fun hj (r ⊗ₜ[ℂ] (s ⊗ₜ[ℂ] x))

end
end Schubert.RS.Representation
