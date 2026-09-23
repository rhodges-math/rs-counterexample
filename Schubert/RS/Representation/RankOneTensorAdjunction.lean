import Schubert.RS.Representation.RankOneCompletion
import Mathlib.RingTheory.Flat.Basic

namespace Schubert.RS.Representation
noncomputable section
universe u v
open LieModule Module TensorProduct

variable {L : Type v} [LieRing L] [LieAlgebra ℂ L]
  {R M X N : Type u} [AddCommGroup R] [Module ℂ R]
  [LieRingModule L R] [LieModule ℂ L R]
  [AddCommGroup M] [Module ℂ M]
  [AddCommGroup X] [Module ℂ X] [LieRingModule L X] [LieModule ℂ L X]
  [AddCommGroup N] [Module ℂ N] [LieRingModule L N] [LieModule ℂ L N]

/-- The actual tensor-product operator with one Lie-module factor and one
factor carrying only a specified endomorphism. -/
def tensorBorelOperator (x : L) (D : Module.End ℂ M) : Module.End ℂ (R ⊗[ℂ] M) :=
  (LieModule.toEnd ℂ L R x).rTensor M + D.lTensor R

theorem tensorBorelOperator_tmul (x : L) (D : Module.End ℂ M) (r : R) (m : M) :
    tensorBorelOperator x D (r ⊗ₜ[ℂ] m) = ⁅x,r⁆ ⊗ₜ[ℂ] m + r ⊗ₜ[ℂ] D m := by
  simp [tensorBorelOperator]

def tensorFlipCurry (g : (R ⊗[ℂ] M) →ₗ[ℂ] N) : M →ₗ[ℂ] R →ₗ[ℂ] N :=
  (TensorProduct.curry g).flip

@[simp] theorem tensorFlipCurry_apply (g : (R ⊗[ℂ] M) →ₗ[ℂ] N) (m : M) (r : R) :
    tensorFlipCurry g m r = g (r ⊗ₜ[ℂ] m) := rfl

theorem tensorFlipCurry_intertwines (x : L) (D : Module.End ℂ M)
    (g : (R ⊗[ℂ] M) →ₗ[ℂ] N)
    (hg : ∀ z, g (tensorBorelOperator x D z) = ⁅x,g z⁆) (m : M) :
    tensorFlipCurry g (D m) = ⁅x,tensorFlipCurry g m⁆ := by
  apply LinearMap.ext
  intro r
  simp only [tensorFlipCurry_apply,LieHom.lie_apply]
  have hh := hg (r ⊗ₜ[ℂ] m)
  rw [tensorBorelOperator_tmul,map_add] at hh
  rw [← hh]
  abel

theorem tensorBoundary_intertwines (x : L) (D : Module.End ℂ M) (ι : M →ₗ[ℂ] X)
    (hι : ∀ m, ι (D m) = ⁅x,ι m⁆) (z : R ⊗[ℂ] M) :
    ι.lTensor R (tensorBorelOperator x D z) = ⁅x,ι.lTensor R z⁆ := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r m =>
      simp only [tensorBorelOperator_tmul,map_add,LinearMap.lTensor_tmul,
        TensorProduct.LieModule.lie_tmul_right,hι]
  | add z w hz hw => simp only [map_add,lie_add,hz,hw]

/-- Currying is equivariant for the actual internal Hom Lie action. -/
def tensorFlipCurryLie (Φ : (R ⊗[ℂ] X) →ₗ⁅ℂ,L⁆ N) : X →ₗ⁅ℂ,L⁆ R →ₗ[ℂ] N where
  toLinearMap := tensorFlipCurry Φ.toLinearMap
  map_lie' := by
    intro a x
    apply LinearMap.ext
    intro r
    change Φ (r ⊗ₜ[ℂ] ⁅a,x⁆) = ⁅a,Φ (r ⊗ₜ[ℂ] x)⁆ - Φ (⁅a,r⁆ ⊗ₜ[ℂ] x)
    have hh := Φ.map_lie a (r ⊗ₜ[ℂ] x)
    rw [TensorProduct.LieModule.lie_tmul_right,map_add] at hh
    rw [← hh]
    abel

@[simp] theorem tensorFlipCurryLie_apply (Φ : (R ⊗[ℂ] X) →ₗ⁅ℂ,L⁆ N) (x : X) (r : R) :
    tensorFlipCurryLie Φ x r = Φ (r ⊗ₜ[ℂ] x) := rfl

/-- The inverse tensor-Hom construction, with the integrable factor first. -/
def tensorFlipLiftLie (g : X →ₗ⁅ℂ,L⁆ R →ₗ[ℂ] N) : (R ⊗[ℂ] X) →ₗ⁅ℂ,L⁆ N where
  toLinearMap := TensorProduct.lift g.toLinearMap.flip
  map_lie' := by
    intro a z
    change (TensorProduct.lift g.toLinearMap.flip) ⁅a,z⁆ =
      ⁅a,(TensorProduct.lift g.toLinearMap.flip) z⁆
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul r x =>
        rw [TensorProduct.LieModule.lie_tmul_right,map_add]
        change g x ⁅a,r⁆ + g ⁅a,x⁆ r = ⁅a,g x r⁆
        rw [g.map_lie₂]
        exact add_comm _ _
    | add z w hz hw => simp only [lie_add,map_add,hz,hw]

@[simp] theorem tensorFlipLiftLie_tmul (g : X →ₗ⁅ℂ,L⁆ R →ₗ[ℂ] N) (r : R) (x : X) :
    tensorFlipLiftLie g (r ⊗ₜ[ℂ] x) = g x r := rfl

theorem tensorFlipCurryLie_injective :
    Function.Injective (tensorFlipCurryLie : ((R ⊗[ℂ] X) →ₗ⁅ℂ,L⁆ N) → _) := by
  intro Φ Ψ h
  apply LieModuleHom.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
      exact congrArg (fun g : X →ₗ⁅ℂ,L⁆ R →ₗ[ℂ] N => g x r) h
  | add z w hz hw => simp only [map_add,hz,hw]

end
end Schubert.RS.Representation
