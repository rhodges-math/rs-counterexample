import Schubert.RS.Sl2FullPrimitive
import Schubert.RS.Representation.RankOneCompletion

namespace Schubert.RS.Representation
noncomputable section
open LieModule Module

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L]
  {h e f : L} (t : IsSl2Triple h e f)
  {M : Type} [AddCommGroup M] [Module ℂ M]
  [LieRingModule (t.toLieSubalgebra ℂ) M] [LieModule ℂ (t.toLieSubalgebra ℂ) M]
  [Module.Finite ℂ M] {m : M} {d : ℕ}
  (P : (sl2SubalgebraTriple t).HasPrimitiveVectorWith m (d:ℂ))
  {N : Type} [AddCommGroup N] [Module ℂ N]
  [LieRingModule (t.toLieSubalgebra ℂ) N] [LieModule ℂ (t.toLieSubalgebra ℂ) N]

def fullPrimitiveHomRestriction
    (Φ : fullPrimitiveModule t P →ₗ⁅ℂ,t.toLieSubalgebra ℂ⁆ N) :
    primitiveStringModule P →ₗ⁅ℂ,(sl2SubalgebraTriple t).toLieSubalgebra ℂ⁆ N where
  toLinearMap := Φ.toLinearMap
  map_lie' := by
    intro z x
    exact Φ.map_lie z.val x

theorem fullPrimitiveHom_ext
    {Φ Ψ : fullPrimitiveModule t P →ₗ⁅ℂ,t.toLieSubalgebra ℂ⁆ N}
    (hΦ : Φ (fullPrimitiveBasis t P 0)=Ψ (fullPrimitiveBasis t P 0)) : Φ=Ψ := by
  have hh : fullPrimitiveHomRestriction t P Φ=fullPrimitiveHomRestriction t P Ψ :=
    primitiveStringHom_ext P hΦ
  apply LieModuleHom.ext
  intro x
  exact congrArg (fun F => F x) hh

def fullPrimitiveBoundary : ℂ →ₗ[ℂ] fullPrimitiveModule t P :=
  LinearMap.smulRight (LinearMap.id : ℂ →ₗ[ℂ] ℂ) (fullPrimitiveBasis t P 0)

theorem fullPrimitiveBoundary_apply (c : ℂ) :
    fullPrimitiveBoundary t P c=c • fullPrimitiveBasis t P 0 := rfl

/-- Existence of the finite universal completion of a dominant weight line,
with its actual injective boundary. -/
theorem fullPrimitiveCompletion :
    IsRankOneCompletion (sl2RaisingElement t) (sl2CartanElement t)
      (0 : Module.End ℂ ℂ) ((d:ℂ) • LinearMap.id) (fullPrimitiveBoundary t P) where
  injective := by
    intro c c' hh
    exact (smul_left_injective ℂ ((fullPrimitiveBasis t P).ne_zero 0)) hh
  map_e := by
    intro c
    simp only [LinearMap.zero_apply,map_zero,fullPrimitiveBoundary_apply,lie_smul,
      fullPrimitiveBasis_e_zero,smul_zero]
  map_h := by
    intro c
    simp only [LinearMap.smul_apply,LinearMap.id_apply,fullPrimitiveBoundary_apply,
      lie_smul,fullPrimitiveBasis_h,Fin.val_zero,Nat.cast_zero,mul_zero,sub_zero,
      smul_smul,smul_eq_mul]
    rw [mul_comm]
  universal := by
    intro N _ _ _ _ _ g he hh
    have hz : ⁅sl2CartanElement t,g 1⁆=(d:ℂ) • g 1 := by
      rw [← hh,LinearMap.smul_apply,LinearMap.id_apply,map_smul]
    have hze : ⁅sl2RaisingElement t,g 1⁆=0 := by
      rw [← he,LinearMap.zero_apply,map_zero]
    refine ⟨fullPrimitiveLift t P (g 1) hz hze,?_,?_⟩
    · intro c
      rw [fullPrimitiveBoundary_apply,map_smul,fullPrimitiveLift_top,← map_smul]
      simp
    · intro Φ hΦ
      apply fullPrimitiveHom_ext t P
      rw [fullPrimitiveLift_top]
      simpa only [fullPrimitiveBoundary_apply,one_smul] using hΦ 1

end
end Schubert.RS.Representation
