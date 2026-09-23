import Schubert.RS.Representation.ParabolicRadicalWeyl
import Schubert.RS.Sl2FullPrimitive

namespace Schubert.RS.Representation
noncomputable section
attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 2000000

theorem exp_of_cube_zero {X : Type*} [AddCommGroup X] [Module ℂ X] [Module ℚ X]
    (D : Module.End ℂ X) (hD : D^3=0) :
    IsNilpotent.exp D = 1+D+(1/2:ℂ) • D^2 := by
  rw [IsNilpotent.exp_eq_sum hD]
  norm_num [Finset.sum_range_succ]
  simpa using (ratCast_smul_eq ℚ ℂ (1/2) (D^2))

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L] {h e f : L} (t : IsSl2Triple h e f)

def sl2AdjointE : Module.End ℂ (t.toLieSubalgebra ℂ) :=
  LieModule.toEnd ℂ _ _ (sl2RaisingElement t)

def sl2AdjointF : Module.End ℂ (t.toLieSubalgebra ℂ) :=
  LieModule.toEnd ℂ _ _ (sl2LoweringElement t)

theorem sl2AdjointE_e : sl2AdjointE t (sl2RaisingElement t)=0 := lie_self _
theorem sl2AdjointE_f : sl2AdjointE t (sl2LoweringElement t)=sl2CartanElement t :=
  (sl2SubalgebraTriple t).lie_e_f
theorem sl2AdjointE_h : sl2AdjointE t (sl2CartanElement t)=(-2:ℂ) • sl2RaisingElement t := by
  change ⁅sl2RaisingElement t,sl2CartanElement t⁆=_
  rw [← lie_skew,(sl2SubalgebraTriple t).lie_h_e_smul ℂ]
  module

theorem sl2AdjointF_e : sl2AdjointF t (sl2RaisingElement t)=-sl2CartanElement t := by
  change ⁅sl2LoweringElement t,sl2RaisingElement t⁆=_
  rw [← lie_skew,(sl2SubalgebraTriple t).lie_e_f]
theorem sl2AdjointF_f : sl2AdjointF t (sl2LoweringElement t)=0 := lie_self _
theorem sl2AdjointF_h : sl2AdjointF t (sl2CartanElement t)=(2:ℂ) • sl2LoweringElement t := by
  change ⁅sl2LoweringElement t,sl2CartanElement t⁆=_
  rw [← lie_skew,(sl2SubalgebraTriple t).lie_h_f_nsmul,neg_neg]
  simp only [two_smul]

theorem sl2AdjointE_cube : sl2AdjointE t ^ 3 = 0 := by
  apply LinearMap.ext
  intro z
  obtain ⟨u,v,w,rfl⟩ := sl2_element_expansion t z
  change sl2AdjointE t (sl2AdjointE t (sl2AdjointE t
    (u • sl2RaisingElement t+v • sl2LoweringElement t+w • sl2CartanElement t)))=0
  simp only [map_add,map_smul,sl2AdjointE_e,sl2AdjointE_f,sl2AdjointE_h,map_zero,smul_zero,add_zero,zero_add]

theorem sl2AdjointF_cube : sl2AdjointF t ^ 3 = 0 := by
  apply LinearMap.ext
  intro z
  obtain ⟨u,v,w,rfl⟩ := sl2_element_expansion t z
  change sl2AdjointF t (sl2AdjointF t (sl2AdjointF t
    (u • sl2RaisingElement t+v • sl2LoweringElement t+w • sl2CartanElement t)))=0
  simp only [map_add,map_smul,map_neg,sl2AdjointF_e,sl2AdjointF_f,sl2AdjointF_h,map_zero,
    smul_zero,neg_zero,add_zero,zero_add]

def sl2AdjointWeyl : t.toLieSubalgebra ℂ ≃ₗ[ℂ] t.toLieSubalgebra ℂ :=
  letI := complexRationalModule (t.toLieSubalgebra ℂ)
  nilpotentWeylEquiv (sl2AdjointE t) (sl2AdjointF t)
    ⟨3,sl2AdjointE_cube t⟩ ⟨3,sl2AdjointF_cube t⟩

theorem sl2AdjointWeyl_h : sl2AdjointWeyl t (sl2CartanElement t) = -sl2CartanElement t := by
  letI := complexRationalModule (t.toLieSubalgebra ℂ)
  have hn : (-sl2AdjointF t)^3=0 := by rw [neg_pow,sl2AdjointF_cube]; simp
  change IsNilpotent.exp (sl2AdjointE t)
    (IsNilpotent.exp (-sl2AdjointF t) (IsNilpotent.exp (sl2AdjointE t) (sl2CartanElement t)))=_
  rw [exp_of_cube_zero _ (sl2AdjointE_cube t),exp_of_cube_zero _ hn]
  simp only [LinearMap.add_apply,Module.End.one_apply,LinearMap.smul_apply,LinearMap.neg_apply,
    pow_two,Module.End.mul_apply,map_add,map_smul,map_neg,
    sl2AdjointE_e,sl2AdjointE_f,sl2AdjointE_h,sl2AdjointF_e,sl2AdjointF_f,sl2AdjointF_h,
    map_zero,smul_zero,neg_zero,zero_add,add_zero]
  module

end
end Schubert.RS.Representation
