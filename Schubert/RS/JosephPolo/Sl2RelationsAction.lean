import Schubert.RS.Representation.PrimitiveStringExtension
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Tactic.FinCases

/-! Turn three operators satisfying the sl2 relations into an action of
a fixed sl2 Lie algebra. The operators may all be zero. -/

namespace Schubert.RS.Representation
noncomputable section
set_option maxHeartbeats 1600000

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L] {h e f : L} (t : IsSl2Triple h e f)

include t in
theorem sl2Triple_independent : LinearIndependent ℂ (![e,f,h] : Fin 3 → L) := by
  apply (LieAlgebra.ad ℂ L h).eigenvectors_linearIndependent' (![2,-2,0] : Fin 3 → ℂ)
  · intro j k hjk
    fin_cases j <;> fin_cases k <;> norm_num at *
  · intro j
    fin_cases j
    · refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, t.e_ne_zero⟩
      change ⁅h,e⁆=(2 : ℂ) • e
      exact t.lie_h_e_smul (R := ℂ)
    · refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, t.f_ne_zero⟩
      change ⁅h,f⁆=(-2 : ℂ) • f
      simpa only [neg_smul] using (t.lie_lie_smul_f (R := ℂ))
    · refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, t.h_ne_zero⟩
      change ⁅h,h⁆=(0 : ℂ) • h
      simp

def sl2TripleVectors : Fin 3 → t.toLieSubalgebra ℂ :=
  ![sl2RaisingElement t,sl2LoweringElement t,sl2CartanElement t]

theorem sl2TripleVectors_independent : LinearIndependent ℂ (sl2TripleVectors t) := by
  apply LinearIndependent.of_comp (t.toLieSubalgebra ℂ).toSubmodule.subtype
  have hv : (t.toLieSubalgebra ℂ).toSubmodule.subtype ∘ sl2TripleVectors t =
      (![e,f,h] : Fin 3 → L) := by
    funext j
    fin_cases j <;> rfl
  rw [hv]
  exact sl2Triple_independent t
theorem sl2TripleVectors_span :
    ⊤ ≤ Submodule.span ℂ (Set.range (sl2TripleVectors t)) := by
  intro x _
  obtain ⟨a,b,c,hx⟩ := (IsSl2Triple.mem_toLieSubalgebra_iff (R := ℂ) (t := t)).mp x.property
  have he : x=a • sl2TripleVectors t 0+b • sl2TripleVectors t 1+c • sl2TripleVectors t 2 := by
    apply Subtype.ext
    change x.val=a • e+b • f+c • h
    simpa only [t.lie_e_f] using hx
  rw [he]
  exact Submodule.add_mem _ (Submodule.add_mem _
    (Submodule.smul_mem _ a (Submodule.subset_span ⟨0,rfl⟩))
    (Submodule.smul_mem _ b (Submodule.subset_span ⟨1,rfl⟩)))
    (Submodule.smul_mem _ c (Submodule.subset_span ⟨2,rfl⟩))

def sl2TripleBasis : Module.Basis (Fin 3) ℂ (t.toLieSubalgebra ℂ) :=
  Module.Basis.mk (sl2TripleVectors_independent t) (sl2TripleVectors_span t)

theorem sl2TripleBasis_apply (j : Fin 3) : sl2TripleBasis t j=sl2TripleVectors t j :=
  Module.Basis.mk_apply _ _ _

variable {X : Type*} [AddCommGroup X] [Module ℂ X]
  (E F H : Module.End ℂ X)

def sl2ActionLinear : t.toLieSubalgebra ℂ →ₗ[ℂ] Module.End ℂ X :=
  (sl2TripleBasis t).constr ℂ ![E,F,H]

theorem sl2ActionLinear_vector (j : Fin 3) :
    sl2ActionLinear t E F H (sl2TripleVectors t j) = (![E,F,H] : Fin 3 → Module.End ℂ X) j := by
  rw [← sl2TripleBasis_apply]
  exact (sl2TripleBasis t).constr_basis ℂ _ j

theorem sl2ActionLinear_raising : sl2ActionLinear t E F H (sl2RaisingElement t)=E :=
  sl2ActionLinear_vector t E F H 0
theorem sl2ActionLinear_lowering : sl2ActionLinear t E F H (sl2LoweringElement t)=F :=
  sl2ActionLinear_vector t E F H 1
theorem sl2ActionLinear_cartan : sl2ActionLinear t E F H (sl2CartanElement t)=H :=
  sl2ActionLinear_vector t E F H 2

attribute [local instance 100] LieRing.ofAssociativeRing

def sl2ActionOfRelations (hEF : ⁅E,F⁆=H) (hHE : ⁅H,E⁆=2 • E) (hHF : ⁅H,F⁆=-(2 • F)) :
    t.toLieSubalgebra ℂ →ₗ⁅ℂ⁆ Module.End ℂ X where
  toLinearMap := sl2ActionLinear t E F H
  map_lie' {x y} := by
    change sl2ActionLinear t E F H ⁅x,y⁆ = ⁅sl2ActionLinear t E F H x,sl2ActionLinear t E F H y⁆
    have st := sl2SubalgebraTriple t
    have seH : ⁅sl2RaisingElement t,sl2CartanElement t⁆=-(2 • sl2RaisingElement t) := by
      rw [← lie_skew, st.lie_h_e_nsmul]
    have sfE : ⁅sl2LoweringElement t,sl2RaisingElement t⁆=-sl2CartanElement t := by
      rw [← lie_skew, st.lie_e_f]
    have sfH : ⁅sl2LoweringElement t,sl2CartanElement t⁆=2 • sl2LoweringElement t := by
      rw [← lie_skew, st.lie_h_f_nsmul, neg_neg]
    have tEH : ⁅E,H⁆=-(2 • E) := by rw [← lie_skew, hHE]
    have tFE : ⁅F,E⁆=-H := by rw [← lie_skew, hEF]
    have tFH : ⁅F,H⁆=2 • F := by rw [← lie_skew, hHF, neg_neg]
    have hb (j k : Fin 3) :
        sl2ActionLinear t E F H ⁅sl2TripleBasis t j,sl2TripleBasis t k⁆ =
          ⁅sl2ActionLinear t E F H (sl2TripleBasis t j),sl2ActionLinear t E F H (sl2TripleBasis t k)⁆ := by
      rw [sl2TripleBasis_apply, sl2TripleBasis_apply]
      fin_cases j <;> fin_cases k <;>
        simp [sl2TripleVectors, st.lie_e_f, st.lie_h_e_nsmul, st.lie_h_f_nsmul,
          seH, sfE, sfH, sl2ActionLinear_raising, sl2ActionLinear_lowering, sl2ActionLinear_cartan,
          hEF, hHE, hHF, tEH, tFE, tFH]
    rw [← (sl2TripleBasis t).sum_repr x, ← (sl2TripleBasis t).sum_repr y]
    simp only [sum_lie, lie_sum, smul_lie, lie_smul, map_sum, map_smul, hb]

end
end Schubert.RS.Representation



