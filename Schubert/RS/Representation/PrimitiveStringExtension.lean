import Schubert.RS.Representation.PrimitiveStringModule

namespace Schubert.RS.Representation
noncomputable section
open LieModule Module

variable {L M : Type*} [LieRing L] [LieAlgebra ℂ L]
  [AddCommGroup M] [Module ℂ M] [LieRingModule L M] [LieModule ℂ L M] [Module.Finite ℂ M]
  {h e f : L} {m : M} {d : ℕ} {t : IsSl2Triple h e f}
  (P : t.HasPrimitiveVectorWith m (d:ℂ))

def sl2RaisingElement (t : IsSl2Triple h e f) : t.toLieSubalgebra ℂ :=
  ⟨e,(IsSl2Triple.mem_toLieSubalgebra_iff (R := ℂ)).mpr ⟨1,0,0,by simp⟩⟩
def sl2LoweringElement (t : IsSl2Triple h e f) : t.toLieSubalgebra ℂ :=
  ⟨f,(IsSl2Triple.mem_toLieSubalgebra_iff (R := ℂ)).mpr ⟨0,1,0,by simp⟩⟩
def sl2CartanElement (t : IsSl2Triple h e f) : t.toLieSubalgebra ℂ :=
  ⟨h,(IsSl2Triple.mem_toLieSubalgebra_iff (R := ℂ)).mpr ⟨0,0,1,by simp [t.lie_e_f]⟩⟩

/-- The distinguished triple remains an sl₂ triple in its generated subalgebra. -/
theorem sl2SubalgebraTriple (t : IsSl2Triple h e f) :
    IsSl2Triple (sl2CartanElement t) (sl2RaisingElement t) (sl2LoweringElement t) where
  h_ne_zero := by
    intro hz
    exact t.h_ne_zero (congrArg Subtype.val hz)
  lie_e_f := Subtype.ext t.lie_e_f
  lie_h_e_nsmul := Subtype.ext t.lie_h_e_nsmul
  lie_h_f_nsmul := Subtype.ext t.lie_h_f_nsmul
theorem primitiveStringBasis_h (k : Fin (d+1)) :
    ⁅sl2CartanElement t,primitiveStringBasis P k⁆ =
      ((d:ℂ)-2*k.val) • primitiveStringBasis P k := by
  apply Subtype.ext
  change ⁅h,(primitiveStringBasis P k).val⁆ = _
  simp only [LieSubmodule.coe_smul,primitiveStringBasis_val]
  exact highestVector_lowering_h t P.lie_h P.lie_e k.val

theorem primitiveStringBasis_e_zero :
    ⁅sl2RaisingElement t,primitiveStringBasis P 0⁆ = 0 := by
  apply Subtype.ext
  change ⁅e,(primitiveStringBasis P 0).val⁆ = 0
  simpa only [primitiveStringBasis_val,Fin.val_zero,primitiveStringVector_zero] using P.lie_e

theorem primitiveStringBasis_e_succ (k : ℕ) (hk : k+1 < d+1) :
    ⁅sl2RaisingElement t,primitiveStringBasis P ⟨k+1,hk⟩⁆ =
      ((k+1)*((d:ℂ)-k)) • primitiveStringBasis P ⟨k,by omega⟩ := by
  apply Subtype.ext
  change ⁅e,(primitiveStringBasis P ⟨k+1,hk⟩).val⁆ = _
  simp only [LieSubmodule.coe_smul,primitiveStringBasis_val]
  exact highestVector_lowering_e t P.lie_h P.lie_e k

theorem primitiveStringBasis_f (k : Fin (d+1)) (hk : k.val < d) :
    ⁅sl2LoweringElement t,primitiveStringBasis P k⁆ =
      primitiveStringBasis P ⟨k.val+1,by omega⟩ := by
  apply Subtype.ext
  change ⁅f,(primitiveStringBasis P k).val⁆ = _
  simp only [primitiveStringBasis_val]
  exact (primitiveStringVector_succ k.val).symm

theorem primitiveStringBasis_f_last :
    ⁅sl2LoweringElement t,primitiveStringBasis P (Fin.last d)⁆ = 0 := by
  apply Subtype.ext
  change ⁅f,(primitiveStringBasis P (Fin.last d)).val⁆ = 0
  rw [primitiveStringBasis_val,← primitiveStringVector_succ]
  exact highestVector_lowering_end t P.lie_h P.lie_e

variable {N : Type*} [AddCommGroup N] [Module ℂ N]
  [LieRingModule (t.toLieSubalgebra ℂ) N] [LieModule ℂ (t.toLieSubalgebra ℂ) N]
/-- Extension sends each actual lowering vector to the corresponding lowering
vector of the chosen target highest vector. -/
def primitiveStringExtension (z : N) : primitiveStringModule P →ₗ[ℂ] N :=
  (primitiveStringBasis P).constr ℂ (fun k => primitiveStringVector (sl2LoweringElement t) z k.val)

theorem primitiveStringExtension_basis (z : N) (k : Fin (d+1)) :
    primitiveStringExtension P z (primitiveStringBasis P k) = primitiveStringVector (sl2LoweringElement t) z k.val :=
  (primitiveStringBasis P).constr_basis ℂ _ k

theorem primitiveStringExtension_h (z : N) (hz : ⁅sl2CartanElement t,z⁆ = (d:ℂ) • z) (he : ⁅sl2RaisingElement t,z⁆ = 0)
    (x : primitiveStringModule P) :
    primitiveStringExtension P z ⁅sl2CartanElement t,x⁆ = ⁅sl2CartanElement t,primitiveStringExtension P z x⁆ := by
  have hh : (primitiveStringExtension P z).comp
      (LieModule.toEnd ℂ (t.toLieSubalgebra ℂ) (primitiveStringModule P) (sl2CartanElement t)) =
      (LieModule.toEnd ℂ (t.toLieSubalgebra ℂ) N (sl2CartanElement t)).comp (primitiveStringExtension P z) := by
    apply (primitiveStringBasis P).ext
    intro k
    change primitiveStringExtension P z ⁅sl2CartanElement t,primitiveStringBasis P k⁆ = _
    rw [primitiveStringBasis_h,map_smul,primitiveStringExtension_basis]
    change _ = ⁅sl2CartanElement t,primitiveStringExtension P z (primitiveStringBasis P k)⁆
    rw [primitiveStringExtension_basis]
    exact (highestVector_lowering_h (sl2SubalgebraTriple t) hz he k.val).symm
  exact LinearMap.congr_fun hh x

theorem primitiveStringExtension_e (z : N) (hz : ⁅sl2CartanElement t,z⁆ = (d:ℂ) • z) (he : ⁅sl2RaisingElement t,z⁆ = 0)
    (x : primitiveStringModule P) :
    primitiveStringExtension P z ⁅sl2RaisingElement t,x⁆ = ⁅sl2RaisingElement t,primitiveStringExtension P z x⁆ := by
  have hh : (primitiveStringExtension P z).comp
      (LieModule.toEnd ℂ (t.toLieSubalgebra ℂ) (primitiveStringModule P) (sl2RaisingElement t)) =
      (LieModule.toEnd ℂ (t.toLieSubalgebra ℂ) N (sl2RaisingElement t)).comp (primitiveStringExtension P z) := by
    apply (primitiveStringBasis P).ext
    rintro ⟨k,hk⟩
    change primitiveStringExtension P z ⁅sl2RaisingElement t,primitiveStringBasis P ⟨k,hk⟩⁆ = _
    cases k with
    | zero =>
        have hk0 : (⟨0,hk⟩ : Fin (d+1))=0 := Fin.ext (by simp)
        rw [hk0]
        rw [primitiveStringBasis_e_zero,map_zero]
        change 0 = ⁅sl2RaisingElement t,primitiveStringExtension P z (primitiveStringBasis P 0)⁆
        rw [primitiveStringExtension_basis,Fin.val_zero,primitiveStringVector_zero,he]
    | succ k =>
        rw [primitiveStringBasis_e_succ,map_smul,primitiveStringExtension_basis]
        change _ = ⁅sl2RaisingElement t,primitiveStringExtension P z (primitiveStringBasis P ⟨k+1,hk⟩)⁆
        rw [primitiveStringExtension_basis,highestVector_lowering_e (sl2SubalgebraTriple t) hz he]
  exact LinearMap.congr_fun hh x

theorem primitiveStringExtension_f [Module.Finite ℂ N]
    (z : N) (hz : ⁅sl2CartanElement t,z⁆ = (d:ℂ) • z) (he : ⁅sl2RaisingElement t,z⁆ = 0)
    (x : primitiveStringModule P) :
    primitiveStringExtension P z ⁅sl2LoweringElement t,x⁆ = ⁅sl2LoweringElement t,primitiveStringExtension P z x⁆ := by
  have hh : (primitiveStringExtension P z).comp
      (LieModule.toEnd ℂ (t.toLieSubalgebra ℂ) (primitiveStringModule P) (sl2LoweringElement t)) =
      (LieModule.toEnd ℂ (t.toLieSubalgebra ℂ) N (sl2LoweringElement t)).comp (primitiveStringExtension P z) := by
    apply (primitiveStringBasis P).ext
    intro k
    change primitiveStringExtension P z ⁅sl2LoweringElement t,primitiveStringBasis P k⁆ = _
    by_cases hk : k.val < d
    · rw [primitiveStringBasis_f P k hk,primitiveStringExtension_basis]
      change _ = ⁅sl2LoweringElement t,primitiveStringExtension P z (primitiveStringBasis P k)⁆
      rw [primitiveStringExtension_basis,primitiveStringVector_succ]
    · have hlast : k=Fin.last d := Fin.ext (by change k.val=d; omega)
      subst k
      rw [primitiveStringBasis_f_last,map_zero]
      change 0 = ⁅sl2LoweringElement t,primitiveStringExtension P z (primitiveStringBasis P (Fin.last d))⁆
      rw [primitiveStringExtension_basis,← primitiveStringVector_succ]
      exact (highestVector_lowering_end (sl2SubalgebraTriple t) hz he).symm
  exact LinearMap.congr_fun hh x

/-- The actual universal extension is a Lie-module homomorphism for the
whole subalgebra generated by the sl₂ triple, not just a linear map. -/
def primitiveStringLift [Module.Finite ℂ N]
    (z : N) (hz : ⁅sl2CartanElement t,z⁆ = (d:ℂ) • z) (he : ⁅sl2RaisingElement t,z⁆ = 0) :
    primitiveStringModule P →ₗ⁅ℂ,t.toLieSubalgebra ℂ⁆ N where
  toLinearMap := primitiveStringExtension P z
  map_lie' := by
    intro a x
    change primitiveStringExtension P z ⁅a,x⁆ = ⁅a,primitiveStringExtension P z x⁆
    obtain ⟨u,v,w,ha⟩ := (IsSl2Triple.mem_toLieSubalgebra_iff (R := ℂ) (t := t)).mp a.property
    have has : a = u • sl2RaisingElement t + v • sl2LoweringElement t + w • sl2CartanElement t := by
      apply Subtype.ext
      change (a:L)=u • e + v • f + w • h
      simpa only [t.lie_e_f] using ha
    rw [has]
    simp only [add_lie,smul_lie,map_add,map_smul,
      primitiveStringExtension_e P z hz he,primitiveStringExtension_f P z hz he,
      primitiveStringExtension_h P z hz he]

end
end Schubert.RS.Representation

