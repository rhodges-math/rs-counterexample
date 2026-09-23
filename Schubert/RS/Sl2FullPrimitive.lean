import Schubert.RS.Representation.PrimitiveStringUniversal

namespace Schubert.RS.Representation
noncomputable section
open LieModule Module

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L]
  {h e f : L} (t : IsSl2Triple h e f)

theorem sl2_element_expansion (z : t.toLieSubalgebra ℂ) :
    ∃ u v w : ℂ, z=u • sl2RaisingElement t+v • sl2LoweringElement t+w • sl2CartanElement t := by
  obtain ⟨u,v,w,hz⟩ := (IsSl2Triple.mem_toLieSubalgebra_iff (R := ℂ) (t := t)).mp z.property
  refine ⟨u,v,w,Subtype.ext ?_⟩
  change (z:L)=u • e+v • f+w • h
  simpa only [t.lie_e_f] using hz

variable {M : Type*} [AddCommGroup M] [Module ℂ M]
  [LieRingModule (t.toLieSubalgebra ℂ) M] [LieModule ℂ (t.toLieSubalgebra ℂ) M]
  [Module.Finite ℂ M] {m : M} {d : ℕ}
  (P : (sl2SubalgebraTriple t).HasPrimitiveVectorWith m (d:ℂ))

/-- The primitive span carries the full generated root algebra. This avoids
restricting later tensor constructions to an unnecessary nested subalgebra. -/
def fullPrimitiveModule : LieSubmodule ℂ (t.toLieSubalgebra ℂ) M where
  toSubmodule := primitiveStringSpan (sl2LoweringElement t) m d
  lie_mem := by
    intro z x hx
    obtain ⟨u,v,w,rfl⟩ := sl2_element_expansion t z
    rw [add_lie,add_lie,smul_lie,smul_lie,smul_lie]
    exact (primitiveStringSpan _ m d).add_mem
      ((primitiveStringSpan _ m d).add_mem
        ((primitiveStringSpan _ m d).smul_mem u (primitiveStringSpan_e P hx))
        ((primitiveStringSpan _ m d).smul_mem v (primitiveStringSpan_f P hx)))
      ((primitiveStringSpan _ m d).smul_mem w (primitiveStringSpan_h P hx))

def fullPrimitiveBasis : Basis (Fin (d+1)) ℂ (fullPrimitiveModule t P) :=
  primitiveStringBasis P

theorem fullPrimitiveBasis_val (k : Fin (d+1)) :
    (fullPrimitiveBasis t P k).val=primitiveStringVector (sl2LoweringElement t) m k.val :=
  primitiveStringBasis_val P k

theorem fullPrimitiveBasis_h (k : Fin (d+1)) :
    ⁅sl2CartanElement t,fullPrimitiveBasis t P k⁆=
      ((d:ℂ)-2*k.val) • fullPrimitiveBasis t P k :=
  primitiveStringBasis_h P k

theorem fullPrimitiveBasis_e_zero : ⁅sl2RaisingElement t,fullPrimitiveBasis t P 0⁆=0 :=
  primitiveStringBasis_e_zero P

theorem fullPrimitiveBasis_e_succ (k : ℕ) (hk : k+1<d+1) :
    ⁅sl2RaisingElement t,fullPrimitiveBasis t P ⟨k+1,hk⟩⁆=
      ((k+1)*((d:ℂ)-k)) • fullPrimitiveBasis t P ⟨k,by omega⟩ :=
  primitiveStringBasis_e_succ P k hk

variable {N : Type*} [AddCommGroup N] [Module ℂ N]
  [LieRingModule (t.toLieSubalgebra ℂ) N] [LieModule ℂ (t.toLieSubalgebra ℂ) N]
  [Module.Finite ℂ N]

def fullPrimitiveLift (z : N) (hz : ⁅sl2CartanElement t,z⁆=(d:ℂ) • z)
    (he : ⁅sl2RaisingElement t,z⁆=0) :
    fullPrimitiveModule t P →ₗ⁅ℂ,t.toLieSubalgebra ℂ⁆ N where
  toLinearMap := primitiveStringExtension P z
  map_lie' := by
    intro a x
    have ha : a∈(sl2SubalgebraTriple t).toLieSubalgebra ℂ := by
      obtain ⟨u,v,w,ha⟩ := sl2_element_expansion t a
      apply IsSl2Triple.mem_toLieSubalgebra_iff.mpr
      exact ⟨u,v,w,by simpa only [(sl2SubalgebraTriple t).lie_e_f] using ha⟩
    exact (primitiveStringLift P z hz he).map_lie ⟨a,ha⟩ x

theorem fullPrimitiveLift_top (z : N) (hz : ⁅sl2CartanElement t,z⁆=(d:ℂ) • z)
    (he : ⁅sl2RaisingElement t,z⁆=0) :
    fullPrimitiveLift t P z hz he (fullPrimitiveBasis t P 0)=z :=
  primitiveStringLift_top P z hz he

end
end Schubert.RS.Representation
