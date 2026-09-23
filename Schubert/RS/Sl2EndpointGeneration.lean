import Schubert.RS.Representation.PrimitiveStringModule

namespace Schubert.RS.Representation
noncomputable section

variable {L X : Type*} [LieRing L] [LieAlgebra ℂ L]
  [AddCommGroup X] [Module ℂ X] [LieRingModule L X] [LieModule ℂ L X]
  {h e f : L} (t : IsSl2Triple h e f) {z : X} {d : ℕ}

include t

/-- Every point of a highest-weight string can be recovered from its
lowest endpoint using raising and nonzero scalar division. -/
theorem highestVector_mem_of_endpoint (hh : ⁅h,z⁆=(d:ℂ) • z) (he : ⁅e,z⁆=0)
    (Y : Submodule ℂ X) (hY : ∀ x, x∈Y → ⁅e,x⁆∈Y)
    (hend : primitiveStringVector f z d∈Y) : z∈Y := by
  have hstep (k : ℕ) (hk : k<d)
      (hnext : primitiveStringVector f z (k+1)∈Y) : primitiveStringVector f z k∈Y := by
    have hh' := hY _ hnext
    rw [highestVector_lowering_e t hh he] at hh'
    apply (Y.smul_mem_iff _).mp hh'
    apply mul_ne_zero
    · exact_mod_cast (show k+1≠0 by omega)
    · apply sub_ne_zero.mpr
      intro hc
      have hd : d=k := by exact_mod_cast hc
      omega
  have h0 : primitiveStringVector f z 0∈Y :=
    Nat.decreasingInduction (motive := fun k _ => primitiveStringVector f z k∈Y)
      hstep hend (Nat.zero_le d)
  exact h0

theorem highestVector_endpoint_h (hh : ⁅h,z⁆=(d:ℂ) • z) (he : ⁅e,z⁆=0) :
    ⁅h,primitiveStringVector f z d⁆=-(d:ℂ) • primitiveStringVector f z d := by
  rw [highestVector_lowering_h t hh he]
  congr 1
  ring

theorem highestVector_endpoint_f [Module.Finite ℂ X]
    (hh : ⁅h,z⁆=(d:ℂ) • z) (he : ⁅e,z⁆=0) :
    ⁅f,primitiveStringVector f z d⁆=0 := by
  rw [← primitiveStringVector_succ]
  exact highestVector_lowering_end t hh he

end
end Schubert.RS.Representation
