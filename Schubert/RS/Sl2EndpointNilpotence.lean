import Schubert.RS.Sl2EndpointGeneration

namespace Schubert.RS.Representation
noncomputable section

variable {L X : Type*} [LieRing L] [LieAlgebra ℂ L]
  [AddCommGroup X] [Module ℂ X] [LieRingModule L X] [LieModule ℂ L X]
  [Module.Finite ℂ X] {h e f : L} (t : IsSl2Triple h e f) {z : X} {d : ℕ}

include t in
theorem highestVector_endpoint_e_end (hh : ⁅h,z⁆=(d:ℂ) • z) (he : ⁅e,z⁆=0) :
    primitiveStringVector e (primitiveStringVector f z d) (d+1)=0 := by
  have hηh : ⁅-h,primitiveStringVector f z d⁆=(d:ℂ) • primitiveStringVector f z d := by
    rw [neg_lie,highestVector_endpoint_h t hh he,neg_smul,neg_neg]
  exact highestVector_lowering_end t.symm hηh (highestVector_endpoint_f t hh he)

end
end Schubert.RS.Representation
