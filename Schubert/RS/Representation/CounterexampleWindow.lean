import Schubert.RS.Representation.WindowPieces

namespace Schubert.RS.Representation
noncomputable section

/-- The paper's K=8 first factor: actual finite quotient pieces agree throughout
the exact coefficient box. The degree exclusion is the checked concrete one. -/
def counterexampleWindowA (hpbw : HasOrderedPBWBasis 28) (d : RootDegree 28)
    (hd : d ≤ Counterexample.coefficientBox) :
    linearDegreePiece Counterexample.a hpbw d ≃ₗ[ℂ] jpDegreePiece Counterexample.a hpbw d :=
  windowDegreeEquiv Counterexample.a hpbw Counterexample.coefficientBox d hd
    (fun r hr => Counterexample.power_a_outside r.val.1 r.val.2 r.property hr)

def counterexampleWindowB (hpbw : HasOrderedPBWBasis 28) (d : RootDegree 28)
    (hd : d ≤ Counterexample.coefficientBox) :
    linearDegreePiece Counterexample.b hpbw d ≃ₗ[ℂ] jpDegreePiece Counterexample.b hpbw d :=
  windowDegreeEquiv Counterexample.b hpbw Counterexample.coefficientBox d hd
    (fun r hr => Counterexample.power_b_outside r.val.1 r.val.2 r.property hr)

def counterexampleWindowG (hpbw : HasOrderedPBWBasis 28) (d : RootDegree 28)
    (hd : d ≤ Counterexample.coefficientBox) :
    linearDegreePiece Counterexample.g hpbw d ≃ₗ[ℂ] jpDegreePiece Counterexample.g hpbw d :=
  windowDegreeEquiv Counterexample.g hpbw Counterexample.coefficientBox d hd
    (fun r hr => Counterexample.power_g_outside r.val.1 r.val.2 r.property hr)

end
end Schubert.RS.Representation
