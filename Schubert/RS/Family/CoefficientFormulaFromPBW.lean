import Schubert.RS.Family.CoefficientFormulaFromRepresentation
import Schubert.RS.JosephPolo.GeneralTheorem

/-! The family atom-coefficient formula from an ordered PBW basis, using
the presentation and character theorems for composition flag modules. -/

namespace Schubert.RS.Family
noncomputable section
open Representation

theorem atomCoefficient_eq_of_pbw (P : Parameters) (hpbw : HasOrderedPBWBasis P.rank) :
    atomCoefficient (key (a P)*key (b P)) (c P)=
      2*(Nat.choose P.m (P.p-1) : ℤ)*Nat.choose P.m P.p-
        P.m*(Nat.choose (P.m-1) (P.p-1) : ℤ)^2 :=
  atomCoefficient_eq_of_representation P compositionFlagJosephPolo compositionFlagDemazureCharacter hpbw

theorem atomCoefficient_factorization_of_pbw (P : Parameters) (hpbw : HasOrderedPBWBasis P.rank) :
    (atomCoefficient (key (a P)*key (b P)) (c P) : ℚ)=
      (P.m : ℚ)/((P.p : ℚ)*P.q)*(Nat.choose (P.m-1) (P.p-1) : ℚ)^2*
        (2-((P.p : ℚ)-2)*((P.q : ℚ)-2)) :=
  atomCoefficient_factorization_of_representation P compositionFlagJosephPolo
    compositionFlagDemazureCharacter hpbw

theorem atomCoefficient_neg_iff_of_pbw (P : Parameters) (hpbw : HasOrderedPBWBasis P.rank) :
    atomCoefficient (key (a P)*key (b P)) (c P)<0 ↔ 2<((P.p : ℤ)-2)*((P.q : ℤ)-2) :=
  atomCoefficient_neg_iff_of_representation P compositionFlagJosephPolo
    compositionFlagDemazureCharacter hpbw

theorem existsUnique_atomExpansion_of_pbw (P : Parameters) (hpbw : HasOrderedPBWBasis P.rank) :
    ∃! t : Composition P.rank →₀ ℤ,
      key (a P)*key (b P)=t.sum (fun u z => z • atom u) ∧ t (c P)=coefficientValue P.m P.p :=
  existsUnique_atomExpansion_of_representation P compositionFlagJosephPolo
    compositionFlagDemazureCharacter hpbw

theorem not_atomPositive_of_pbw (P : Parameters) (hpbw : HasOrderedPBWBasis P.rank)
    (hneg : 2<((P.p : ℤ)-2)*((P.q : ℤ)-2)) :
    ¬AtomPositive (key (a P)*key (b P)) :=
  not_atomPositive_of_representation P compositionFlagJosephPolo
    compositionFlagDemazureCharacter hpbw hneg

theorem rank28_atomCoefficient_of_pbw (hpbw : HasOrderedPBWBasis 28) :
    atomCoefficient (key Counterexample.a*key Counterexample.b) Counterexample.c = -350 := by
  have h := atomCoefficient_eq_of_pbw rank28Parameters hpbw
  rw [rank28_a,rank28_b,rank28_c] at h
  norm_num [rank28Parameters,Parameters.m,Nat.choose] at h
  exact h

theorem rank28_not_atomPositive_of_pbw (hpbw : HasOrderedPBWBasis 28) :
    ¬AtomPositive (key Counterexample.a*key Counterexample.b) := by
  have h := not_atomPositive_of_pbw rank28Parameters hpbw (by decide)
  rw [rank28_a,rank28_b] at h
  exact h

end
end Schubert.RS.Family
