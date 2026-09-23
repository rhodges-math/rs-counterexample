import Schubert.RS.Family.RectangleFormula
import Schubert.RS.AtomCoefficients

/-! The family atom-coefficient formula from the Joseph-Polo presentation,
Demazure character formula, and ordered PBW basis. -/

namespace Schubert.RS.Family
noncomputable section
open Representation

theorem atomCoefficient_eq_of_representation (P : Parameters)
    (hJP : ∀ u : Composition P.rank,CompositionFlagJosephPolo u)
    (hDCF : ∀ u : Composition P.rank,CompositionFlagDemazureCharacter u) (hpbw : HasOrderedPBWBasis P.rank) :
    atomCoefficient (key (a P)*key (b P)) (c P)=
      2*(Nat.choose P.m (P.p-1) : ℤ)*Nat.choose P.m P.p-
        P.m*(Nat.choose (P.m-1) (P.p-1) : ℤ)^2 := by
  rw [atomCoefficient_eq_rectangleCoefficient hJP hDCF hpbw P.rectangle (c P) (c_le P)]
  exact family_rectangle_coefficient P hJP hDCF hpbw

theorem atomCoefficient_factorization_of_representation (P : Parameters)
    (hJP : ∀ u : Composition P.rank,CompositionFlagJosephPolo u)
    (hDCF : ∀ u : Composition P.rank,CompositionFlagDemazureCharacter u) (hpbw : HasOrderedPBWBasis P.rank) :
    (atomCoefficient (key (a P)*key (b P)) (c P) : ℚ)=
      (P.m : ℚ)/((P.p : ℚ)*P.q)*(Nat.choose (P.m-1) (P.p-1) : ℚ)^2*
        (2-((P.p : ℚ)-2)*((P.q : ℚ)-2)) := by
  rw [atomCoefficient_eq_rectangleCoefficient hJP hDCF hpbw P.rectangle (c P) (c_le P)]
  exact family_coefficient_factorization P hJP hDCF hpbw

theorem atomCoefficient_neg_iff_of_representation (P : Parameters)
    (hJP : ∀ u : Composition P.rank,CompositionFlagJosephPolo u)
    (hDCF : ∀ u : Composition P.rank,CompositionFlagDemazureCharacter u) (hpbw : HasOrderedPBWBasis P.rank) :
    atomCoefficient (key (a P)*key (b P)) (c P)<0 ↔ 2<((P.p : ℤ)-2)*((P.q : ℤ)-2) := by
  rw [atomCoefficient_eq_rectangleCoefficient hJP hDCF hpbw P.rectangle (c P) (c_le P)]
  exact family_coefficient_negative_iff P hJP hDCF hpbw

/-- The unique integral atom expansion, including the distinguished coefficient. -/
theorem existsUnique_atomExpansion_of_representation (P : Parameters)
    (hJP : ∀ u : Composition P.rank,CompositionFlagJosephPolo u)
    (hDCF : ∀ u : Composition P.rank,CompositionFlagDemazureCharacter u) (hpbw : HasOrderedPBWBasis P.rank) :
    ∃! t : Composition P.rank →₀ ℤ,
      key (a P)*key (b P)=t.sum (fun u z => z • atom u) ∧ t (c P)=coefficientValue P.m P.p := by
  obtain ⟨t,ht,hunique⟩:=existsUnique_integral_atom_expansion hJP hDCF hpbw (key (a P)*key (b P))
  exact ⟨t,⟨ht,family_atom_coefficient P hJP hDCF hpbw t ht⟩,fun s hs => hunique s hs.1⟩

end
end Schubert.RS.Family
