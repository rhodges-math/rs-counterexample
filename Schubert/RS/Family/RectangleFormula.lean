import Schubert.RS.Family.SourceProducts
import Schubert.RS.Family.PaperSlots

/-! The general p,q,K coefficient formula, following the manuscript's
extraction method under explicit Joseph-Polo, Demazure character, and PBW
hypotheses. Integral atom-expansion existence is established separately. -/

namespace Schubert.RS.Family
noncomputable section
open Representation

theorem family_rectangle_eq_hall_coefficient (P : Parameters)
    (hJP : ∀ u : Composition P.rank,CompositionFlagJosephPolo u)
    (hDCF : ∀ u : Composition P.rank,CompositionFlagDemazureCharacter u) (hpbw : HasOrderedPBWBasis P.rank) :
    rectangleCoefficient P.rectangle (c P) (key (a P)*key (b P))=
      (targetNumerator P.m*hallPolynomial (hallHeights P.m_pos P.p) slotVariable*
        hallPolynomial (hallHeights P.m_pos P.q) slotVariable).coeff (fun _ => 1) := by
  rw [family_rectangle_eq_finite_laurent P hJP hDCF hpbw (2*P.m) (hall_cutoff_bounds P).1]
  rw [← nestedLaurent_residual_coefficient,nested_finite_root_product]
  rw [double_source_extraction (hallHeights P.m_pos P.p) (hallHeights_monotone P.m_pos P.p)
    (hallHeights P.m_pos P.q) (hallHeights_monotone P.m_pos P.q)
    slotVariable (targetNumerator P.m) (2*P.m) (hall_cutoff_bounds P).2.1 (hall_cutoff_bounds P).2.2]

/-- After Hall extraction, the family's source polynomials and target factors
are exactly the forward-slot expression in the paper. -/
theorem family_rectangle_eq_paper_coefficient (P : Parameters)
    (hJP : ∀ u : Composition P.rank,CompositionFlagJosephPolo u)
    (hDCF : ∀ u : Composition P.rank,CompositionFlagDemazureCharacter u) (hpbw : HasOrderedPBWBasis P.rank) :
    rectangleCoefficient P.rectangle (c P) (key (a P)*key (b P)) =
      (paperSourcePolynomial P.m P.p * paperSourcePolynomial P.m P.q *
        paperTargetNumerator Fin.revPerm).coeff (fun _ => 1) := by
  rw [family_rectangle_eq_hall_coefficient P hJP hDCF hpbw,
    hall_coefficient_eq_paper P.m_pos P.p_pos P.q_pos]

/-- The full formula, obtained by the paper's direct marked-pair count. -/
theorem family_rectangle_coefficient (P : Parameters)
    (hJP : ∀ u : Composition P.rank,CompositionFlagJosephPolo u)
    (hDCF : ∀ u : Composition P.rank,CompositionFlagDemazureCharacter u) (hpbw : HasOrderedPBWBasis P.rank) :
    rectangleCoefficient P.rectangle (c P) (key (a P)*key (b P))=
      2*(Nat.choose P.m (P.p-1) : ℤ)*Nat.choose P.m P.p-
        P.m*(Nat.choose (P.m-1) (P.p-1) : ℤ)^2 := by
  rw [family_rectangle_eq_paper_coefficient P hJP hDCF hpbw]
  exact paper_two_source_count P.p_pos P.q_pos P.pq_eq Fin.revPerm

/-- In every integral atom expansion the distinguished coefficient is the
paper's stated binomial difference, for every allowed parameter choice. -/
theorem family_atom_coefficient (P : Parameters)
    (hJP : ∀ u : Composition P.rank,CompositionFlagJosephPolo u)
    (hDCF : ∀ u : Composition P.rank,CompositionFlagDemazureCharacter u) (hpbw : HasOrderedPBWBasis P.rank)
    (t : Composition P.rank →₀ ℤ)
    (ht : key (a P)*key (b P)=t.sum (fun u z => z • atom u)) :
    t (c P)=coefficientValue P.m P.p := by
  rw [← rectangleCoefficient_expansion compositionFlagTorus compositionFlagGenerator
    hJP hDCF hpbw P.rectangle (c P) (c_le P) t,← ht,
    family_rectangle_coefficient P hJP hDCF hpbw]
  rfl

theorem family_coefficient_factorization (P : Parameters)
    (hJP : ∀ u : Composition P.rank,CompositionFlagJosephPolo u)
    (hDCF : ∀ u : Composition P.rank,CompositionFlagDemazureCharacter u) (hpbw : HasOrderedPBWBasis P.rank) :
    (rectangleCoefficient P.rectangle (c P) (key (a P)*key (b P)) : ℚ)=
      (P.m : ℚ)/((P.p : ℚ)*P.q)*(Nat.choose (P.m-1) (P.p-1) : ℚ)^2*
        (2-((P.p : ℚ)-2)*((P.q : ℚ)-2)) := by
  rw [family_rectangle_coefficient P hJP hDCF hpbw]
  exact coefficientValue_factorization P.p_pos P.q_pos P.pq_eq

theorem family_coefficient_negative_iff (P : Parameters)
    (hJP : ∀ u : Composition P.rank,CompositionFlagJosephPolo u)
    (hDCF : ∀ u : Composition P.rank,CompositionFlagDemazureCharacter u) (hpbw : HasOrderedPBWBasis P.rank) :
    rectangleCoefficient P.rectangle (c P) (key (a P)*key (b P))<0 ↔
      2<((P.p : ℤ)-2)*((P.q : ℤ)-2) := by
  rw [family_rectangle_coefficient P hJP hDCF hpbw]
  exact coefficientValue_negative_iff P.p_pos P.q_pos P.pq_eq

/-- Every parameter value in the negative region refutes atom positivity. -/
theorem not_atomPositive_of_representation (P : Parameters)
    (hJP : ∀ u : Composition P.rank,CompositionFlagJosephPolo u)
    (hDCF : ∀ u : Composition P.rank,CompositionFlagDemazureCharacter u) (hpbw : HasOrderedPBWBasis P.rank)
    (hneg : 2<((P.p : ℤ)-2)*((P.q : ℤ)-2)) :
    ¬AtomPositive (key (a P)*key (b P)) := by
  exact not_atomPositive_of_negative_rectangle compositionFlagTorus compositionFlagGenerator
    hJP hDCF hpbw P.rectangle (c P) (c_le P) _
    ((family_coefficient_negative_iff P hJP hDCF hpbw).mpr hneg)

theorem rank28_coefficientValue : coefficientValue 7 4=-350 := by
  norm_num [coefficientValue,Nat.choose]

end
end Schubert.RS.Family
