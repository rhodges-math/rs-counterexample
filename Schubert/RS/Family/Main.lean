import Schubert.RS.Family.CoefficientFormulaFromPBW
import Schubert.RS.PBW.Theorem

/-! Theorem 1.1: the full counterexample family and its negativity criterion.
The Joseph-Polo presentation, Demazure character formula, and ordered PBW
basis theorem are supplied by the preceding formal proofs. -/
namespace Schubert.RS.Family
noncomputable section
open Representation

/-- Theorem 1.1: the family atom coefficient as an integer binomial expression. -/
theorem atomCoefficient_eq (P : Parameters) :
    atomCoefficient (key (a P)*key (b P)) (c P)=
      2*(Nat.choose P.m (P.p-1) : ℤ)*Nat.choose P.m P.p-
        P.m*(Nat.choose (P.m-1) (P.p-1) : ℤ)^2 :=
  atomCoefficient_eq_of_pbw P (orderedPBWBasis_exists P.rank)

/-- The factored coefficient formula, viewed in the rationals. -/
theorem atomCoefficient_factorization (P : Parameters) :
    (atomCoefficient (key (a P)*key (b P)) (c P) : ℚ)=
      (P.m : ℚ)/((P.p : ℚ)*P.q)*(Nat.choose (P.m-1) (P.p-1) : ℚ)^2*
        (2-((P.p : ℚ)-2)*((P.q : ℚ)-2)) :=
  atomCoefficient_factorization_of_pbw P (orderedPBWBasis_exists P.rank)

/-- The family coefficient is negative exactly when (p - 2)(q - 2) > 2. -/
theorem atomCoefficient_neg_iff (P : Parameters) :
    atomCoefficient (key (a P)*key (b P)) (c P)<0 ↔ 2<((P.p : ℤ)-2)*((P.q : ℤ)-2) :=
  atomCoefficient_neg_iff_of_pbw P (orderedPBWBasis_exists P.rank)

/-- The unique integral atom expansion and its distinguished coefficient. -/
theorem existsUnique_atomExpansion (P : Parameters) :
    ∃! t : Composition P.rank →₀ ℤ,
      key (a P)*key (b P)=t.sum (fun u z => z • atom u) ∧ t (c P)=coefficientValue P.m P.p :=
  existsUnique_atomExpansion_of_pbw P (orderedPBWBasis_exists P.rank)

/-- The family key product fails atom positivity in the negative range. -/
theorem not_atomPositive (P : Parameters)
    (hneg : 2<((P.p : ℤ)-2)*((P.q : ℤ)-2)) :
    ¬AtomPositive (key (a P)*key (b P)) :=
  not_atomPositive_of_pbw P (orderedPBWBasis_exists P.rank) hneg

/-- The rank-28 example has atom coefficient -350. -/
theorem rank28_atomCoefficient :
    atomCoefficient (key Counterexample.a*key Counterexample.b) Counterexample.c = -350 :=
  rank28_atomCoefficient_of_pbw (orderedPBWBasis_exists 28)

/-- The rank-28 key product is not atom positive. -/
theorem rank28_not_atomPositive :
    ¬AtomPositive (key Counterexample.a*key Counterexample.b) :=
  rank28_not_atomPositive_of_pbw (orderedPBWBasis_exists 28)

/-- The universal Reiner-Shimozono key-product positivity assertion is false. -/
theorem reiner_shimozono_false :
    ¬ (∀ n : ℕ, ∀ a b : Composition n, AtomPositive (key a * key b)) := by
  intro h
  exact rank28_not_atomPositive (h 28 Counterexample.a Counterexample.b)

end
end Schubert.RS.Family
