import Schubert.RS.PBW.OrderedWords
import Mathlib.Data.Finset.Max

/-! Independence is detected by the actual polynomial representation, using
the top degree of a finite relation. No PBW, JP, or character input occurs. -/
namespace Schubert.RS.Representation
noncomputable section
open scoped BigOperators
open MvPolynomial
open Schubert.RS.PBW

def orderedMonomialTest {n : ℕ} (order : RootOrdering n) (powers : PositiveRoot n → ℕ) :
    Enveloping n →ₗ[ℂ] ℂ :=
  (evaluateIdentity n).toLinearMap.comp
    (envelopingOrbitMap (polynomialEnveloping n)
      (centerPolynomial n (monomial (wordExponent rootCoordinate (powersWord order powers)) 1)))

theorem orderedMonomialTest_diagonal {n : ℕ} (order : RootOrdering n)
    (powers : PositiveRoot n → ℕ) :
    orderedMonomialTest order powers (orderedRootMonomial order powers) ≠ 0 := by
  rw [← rootWord_powersWord]
  change evaluateIdentity n (polynomialEnveloping n (rootWord (powersWord order powers))
    (centerPolynomial n (monomial (wordExponent rootCoordinate (powersWord order powers)) 1))) ≠ 0
  have hp : monomial (wordExponent rootCoordinate (powersWord order powers)) (1 : ℂ) ∈
      jet (powersWord order powers).length := by
    simpa using monomial_mem_jet (wordExponent rootCoordinate (powersWord order powers)) (1 : ℂ)
  rw [rootWord_principal _ _ hp]
  obtain ⟨c, hc, h⟩ := partialWord_constant rootCoordinate (powersWord order powers)
  rw [h]
  simpa using hc

theorem orderedMonomialTest_off_diagonal {n : ℕ} (order : RootOrdering n)
    (a b : PositiveRoot n → ℕ) (hab : b ≠ a)
    (hdeg : (powersWord order b).length ≤ (powersWord order a).length) :
    orderedMonomialTest order a (orderedRootMonomial order b) = 0 := by
  rw [← rootWord_powersWord]
  change evaluateIdentity n (polynomialEnveloping n (rootWord (powersWord order b))
    (centerPolynomial n (monomial (wordExponent rootCoordinate (powersWord order a)) 1))) = 0
  have hp : monomial (wordExponent rootCoordinate (powersWord order a)) (1 : ℂ) ∈
      jet (powersWord order a).length := by
    simpa using monomial_mem_jet (wordExponent rootCoordinate (powersWord order a)) (1 : ℂ)
  rcases lt_or_eq_of_le hdeg with hlt | heq
  · exact rootWord_constant_zero _ _ (jet_antitone (by omega) hp)
  · rw [rootWord_principal _ _ (by simpa [heq] using hp)]
    obtain ⟨c, _, h⟩ := partialWord_constant rootCoordinate (powersWord order b)
    rw [h, coeff_monomial]
    have hne : wordExponent rootCoordinate (powersWord order a) ≠
        wordExponent rootCoordinate (powersWord order b) := by
      intro h
      exact hab ((powersWord_exponent_injective order h).symm)
    simp [hne]

theorem orderedRootMonomial_linearIndependent {n : ℕ} (order : RootOrdering n) :
    LinearIndependent ℂ (orderedRootMonomial order) := by
  classical
  apply linearIndependent_iff'.mpr
  intro s g hsum i hi
  by_contra hgi
  let support := s.filter (fun a => g a ≠ 0)
  have hnonempty : support.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨hi, hgi⟩⟩
  obtain ⟨a, ha, hmax⟩ := Finset.exists_max_image support
    (fun a => (powersWord order a).length) hnonempty
  have has : a ∈ s := (Finset.mem_filter.mp ha).1
  have hga : g a ≠ 0 := (Finset.mem_filter.mp ha).2
  have htest := congrArg (orderedMonomialTest order a) hsum
  rw [map_sum, map_zero] at htest
  simp only [map_smul, smul_eq_mul] at htest
  have hsingle : (∑ b ∈ s, g b * orderedMonomialTest order a (orderedRootMonomial order b)) =
      g a * orderedMonomialTest order a (orderedRootMonomial order a) := by
    apply Finset.sum_eq_single a
    · intro b hb hba
      by_cases hgb : g b = 0
      · simp [hgb]
      · rw [orderedMonomialTest_off_diagonal order a b hba
          (hmax b (Finset.mem_filter.mpr ⟨hb, hgb⟩)), mul_zero]
    · intro hnot; exact False.elim (hnot has)
  rw [hsingle] at htest
  exact mul_ne_zero hga (orderedMonomialTest_diagonal order a) htest

end
end Schubert.RS.Representation
