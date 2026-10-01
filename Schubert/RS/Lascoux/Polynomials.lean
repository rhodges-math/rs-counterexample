import Schubert.RS.Lascoux.Operators
import Schubert.RS.Keys

/-!
# Lascoux polynomials and Lascoux atoms

Operator definitions (Lascoux; Monical; Monical–Pechenik–Searles, arXiv:1806.03802,
Remark 4.24), with the same leftmost-ascent sorting convention as `key` and `atom`:
* `𝔏_a = x^a` and `𝔏̄_a = x^a` when `a` has no strict ascent (is weakly decreasing);
* `𝔏_a = πᵢ^{(β)} 𝔏_{sᵢ a}` and `𝔏̄_a = π̄ᵢ^{(β)} 𝔏̄_{sᵢ a}` at the leftmost strict ascent
  `aᵢ < a_{i+1}`.

At `β = 0` they specialize to key polynomials and Demazure atoms
(`betaZero_lascoux`, `betaZero_lascouxAtom`).
-/

namespace Schubert.RS

open FinPermutation

noncomputable section

variable {n : ℕ}

/-- The Lascoux polynomial `𝔏_a`, by the key recursion at the leftmost strict ascent. -/
def lascoux (a : Composition n) : BetaPolynomial n :=
  if h : (ascentSet a).Nonempty then
    betaIsobaric (firstAscent a h) (lascoux (swapComposition a (firstAscent a h)))
  else _root_.Polynomial.C (compositionMonomial a)
termination_by sortingMeasure a
decreasing_by exact sortingMeasure_firstAscent a h

/-- The Lascoux atom `𝔏̄_a`, with the same sorting convention as `lascoux`. -/
def lascouxAtom (a : Composition n) : BetaPolynomial n :=
  if h : (ascentSet a).Nonempty then
    betaAtomOperator (firstAscent a h) (lascouxAtom (swapComposition a (firstAscent a h)))
  else _root_.Polynomial.C (compositionMonomial a)
termination_by sortingMeasure a
decreasing_by exact sortingMeasure_firstAscent a h

theorem lascoux_ascent (a : Composition n) (h : (ascentSet a).Nonempty) :
    lascoux a = betaIsobaric (firstAscent a h) (lascoux (swapComposition a (firstAscent a h))) := by
  rw [lascoux, dite_eq_left h]

theorem lascouxAtom_ascent (a : Composition n) (h : (ascentSet a).Nonempty) :
    lascouxAtom a =
      betaAtomOperator (firstAscent a h) (lascouxAtom (swapComposition a (firstAscent a h))) := by
  rw [lascouxAtom, dite_eq_left h]

theorem lascoux_of_no_ascent (a : Composition n) (h : ¬(ascentSet a).Nonempty) :
    lascoux a = _root_.Polynomial.C (compositionMonomial a) := by
  rw [lascoux, dite_eq_right h]

theorem lascouxAtom_of_no_ascent (a : Composition n) (h : ¬(ascentSet a).Nonempty) :
    lascouxAtom a = _root_.Polynomial.C (compositionMonomial a) := by
  rw [lascouxAtom, dite_eq_right h]

theorem lascoux_of_antitone (a : Composition n) (h : Antitone a) :
    lascoux a = _root_.Polynomial.C (compositionMonomial a) :=
  lascoux_of_no_ascent a (no_ascent_of_antitone a h)

theorem lascouxAtom_of_antitone (a : Composition n) (h : Antitone a) :
    lascouxAtom a = _root_.Polynomial.C (compositionMonomial a) :=
  lascouxAtom_of_no_ascent a (no_ascent_of_antitone a h)

/-- At `β = 0` Lascoux polynomials specialize to key polynomials. -/
theorem betaZero_lascoux (a : Composition n) : betaZero (lascoux a) = key a := by
  by_cases h : (ascentSet a).Nonempty
  · rw [lascoux_ascent a h, key_ascent a h, betaZero_betaIsobaric,
      betaZero_lascoux (swapComposition a (firstAscent a h))]
  · rw [lascoux_of_no_ascent a h, key_of_no_ascent a h, betaZero_C]
termination_by sortingMeasure a
decreasing_by exact sortingMeasure_firstAscent a h

/-- At `β = 0` Lascoux atoms specialize to Demazure atoms. -/
theorem betaZero_lascouxAtom (a : Composition n) : betaZero (lascouxAtom a) = atom a := by
  by_cases h : (ascentSet a).Nonempty
  · rw [lascouxAtom_ascent a h, atom_ascent a h, betaZero_betaAtomOperator,
      betaZero_lascouxAtom (swapComposition a (firstAscent a h))]
  · rw [lascouxAtom_of_no_ascent a h, atom_of_no_ascent a h, betaZero_C]
termination_by sortingMeasure a
decreasing_by exact sortingMeasure_firstAscent a h

end
end Schubert.RS
