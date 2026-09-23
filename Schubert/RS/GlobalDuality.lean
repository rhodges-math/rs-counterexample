import Schubert.RS.PairingSorting
import Schubert.RS.LaurentInitialCoefficient
import Schubert.RS.KeyInitialCoefficient
import Schubert.RS.OrthogonalityInduction

/-! Fu-Lascoux duality with the dominant base case proved. The theorem is
stated for an explicit module family satisfying the Joseph-Polo presentation,
Demazure character, and PBW hypotheses. -/

namespace Schubert.RS
noncomputable section
open Representation
variable {n : ℕ}

theorem dominant_pairing_of_key_support
    (hs : ∀ a : Composition n, PrefixSupported (fun i => (a i : ℤ)) (toLaurent (key a)))
    (hc : ∀ a : Composition n, (toLaurent (key a)).coeff (fun i => (a i : ℤ)) = 1)
    (u : Composition n) (hu : Antitone u) (a : Composition n) :
    keyAtomPairing (key a) (compositionMonomial u) =
      if a = (fun i => u i.rev) then 1 else 0 := by
  classical
  by_cases he : a = (fun i => u i.rev)
  · rw [if_pos he, pairing_monomial_coefficient]
    have h := prefixSupported_mul_initial (hs a) (weylFactor_prefixSupported n)
    simp only [add_zero, hc a, weylFactor_constant, mul_one] at h
    simpa only [he] using h
  · rw [if_neg he]
    by_contra hn
    exact he (dominant_pairing_index hs u hu a hn)

variable {E : Composition n → Type*}
  [∀ u, AddCommGroup (E u)] [∀ u, Module ℂ (E u)]
  [∀ u, Module (Enveloping n) (E u)] [∀ u, IsScalarTower ℂ (Enveloping n) (E u)]

/-- Operator-defined keys and atoms are dual for the constant-term pairing,
under the stated representation-theoretic hypotheses. -/
theorem keyAtom_orthogonality
    (ρ : (u : Composition n) → DiagonalTorus n →* Module.End ℂ (E u))
    (ξ : (u : Composition n) → E u)
    (hJP : ∀ u, HasJosephPoloPresentation u (ρ u) (ξ u))
    (hDCF : ∀ u, HasDemazureCharacter u (ρ u)) (hpbw : HasOrderedPBWBasis n)
    (u a : Composition n) :
    keyAtomPairing (key a) (atom u) = if a = (fun i => u i.rev) then 1 else 0 := by
  apply keyAtom_orthogonality_of_dominant
  exact dominant_pairing_of_key_support
    (fun a => key_prefixSupported a (ρ a) (ξ a) (hJP a) (hDCF a) hpbw)
    (fun a => key_initial_coefficient a (ρ a) (ξ a) (hJP a) (hDCF a) hpbw)

theorem rectangleCoefficient_atom
    (ρ : (u : Composition n) → DiagonalTorus n →* Module.End ℂ (E u))
    (ξ : (u : Composition n) → E u)
    (hJP : ∀ u, HasJosephPoloPresentation u (ρ u) (ξ u))
    (hDCF : ∀ u, HasDemazureCharacter u (ρ u)) (hpbw : HasOrderedPBWBasis n)
    (w : ℕ) (c u : Composition n) (hc : ∀ i, c i ≤ w) :
    rectangleCoefficient w c (atom u) = if u = c then 1 else 0 := by
  classical
  rw [rectangleCoefficient_eq_pairing w c hc,
    keyAtom_orthogonality ρ ξ hJP hDCF hpbw]
  have he : (fun i : Fin n => c i.rev) = (fun i : Fin n => u i.rev) ↔ u = c := by
    constructor
    · intro h
      funext i
      simpa using (congrFun h i.rev).symm
    · rintro rfl; rfl
  simp only [he]

end
end Schubert.RS
