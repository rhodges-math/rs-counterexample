import Schubert.RS.Family.Main
import Schubert.RS.Lascoux.Positivity

/-!
# Corollary 1.3: products of Lascoux polynomials are not Lascoux-atom positive

For the family of Theorem 1.1 in the negative range, `𝔏_a 𝔏_b` has no expansion in Lascoux
atoms with coefficients in `ℤ_{≥0}[β]`; this disproves the operator form of
Monical–Pechenik–Searles, Conjecture 4.25. Two forms are proved:
* `not_lascouxAtomPositive`: no expansion with coefficients in `ℤ_{≥0}[β]`;
* `no_lascouxExpansion_nonnegAtZero` (stronger): no expansion with coefficients in `ℤ[β]`
  whose values at `β = 0` are nonnegative.

Both follow from Theorem 1.1 by specializing at `β = 0`, where Lascoux polynomials become
key polynomials and Lascoux atoms become Demazure atoms.
-/

namespace Schubert.RS.Family
noncomputable section

theorem betaZero_lascoux_mul {n : ℕ} (a b : Composition n) :
    betaZero (lascoux a * lascoux b) = key a * key b := by
  rw [map_mul, betaZero_lascoux, betaZero_lascoux]

/-- Stronger form of Corollary 1.3: in the negative range, `𝔏_a 𝔏_b` has no Lascoux-atom
expansion whose coefficients `d_c ∈ ℤ[β]` satisfy `d_c(0) ≥ 0`. -/
theorem no_lascouxExpansion_nonnegAtZero (P : Parameters)
    (hneg : 2 < ((P.p : ℤ) - 2) * ((P.q : ℤ) - 2)) :
    ¬ ∃ d : Composition P.rank →₀ _root_.Polynomial ℤ, (∀ c, 0 ≤ (d c).coeff 0) ∧
      lascoux (a P) * lascoux (b P) =
        d.sum fun c dc => dc.map (Int.castRingHom (Polynomial P.rank)) * lascouxAtom c := by
  rintro ⟨d, hd, hf⟩
  have h := atomPositive_betaZero_of_expansion d hd hf
  rw [betaZero_lascoux_mul] at h
  exact not_atomPositive P hneg h

/-- Corollary 1.3: in the negative range, `𝔏_a 𝔏_b` has no expansion in Lascoux atoms with
coefficients in `ℤ_{≥0}[β]`. -/
theorem not_lascouxAtomPositive (P : Parameters)
    (hneg : 2 < ((P.p : ℤ) - 2) * ((P.q : ℤ) - 2)) :
    ¬ LascouxAtomPositive (lascoux (a P) * lascoux (b P)) := fun h =>
  no_lascouxExpansion_nonnegAtZero P hneg h.exists_int_expansion

/-- The rank-28 example: the stronger form. -/
theorem rank28_no_lascouxExpansion_nonnegAtZero :
    ¬ ∃ d : Composition 28 →₀ _root_.Polynomial ℤ, (∀ c, 0 ≤ (d c).coeff 0) ∧
      lascoux Counterexample.a * lascoux Counterexample.b =
        d.sum fun c dc => dc.map (Int.castRingHom (Polynomial 28)) * lascouxAtom c := by
  rintro ⟨d, hd, hf⟩
  have h := atomPositive_betaZero_of_expansion d hd hf
  rw [betaZero_lascoux_mul] at h
  exact rank28_not_atomPositive h

/-- The rank-28 example: `𝔏_a 𝔏_b` is not Lascoux-atom positive. -/
theorem rank28_not_lascouxAtomPositive :
    ¬ LascouxAtomPositive (lascoux Counterexample.a * lascoux Counterexample.b) := fun h =>
  rank28_no_lascouxExpansion_nonnegAtZero h.exists_int_expansion

/-- Lascoux-atom positivity of products of Lascoux polynomials (Monical–Pechenik–Searles,
Conjecture 4.25, operator form) is false. -/
theorem lascoux_product_positivity_false :
    ¬ ∀ (n : ℕ) (a b : Composition n), LascouxAtomPositive (lascoux a * lascoux b) := by
  intro h
  exact rank28_not_lascouxAtomPositive (h 28 Counterexample.a Counterexample.b)

end
end Schubert.RS.Family
