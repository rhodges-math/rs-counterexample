import Schubert.RS.Lascoux.Polynomials
import Schubert.RS.AtomExpansionCertificate

/-!
# Lascoux-atom positivity specializes to atom positivity

`LascouxAtomPositive f` says that `f` is a finite combination of Lascoux atoms with
coefficients in `ℤ_{≥0}[β]`, the positivity of Monical–Pechenik–Searles
(arXiv:1806.03802, Conjecture 4.25). Specializing at `β = 0`, a ring homomorphism sending
Lascoux atoms to Demazure atoms, turns any such expansion into an `ℕ`-combination of
Demazure atoms. Only the constant terms of the coefficients matter:
`atomPositive_betaZero_of_expansion` needs just `d_c(0) ≥ 0` for coefficients `d_c ∈ ℤ[β]`.
No basis property of Lascoux atoms is used.
-/

namespace Schubert.RS

noncomputable section

variable {n : ℕ}

/-- `f` is a finite combination of Lascoux atoms with coefficients in `ℤ_{≥0}[β]`. -/
def LascouxAtomPositive (f : BetaPolynomial n) : Prop :=
  ∃ d : Composition n →₀ _root_.Polynomial ℕ,
    f = d.sum fun c dc => dc.map (Nat.castRingHom (Polynomial n)) * lascouxAtom c

theorem betaZero_map_intCast (d : _root_.Polynomial ℤ) :
    betaZero (d.map (Int.castRingHom (Polynomial n))) = ((d.coeff 0 : ℤ) : Polynomial n) := by
  rw [betaZero_apply, _root_.Polynomial.coeff_map]
  rfl

/-- An expansion `f = Σ_c d_c(β)·𝔏̄_c` with `d_c ∈ ℤ[β]` and `d_c(0) ≥ 0` specializes at
`β = 0` to an atom-positive expansion. -/
theorem atomPositive_betaZero_of_expansion {f : BetaPolynomial n}
    (d : Composition n →₀ _root_.Polynomial ℤ) (hd : ∀ c, 0 ≤ (d c).coeff 0)
    (hf : f = d.sum fun c dc => dc.map (Int.castRingHom (Polynomial n)) * lascouxAtom c) :
    AtomPositive (betaZero f) := by
  refine ⟨d.mapRange (fun dc => (dc.coeff 0).toNat)
    (by rw [_root_.Polynomial.coeff_zero, Int.toNat_zero]), ?_⟩
  rw [Finsupp.sum_mapRange_index (by simp), hf, map_finsuppSum]
  refine Finsupp.sum_congr fun c _ => ?_
  rw [map_mul, betaZero_lascouxAtom, betaZero_map_intCast, nsmul_eq_mul, ← Int.cast_natCast,
    Int.toNat_of_nonneg (hd c)]

/-- A `ℤ_{≥0}[β]` expansion is in particular a `ℤ[β]` expansion whose coefficients are
nonnegative at `β = 0`. -/
theorem LascouxAtomPositive.exists_int_expansion {f : BetaPolynomial n}
    (hf : LascouxAtomPositive f) :
    ∃ d : Composition n →₀ _root_.Polynomial ℤ, (∀ c, 0 ≤ (d c).coeff 0) ∧
      f = d.sum fun c dc => dc.map (Int.castRingHom (Polynomial n)) * lascouxAtom c := by
  obtain ⟨d, rfl⟩ := hf
  refine ⟨d.mapRange (_root_.Polynomial.map (Nat.castRingHom ℤ)) (_root_.Polynomial.map_zero _),
    fun c => ?_, ?_⟩
  · simp [_root_.Polynomial.coeff_map]
  · rw [Finsupp.sum_mapRange_index (by simp)]
    refine Finsupp.sum_congr fun c _ => ?_
    rw [_root_.Polynomial.map_map]
    congr 2

/-- Lascoux-atom positivity specializes at `β = 0` to atom positivity. -/
theorem LascouxAtomPositive.atomPositive_betaZero {f : BetaPolynomial n}
    (hf : LascouxAtomPositive f) : AtomPositive (betaZero f) := by
  obtain ⟨d, hd, hfd⟩ := hf.exists_int_expansion
  exact atomPositive_betaZero_of_expansion d hd hfd

end
end Schubert.RS
