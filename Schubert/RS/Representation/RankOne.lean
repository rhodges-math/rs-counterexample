import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Algebra.MvPolynomial.Basic

/-!
# The actual rank-one cyclic quotient

`CyclicQuotient m` is the algebra C[T]/(T^(m+1)), independently of any
character formula. Its power basis and the dimensions of the homogeneous
lines are derived from the quotient. No Demazure character formula is used.
-/
namespace Schubert.RS.Representation

noncomputable section
open scoped BigOperators

/-- The rank-one Joseph–Polo quotient, with nilpotence exponent `m+1`. -/
abbrev CyclicQuotient (m : ℕ) := AdjoinRoot ((Polynomial.X : Polynomial ℂ) ^ (m + 1))

/-- Multiplication by this element is the positive-root operator. -/
def raisingGenerator (m : ℕ) : CyclicQuotient m := AdjoinRoot.root _

private theorem cutoff_monic (m : ℕ) :
    ((Polynomial.X : Polynomial ℂ) ^ (m + 1)).Monic := Polynomial.monic_X_pow _

private theorem cutoff_degree (m : ℕ) :
    ((Polynomial.X : Polynomial ℂ) ^ (m + 1)).natDegree = m + 1 := by simp

/-- A basis of the actual quotient, not a postulated list of weights. -/
def cyclicBasis (m : ℕ) : Module.Basis (Fin (m + 1)) ℂ (CyclicQuotient m) :=
  ((AdjoinRoot.powerBasis' (cutoff_monic m)).basis).reindex
    (finCongr (cutoff_degree m))

@[simp] theorem cyclicBasis_apply (m : ℕ) (k : Fin (m + 1)) :
    cyclicBasis m k = raisingGenerator m ^ (k : ℕ) := by
  rw [cyclicBasis, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow]
  rfl

/-- The JP relation holds in the quotient itself. -/
theorem raisingGenerator_nilpotent (m : ℕ) :
    raisingGenerator m ^ (m + 1) = 0 := by
  have h := AdjoinRoot.eval₂_root ((Polynomial.X : Polynomial ℂ) ^ (m + 1))
  simpa [raisingGenerator] using h

/-- Scaling the polynomial variable descends to the actual quotient. -/
def cyclicScale (m : ℕ) (t : ℂ) : CyclicQuotient m →ₐ[ℂ] CyclicQuotient m :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId ℂ (CyclicQuotient m))
    (algebraMap ℂ (CyclicQuotient m) t * raisingGenerator m) (by
      simp only [Polynomial.eval₂_pow, Polynomial.eval₂_X]
      rw [mul_pow, raisingGenerator_nilpotent, mul_zero])

@[simp] theorem cyclicScale_generator (m : ℕ) (t : ℂ) :
    cyclicScale m t (raisingGenerator m) =
      algebraMap ℂ (CyclicQuotient m) t * raisingGenerator m := by
  exact AdjoinRoot.liftAlgHom_root _ _ _ _

/-- The grading eigenvalue is deduced from scaling the quotient variable. -/
theorem cyclicScale_basis (m : ℕ) (t : ℂ) (k : Fin (m + 1)) :
    cyclicScale m t (cyclicBasis m k) = t ^ (k : ℕ) • cyclicBasis m k := by
  simp only [cyclicBasis_apply, map_pow, cyclicScale_generator, mul_pow,
    Algebra.smul_def, map_pow]
/-- None of the surviving powers vanishes. -/
theorem raisingGenerator_pow_ne_zero (m : ℕ) (k : Fin (m + 1)) :
    raisingGenerator m ^ (k : ℕ) ≠ 0 := by
  simpa using (cyclicBasis m).ne_zero k

/-- The root action moves along the surviving string. -/
theorem raisingGenerator_mul_basis (m : ℕ) (k : Fin m) :
    raisingGenerator m * cyclicBasis m k.castSucc = cyclicBasis m k.succ := by
  simp [pow_succ, mul_comm]

/-- The last vector is killed, as required for the actual truncated action. -/
theorem raisingGenerator_mul_last (m : ℕ) :
    raisingGenerator m * cyclicBasis m (Fin.last m) = 0 := by
  simpa [pow_succ, mul_comm] using raisingGenerator_nilpotent m

theorem cyclicQuotient_finrank (m : ℕ) :
    Module.finrank ℂ (CyclicQuotient m) = m + 1 := by
  simpa using Module.finrank_eq_card_basis (cyclicBasis m)

/-- The degree-`k` line in the polynomial quotient. -/
def cyclicPiece (m : ℕ) (k : Fin (m + 1)) : Submodule ℂ (CyclicQuotient m) :=
  Submodule.span ℂ {raisingGenerator m ^ (k : ℕ)}

@[simp] theorem cyclicPiece_finrank (m : ℕ) (k : Fin (m + 1)) :
    Module.finrank ℂ (cyclicPiece m k) = 1 := by
  exact finrank_span_singleton (raisingGenerator_pow_ne_zero m k)

/-- Character of the quotient's homogeneous lines, with supplied weight labels.
For a positive root `e_i-e_j`, the labels are `u + k*(e_i-e_j)`.
The labels alone do not assert identification with any ambient Demazure module. -/
def cyclicCharacter {n : ℕ} (m : ℕ) (weight : Fin (m + 1) → Fin n →₀ ℕ) :
    MvPolynomial (Fin n) ℤ :=
  ∑ k, MvPolynomial.monomial (weight k)
    (Module.finrank ℂ (cyclicPiece m k) : ℤ)

theorem cyclicCharacter_eq_sum {n : ℕ} (m : ℕ)
    (weight : Fin (m + 1) → Fin n →₀ ℕ) :
    cyclicCharacter m weight = ∑ k, MvPolynomial.monomial (weight k) 1 := by
  simp [cyclicCharacter]

end
end Schubert.RS.Representation



