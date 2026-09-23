import Schubert.RS.LaurentSymmetry

/-! The key operator identity inside the finite Laurent algebra. -/

namespace Schubert.RS

open FinPermutation Schubert
noncomputable section
variable {n : ℕ}

theorem weightSwap_exponent (i : AdjacentPosition n) (a : Fin n →₀ ℕ) :
    weightSwap i (exponentWeight a) =
      exponentWeight (replaceAdjacentExponents a i (a i.right) (a i.left)) := by
  rw [← mapDomain_adjacentTransposition]
  ext j
  change (a (adjacentTransposition i j) : ℤ) =
    ((Finsupp.mapDomain (adjacentTransposition i) a) j : ℤ)
  simp [Finsupp.mapDomain_equiv_apply, adjacentTransposition]

theorem laurentSwap_toLaurent (i : AdjacentPosition n) (p : Polynomial n) :
    laurentSwap i (toLaurent p) = toLaurent (adjacentVariableSwap i p) := by
  have hm (a : Fin n →₀ ℕ) (z : ℤ) :
      laurentSwap i (toLaurent (MvPolynomial.monomial a z)) =
        toLaurent (adjacentVariableSwap i (MvPolynomial.monomial a z)) := by
    rw [adjacentVariableSwap_monomial, toLaurent_monomial, toLaurent_monomial,
      laurentSwap_single, weightSwap_exponent]
  induction p using MvPolynomial.monomial_add_induction_on with
  | C z => simpa [MvPolynomial.C_apply] using hm 0 z
  | monomial_add a z p _ _ ih => simp only [map_add, hm, ih]

theorem exponentWeight_single (i : Fin n) :
    exponentWeight (Finsupp.single i 1) = Pi.single i 1 := by
  ext j
  by_cases h : i = j
  · subst j; simp [exponentWeight]
  · simp [exponentWeight, Finsupp.single_eq_of_ne (Ne.symm h), Pi.single_eq_of_ne (Ne.symm h)]

@[simp] theorem toLaurent_X (i : Fin n) :
    toLaurent (MvPolynomial.X i) = AddMonoidAlgebra.single (Pi.single i 1) 1 := by
  rw [MvPolynomial.X, toLaurent_monomial, exponentWeight_single]

theorem rootMonomial_mul_right (i : AdjacentPosition n) :
    AddMonoidAlgebra.single (positiveRoot i.left i.right) (1 : ℤ) *
      toLaurent (MvPolynomial.X i.right) = toLaurent (MvPolynomial.X i.left) := by
  simp [positiveRoot, AddMonoidAlgebra.single_mul_single]

/-- Laurent form of the isobaric identity, with no formal division. -/
theorem isobaric_laurent_identity (i : AdjacentPosition n) (p : Polynomial n) :
    (1 - AddMonoidAlgebra.single (positiveRoot i.left i.right) 1) *
        toLaurent (isobaric i p) =
      laurentSwap i (toLaurent p) -
        AddMonoidAlgebra.single (positiveRoot i.left i.right) 1 * toLaurent p := by
  let y : Laurent n := toLaurent (MvPolynomial.X i.right)
  let t : Laurent n := AddMonoidAlgebra.single (positiveRoot i.left i.right) 1
  have hyt : t * y = toLaurent (MvPolynomial.X i.left) := rootMonomial_mul_right i
  have h := congrArg toLaurent (isobaric_formula i p)
  simp only [map_mul, map_sub, ← laurentSwap_toLaurent] at h
  rw [← hyt] at h
  have hmul : y * ((1 - t) * toLaurent (isobaric i p)) =
      y * (laurentSwap i (toLaurent p) - t * toLaurent p) := by
    calc
      _ = -((t * y - y) * toLaurent (isobaric i p)) := by ring
      _ = -(t * y * toLaurent p - y * laurentSwap i (toLaurent p)) := by rw [h]
      _ = _ := by ring
  have hi : AddMonoidAlgebra.single (-Pi.single i.right 1) (1 : ℤ) * y = 1 := by
    simp [y, AddMonoidAlgebra.single_mul_single, ← AddMonoidAlgebra.one_def]
  have hh := congrArg (fun q => AddMonoidAlgebra.single (-Pi.single i.right 1) (1 : ℤ) * q) hmul
  simpa only [← mul_assoc, hi, one_mul] using hh

end
end Schubert.RS
