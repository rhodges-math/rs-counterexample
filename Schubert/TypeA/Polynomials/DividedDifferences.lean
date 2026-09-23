import Schubert.RS.Support.PolynomialRing
import Schubert.TypeA.Permutations.AdjacentTranspositions

/-!
# Integral divided-difference operators

We define the type-A divided difference directly on the monomial basis.  This
avoids introducing a rational function and subsequently proving divisibility
by `x_i - x_(i+1)`: polynomiality is built into the finite-sum formula.
-/

namespace Schubert

namespace Schubert

noncomputable section

open FinPermutation

variable {n : ℕ}

/-- The algebra automorphism exchanging the two variables of an adjacent
position. -/
def adjacentVariableSwap (i : AdjacentPosition n) :
    BorelPresentation.PolynomialRing n ≃ₐ[ℤ]
      BorelPresentation.PolynomialRing n :=
  MvPolynomial.renameEquiv ℤ (adjacentTransposition i)

@[simp] theorem adjacentVariableSwap_X_left
    (i : AdjacentPosition n) :
    adjacentVariableSwap i (MvPolynomial.X i.left) =
      MvPolynomial.X i.right := by
  simp [adjacentVariableSwap, adjacentTransposition]

@[simp] theorem adjacentVariableSwap_X_right
    (i : AdjacentPosition n) :
    adjacentVariableSwap i (MvPolynomial.X i.right) =
      MvPolynomial.X i.left := by
  simp [adjacentVariableSwap, adjacentTransposition]

@[simp] theorem adjacentVariableSwap_X_other
    (i : AdjacentPosition n) (j : Fin n)
    (hjleft : j ≠ i.left) (hjright : j ≠ i.right) :
    adjacentVariableSwap i (MvPolynomial.X j) = MvPolynomial.X j := by
  simp [adjacentVariableSwap, adjacentTransposition,
    Equiv.swap_apply_of_ne_of_ne hjleft hjright]

/-- Exchanging the same adjacent variables twice is the identity. -/
@[simp] theorem adjacentVariableSwap_involutive
    (i : AdjacentPosition n)
    (p : BorelPresentation.PolynomialRing n) :
    adjacentVariableSwap i (adjacentVariableSwap i p) = p := by
  change MvPolynomial.rename (adjacentTransposition i)
    (MvPolynomial.rename (adjacentTransposition i) p) = p
  rw [MvPolynomial.rename_rename]
  have hcomp : adjacentTransposition i ∘ adjacentTransposition i = id := by
    funext j
    simp [adjacentTransposition]
  rw [hcomp, MvPolynomial.rename_id_apply]

/-- Replace the exponents at the two positions of an adjacent pair. -/
def replaceAdjacentExponents (a : Fin n →₀ ℕ)
    (i : AdjacentPosition n) (leftExponent rightExponent : ℕ) :
    Fin n →₀ ℕ :=
  (a.update i.left leftExponent).update i.right rightExponent

@[simp] theorem replaceAdjacentExponents_left
    (a : Fin n →₀ ℕ) (i : AdjacentPosition n) (p q : ℕ) :
    replaceAdjacentExponents a i p q i.left = p := by
  simp [replaceAdjacentExponents, i.left_ne_right]

@[simp] theorem replaceAdjacentExponents_right
    (a : Fin n →₀ ℕ) (i : AdjacentPosition n) (p q : ℕ) :
    replaceAdjacentExponents a i p q i.right = q := by
  simp [replaceAdjacentExponents]

theorem replaceAdjacentExponents_of_ne
    (a : Fin n →₀ ℕ) (i : AdjacentPosition n) (p q : ℕ) (j : Fin n)
    (hjleft : j ≠ i.left) (hjright : j ≠ i.right) :
    replaceAdjacentExponents a i p q j = a j := by
  simp [replaceAdjacentExponents, hjleft, hjright]

theorem single_left_add_replaceAdjacentExponents
    (a : Fin n →₀ ℕ) (i : AdjacentPosition n) (p q : ℕ) :
    Finsupp.single i.left 1 + replaceAdjacentExponents a i p q =
      replaceAdjacentExponents a i (p + 1) q := by
  ext j
  by_cases hjleft : j = i.left
  · subst j
    simp [Nat.add_comm]
  · by_cases hjright : j = i.right
    · subst j
      simp [i.left_ne_right]
    · simp [replaceAdjacentExponents_of_ne _ _ _ _ _ hjleft hjright,
        Finsupp.single_eq_of_ne hjleft]

theorem single_right_add_replaceAdjacentExponents
    (a : Fin n →₀ ℕ) (i : AdjacentPosition n) (p q : ℕ) :
    Finsupp.single i.right 1 + replaceAdjacentExponents a i p q =
      replaceAdjacentExponents a i p (q + 1) := by
  ext j
  by_cases hjleft : j = i.left
  · subst j
    simp [i.left_ne_right]
  · by_cases hjright : j = i.right
    · subst j
      simp [Nat.add_comm]
    · simp [replaceAdjacentExponents_of_ne _ _ _ _ _ hjleft hjright,
        Finsupp.single_eq_of_ne hjright]

theorem X_left_mul_replaceAdjacentExponents
    (a : Fin n →₀ ℕ) (i : AdjacentPosition n) (p q : ℕ) :
    MvPolynomial.X i.left *
        MvPolynomial.monomial (replaceAdjacentExponents a i p q) (1 : ℤ) =
      MvPolynomial.monomial (replaceAdjacentExponents a i (p + 1) q) 1 := by
  rw [MvPolynomial.X, MvPolynomial.monomial_mul,
    single_left_add_replaceAdjacentExponents]
  simp

theorem X_right_mul_replaceAdjacentExponents
    (a : Fin n →₀ ℕ) (i : AdjacentPosition n) (p q : ℕ) :
    MvPolynomial.X i.right *
        MvPolynomial.monomial (replaceAdjacentExponents a i p q) (1 : ℤ) =
      MvPolynomial.monomial (replaceAdjacentExponents a i p (q + 1)) 1 := by
  rw [MvPolynomial.X, MvPolynomial.monomial_mul,
    single_right_add_replaceAdjacentExponents]
  simp

/-- Renaming by the adjacent transposition exchanges exactly the two adjacent
exponents. -/
theorem mapDomain_adjacentTransposition
    (a : Fin n →₀ ℕ) (i : AdjacentPosition n) :
    Finsupp.mapDomain (adjacentTransposition i) a =
      replaceAdjacentExponents a i (a i.right) (a i.left) := by
  ext j
  rw [Finsupp.mapDomain_equiv_apply]
  simp only [adjacentTransposition]
  by_cases hjleft : j = i.left
  · subst j
    simp
  · by_cases hjright : j = i.right
    · subst j
      simp
    · simp [replaceAdjacentExponents_of_ne _ _ _ _ _ hjleft hjright,
        Equiv.swap_apply_of_ne_of_ne hjleft hjright]

@[simp] theorem adjacentVariableSwap_monomial
    (i : AdjacentPosition n) (a : Fin n →₀ ℕ) (c : ℤ) :
    adjacentVariableSwap i (MvPolynomial.monomial a c) =
      MvPolynomial.monomial
        (replaceAdjacentExponents a i (a i.right) (a i.left)) c := by
  rw [adjacentVariableSwap, MvPolynomial.renameEquiv_apply,
    MvPolynomial.rename_monomial, mapDomain_adjacentTransposition]

theorem replaceAdjacentExponents_self
    (a : Fin n →₀ ℕ) (i : AdjacentPosition n) :
    replaceAdjacentExponents a i (a i.left) (a i.right) = a := by
  ext j
  by_cases hjleft : j = i.left
  · subst j
    simp
  · by_cases hjright : j = i.right
    · subst j
      simp
    · exact replaceAdjacentExponents_of_ne a i _ _ j hjleft hjright

/-- The two replacement exponents can be recovered by evaluating at the two
adjacent positions. -/
theorem replaceAdjacentExponents_injective_pair
    (a : Fin n →₀ ℕ) (i : AdjacentPosition n) :
    Function.Injective (fun pq : ℕ × ℕ =>
      replaceAdjacentExponents a i pq.1 pq.2) := by
  rintro ⟨p, q⟩ ⟨p', q'⟩ h
  apply Prod.ext
  · have hleft := DFunLike.congr_fun h i.left
    simpa using hleft
  · have hright := DFunLike.congr_fun h i.right
    simpa using hright

/-- Divided difference of a coefficient-one monomial.  If the two relevant
exponents are equal, the result is zero; otherwise this is the usual finite
geometric-series quotient. -/
def monomialDividedDifference
    (i : AdjacentPosition n) (a : Fin n →₀ ℕ) :
    BorelPresentation.PolynomialRing n :=
  if _h : a i.right < a i.left then
    ∑ k ∈ Finset.range (a i.left - a i.right),
      MvPolynomial.monomial
        (replaceAdjacentExponents a i
          (a i.left - 1 - k) (a i.right + k)) 1
  else if _h' : a i.left < a i.right then
    -∑ k ∈ Finset.range (a i.right - a i.left),
      MvPolynomial.monomial
        (replaceAdjacentExponents a i
          (a i.left + k) (a i.right - 1 - k)) 1
  else 0

/-- The integral type-A divided-difference operator `∂ᵢ`, extended linearly
from the monomial formula. -/
def adjacentDividedDifference (i : AdjacentPosition n) :
    BorelPresentation.PolynomialRing n →ₗ[ℤ]
      BorelPresentation.PolynomialRing n :=
  (MvPolynomial.basisMonomials (Fin n) ℤ).constr ℤ
    (monomialDividedDifference i)

@[simp] theorem adjacentDividedDifference_monomial_one
    (i : AdjacentPosition n) (a : Fin n →₀ ℕ) :
    adjacentDividedDifference i (MvPolynomial.monomial a 1) =
      monomialDividedDifference i a := by
  change adjacentDividedDifference i
      (MvPolynomial.basisMonomials (Fin n) ℤ a) = _
  exact Module.Basis.constr_basis
    (MvPolynomial.basisMonomials (Fin n) ℤ) ℤ
      (monomialDividedDifference i) a

theorem adjacentDividedDifference_monomial
    (i : AdjacentPosition n) (a : Fin n →₀ ℕ) (c : ℤ) :
    adjacentDividedDifference i (MvPolynomial.monomial a c) =
      c • monomialDividedDifference i a := by
  rw [show MvPolynomial.monomial a c =
      c • MvPolynomial.monomial a 1 by
        rw [MvPolynomial.smul_monomial]
        simp]
  rw [map_smul, adjacentDividedDifference_monomial_one]

@[simp] theorem monomialDividedDifference_equal
    (i : AdjacentPosition n) (a : Fin n →₀ ℕ)
    (h : a i.left = a i.right) :
    monomialDividedDifference i a = 0 := by
  simp [monomialDividedDifference, h]

@[simp] theorem adjacentDividedDifference_zero
    (i : AdjacentPosition n) : adjacentDividedDifference i 0 = 0 :=
  map_zero _

/-- In the positive geometric-series case, the endpoint obtained by fully
moving the excess exponent from left to right occurs with coefficient one. -/
theorem coeff_monomialDividedDifference_positive_endpoint
    (i : AdjacentPosition n) (a : Fin n →₀ ℕ)
    (h : a i.right < a i.left) :
    MvPolynomial.coeff
        (replaceAdjacentExponents a i (a i.right) (a i.left - 1))
        (monomialDividedDifference i a) = 1 := by
  rw [monomialDividedDifference, dif_pos h]
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  let k₀ := a i.left - a i.right - 1
  have hk₀ : k₀ < a i.left - a i.right := by
    dsimp [k₀]
    omega
  rw [Finset.sum_eq_single k₀]
  · have hleft : a i.left - 1 - k₀ = a i.right := by
      dsimp [k₀]
      omega
    have hright : a i.right + k₀ = a i.left - 1 := by
      dsimp [k₀]
      omega
    simp [hleft, hright]
  · intro k hk hkne
    have hpair :
        (a i.left - 1 - k, a i.right + k) ≠
          (a i.right, a i.left - 1) := by
      intro heq
      have hsecond := congrArg Prod.snd heq
      have hk : k = k₀ := by
        dsimp [k₀]
        dsimp at hsecond
        omega
      exact hkne hk
    have hrepl :
        replaceAdjacentExponents a i
            (a i.left - 1 - k) (a i.right + k) ≠
          replaceAdjacentExponents a i (a i.right) (a i.left - 1) := by
      intro heq
      exact hpair ((replaceAdjacentExponents_injective_pair a i) heq)
    rw [if_neg hrepl]
  · simp [hk₀]

private theorem positive_monomial_telescoping
    (a : Fin n →₀ ℕ) (i : AdjacentPosition n)
    (h : a i.right < a i.left) :
    (MvPolynomial.X i.left - MvPolynomial.X i.right) *
        (∑ k ∈ Finset.range (a i.left - a i.right),
          MvPolynomial.monomial
            (replaceAdjacentExponents a i
              (a i.left - 1 - k) (a i.right + k)) (1 : ℤ)) =
      MvPolynomial.monomial a 1 -
        MvPolynomial.monomial
          (replaceAdjacentExponents a i (a i.right) (a i.left)) 1 := by
  let F : ℕ → BorelPresentation.PolynomialRing n := fun k =>
    MvPolynomial.monomial
      (replaceAdjacentExponents a i
        (a i.left - k) (a i.right + k)) 1
  rw [sub_mul, Finset.mul_sum, Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  have hterm : ∀ k ∈ Finset.range (a i.left - a i.right),
      MvPolynomial.X i.left *
          MvPolynomial.monomial
            (replaceAdjacentExponents a i
              (a i.left - 1 - k) (a i.right + k)) (1 : ℤ) -
        MvPolynomial.X i.right *
          MvPolynomial.monomial
            (replaceAdjacentExponents a i
              (a i.left - 1 - k) (a i.right + k)) 1 =
        F k - F (k + 1) := by
    intro k hk
    simp only [Finset.mem_range] at hk
    have hkleft : k < a i.left :=
      lt_of_lt_of_le hk (Nat.sub_le _ _)
    rw [X_left_mul_replaceAdjacentExponents,
      X_right_mul_replaceAdjacentExponents]
    dsimp [F]
    congr 4 <;> omega
  rw [Finset.sum_congr rfl hterm]
  rw [Finset.sum_range_sub']
  dsimp [F]
  have hendLeft : a i.left - (a i.left - a i.right) = a i.right := by
    omega
  have hendRight : a i.right + (a i.left - a i.right) = a i.left := by
    omega
  rw [hendLeft, hendRight, replaceAdjacentExponents_self]

private theorem negative_monomial_telescoping
    (a : Fin n →₀ ℕ) (i : AdjacentPosition n)
    (h : a i.left < a i.right) :
    (MvPolynomial.X i.left - MvPolynomial.X i.right) *
        (-∑ k ∈ Finset.range (a i.right - a i.left),
          MvPolynomial.monomial
            (replaceAdjacentExponents a i
              (a i.left + k) (a i.right - 1 - k)) (1 : ℤ)) =
      MvPolynomial.monomial a 1 -
        MvPolynomial.monomial
          (replaceAdjacentExponents a i (a i.right) (a i.left)) 1 := by
  let F : ℕ → BorelPresentation.PolynomialRing n := fun k =>
    MvPolynomial.monomial
      (replaceAdjacentExponents a i
        (a i.left + k) (a i.right - k)) 1
  rw [mul_neg, sub_mul, neg_sub, Finset.mul_sum, Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  have hterm : ∀ k ∈ Finset.range (a i.right - a i.left),
      MvPolynomial.X i.right *
          MvPolynomial.monomial
            (replaceAdjacentExponents a i
              (a i.left + k) (a i.right - 1 - k)) (1 : ℤ) -
        MvPolynomial.X i.left *
          MvPolynomial.monomial
            (replaceAdjacentExponents a i
              (a i.left + k) (a i.right - 1 - k)) 1 =
        F k - F (k + 1) := by
    intro k hk
    simp only [Finset.mem_range] at hk
    have hkright : k < a i.right :=
      lt_of_lt_of_le hk (Nat.sub_le _ _)
    rw [X_right_mul_replaceAdjacentExponents,
      X_left_mul_replaceAdjacentExponents]
    dsimp [F]
    congr 4 <;> omega
  rw [Finset.sum_congr rfl hterm]
  rw [Finset.sum_range_sub']
  dsimp [F]
  have hendLeft : a i.left + (a i.right - a i.left) = a i.right := by
    omega
  have hendRight : a i.right - (a i.right - a i.left) = a i.left := by
    omega
  rw [hendLeft, hendRight, replaceAdjacentExponents_self]

/-- The finite monomial formula is the polynomial quotient of the alternating
difference by the adjacent root.  This coefficient-one statement is the
telescoping core of the integral divided-difference theory. -/
theorem adjacentRoot_mul_monomialDividedDifference
    (i : AdjacentPosition n) (a : Fin n →₀ ℕ) :
    (MvPolynomial.X i.left - MvPolynomial.X i.right) *
        monomialDividedDifference i a =
      MvPolynomial.monomial a 1 -
        adjacentVariableSwap i (MvPolynomial.monomial a 1) := by
  rw [adjacentVariableSwap_monomial]
  by_cases hrightLeft : a i.right < a i.left
  · simpa [monomialDividedDifference, hrightLeft] using
      positive_monomial_telescoping a i hrightLeft
  · by_cases hleftRight : a i.left < a i.right
    · simpa [monomialDividedDifference, hrightLeft, hleftRight] using
        negative_monomial_telescoping a i hleftRight
    · have heq : a i.left = a i.right := by omega
      rw [monomialDividedDifference_equal i a heq]
      rw [mul_zero]
      have hreplace :
          replaceAdjacentExponents a i (a i.right) (a i.left) = a := by
        simpa only [heq] using replaceAdjacentExponents_self a i
      rw [hreplace, sub_self]

theorem adjacentRoot_mul_adjacentDividedDifference_monomial
    (i : AdjacentPosition n) (a : Fin n →₀ ℕ) (c : ℤ) :
    (MvPolynomial.X i.left - MvPolynomial.X i.right) *
        adjacentDividedDifference i (MvPolynomial.monomial a c) =
      MvPolynomial.monomial a c -
        adjacentVariableSwap i (MvPolynomial.monomial a c) := by
  rw [adjacentDividedDifference_monomial]
  rw [show MvPolynomial.monomial a c =
      c • MvPolynomial.monomial a (1 : ℤ) by
        rw [MvPolynomial.smul_monomial]
        simp]
  rw [map_smul, mul_smul_comm,
    adjacentRoot_mul_monomialDividedDifference, smul_sub]

/-- Fundamental identity for the integral type-A divided difference:
`(x_i-x_(i+1)) ∂ᵢ(p) = p-sᵢ(p)`. -/
theorem adjacentRoot_mul_adjacentDividedDifference
    (i : AdjacentPosition n)
    (p : BorelPresentation.PolynomialRing n) :
    (MvPolynomial.X i.left - MvPolynomial.X i.right) *
        adjacentDividedDifference i p =
      p - adjacentVariableSwap i p := by
  induction p using MvPolynomial.monomial_add_induction_on with
  | C c =>
      simpa [MvPolynomial.C_apply] using
        adjacentRoot_mul_adjacentDividedDifference_monomial i 0 c
  | monomial_add a c f _ _ ih =>
      rw [map_add, map_add, mul_add, ih,
        adjacentRoot_mul_adjacentDividedDifference_monomial]
      abel

theorem adjacentRoot_ne_zero (i : AdjacentPosition n) :
    (MvPolynomial.X i.left - MvPolynomial.X i.right :
      BorelPresentation.PolynomialRing n) ≠ 0 := by
  rw [sub_ne_zero]
  exact fun h => i.left_ne_right (MvPolynomial.X_injective h)

/-- Twisted Leibniz rule `∂ᵢ(pq)=∂ᵢ(p)q+sᵢ(p)∂ᵢ(q)`. -/
theorem adjacentDividedDifference_mul
    (i : AdjacentPosition n)
    (p q : BorelPresentation.PolynomialRing n) :
    adjacentDividedDifference i (p * q) =
      adjacentDividedDifference i p * q +
        adjacentVariableSwap i p * adjacentDividedDifference i q := by
  apply mul_left_cancel₀ (adjacentRoot_ne_zero i)
  rw [adjacentRoot_mul_adjacentDividedDifference]
  rw [mul_add]
  calc
    p * q - adjacentVariableSwap i (p * q) =
        p * q - adjacentVariableSwap i p * adjacentVariableSwap i q := by
          rw [map_mul]
    _ = (MvPolynomial.X i.left - MvPolynomial.X i.right) *
            adjacentDividedDifference i p * q +
          adjacentVariableSwap i p *
            ((MvPolynomial.X i.left - MvPolynomial.X i.right) *
              adjacentDividedDifference i q) := by
          rw [adjacentRoot_mul_adjacentDividedDifference,
            adjacentRoot_mul_adjacentDividedDifference]
          ring
    _ = (MvPolynomial.X i.left - MvPolynomial.X i.right) *
          (adjacentDividedDifference i p * q) +
        (MvPolynomial.X i.left - MvPolynomial.X i.right) *
          (adjacentVariableSwap i p * adjacentDividedDifference i q) := by
          ring

/-- A divided difference is invariant under the adjacent variable swap. -/
theorem adjacentVariableSwap_adjacentDividedDifference
    (i : AdjacentPosition n)
    (p : BorelPresentation.PolynomialRing n) :
    adjacentVariableSwap i (adjacentDividedDifference i p) =
      adjacentDividedDifference i p := by
  apply mul_left_cancel₀ (adjacentRoot_ne_zero i)
  have hmap := congrArg (fun q : BorelPresentation.PolynomialRing n =>
      adjacentVariableSwap i q)
    (adjacentRoot_mul_adjacentDividedDifference i p)
  simp only [map_mul, map_sub, adjacentVariableSwap_X_left,
    adjacentVariableSwap_X_right, adjacentVariableSwap_involutive] at hmap
  calc
    (MvPolynomial.X i.left - MvPolynomial.X i.right) *
        adjacentVariableSwap i (adjacentDividedDifference i p) =
      -((MvPolynomial.X i.right - MvPolynomial.X i.left) *
        adjacentVariableSwap i (adjacentDividedDifference i p)) := by ring
    _ = -(adjacentVariableSwap i p - p) := by rw [hmap]
    _ = p - adjacentVariableSwap i p := by ring
    _ = (MvPolynomial.X i.left - MvPolynomial.X i.right) *
        adjacentDividedDifference i p := by
          rw [adjacentRoot_mul_adjacentDividedDifference]

/-- Nil-Coxeter square relation `∂ᵢ²=0`. -/
@[simp] theorem adjacentDividedDifference_sq
    (i : AdjacentPosition n)
    (p : BorelPresentation.PolynomialRing n) :
    adjacentDividedDifference i (adjacentDividedDifference i p) = 0 := by
  apply mul_left_cancel₀ (adjacentRoot_ne_zero i)
  rw [adjacentRoot_mul_adjacentDividedDifference,
    adjacentVariableSwap_adjacentDividedDifference, sub_self, mul_zero]

private theorem replaceAdjacentExponents_single_left_zero
    (i : AdjacentPosition n) :
    replaceAdjacentExponents (Finsupp.single i.left 1) i 0 0 = 0 := by
  ext j
  by_cases hjleft : j = i.left
  · subst j
    simp
  · by_cases hjright : j = i.right
    · subst j
      simp
    · simp [replaceAdjacentExponents_of_ne _ _ _ _ _ hjleft hjright,
        Finsupp.single_eq_of_ne hjleft]

private theorem replaceAdjacentExponents_single_right_zero
    (i : AdjacentPosition n) :
    replaceAdjacentExponents (Finsupp.single i.right 1) i 0 0 = 0 := by
  ext j
  by_cases hjleft : j = i.left
  · subst j
    simp
  · by_cases hjright : j = i.right
    · subst j
      simp
    · simp [replaceAdjacentExponents_of_ne _ _ _ _ _ hjleft hjright,
        Finsupp.single_eq_of_ne hjright]

@[simp] theorem monomialDividedDifference_left_variable
    (i : AdjacentPosition n) :
    monomialDividedDifference i (Finsupp.single i.left 1) = 1 := by
  classical
  simp [monomialDividedDifference, i.left_ne_right,
    replaceAdjacentExponents_single_left_zero]

@[simp] theorem monomialDividedDifference_right_variable
    (i : AdjacentPosition n) :
    monomialDividedDifference i (Finsupp.single i.right 1) = -1 := by
  classical
  simp [monomialDividedDifference, i.left_ne_right,
    replaceAdjacentExponents_single_right_zero]

@[simp] theorem adjacentDividedDifference_X_left
    (i : AdjacentPosition n) :
    adjacentDividedDifference i (MvPolynomial.X i.left) = 1 := by
  rw [MvPolynomial.X, adjacentDividedDifference_monomial_one]
  exact monomialDividedDifference_left_variable i

@[simp] theorem adjacentDividedDifference_X_right
    (i : AdjacentPosition n) :
    adjacentDividedDifference i (MvPolynomial.X i.right) = -1 := by
  rw [MvPolynomial.X, adjacentDividedDifference_monomial_one]
  exact monomialDividedDifference_right_variable i

@[simp] theorem monomialDividedDifference_other_variable
    (i : AdjacentPosition n) (j : Fin n)
    (hjleft : j ≠ i.left) (hjright : j ≠ i.right) :
    monomialDividedDifference i (Finsupp.single j 1) = 0 := by
  classical
  have hleft : (Finsupp.single j 1) i.left = 0 :=
    Finsupp.single_eq_of_ne hjleft.symm
  have hright : (Finsupp.single j 1) i.right = 0 :=
    Finsupp.single_eq_of_ne hjright.symm
  exact monomialDividedDifference_equal i _ (hleft.trans hright.symm)

@[simp] theorem adjacentDividedDifference_X_other
    (i : AdjacentPosition n) (j : Fin n)
    (hjleft : j ≠ i.left) (hjright : j ≠ i.right) :
    adjacentDividedDifference i (MvPolynomial.X j) = 0 := by
  rw [MvPolynomial.X, adjacentDividedDifference_monomial_one]
  exact monomialDividedDifference_other_variable i j hjleft hjright

end

end Schubert

end Schubert
