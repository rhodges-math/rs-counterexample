import RSCounterexample.FlagVarieties.Modules.Geometric
import RSCounterexample.FlagVarieties.Schubert.RankOneInduction
import RSCounterexample.Demazure.MonomialOperators

/-!
# Characters of rank-one induction and the Demazure recurrences

For an adjacent position `i` (rows `i`, `i + 1`) let `αᵢ = eᵢ − e_{i+1}`.

* **The Demazure operator on Laurent polynomials** (`FlagVarieties.laurentIsobaric`): on monomials,
  `πᵢ(x^μ) = Σ_{k=0}^{μᵢ - μ_{i+1}} x^{μ - k αᵢ}` if `μ_{i+1} ≤ μᵢ`, and
  `πᵢ(x^μ) = -Σ_{k=1}^{μ_{i+1} - μᵢ - 1} x^{μ + k αᵢ}` otherwise. It extends the isobaric
  divided difference of `Demazure` (`FlagVarieties.toLaurent_isobaric`); `π̄ᵢ = πᵢ - 1` is
  `FlagVarieties.laurentAtomOperator`.
* **The torus acts diagonally on `H⁰(X_{sᵢ}, 𝓛(η))`**: in the basis `τᵏ` of
  `FlagVarieties.simpleSchubertSectionsEquiv` (`f ↦ f(1 + τ E_{i+1,i})`), the vector `τᵏ` has
  weight `η + k αᵢ` (`FlagVarieties.sectionsRep_borelTorus_simpleSchubertBasis`, over every
  commutative ring).
* **`ch H⁰(X_{sᵢ}, 𝓛(η)) = πᵢ(x^{−η})`** for `η_{i+1} - ηᵢ ≥ -1`
  (`FlagVarieties.ch_sections_simpleSchubert`),
  hence **`ch H_{sᵢ}(K_η) = πᵢ ch(K_η)`** for the rank-one induction of a character
  (`FlagVarieties.ch_rankOneInduction_charCoaction`).
* **The recurrences in Laurent form**: `ch P(−sᵢu) = πᵢ ch P(−u)` and `ch Q(−sᵢu) = π̄ᵢ ch Q(−u)`
  for `uᵢ > u_{i+1}` (`FlagVarieties.SectionRep.ch_dualJoseph_step_laurent`,
  `FlagVarieties.SectionRep.ch_minimalRelativeSchubert_step_laurent`,
  `FlagVarieties.ch_dualJoseph_step_laurent`).
* **Geometric reading of the first step**: if `σ(ν) = sᵢ`, then `P(ν) = H⁰(X_{sᵢ}, 𝓛(η(ν)))` is the
  rank-one induction `H_{sᵢ}(ℂ_{η(ν)})` (`FlagVarieties.dualJosephRankOneEquiv`). For a
  partition `u` with `uᵢ > u_{i+1}`, `P(−u) = ℂ_{−u}` is a line and
  `P(−sᵢu) ≅ H_{sᵢ}(ℂ_{−u})` (`FlagVarieties.dualJosephSwapEquiv`), so the recurrence
  `ch P(−sᵢu) = πᵢ ch P(−u)` is `ch H_{sᵢ}(M) = πᵢ ch M` for the line `M = P(−u)`
  (`FlagVarieties.ch_dualJoseph_swap`).
-/

open Schubert GLRep TauCeti Demazure FinPermutation Polynomial

namespace FlagVarieties

noncomputable section

/-! ### The Demazure operator on Laurent polynomials -/

section LaurentOperators

variable {n : ℕ}

/-- The simple root `αᵢ = eᵢ − e_{i+1}`. -/
def simpleRoot (i : AdjacentPosition n) : Demazure.Weight n :=
  Pi.single i.left 1 - Pi.single i.right 1

theorem simpleRoot_left (i : AdjacentPosition n) : simpleRoot i i.left = 1 := by
  simp [simpleRoot, i.left_ne_right]

theorem simpleRoot_right (i : AdjacentPosition n) : simpleRoot i i.right = -1 := by
  simp [simpleRoot, i.left_ne_right.symm]

theorem simpleRoot_of_ne (i : AdjacentPosition n) {j : Fin n} (hl : j ≠ i.left)
    (hr : j ≠ i.right) : simpleRoot i j = 0 := by
  simp [simpleRoot, hl, hr]

/-- `πᵢ(x^μ)`. -/
def laurentString (i : AdjacentPosition n) (μ : Demazure.Weight n) : Demazure.Laurent n :=
  if μ i.right ≤ μ i.left then
    ∑ k ∈ Finset.range ((μ i.left - μ i.right).toNat + 1),
      AddMonoidAlgebra.single (μ - k • simpleRoot i) 1
  else
    -∑ k ∈ Finset.range ((μ i.right - μ i.left - 1).toNat),
      AddMonoidAlgebra.single (μ + (k + 1) • simpleRoot i) 1

/-- **The Demazure operator `πᵢ` on Laurent polynomials**, extended linearly from
`FlagVarieties.laurentString`. -/
def laurentIsobaric (i : AdjacentPosition n) (f : Demazure.Laurent n) : Demazure.Laurent n :=
  Finsupp.sum f.coeff fun μ c => c • laurentString i μ

/-- The operator `π̄ᵢ = πᵢ - 1`. -/
def laurentAtomOperator (i : AdjacentPosition n) (f : Demazure.Laurent n) : Demazure.Laurent n :=
  laurentIsobaric i f - f

theorem laurentIsobaric_single (i : AdjacentPosition n) (μ : Demazure.Weight n) (c : ℤ) :
    laurentIsobaric i (AddMonoidAlgebra.single μ c) = c • laurentString i μ := by
  rw [laurentIsobaric, AddMonoidAlgebra.coeff_single]
  exact Finsupp.sum_single_index (zero_smul _ _)

theorem laurentIsobaric_add (i : AdjacentPosition n) (f g : Demazure.Laurent n) :
    laurentIsobaric i (f + g) = laurentIsobaric i f + laurentIsobaric i g := by
  rw [laurentIsobaric, laurentIsobaric, laurentIsobaric, AddMonoidAlgebra.coeff_add]
  exact Finsupp.sum_add_index' (fun _ => zero_smul _ _) fun _ _ _ => add_smul _ _ _

theorem laurentIsobaric_zero (i : AdjacentPosition n) : laurentIsobaric i 0 = 0 := by
  rw [laurentIsobaric, AddMonoidAlgebra.coeff_zero]
  exact Finsupp.sum_zero_index

theorem exponentWeight_apply (a : Fin n →₀ ℕ) (j : Fin n) : exponentWeight a j = (a j : ℤ) :=
  rfl

/-- The exponents of a descending string. -/
theorem exponentWeight_replace_sub (a : Fin n →₀ ℕ) (i : AdjacentPosition n) (k : ℕ)
    (hk : k ≤ a i.left) :
    exponentWeight (replaceAdjacentExponents a i (a i.left - k) (a i.right + k)) =
      exponentWeight a - k • simpleRoot i := by
  funext j
  simp only [Pi.sub_apply, Pi.smul_apply, exponentWeight_apply]
  by_cases hl : j = i.left
  · subst hl
    rw [replaceAdjacentExponents_left, simpleRoot_left, nsmul_eq_mul]
    push_cast [hk]
    ring
  · by_cases hr : j = i.right
    · subst hr
      rw [replaceAdjacentExponents_right, simpleRoot_right, nsmul_eq_mul]
      push_cast
      ring
    · rw [replaceAdjacentExponents_of_ne _ _ _ _ _ hl hr, simpleRoot_of_ne i hl hr, smul_zero,
        sub_zero]

/-- The exponents of an ascending string. -/
theorem exponentWeight_replace_add (a : Fin n →₀ ℕ) (i : AdjacentPosition n) (k : ℕ)
    (hk : k + 1 ≤ a i.right) :
    exponentWeight (replaceAdjacentExponents (Finsupp.single i.left 1 + a) i
        ((Finsupp.single i.left 1 + a : Fin n →₀ ℕ) i.left + k)
        ((Finsupp.single i.left 1 + a : Fin n →₀ ℕ) i.right - 1 - k)) =
      exponentWeight a + (k + 1) • simpleRoot i := by
  have hr0 : (Finsupp.single i.left 1 + a : Fin n →₀ ℕ) i.right = a i.right := by
    simp [i.left_ne_right.symm]
  have hl0 : (Finsupp.single i.left 1 + a : Fin n →₀ ℕ) i.left = a i.left + 1 := by
    simp [Nat.add_comm]
  funext j
  simp only [Pi.add_apply, Pi.smul_apply, exponentWeight_apply]
  by_cases hl : j = i.left
  · subst hl
    rw [replaceAdjacentExponents_left, simpleRoot_left, hl0, nsmul_eq_mul]
    push_cast
    ring
  · by_cases hr : j = i.right
    · subst hr
      rw [replaceAdjacentExponents_right, simpleRoot_right, hr0, nsmul_eq_mul]
      have : a i.right - 1 - k = a i.right - (k + 1) := by omega
      rw [this]
      push_cast [hk]
      ring
    · rw [replaceAdjacentExponents_of_ne _ _ _ _ _ hl hr, simpleRoot_of_ne i hl hr, smul_zero,
        add_zero, Finsupp.add_apply, Finsupp.single_apply, ite_eq_right (Ne.symm hl), zero_add]

theorem isobaric_monomial_eq (i : AdjacentPosition n) (a : Fin n →₀ ℕ) :
    isobaric i (MvPolynomial.monomial a 1) =
      monomialDividedDifference i (Finsupp.single i.left 1 + a) := by
  unfold isobaric
  rw [MvPolynomial.X, MvPolynomial.monomial_mul_monomial, one_mul,
    adjacentDividedDifference_monomial_one]

/-- `πᵢ` on a polynomial monomial. -/
theorem toLaurent_isobaric_monomial (i : AdjacentPosition n) (a : Fin n →₀ ℕ) :
    toLaurent (isobaric i (MvPolynomial.monomial a 1)) = laurentString i (exponentWeight a) := by
  by_cases h : a i.right ≤ a i.left
  · rw [isobaric_monomial i a h, map_sum, laurentString, ite_eq_left (by
      simp only [exponentWeight_apply]; exact_mod_cast h)]
    have hlen : ((exponentWeight a i.left - exponentWeight a i.right).toNat + 1) =
        a i.left - a i.right + 1 := by
      simp only [exponentWeight_apply]
      omega
    rw [hlen]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    rw [toLaurent_monomial, exponentWeight_replace_sub a i k (by omega)]
  · rw [not_le] at h
    have hr0 : (Finsupp.single i.left 1 + a : Fin n →₀ ℕ) i.right = a i.right := by
      simp [i.left_ne_right.symm]
    have hl0 : (Finsupp.single i.left 1 + a : Fin n →₀ ℕ) i.left = a i.left + 1 := by
      simp [Nat.add_comm]
    rw [isobaric_monomial_eq, monomialDividedDifference, laurentString, ite_eq_right (by
      simp only [exponentWeight_apply]; exact_mod_cast not_le.mpr h)]
    have hlen : (exponentWeight a i.right - exponentWeight a i.left - 1).toNat =
        a i.right - a i.left - 1 := by
      simp only [exponentWeight_apply]
      omega
    rw [hlen, dite_eq_right (by rw [hl0, hr0]; omega)]
    by_cases h2 : a i.left + 1 < a i.right
    · rw [dite_eq_left (by rw [hl0, hr0]; exact h2), map_neg, map_sum, hl0, hr0]
      have hlen' : a i.right - (a i.left + 1) = a i.right - a i.left - 1 := by omega
      rw [hlen']
      congr 1
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk' := Finset.mem_range.mp hk
      rw [toLaurent_monomial, ← hl0, ← hr0, exponentWeight_replace_add a i k (by omega)]
    · rw [dite_eq_right (by rw [hl0, hr0]; omega)]
      have h0 : a i.right - a i.left - 1 = 0 := by omega
      rw [h0, Finset.range_zero, Finset.sum_empty, neg_zero, map_zero]

/-- **`πᵢ` on Laurent polynomials extends the isobaric divided difference.** -/
theorem toLaurent_isobaric (i : AdjacentPosition n) (p : Demazure.Polynomial n) :
    toLaurent (isobaric i p) = laurentIsobaric i (toLaurent p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial a c =>
    rw [show MvPolynomial.monomial a c = c • MvPolynomial.monomial a (1 : ℤ) by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]]
    rw [isobaric_smul, map_zsmul, toLaurent_isobaric_monomial, map_zsmul, toLaurent_monomial,
      show c • (AddMonoidAlgebra.single (exponentWeight a) (1 : ℤ) : Demazure.Laurent n) =
        AddMonoidAlgebra.single (exponentWeight a) c by
        rw [AddMonoidAlgebra.smul_single', mul_one],
      laurentIsobaric_single]
  | add p q hp hq => rw [isobaric_add, map_add, hp, hq, map_add, laurentIsobaric_add]

/-- `π̄ᵢ` on Laurent polynomials extends the atom operator. -/
theorem toLaurent_atomOperator (i : AdjacentPosition n) (p : Demazure.Polynomial n) :
    toLaurent (atomOperator i p) = laurentAtomOperator i (toLaurent p) := by
  rw [atomOperator, map_sub, toLaurent_isobaric, laurentAtomOperator]

/-- `πᵢ(x^μ)` for `μ_{i+1} ≤ μᵢ + 1`: the string `x^μ, x^{μ − αᵢ}, …, x^{sᵢ μ}` (empty if
`μ_{i+1} = μᵢ + 1`). -/
theorem laurentIsobaric_single_one (i : AdjacentPosition n) (μ : Demazure.Weight n)
    (hμ : μ i.right ≤ μ i.left + 1) :
    laurentIsobaric i (AddMonoidAlgebra.single μ 1) =
      ∑ k ∈ Finset.range (μ i.left - μ i.right + 1).toNat,
        AddMonoidAlgebra.single (μ - k • simpleRoot i) 1 := by
  rw [laurentIsobaric_single, one_smul, laurentString]
  split_ifs with h
  · have h1 := Int.toNat_of_nonneg (show 0 ≤ μ i.left - μ i.right by omega)
    have h2 := Int.toNat_of_nonneg (show 0 ≤ μ i.left - μ i.right + 1 by omega)
    have h3 : (μ i.left - μ i.right + 1).toNat = (μ i.left - μ i.right).toNat + 1 := by omega
    rw [h3]
  · have h0 : (μ i.left - μ i.right + 1).toNat = 0 := by omega
    have h1 : (μ i.right - μ i.left - 1).toNat = 0 := by omega
    rw [h0, h1, Finset.range_zero, Finset.sum_empty, Finset.sum_empty, neg_zero]

end LaurentOperators

/-! ### The torus on `H⁰(X_{sᵢ}, 𝓛(η))` -/

section Torus

variable (R : Type*) [CommRing R] {n : ℕ} (i : ℕ) (hi : i + 1 < n)

/-- The adjacent position of the rows `i`, `i + 1`. -/
def adjacentOfLt : AdjacentPosition n :=
  ⟨rowA n i hi, hi⟩

variable {R i}

theorem adjacentOfLt_left : (adjacentOfLt i hi).left = rowA n i hi :=
  rfl

theorem adjacentOfLt_right : (adjacentOfLt i hi).right = rowB n i hi :=
  rfl

/-- Composing a point with left translation multiplies its matrix on the left by `g⁻¹`. -/
theorem glPointOfMatrix_comp_leftTranslHom {A : Type*} [CommRing A] [Algebra R A]
    (g : GL (Fin n) R) (L : Matrix (Fin n) (Fin n) A) (hL : IsUnit L.det)
    (hgL : IsUnit ((((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R).map (algebraMap R A)) *
      L).det) :
    (glPointOfMatrix R L hL).comp (GLRep.leftTranslHom R n g) =
      glPointOfMatrix R ((((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R).map
        (algebraMap R A)) * L) hgL := by
  refine genericMatrix_algHom_ext ?_
  ext r c
  rw [Matrix.map_apply, AlgHom.comp_apply, genericMatrix_map_glPointOfMatrix]
  have h := congrFun (congrFun (pointMatrix_leftTranslHom R n g) r) c
  change GLRep.leftTranslHom R n g (genericMatrix R n r c) = _ at h
  rw [h, Matrix.mul_apply, map_sum, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, Matrix.map_apply, Matrix.map_apply, AlgHom.commutes]
  exact congrArg _ (congrFun (congrFun (genericMatrix_map_glPointOfMatrix R L hL) k) c)

/-- The diagonal matrix `t⁻¹` over `R[τ]`. -/
abbrev torusInvMatrix (t : Fin n → Rˣ) : Matrix (Fin n) (Fin n) R[X] :=
  Matrix.diagonal fun k => C (((t k)⁻¹ : Rˣ) : R)

theorem isUnit_det_torusInvMatrix (t : Fin n → Rˣ) : IsUnit (torusInvMatrix t).det := by
  rw [Matrix.det_diagonal]
  exact Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one
    fun k _ => (Units.isUnit _).map (C : R →+* R[X])

theorem torusInvMatrix_blockTriangular (t : Fin n → Rˣ) {α : Type*} [Preorder α]
    (b : Fin n → α) :
    (torusInvMatrix t).BlockTriangular b :=
  Matrix.blockTriangular_diagonal _

theorem torusInv_mul_lowerLineMatrix (t : Fin n → Rˣ) :
    torusInvMatrix t * lowerLineMatrix i hi (X : R[X]) =
      lowerLineMatrix i hi (C ((t (rowA n i hi) : R) * ((t (rowB n i hi))⁻¹ : Rˣ)) * X) *
        torusInvMatrix t := by
  have hAB := rowA_ne_rowB n i hi
  have key : (((t (rowB n i hi))⁻¹ : Rˣ) : R) =
      ((t (rowA n i hi) : R) * ((t (rowB n i hi))⁻¹ : Rˣ)) * ((t (rowA n i hi))⁻¹ : Rˣ) := by
    rw [mul_comm (t (rowA n i hi) : R), mul_assoc, Units.mul_inv, mul_one]
  refine Matrix.ext fun r c => ?_
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  simp only [lowerLineMatrix, Matrix.transvection, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply]
  split_ifs with h1 h2 h2
  · exact absurd (h2.2.trans (h1.symm.trans h2.1.symm)) hAB
  · subst h1
    ring
  · obtain ⟨rfl, rfl⟩ := h2
    conv_lhs => rw [key]
    simp only [C_mul]
    ring
  · ring

theorem isUnit_det_torusInv_mul_lowerLineMatrix (t : Fin n → Rˣ) :
    IsUnit (torusInvMatrix t * lowerLineMatrix i hi (X : R[X])).det := by
  rw [Matrix.det_mul]
  exact (isUnit_det_torusInvMatrix t).mul (isUnit_det_lowerLineMatrix i hi _)

theorem coe_inv_borelTorus_map (t : Fin n → Rˣ) :
    (((((GLRep.borelTorus R n t : GLRep.borel R n) : GL (Fin n) R)⁻¹ : GL (Fin n) R) :
      Matrix (Fin n) (Fin n) R).map (algebraMap R R[X])) = torusInvMatrix t := by
  rw [GLRep.coe_borelTorus, ← map_inv, diagGL_coe, Matrix.diagonal_map (map_zero _)]
  rfl

theorem glPointOfMatrix_congr' {A : Type*} [CommRing A] [Algebra R A]
    {M M' : Matrix (Fin n) (Fin n) A} (h : M = M') (hM : IsUnit M.det) (hM' : IsUnit M'.det) :
    glPointOfMatrix R M hM = glPointOfMatrix R M' hM' := by
  subst h
  rfl

theorem units_map_C_borelCharacter_inv (η : Fin n → ℤ) (t : Fin n → Rˣ) :
    ((((∏ k, Units.map (C : R →+* R[X]).toMonoidHom ((t k)⁻¹) ^ η k)⁻¹ : R[X]ˣ)) : R[X]) =
      C (weightCharHom R η t) := by
  have h : (∏ k, Units.map (C : R →+* R[X]).toMonoidHom ((t k)⁻¹) ^ η k)⁻¹ =
      Units.map (C : R →+* R[X]).toMonoidHom (weightChar R η t) := by
    rw [weightChar_apply, torusCharacter_def, map_prod, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [map_zpow, map_inv, inv_zpow', zpow_neg, inv_inv]
  rw [h, Units.coe_map, weightCharHom_apply]
  rfl

/-- **The torus on `𝒪(Pᵢ)` restricted to the line `1 + τ E_{i+1,i}`**: for a semi-invariant `f` of
weight `η`, `(t · f)(1 + τ E_{i+1,i}) = η(t) f(1 + c τ E_{i+1,i})` with `c = tᵢ t_{i+1}⁻¹`. -/
theorem lowerEval_leftTranslQuot_borelTorus {η : Fin n → ℤ} {f : ParabolicCoord R n i}
    (hf : IsParabolicSemiInvariant η f) (t : Fin n → Rˣ) :
    lowerEval R i hi (leftTranslQuot (parabolicIdeal R n i)
        (isLeftTranslStable_parabolicIdeal R n i) (GLRep.borelTorus R n t) f) =
      C (weightCharHom R η t) *
        aeval (C ((t (rowA n i hi) : R) * ((t (rowB n i hi))⁻¹ : Rˣ)) * X)
          (lowerEval R i hi f) := by
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective f
  set c : R := (t (rowA n i hi) : R) * ((t (rowB n i hi))⁻¹ : Rˣ)
  have hL := isUnit_det_lowerLineMatrix i hi (X : R[X])
  have hDL := isUnit_det_torusInv_mul_lowerLineMatrix hi t
  have hbDL : (torusInvMatrix t * lowerLineMatrix i hi (X : R[X])).BlockTriangular
      (parabolicBlock n i) :=
    (torusInvMatrix_blockTriangular t _).mul (lowerLineMatrix_blockTriangular i hi _)
  have e1 : ∀ x : GLCoord R n, lowerEval R i hi (Ideal.Quotient.mk (parabolicIdeal R n i) x) =
      glPointOfMatrix R (lowerLineMatrix i hi (X : R[X])) hL x := fun _ => rfl
  -- left translation by `t` moves the line to `t⁻¹ (1 + τ E_{i+1,i}) = (1 + c τ E_{i+1,i}) t⁻¹`
  have h1 : lowerEval R i hi (leftTranslQuot (parabolicIdeal R n i)
      (isLeftTranslStable_parabolicIdeal R n i) (GLRep.borelTorus R n t)
        (Ideal.Quotient.mk _ g)) =
      parabolicPointOfMatrix i (torusInvMatrix t * lowerLineMatrix i hi (X : R[X])) hDL hbDL
        (Ideal.Quotient.mk _ g) := by
    rw [leftTranslQuot_mk, e1, ← AlgHom.comp_apply, glPointOfMatrix_comp_leftTranslHom _ _ hL
      (by rw [coe_inv_borelTorus_map]; exact hDL),
      glPointOfMatrix_congr' (congrArg (· * lowerLineMatrix i hi (X : R[X]))
        (coe_inv_borelTorus_map t)) _ hDL]
    rfl
  have hcomm := torusInv_mul_lowerLineMatrix hi t
  have hL' := isUnit_det_lowerLineMatrix i hi (C c * X)
  have hbL' := lowerLineMatrix_blockTriangular i hi (C c * X)
  have hD := isUnit_det_torusInvMatrix t
  have hDu := torusInvMatrix_blockTriangular t id
  have hLD : IsUnit (lowerLineMatrix i hi (C c * X) * torusInvMatrix t).det := by
    rw [← hcomm]; exact hDL
  have hbLD : (lowerLineMatrix i hi (C c * X) * torusInvMatrix t).BlockTriangular
      (parabolicBlock n i) := by
    rw [← hcomm]; exact hbDL
  rw [h1, parabolicPointOfMatrix_congr i hcomm hDL hbDL hLD hbLD,
    hf.eval_mul _ _ hL' hbL' hD hDu hLD hbLD]
  -- the value on the line `1 + c τ E_{i+1,i}` and the value of `η⁻¹` at `t⁻¹`
  have h2 : parabolicPointOfMatrix i (lowerLineMatrix i hi (C c * X)) hL' hbL'
      (Ideal.Quotient.mk _ g) = aeval (C c * X) (lowerEval R i hi (Ideal.Quotient.mk _ g)) := by
    rw [← AlgHom.comp_apply, comp_lowerEval]
    exact congrFun (congrArg DFunLike.coe (parabolicPointOfMatrix_congr i
      (by rw [aeval_X]) hL' hbL' _ _)) _
  have h3 : borelPointOfMatrix R (torusInvMatrix t) hD hDu
      (((borelCharacterUnit R n η)⁻¹ : (BorelCoord R n)ˣ) : BorelCoord R n) =
      C (weightCharHom R η t) := by
    rw [borelPointOfMatrix_inv_borelCharacterUnit (R := R) (torusInvMatrix t) hD hDu
      (fun k => Units.map (C : R →+* R[X]).toMonoidHom ((t k)⁻¹))
      (fun k => by
        rw [Units.coe_map]
        exact (Matrix.diagonal_apply_eq (fun k => C (((t k)⁻¹ : Rˣ) : R)) k).symm) η]
    exact units_map_C_borelCharacter_inv η t
  rw [h2, h3, mul_comm]

/-- The torus on `H⁰(X_{sᵢ}, 𝓛(η))`, read on the polynomials `f(1 + τ E_{i+1,i})`. -/
theorem simpleSchubertSectionsEquiv_borelTorus (η : Fin n → ℤ) (t : Fin n → Rˣ)
    (s : sections R n (simpleSchubert R n i hi) η) :
    (simpleSchubertSectionsEquiv R i hi η (sectionsRep R n (simpleSchubert R n i hi) η
        (isLeftTranslStable_preimageIdeal_simpleSchubert R n i hi) (GLRep.borelTorus R n t) s) :
        R[X]) =
      C (weightCharHom R η t) *
        aeval (C ((t (rowA n i hi) : R) * ((t (rowB n i hi))⁻¹ : Rˣ)) * X)
          (simpleSchubertSectionsEquiv R i hi η s : R[X]) := by
  simp only [simpleSchubertSectionsEquiv, LinearEquiv.trans_apply]
  rw [sectionsEquivSemiInvariants_sectionsRep, semiInvariantsEquivOfEq_semiInvariantsRep
    (preimageIdeal_simpleSchubert R n i hi) _ (isLeftTranslStable_parabolicIdeal R n i)]
  set y := semiInvariantsEquivOfEq (preimageIdeal_simpleSchubert R n i hi) η
    (sectionsEquivSemiInvariants R n _ η s)
  exact lowerEval_leftTranslQuot_borelTorus hi
    ((mem_quotientSemiInvariants_parabolicIdeal_iff η y.1).mp y.2) t

variable (R) in
/-- The basis `1, τ, …, τ^{m-1}` of the polynomials of degree `< m`. -/
def degreeLTBasis (m : ℕ) : Module.Basis (Fin m) R (degreeLT R m) :=
  (Pi.basisFun R (Fin m)).map (degreeLTEquiv R m).symm

theorem coe_degreeLTBasis (m : ℕ) (k : Fin m) : (degreeLTBasis R m k : R[X]) = X ^ (k : ℕ) := by
  have hmem : (X ^ (k : ℕ) : R[X]) ∈ degreeLT R m := by
    rw [mem_degreeLT]
    exact (degree_X_pow_le _).trans_lt (by exact_mod_cast k.2)
  have h : degreeLTBasis R m k = ⟨X ^ (k : ℕ), hmem⟩ := by
    rw [degreeLTBasis, Module.Basis.map_apply, Pi.basisFun_apply, LinearEquiv.symm_apply_eq]
    funext j
    simp only [degreeLTEquiv, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, coeff_X_pow,
      Pi.single_apply, Fin.ext_iff]
  rw [h]

variable (R i) in
/-- **The basis of `H⁰(X_{sᵢ}, 𝓛(η))`** corresponding to `1, τ, …, τᵈ`. -/
def simpleSchubertBasis (η : Fin n → ℤ) :
    Module.Basis (Fin (η (rowB n i hi) - η (rowA n i hi) + 1).toNat) R
      (sections R n (simpleSchubert R n i hi) η) :=
  (degreeLTBasis R _).map (simpleSchubertSectionsEquiv R i hi η).symm

theorem simpleSchubertSectionsEquiv_basis (η : Fin n → ℤ)
    (k : Fin (η (rowB n i hi) - η (rowA n i hi) + 1).toNat) :
    (simpleSchubertSectionsEquiv R i hi η (simpleSchubertBasis R i hi η k) : R[X]) =
      X ^ (k : ℕ) := by
  rw [simpleSchubertBasis, Module.Basis.map_apply, LinearEquiv.apply_symm_apply,
    coe_degreeLTBasis]

theorem weightChar_neg' (μ : Fin n → ℤ) (t : Fin n → Rˣ) :
    weightChar R (-μ) t = (weightChar R μ t)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← MonoidHom.mul_apply, ← weightChar_add, neg_add_cancel,
    weightChar_zero, MonoidHom.one_apply]

theorem weightCharHom_add_nsmul_simpleRoot (η : Fin n → ℤ) (k : ℕ) (t : Fin n → Rˣ) :
    weightCharHom R (η + k • simpleRoot (adjacentOfLt i hi)) t =
      weightCharHom R η t * ((t (rowA n i hi) : R) * ((t (rowB n i hi))⁻¹ : Rˣ)) ^ k := by
  have hα : ((weightChar R (simpleRoot (adjacentOfLt i hi)) t : Rˣ) : R) =
      (t (rowA n i hi) : R) * ((t (rowB n i hi))⁻¹ : Rˣ) := by
    rw [simpleRoot, sub_eq_add_neg, weightChar_add, MonoidHom.mul_apply, weightChar_neg',
      weightChar_single, weightChar_single, Units.val_mul]
    rfl
  rw [weightCharHom_apply, weightCharHom_apply, weightChar_add, MonoidHom.mul_apply,
    Units.val_mul]
  congr 1
  induction k with
  | zero => rw [zero_smul, weightChar_zero, MonoidHom.one_apply, Units.val_one, pow_zero]
  | succ k ih => rw [succ_nsmul, weightChar_add, MonoidHom.mul_apply, Units.val_mul, ih, hα,
      pow_succ]

/-- **The torus acts diagonally on `H⁰(X_{sᵢ}, 𝓛(η))`**: the basis vector `τᵏ` has weight
`η + k αᵢ`. -/
theorem sectionsRep_borelTorus_simpleSchubertBasis (η : Fin n → ℤ) (t : Fin n → Rˣ)
    (k : Fin (η (rowB n i hi) - η (rowA n i hi) + 1).toNat) :
    sectionsRep R n (simpleSchubert R n i hi) η
        (isLeftTranslStable_preimageIdeal_simpleSchubert R n i hi) (GLRep.borelTorus R n t)
        (simpleSchubertBasis R i hi η k) =
      weightCharHom R (η + (k : ℕ) • simpleRoot (adjacentOfLt i hi)) t •
        simpleSchubertBasis R i hi η k := by
  apply (simpleSchubertSectionsEquiv R i hi η).injective
  apply Subtype.ext
  rw [simpleSchubertSectionsEquiv_borelTorus, simpleSchubertSectionsEquiv_basis,
    LinearEquiv.map_smul, Submodule.coe_smul, simpleSchubertSectionsEquiv_basis,
    weightCharHom_add_nsmul_simpleRoot, map_pow, aeval_X, smul_eq_C_mul]
  simp only [map_mul, map_pow]
  ring

/-! ### Characters -/

section Field

variable {K : Type*} [Field K] [Infinite K]

/-- **`ch H⁰(X_{sᵢ}, 𝓛(η)) = πᵢ(x^{−η})`** for `η_{i+1} - ηᵢ ≥ -1` (in the convention `ch M =
Σ dim M_μ x^{−μ}`). -/
theorem ch_sections_simpleSchubert (η : Fin n → ℤ)
    (hd : η (rowA n i hi) ≤ η (rowB n i hi) + 1) :
    ch (sectionsRep K n (simpleSchubert K n i hi) η
        (isLeftTranslStable_preimageIdeal_simpleSchubert K n i hi)) =
      laurentIsobaric (adjacentOfLt i hi) (AddMonoidAlgebra.single (-η) 1) := by
  rw [ch_eq_sum_of_basis (simpleSchubertBasis K i hi η)
      (fun k => η + (k : ℕ) • simpleRoot (adjacentOfLt i hi))
      (fun t k => sectionsRep_borelTorus_simpleSchubertBasis hi η t k),
    laurentIsobaric_single_one _ _ (by
      simp only [Pi.neg_apply, adjacentOfLt_left, adjacentOfLt_right]; omega),
    Fin.sum_univ_eq_sum_range (fun k => AddMonoidAlgebra.single
      (-(η + k • simpleRoot (adjacentOfLt i hi))) (1 : ℤ))]
  have hm : (η (rowB n i hi) - η (rowA n i hi) + 1).toNat =
      ((-η) (adjacentOfLt i hi).left - (-η) (adjacentOfLt i hi).right + 1).toNat := by
    simp only [Pi.neg_apply, adjacentOfLt_left, adjacentOfLt_right]
    congr 1
    ring
  rw [hm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [neg_add', sub_eq_add_neg]

set_option synthInstance.maxHeartbeats 200000 in
variable (K i) in
/-- **`H_{sᵢ}(K_η) ≅ H⁰(X_{sᵢ}, 𝓛(η))` as representations of `B(K)`.** -/
def rankOneInductionSectionsRepEquiv (η : Fin n → ℤ) :
    (rankOneInductionRep K n i (charCoaction K η)).Equiv
      (sectionsRep K n (simpleSchubert K n i hi) η
        (isLeftTranslStable_preimageIdeal_simpleSchubert K n i hi)) :=
  .mk (rankOneInductionSectionsEquiv K n i hi η) fun b => LinearMap.ext fun x =>
    rankOneInductionSectionsEquiv_rep hi η b x

set_option synthInstance.maxHeartbeats 200000 in
/-- **`ch H_{sᵢ}(K_η) = πᵢ(x^{−η})`**: rank-one induction of a character acts on characters as the
Demazure operator, for `η_{i+1} - ηᵢ ≥ -1`. -/
theorem ch_rankOneInduction_charCoaction (η : Fin n → ℤ)
    (hd : η (rowA n i hi) ≤ η (rowB n i hi) + 1) :
    @ch n K _ _ (Submodule.addCommGroup _) _ (rankOneInductionRep K n i (charCoaction K η)) =
      laurentIsobaric (adjacentOfLt i hi) (AddMonoidAlgebra.single (-η) 1) := by
  rw [ch_eq_of_equiv (rankOneInductionSectionsRepEquiv (K := K) (i := i) hi η),
    ch_sections_simpleSchubert hi η hd]

end Field


end Torus

/-! ### The Demazure recurrences in Laurent form -/

section Recurrences

variable {n : ℕ}

namespace SectionRep

/-- **`ch P(−sᵢu) = πᵢ ch P(−u)`** for `uᵢ > u_{i+1}`, with `πᵢ` the Demazure operator on Laurent
polynomials. -/
theorem ch_dualJoseph_step_laurent (u : Fin n → ℕ) (i : AdjacentPosition n)
    (h : u i.right < u i.left) :
    ch (dualJoseph (negWeight (swapComposition u i))) =
      laurentIsobaric i (ch (dualJoseph (negWeight u))) := by
  rw [ch_dualJoseph_step u i h, toLaurent_isobaric, ch_dualJoseph_negWeight]

/-- **`ch Q(−sᵢu) = π̄ᵢ ch Q(−u)`** for `uᵢ > u_{i+1}`. -/
theorem ch_minimalRelativeSchubert_step_laurent (u : Fin n → ℕ) (i : AdjacentPosition n)
    (h : u i.right < u i.left) :
    ch (minimalRelativeSchubert (negWeight (swapComposition u i))) =
      laurentAtomOperator i (ch (minimalRelativeSchubert (negWeight u))) := by
  rw [ch_minimalRelativeSchubert_step u i h, toLaurent_atomOperator,
      ch_minimalRelativeSchubert_negWeight]

end SectionRep

/-- **`ch P(−sᵢu) = πᵢ ch P(−u)` for the sheaf-theoretic modules** `P(ν) = H⁰(X_σ, 𝓛(η))`. -/
theorem ch_dualJoseph_step_laurent (u : Fin n → ℕ) (i : AdjacentPosition n)
    (h : u i.right < u i.left) :
    ch (dualJoseph (negWeight (swapComposition u i))) =
      laurentIsobaric i (ch (dualJoseph (negWeight u))) := by
  rw [ch_eq_of_equiv (dualJosephEquiv _), ch_eq_of_equiv (dualJosephEquiv _),
    SectionRep.ch_dualJoseph_step_laurent u i h]

end Recurrences

/-! ### `P(ν)` as a rank-one induction when `σ(ν) = sᵢ` -/

section Geometric

variable {n : ℕ} (i : ℕ) (hi : i + 1 < n)

/-- Sections over equal closed subschemes are equivalent representations. -/
def sectionsRepEquivOfEq {R : Type*} [CommRing R] {I I' : (FlagScheme R n).IdealSheafData}
    (h : I = I') (η : Fin n → ℤ) (hJ : IsLeftTranslStable (preimageIdeal R n I))
    (hJ' : IsLeftTranslStable (preimageIdeal R n I')) :
    (sectionsRep R n I η hJ).Equiv (sectionsRep R n I' η hJ') := by
  subst h
  exact Representation.Equiv.refl _

set_option synthInstance.maxHeartbeats 200000 in
/-- Rank-one inductions of equal characters are equivalent representations. -/
def rankOneInductionRepEquivOfEq {R : Type*} [CommRing R] {η η' : Fin n → ℤ} (h : η = η') :
    (rankOneInductionRep R n i (charCoaction R η)).Equiv
      (rankOneInductionRep R n i (charCoaction R η')) := by
  subst h
  exact Representation.Equiv.refl _

set_option synthInstance.maxHeartbeats 200000 in
/-- **`P(ν) = H_{sᵢ}(ℂ_{η(ν)})`** when `σ(ν) = sᵢ`: the sheaf-theoretic dual Joseph module is the
rank-one induction of the character `η(ν)`, as representations of `B`. -/
def dualJosephRankOneEquiv (ν : Fin n → ℤ)
    (h : schubertIndex ν = simpleReflection n i hi) :
    (dualJoseph ν).Equiv (rankOneInductionRep ℂ n i (charCoaction ℂ (fibreWeight ν))) :=
  (sectionsRepEquivOfEq (congrArg (schubertVariety ℂ n) h) _ _ _).trans
    (rankOneInductionSectionsRepEquiv (K := ℂ) (i := i) hi _).symm

theorem infinite_complex : Infinite ℂ :=
  Infinite.of_injective (Nat.cast : ℕ → ℂ) Nat.cast_injective

/-- **`ch P(ν) = πᵢ(x^{−η(ν)})`** when `σ(ν) = sᵢ`. -/
theorem ch_dualJoseph_of_eq_simpleReflection (ν : Fin n → ℤ)
    (h : schubertIndex ν = simpleReflection n i hi) :
    ch (dualJoseph ν) =
      laurentIsobaric (adjacentOfLt i hi) (AddMonoidAlgebra.single (-fibreWeight ν) 1) := by
  have := infinite_complex
  have hle : fibreWeight ν (rowA n i hi) ≤ fibreWeight ν (rowB n i hi) :=
    isAntidominant_fibreWeight ν (Fin.mk_le_mk.mpr (Nat.le_succ i))
  rw [ch_eq_of_equiv (sectionsRepEquivOfEq (congrArg (schubertVariety ℂ n) h) _ _
    (isLeftTranslStable_preimageIdeal_simpleSchubert ℂ n i hi)),
    ch_sections_simpleSchubert hi _ (by omega)]

/-! ### The first step of the recurrence for a partition -/

/-- For a partition `u` with `uᵢ > u_{i+1}`, the Schubert index of `−sᵢu` is `sᵢ`. -/
theorem schubertIndex_negWeight_swap (u : Fin n → ℕ) (hu : Antitone u)
    (h : u (rowB n i hi) < u (rowA n i hi)) :
    schubertIndex (negWeight (swapComposition u (adjacentOfLt i hi))) =
      simpleReflection n i hi := by
  set σ := simpleReflection n i hi
  have hσ : ∀ j, swapComposition u (adjacentOfLt i hi) (σ j) = u j := fun j => by
    simp only [swapComposition, adjacentTransposition, adjacentOfLt_left, adjacentOfLt_right, σ,
      simpleReflection]
    exact congrArg u (Equiv.swap_apply_self _ _ j)
  have hAB : (rowA n i hi : Fin n) < rowB n i hi := Fin.mk_lt_mk.mpr (Nat.lt_succ_self i)
  symm
  rw [eq_schubertIndex_iff]
  refine ⟨fun a b hab => ?_, fun a b hab heq => ?_⟩
  · simp only [Function.comp_apply, negWeight, hσ]
    exact neg_le_neg (by exact_mod_cast hu hab)
  · simp only [negWeight, hσ, neg_inj, Nat.cast_inj] at heq
    have hA : a ≠ rowA n i hi := by
      rintro rfl
      have hb : rowB n i hi ≤ b := Fin.le_iff_val_le_val.mpr (by
        have := Fin.lt_def.mp hab
        simp only at this ⊢
        omega)
      have := hu hb
      omega
    have hB : b ≠ rowB n i hi := by
      rintro rfl
      have ha : a ≤ rowA n i hi := Fin.le_iff_val_le_val.mpr (by
        have := Fin.lt_def.mp hab
        simp only at this ⊢
        omega)
      have := hu ha
      omega
    simp only [σ, simpleReflection]
    by_cases haB : a = rowB n i hi
    · subst haB
      have hbA : b ≠ rowA n i hi := by
        rintro rfl
        exact absurd hab (not_lt.mpr hAB.le)
      rw [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hbA hB]
      exact hAB.trans hab
    · rw [Equiv.swap_apply_of_ne_of_ne hA haB]
      by_cases hbA : b = rowA n i hi
      · subst hbA
        rw [Equiv.swap_apply_left]
        exact hab.trans hAB
      · rw [Equiv.swap_apply_of_ne_of_ne hbA hB]
        exact hab

/-- For a partition `u` with `uᵢ > u_{i+1}`, the fibre weight of `−sᵢu` is `−u`. -/
theorem fibreWeight_negWeight_swap (u : Fin n → ℕ) (hu : Antitone u)
    (h : u (rowB n i hi) < u (rowA n i hi)) :
    fibreWeight (negWeight (swapComposition u (adjacentOfLt i hi))) = negWeight u := by
  funext j
  rw [fibreWeight, Function.comp_apply, schubertIndex_negWeight_swap i hi u hu h]
  simp only [negWeight, swapComposition, adjacentTransposition, adjacentOfLt_left,
    adjacentOfLt_right, simpleReflection]
  exact congrArg (fun m : ℕ => -(m : ℤ)) (congrArg u (Equiv.swap_apply_self _ _ j))

set_option synthInstance.maxHeartbeats 200000 in
/-- **`P(−sᵢu) ≅ H_{sᵢ}(ℂ_{−u})`** for a partition `u` with `uᵢ > u_{i+1}`: the first step of the
Demazure recurrence is rank-one induction of the line `ℂ_{−u} = P(−u)`. -/
def dualJosephSwapEquiv (u : Fin n → ℕ) (hu : Antitone u)
    (h : u (rowB n i hi) < u (rowA n i hi)) :
    (dualJoseph (negWeight (swapComposition u (adjacentOfLt i hi)))).Equiv
      (rankOneInductionRep ℂ n i (charCoaction ℂ (negWeight u))) :=
  (dualJosephRankOneEquiv i hi _ (schubertIndex_negWeight_swap i hi u hu h)).trans
    (rankOneInductionRepEquivOfEq i (fibreWeight_negWeight_swap i hi u hu h))

/-- For a partition `u`, `P(−u)` is the line of weight `−u`: `ch P(−u) = x^u`. -/
theorem ch_dualJoseph_negWeight_of_antitone (u : Fin n → ℕ) (hu : Antitone u) :
    ch (dualJoseph (negWeight u)) =
      AddMonoidAlgebra.single (-negWeight u) 1 := by
  rw [ch_dualJoseph_negWeight, key_of_antitone u hu, compositionMonomial,
    toLaurent_monomial]
  congr 1
  funext j
  simp [exponentWeight_apply, negWeight]

set_option synthInstance.maxHeartbeats 200000 in
/-- **The geometric reading of `ch P(−sᵢu) = πᵢ ch P(−u)`** for a partition `u` with
`uᵢ > u_{i+1}`: `P(−sᵢu) ≅ H_{sᵢ}(P(−u))`, `P(−u)` being the line `ℂ_{−u}`, and rank-one induction
acts on characters as `πᵢ`. -/
theorem ch_dualJoseph_swap (u : Fin n → ℕ) (hu : Antitone u)
    (h : u (rowB n i hi) < u (rowA n i hi)) :
    ch (dualJoseph (negWeight (swapComposition u (adjacentOfLt i hi)))) =
        @ch n ℂ _ _ (Submodule.addCommGroup _) _
          (rankOneInductionRep ℂ n i (charCoaction ℂ (negWeight u))) ∧
      @ch n ℂ _ _ (Submodule.addCommGroup _) _
          (rankOneInductionRep ℂ n i (charCoaction ℂ (negWeight u))) =
        laurentIsobaric (adjacentOfLt i hi) (ch (dualJoseph (negWeight u))) := by
  have := infinite_complex
  refine ⟨ch_eq_of_equiv (dualJosephSwapEquiv i hi u hu h), ?_⟩
  rw [ch_rankOneInduction_charCoaction hi _ (by simp only [negWeight]; omega),
    ch_dualJoseph_negWeight_of_antitone u hu]

end Geometric

end

end FlagVarieties
