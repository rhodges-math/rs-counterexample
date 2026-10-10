import RSCounterexample.Paper.HighestWeight.LongestDemazure
import RSCounterexample.Paper.Representation.PolynomialCovariance
import RSCounterexample.Paper.PolynomialDiagonalWeights

/-!
# Highest-weight data of the flag-minor span (E4)

For `λ = shapeWeight m` (the dominant weight `dominantWeight m`):
* `v_λ = highestFlag m` has weight `λ` and is killed by `𝔫⁺` (`highestFlag_mem_weightSpace`,
  `highestFlag_upper_invariant`);
* `E_ab` shifts torus weights by `ε_a - ε_b` (`matrixUnitDerivation_mem_weightSpace`);
* the weight-`λ` space of `V = flagOrbitSpan m` is the line `ℂ·v_λ`
  (`flagOrbitSpan_inf_weightSpace`).

For the last point, `V = U(𝔫⁻)·v_λ` (E3), and lowering operators strictly increase the depth
`Σ_i i·μ_i` of a weight. So every element of `V` is `c·v_λ` plus a combination of monomials
of depth larger than that of `λ`.
-/

namespace Schubert.RS.HighestWeight

open Schubert.RS.Representation

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : ℕ}

/-- The dominant weight `λ = shapeWeight m`. -/
def dominantWeight (m : ColumnShape n) : Weight n := fun i => (shapeWeight m i : ℤ)

/-- `v_λ` is a torus weight vector of weight `λ`. -/
theorem highestFlag_mem_weightSpace (m : ColumnShape n) :
    highestFlag m ∈ torusWeightSpace (polynomialTorus n) (dominantWeight m) :=
  fun t => highestFlag_weight m t

/-- The character of the root `ε_a - ε_b` is `t_a / t_b`. -/
theorem integerWeightScalar_rootShift (a b : Fin n) (t : DiagonalTorus n) :
    integerWeightScalar (Pi.single a 1 - Pi.single b 1) t = rootScalar t a b := by
  have h1 : ∀ c : Fin n, ∏ i, (t i : ℂ) ^ ((Pi.single c (1 : ℤ) : Weight n) i) = t c := by
    intro c
    rw [Finset.prod_eq_single c]
    · simp
    · intro i _ hi
      simp [hi]
    · simp
  unfold integerWeightScalar rootScalar
  simp_rw [Pi.sub_apply, zpow_sub₀ (Units.ne_zero _)]
  rw [Finset.prod_div_distrib, h1, h1, Units.val_div_eq_div_val]

theorem torusMatrix_single (t : DiagonalTorus n) (a b : Fin n) :
    torusMatrix t (Matrix.single a b 1) = rootScalar t a b • Matrix.single a b 1 := by
  ext i j
  simp only [torusMatrix, Matrix.smul_apply, smul_eq_mul, Matrix.single_apply]
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    rfl
  · simp

/-- `E_ab` maps weight `μ` to weight `μ + ε_a - ε_b`. -/
theorem matrixUnitDerivation_mem_weightSpace (a b : Fin n) {μ : Weight n}
    {p : MatrixPolynomial n} (hp : p ∈ torusWeightSpace (polynomialTorus n) μ) :
    matrixUnitDerivation a b p ∈
      torusWeightSpace (polynomialTorus n) (μ + (Pi.single a 1 - Pi.single b 1)) := by
  intro t
  change rowAction (Matrix.diagonal fun i => (t i : ℂ)) (rowDerivation (Matrix.single a b 1) p) = _
  rw [rowDerivation_torus, torusMatrix_single]
  have hs : rowDerivation (rootScalar t a b • Matrix.single a b (1 : ℂ)) =
      rootScalar t a b • rowDerivation (Matrix.single a b 1) :=
    (rowDerivationLinear n).map_smul _ _
  have hp' : rowAction (Matrix.diagonal fun i => (t i : ℂ)) p = integerWeightScalar μ t • p :=
    hp t
  rw [hs, Derivation.smul_apply, hp', Derivation.map_smul, smul_smul, integerWeightScalar_add,
    integerWeightScalar_rootShift, mul_comm]
  rfl

/-- A monomial is a weight vector for the weight given by its row degrees. -/
theorem monomial_mem_weightSpace (d : (Fin n × Fin n) →₀ ℕ) (c : ℂ) :
    MvPolynomial.monomial d c ∈
      torusWeightSpace (polynomialTorus n) (matrixMonomialWeight d) := by
  intro t
  ext e
  rw [polynomialTorus_coeff_weight, MvPolynomial.coeff_smul, smul_eq_mul,
    MvPolynomial.coeff_monomial]
  split_ifs with h
  · rw [h]
  · rw [mul_zero, mul_zero]

/-- The depth `Σ_i i·μ_i` of a weight; lowering operators increase it. -/
def weightDepth (μ : Weight n) : ℤ := ∑ i : Fin n, (i : ℤ) * μ i

theorem weightDepth_rootShift (μ : Weight n) (a b : Fin n) :
    weightDepth (μ + (Pi.single a 1 - Pi.single b 1)) = weightDepth μ + a - b := by
  have h1 : ∀ c : Fin n, ∑ i : Fin n, (i : ℤ) * (Pi.single c (1 : ℤ) : Weight n) i = c := by
    intro c
    rw [Finset.sum_eq_single c]
    · simp
    · intro i _ hi
      simp [hi]
    · simp
  simp only [weightDepth, Pi.add_apply, Pi.sub_apply, mul_add, mul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, h1]
  ring

/-- Polynomials all of whose monomials have depth larger than `h`. -/
def deepSubmodule (h : ℤ) : Submodule ℂ (MatrixPolynomial n) where
  carrier := {q | ∀ e ∈ q.support, h < weightDepth (matrixMonomialWeight e)}
  zero_mem' := by intro e he; simp at he
  add_mem' := by
    intro p q hp hq e he
    rcases Finset.mem_union.mp (MvPolynomial.support_add he) with he | he
    · exact hp e he
    · exact hq e he
  smul_mem' := by
    intro c p hp e he
    exact hp e (MvPolynomial.support_smul he)

/-- All monomials of a weight vector have its weight. -/
theorem support_weight_of_mem_weightSpace {μ : Weight n} {p : MatrixPolynomial n}
    (hp : p ∈ torusWeightSpace (polynomialTorus n) μ) {e : (Fin n × Fin n) →₀ ℕ}
    (he : e ∈ p.support) : matrixMonomialWeight e = μ :=
  polynomial_support_weight p μ hp e (MvPolynomial.mem_support_iff.mp he)

/-- A lowering operator maps a weight-`μ` vector to a combination of monomials deeper than `μ`. -/
theorem matrixUnitDerivation_mem_deep_of_weight {a b : Fin n} (hba : b < a) {μ : Weight n}
    {p : MatrixPolynomial n} (hp : p ∈ torusWeightSpace (polynomialTorus n) μ) :
    matrixUnitDerivation a b p ∈ deepSubmodule (n := n) (weightDepth μ) := by
  intro e he
  rw [support_weight_of_mem_weightSpace (matrixUnitDerivation_mem_weightSpace a b hp) he,
    weightDepth_rootShift]
  have : (b : ℤ) < a := by exact_mod_cast hba
  omega

/-- Lowering operators preserve `deepSubmodule h`. -/
theorem matrixUnitDerivation_mem_deep {a b : Fin n} (hba : b < a) {h : ℤ}
    {q : MatrixPolynomial n} (hq : q ∈ deepSubmodule (n := n) h) :
    matrixUnitDerivation a b q ∈ deepSubmodule (n := n) h := by
  rw [MvPolynomial.as_sum q, map_sum]
  refine Submodule.sum_mem _ fun d hd => ?_
  have hmono := monomial_mem_weightSpace d (q.coeff d)
  have h1 := matrixUnitDerivation_mem_deep_of_weight hba hmono
  intro e he
  exact lt_trans (hq d hd) (h1 e he)

/-- E4: the weight-`λ` space of the flag-minor span is the line through `v_λ`. -/
theorem flagOrbitSpan_inf_weightSpace (m : ColumnShape n) :
    flagOrbitSpan m ⊓ torusWeightSpace (polynomialTorus n) (dominantWeight m) =
      ℂ ∙ highestFlag m := by
  apply le_antisymm
  · rintro q ⟨hqV, hqW⟩
    set v := highestFlag m
    let S : Submodule ℂ (MatrixPolynomial n) :=
      { carrier :=
          {q | ∃ c : ℂ, q - c • v ∈ deepSubmodule (n := n) (weightDepth (dominantWeight m))}
        add_mem' := by
          rintro x y ⟨c, hc⟩ ⟨d, hd⟩
          refine ⟨c + d, ?_⟩
          rw [show x + y - (c + d) • v = (x - c • v) + (y - d • v) by rw [add_smul]; abel]
          exact Submodule.add_mem _ hc hd
        zero_mem' := ⟨0, by rw [zero_smul, sub_zero]; exact Submodule.zero_mem _⟩
        smul_mem' := by
          rintro c x ⟨d, hd⟩
          refine ⟨c * d, ?_⟩
          rw [show c • x - (c * d) • v = c • (x - d • v) by rw [smul_sub, smul_smul]]
          exact Submodule.smul_mem _ c hd }
    have hVS : flagOrbitSpan m ≤ S := by
      rw [flagOrbitSpan_eq_lowerCyclic]
      refine lowerCyclic_le _ ⟨1, by rw [one_smul, sub_self]; exact Submodule.zero_mem _⟩ ?_
      rintro a b hba x ⟨c, hc⟩
      refine ⟨0, ?_⟩
      rw [zero_smul, sub_zero,
        show x = (x - c • v) + c • v by abel, map_add, Derivation.map_smul]
      exact Submodule.add_mem _ (matrixUnitDerivation_mem_deep hba hc)
        (Submodule.smul_mem _ c
          (matrixUnitDerivation_mem_deep_of_weight hba (highestFlag_mem_weightSpace m)))
    obtain ⟨c, hc⟩ := hVS hqV
    have hdiff : q - c • v ∈ torusWeightSpace (polynomialTorus n) (dominantWeight m) :=
      Submodule.sub_mem _ hqW (Submodule.smul_mem _ c (highestFlag_mem_weightSpace m))
    have hzero : q - c • v = 0 := by
      by_contra hne
      obtain ⟨e, he⟩ := (MvPolynomial.support_nonempty).mpr hne
      have h1 := hc e he
      rw [support_weight_of_mem_weightSpace hdiff he] at h1
      exact lt_irrefl _ h1
    rw [sub_eq_zero] at hzero
    rw [hzero]
    exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self v)
  · rw [Submodule.span_singleton_le_iff_mem]
    exact ⟨highestFlag_mem_orbitSpan m, highestFlag_mem_weightSpace m⟩

end
end Schubert.RS.HighestWeight
