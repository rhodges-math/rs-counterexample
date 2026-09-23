import Schubert.RS.CounterexampleExtraction

/-! Replace the root series by finite Laurent polynomials before any source
substitution. This avoids applying a Laurent map to an infinite series. -/

namespace Schubert.RS
noncomputable section
open Representation

theorem geometric_truncation_uniform {σ : Type*} [Fintype σ] [DecidableEq σ]
    (d : σ →₀ ℕ) (cut : σ) (hc : d cut = 1) (β : σ →₀ ℕ)
    (B : ℕ) (hB : ∀ i, β i ≤ B) :
    WindowEq β (∑ k : Fin (B+1), MvPowerSeries.monomial (k.val • d) 1) (rootGeometricSeries d) := by
  let γ : σ →₀ ℕ := Finsupp.onFinset Finset.univ (fun _ => B) (by intros; simp)
  have hγ (i : σ) : γ i = B := by simp [γ]
  have hw := geometric_truncation_window d cut hc γ
  change WindowEq γ (∑ k : Fin (B+1), MvPowerSeries.monomial (k.val • d) 1)
    (rootGeometricSeries d) at hw
  intro e he
  apply hw
  intro i
  rw [hγ]
  exact (he i).trans (hB i)

theorem rootCoordinateEmbedding_coeff {n : ℕ} (p : MvPolynomial (Fin (n-1)) ℤ)
    (d : RootDegree n) :
    (rootCoordinateEmbedding p).coeff (rootWeight d) = MvPolynomial.coeff d p := by
  change Finsupp.mapDomain rootWeight (AddMonoidAlgebra.coeff p) (rootWeight d) = _
  exact Finsupp.mapDomain_apply rootWeight_injective _ _

namespace Counterexample

def finiteRootFactor (B : ℕ) (r : PositiveRoot 28) : MvPolynomial (Fin 27) ℤ :=
  if coordinateClass r.val.1 = coordinateClass r.val.2 then
    1-MvPolynomial.monomial (rootDegree r.val.1 r.val.2) 1
  else if isSource r.val.1 ∧ ¬isSource r.val.2 then
    ∑ k : Fin (B+1), MvPolynomial.monomial (k.val • rootDegree r.val.1 r.val.2) 1
  else 1

theorem finiteRootFactor_window (B : ℕ) (hB : 8 ≤ B) (r : PositiveRoot 28) :
    WindowEq coefficientBox ((finiteRootFactor B r : MvPolynomial (Fin 27) ℤ) :
      MvPowerSeries (Fin 27) ℤ) (counterexampleRootFactor r) := by
  classical
  unfold finiteRootFactor counterexampleRootFactor
  split_ifs with hC hS
  · change WindowEq coefficientBox
      (MvPolynomial.coeToMvPowerSeries.ringHom (1-MvPolynomial.monomial (rootDegree r.val.1 r.val.2) 1)) _
    simp only [map_sub, map_one, MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coe_monomial]
    exact WindowEq.refl _ _
  · change WindowEq coefficientBox
      (MvPolynomial.coeToMvPowerSeries.ringHom (∑ k : Fin (B+1), _)) _
    simp only [map_sum, MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coe_monomial]
    apply geometric_truncation_uniform _ (rootFirstCut r.val.1 r.val.2 r.property)
      (rootDegree_first r.val.1 r.val.2 r.property)
    intro i
    exact (coefficientBox_le_eight i).trans hB
  · simp only [MvPolynomial.coe_one]
    exact WindowEq.refl _ _

theorem finite_root_product_coefficient (B : ℕ) (hB : 8 ≤ B) :
    MvPolynomial.coeff coefficientBox (∏ r : PositiveRoot 28, finiteRootFactor B r) =
      MvPowerSeries.coeff coefficientBox (∏ r : PositiveRoot 28, counterexampleRootFactor r) := by
  have hw := WindowEq.prod coefficientBox Finset.univ
    (fun r : PositiveRoot 28 => ((finiteRootFactor B r : MvPolynomial (Fin 27) ℤ) : MvPowerSeries (Fin 27) ℤ))
    counterexampleRootFactor (fun r _ => finiteRootFactor_window B hB r)
  have hc := hw coefficientBox le_rfl
  have he : ((∏ r : PositiveRoot 28, finiteRootFactor B r : MvPolynomial (Fin 27) ℤ) :
      MvPowerSeries (Fin 27) ℤ) = ∏ r : PositiveRoot 28,
      ((finiteRootFactor B r : MvPolynomial (Fin 27) ℤ) : MvPowerSeries (Fin 27) ℤ) :=
    map_prod MvPolynomial.coeToMvPowerSeries.ringHom _ _
  rw [← he] at hc
  simpa only [MvPolynomial.coeff_coe] using hc

/-- A finite Laurent-coefficient formula under the Joseph-Polo, Demazure
character, and PBW hypotheses. -/
theorem rank28_rectangle_eq_finite_laurent
    (hJP : ∀ u : Composition 28, CompositionFlagJosephPolo u)
    (hDCF : ∀ u : Composition 28, CompositionFlagDemazureCharacter u) (hpbw : HasOrderedPBWBasis 28) :
    rectangleCoefficient 79 c (key a * key b) =
      (rootCoordinateEmbedding (∏ r : PositiveRoot 28, finiteRootFactor 8 r)).coeff
        (fun i => (c i : ℤ)-a i-b i) := by
  change rectangleCoefficient 79 c (key a * key b) =
    (rootCoordinateEmbedding (∏ r : PositiveRoot 28, finiteRootFactor 8 r)).coeff targetDifference
  rw [← rootWeight_coefficientBox, rootCoordinateEmbedding_coeff,
    finite_root_product_coefficient 8 le_rfl]
  exact rank28_rectangle_eq_root_product hJP hDCF hpbw

end Counterexample
end
end Schubert.RS
