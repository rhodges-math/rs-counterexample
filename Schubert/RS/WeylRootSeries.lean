import Schubert.RS.RootSeriesWindow

/-! The finite Weyl denominator in nonnegative root coordinates. -/

namespace Schubert.RS
noncomputable section
open Representation
variable {n : ℕ}

@[simp] theorem rootCoordinateEmbedding_monomial (d : RootDegree n) (z : ℤ) :
    rootCoordinateEmbedding (MvPolynomial.monomial d z) =
      AddMonoidAlgebra.single (rootWeight d) z := AddMonoidAlgebra.mapDomain_single

theorem rootCoordinates_weylFactor (n : ℕ) :
    rootCoordinates (weylFactor n) =
      ∏ i : Fin n, ∏ j ∈ Finset.univ.filter (i < ·),
        (1 - MvPolynomial.monomial (rootDegree i j) (1 : ℤ)) := by
  apply rootCoordinateEmbedding_injective
  rw [rootCoordinateEmbedding_rootCoordinates _ (weylFactor_rootSupported n)]
  simp only [map_prod, map_sub, map_one, rootCoordinateEmbedding_monomial]
  unfold weylFactor
  apply Finset.prod_congr rfl
  intro i hi
  apply Finset.prod_congr rfl
  intro j hj
  rw [rootWeight_rootDegree i j (Finset.mem_filter.mp hj).2]

theorem weylRootSeries_eq_double_product (n : ℕ) :
    weylRootSeries n = ∏ i : Fin n, ∏ j ∈ Finset.univ.filter (i < ·),
      (1 - MvPowerSeries.monomial (rootDegree i j) (1 : ℤ)) := by
  change MvPolynomial.coeToMvPowerSeries.ringHom (rootCoordinates (weylFactor n)) = _
  rw [rootCoordinates_weylFactor]
  simp only [map_prod, map_sub, map_one, MvPolynomial.coeToMvPowerSeries.ringHom_apply,
    MvPolynomial.coe_monomial]

theorem positiveRoot_product {R : Type*} [CommMonoid R] (f : Fin n → Fin n → R) :
    ∏ i : Fin n, ∏ j ∈ Finset.univ.filter (i < ·), f i j =
      ∏ r : PositiveRoot n, f r.val.1 r.val.2 := by
  classical
  have h := Finset.prod_subtype (p := fun p : Fin n × Fin n => p.1 < p.2)
    (F := inferInstance) (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2))
    (by intro p; simp) (fun p => f p.1 p.2)
  rw [← h, Finset.prod_filter, Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro i hi
  rw [Finset.prod_filter]

theorem weylRootSeries_eq_product (n : ℕ) :
    weylRootSeries n = ∏ r : PositiveRoot n,
      (1 - MvPowerSeries.monomial (rootDegree r.val.1 r.val.2) (1 : ℤ)) := by
  rw [weylRootSeries_eq_double_product, positiveRoot_product]

end
end Schubert.RS
