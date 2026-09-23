import Schubert.RS.RootGeometricSeries
import Schubert.RS.WeylRootSeries
import Schubert.RS.RootPattern

/-! Cancellation of the three key denominators against the Weyl factors. -/

namespace Schubert.RS
noncomputable section
open Representation
variable {n : ℕ}

def combinedRootFactor (a b g : Composition n) (r : PositiveRoot n) :
    MvPowerSeries (Fin (n-1)) ℤ :=
  (if a r.val.1 < a r.val.2 then rootGeometricSeries (rootDegree r.val.1 r.val.2) else 1) *
  (if b r.val.1 < b r.val.2 then rootGeometricSeries (rootDegree r.val.1 r.val.2) else 1) *
  (if g r.val.1 < g r.val.2 then rootGeometricSeries (rootDegree r.val.1 r.val.2) else 1) *
  (1 - MvPowerSeries.monomial (rootDegree r.val.1 r.val.2) 1)

theorem ascentRootSeries_eq_product (u : Composition n) :
    ascentRootSeries u = ∏ r : PositiveRoot n,
      if u r.val.1 < u r.val.2 then rootGeometricSeries (rootDegree r.val.1 r.val.2) else 1 := by
  classical
  rw [ascentRootSeries_eq_geometric]
  symm
  apply Finset.prod_congr_set {r : PositiveRoot n | u r.val.1 < u r.val.2}
  · intro r hr
    simp only [Set.mem_setOf_eq] at hr
    simp [hr]
  · intro r hr
    simp only [Set.mem_setOf_eq] at hr
    simp [hr]

theorem three_root_series_eq_product (a b g : Composition n) :
    ascentRootSeries a * ascentRootSeries b * ascentRootSeries g * weylRootSeries n =
      ∏ r : PositiveRoot n, combinedRootFactor a b g r := by
  rw [ascentRootSeries_eq_product a, ascentRootSeries_eq_product b,
    ascentRootSeries_eq_product g, weylRootSeries_eq_product]
  simp only [combinedRootFactor, Finset.prod_mul_distrib]

namespace Counterexample

def counterexampleRootFactor (r : PositiveRoot 28) : MvPowerSeries (Fin 27) ℤ :=
  if coordinateClass r.val.1 = coordinateClass r.val.2 then
    1 - MvPowerSeries.monomial (rootDegree r.val.1 r.val.2) 1
  else if isSource r.val.1 ∧ ¬isSource r.val.2 then
    rootGeometricSeries (rootDegree r.val.1 r.val.2)
  else 1

theorem combinedRootFactor_concrete (r : PositiveRoot 28) :
    combinedRootFactor a b g r = counterexampleRootFactor r := by
  classical
  have hp := class_pattern r.val.1 r.val.2 r.property
  have hd : rootDegree r.val.1 r.val.2 ≠ 0 := by
    intro h
    have hc := rootDegree_first r.val.1 r.val.2 r.property
    rw [h] at hc
    simp at hc
  have hi := rootGeometricSeries_mul (rootDegree r.val.1 r.val.2) hd
  by_cases hA : a r.val.1 < a r.val.2 <;>
    by_cases hB : b r.val.1 < b r.val.2 <;>
    by_cases hG : g r.val.1 < g r.val.2 <;>
    by_cases hC : coordinateClass r.val.1 = coordinateClass r.val.2 <;>
    by_cases hS : isSource r.val.1 ∧ ¬isSource r.val.2 <;>
    simp only [combinedRootFactor, counterexampleRootFactor, comparisonWeight,
      hA, hB, hG, hC, hS, if_true, if_false, mul_one, one_mul, mul_assoc] at hp ⊢ <;>
    norm_num at hp <;> simp [hi]

theorem concrete_root_series_eq_product :
    ascentRootSeries a * ascentRootSeries b * ascentRootSeries g * weylRootSeries 28 =
      ∏ r : PositiveRoot 28, counterexampleRootFactor r := by
  rw [three_root_series_eq_product]
  apply Finset.prod_congr rfl
  intro r hr
  exact combinedRootFactor_concrete r

end Counterexample
end
end Schubert.RS
