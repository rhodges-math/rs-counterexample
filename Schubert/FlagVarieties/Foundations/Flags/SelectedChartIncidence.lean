import Schubert.FlagVarieties.Foundations.Schemes.SelectedPresentationNaturality

/-!
# Exact incidence equations for two selected quotient charts

Inclusion of the kernels is equivalent to a finite list of equations
between the two original quotient maps. The selected section of the first
map determines the only possible factor map, so there is no existential
choice or field hypothesis in the equations.
-/

noncomputable section
namespace FlagVarieties.Foundations.QuotientCharts
universe u

theorem ker_le_ker_iff_selected_factor
    {A : Type*} [CommRing A] {M Q N : Type*}
    [AddCommGroup M] [Module A M] [AddCommGroup Q] [Module A Q]
    [AddCommGroup N] [Module A N]
    (q : M →ₗ[A] Q) (s : Q →ₗ[A] M) (r : M →ₗ[A] N)
    (hs : q.comp s = LinearMap.id) :
    LinearMap.ker q ≤ LinearMap.ker r ↔ (r.comp s).comp q = r := by
  constructor
  · intro h
    ext v
    have hv : v - s (q v) ∈ LinearMap.ker q := by
      change q (v - s (q v)) = 0
      simp only [map_sub]
      have hsq := LinearMap.congr_fun hs (q v)
      simpa only [LinearMap.comp_apply, LinearMap.id_apply] using sub_eq_zero.mpr hsq.symm
    have hr : r v - r (s (q v)) = 0 := by
      simpa only [LinearMap.mem_ker, map_sub] using h hv
    exact (sub_eq_zero.mp hr).symm
  · intro h v hv
    change r v = 0
    rw [← h]
    simp only [LinearMap.comp_apply, LinearMap.mem_ker.mp hv, map_zero]

variable (R : Type u) [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
  {n d e : ℕ} (a : Fin d ↪ Fin n) (b : Fin e ↪ Fin n)
  (f : MvPolynomial (Fin d × Fin (n-d)) R →ₐ[R] A)
  (g : MvPolynomial (Fin e × Fin (n-e)) R →ₐ[R] A)

/-- Incidence of chart kernels is equivalent to the forced factorization. -/
theorem selectedChartPoint_le_iff_factor :
    (selectedChartPoint R a f).toSubmodule ≤ (selectedChartPoint R b g).toSubmodule ↔
      ((selectedPresentationMap R b g).comp (coordinateInclusion a)).comp
        (selectedPresentationMap R a f) = selectedPresentationMap R b g := by
  rw [← selectedPresentationMap_ker, ← selectedPresentationMap_ker]
  exact ker_le_ker_iff_selected_factor _ _ _ (selectedPresentationMap_section R a f)

/-- A finite set of basis-entry equations cuts out precisely kernel incidence. -/
theorem selectedChartPoint_le_iff_entries :
    (selectedChartPoint R a f).toSubmodule ≤ (selectedChartPoint R b g).toSubmodule ↔
      ∀ (i : Fin e) (j : Fin n),
        selectedPresentationMap R b g (Pi.single j 1) i -
          selectedPresentationMap R b g
            (coordinateInclusion a (selectedPresentationMap R a f (Pi.single j 1))) i = 0 := by
  classical
  rw [selectedChartPoint_le_iff_factor]
  constructor
  · intro h i j
    have hv := congrFun (LinearMap.congr_fun h (Pi.single j 1)) i
    exact sub_eq_zero.mpr hv.symm
  · intro h
    apply (Pi.basisFun A (Fin n)).ext
    intro j
    ext i
    simpa only [LinearMap.comp_apply, Pi.basisFun_apply] using (sub_eq_zero.mp (h i j)).symm

end FlagVarieties.Foundations.QuotientCharts
