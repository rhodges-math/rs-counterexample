import Schubert.FlagVarieties.Foundations.Schemes.SelectedChartOverlapReturn
import Schubert.FlagVarieties.Foundations.Flags.QuotientPresentationEquiv

/-!
# The free quotient on each selected matrix chart

The normalized matrix is written in the original ambient coordinates.
Its section is the original selected-coordinate inclusion, and its
kernel is precisely the quotient point used in the chart scheme.
-/

noncomputable section

namespace FlagVarieties.Foundations.QuotientCharts

universe u

variable (R : Type u) [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
  {n d : ℕ} (a : Fin d ↪ Fin n)
  (f : MvPolynomial (Fin d × Fin (n - d)) R →ₐ[R] A)

/-- The chart's free quotient map in the unchanged ambient coordinates. -/
def selectedPresentationMap : (Fin n → A) →ₗ[A] (Fin d → A) :=
  (normalizedMap (Matrix.toLin' (matrixEvaluationEquiv R d (n - d) A f))).comp
    (selectedCoordinateEquiv a).toLinearMap

/-- The original selected coordinates give a section of this quotient. -/
theorem selectedPresentationMap_section :
    (selectedPresentationMap R a f).comp (coordinateInclusion a) = LinearMap.id := by
  rw [selectedPresentationMap, LinearMap.comp_assoc, selectedCoordinateEquiv_inclusion]
  apply LinearMap.ext
  intro x
  exact normalizedMap_inl _ x

theorem selectedPresentationMap_surjective :
    Function.Surjective (selectedPresentationMap R a f) := by
  intro y
  exact ⟨coordinateInclusion a y, LinearMap.congr_fun (selectedPresentationMap_section R a f) y⟩

/-- Its kernel is the exact quotient underlying the selected chart point. -/
theorem selectedPresentationMap_ker :
    LinearMap.ker (selectedPresentationMap R a f) = (selectedChartPoint R a f).toSubmodule := by
  rw [selectedPresentationMap, LinearMap.ker_comp, selectedChartPoint,
    grassmannianTransport_submodule, matrixGrassmannianChartEquiv_submodule]
  exact ((LinearMap.ker (normalizedMap (Matrix.toLin'
    (matrixEvaluationEquiv R d (n - d) A f)))).map_equiv_eq_comap_symm
      (selectedCoordinateEquiv (R := A) a).symm).symm

/-- Each selected chart has a quotient frame preserving the original quotient vectors. -/
def selectedPresentationQuotientEquiv :
    ((Fin n → A) ⧸ (selectedChartPoint R a f).toSubmodule) ≃ₗ[A] (Fin d → A) :=
  (Submodule.quotEquivOfEq _ _ (selectedPresentationMap_ker R a f).symm).trans
    ((selectedPresentationMap R a f).quotKerEquivOfSurjective
      (selectedPresentationMap_surjective R a f))

@[simp] theorem selectedPresentationQuotientEquiv_mk (v : Fin n → A) :
    selectedPresentationQuotientEquiv R a f (Submodule.Quotient.mk v) =
      selectedPresentationMap R a f v := by
  simp [selectedPresentationQuotientEquiv]

end FlagVarieties.Foundations.QuotientCharts
