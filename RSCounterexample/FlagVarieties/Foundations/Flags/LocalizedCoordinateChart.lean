import RSCounterexample.FlagVarieties.Foundations.Flags.CoordinateBaseChange
import RSCounterexample.FlagVarieties.Foundations.Flags.CoordinateChartCover
import Mathlib.RingTheory.Localization.BaseChange

/-!
# Normalized matrix charts on a finite principal-open cover

The localizations used to spread a coordinate basis agree with the
tensor base change of the quotient. Consequently every Grassmannian point
has a finite principal-open cover on which its base change has a
unique normalized matrix presentation. The glued chart scheme and its
classification of coordinate quotients are in
`Schemes/SelectedChartGlueData.lean` and
`Schemes/SelectedAffineClassification.lean`.
-/

noncomputable section

namespace FlagVarieties.Foundations.QuotientCharts

open TensorProduct

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- The localization/tensor equivalence commutes with the localized map. -/
theorem localizedMap_tensor_equiv (S : Submonoid R) (f : M →ₗ[R] N) :
    (LocalizedModule.equivTensorProduct S N).toLinearMap.comp (LocalizedModule.map S f) =
      (f.baseChange (Localization S)).comp
        (LocalizedModule.equivTensorProduct S M).toLinearMap := by
  apply LinearMap.ext
  intro x
  induction x using LocalizedModule.induction_on with
  | _ m s => simp

/-- Bijectivity of localization and tensor base change are the same assertion. -/
theorem localizedMap_bijective_iff_baseChange (S : Submonoid R) (f : M →ₗ[R] N) :
    Function.Bijective (LocalizedModule.map S f) ↔
      Function.Bijective (f.baseChange (Localization S)) := by
  have h := (LocalizedModule.equivTensorProduct S N).bijective.of_comp_iff'
    (LocalizedModule.map S f)
  change Function.Bijective ((LocalizedModule.equivTensorProduct S N).toLinearMap.comp
    (LocalizedModule.map S f)) ↔ _ at h
  rw [localizedMap_tensor_equiv] at h
  exact h.symm.trans ((LocalizedModule.equivTensorProduct S M).bijective.of_comp_iff _)

variable {n d : ℕ}

/-- The selected-map criterion on a localized module is exactly the chart
criterion for the scalar-extended Grassmannian point. -/
theorem coordinateGrassmannian_localized_selected_iff
    (P : Module.Grassmannian R (Fin n → R) d) (S : Submonoid R) (a : Fin d ↪ Fin n) :
    Function.Bijective ((coordinateGrassmannianBaseChange (Localization S) P).toSubmodule.mkQ.comp
      (coordinateInclusion a)) ↔
      Function.Bijective (LocalizedModule.map S
        (P.toSubmodule.mkQ.comp (coordinateInclusion a))) := by
  rw [coordinateGrassmannianBaseChange_selected_iff,
    localizedMap_bijective_iff_baseChange]

/-- A finite principal-open cover carries unique matrix presentations of
the scalar-extended Grassmannian quotient. The empty spectrum is allowed. -/
theorem grassmannian_exists_selectedMatrix_finiteOpenCover
    (P : Module.Grassmannian R (Fin n → R) d) :
    ∃ (s : Finset (PrimeSpectrum R)) (a : s → (Fin d ↪ Fin n)) (g : s → R),
      TopologicalSpace.IsOpenCover (fun p => PrimeSpectrum.basicOpen (g p)) ∧
      ∀ p, ∃! C : Matrix (Fin d) (Fin (n - d)) (Localization.Away (g p)),
        (matrixGrassmannianChartEquiv C).val =
          grassmannianTransport (coordinateGrassmannianBaseChange (Localization.Away (g p)) P)
            (selectedCoordinateEquiv (a p)) := by
  obtain ⟨s, a, g, hcover, hbij⟩ := grassmannian_exists_selectedMap_finiteOpenCover P
  refine ⟨s, a, g, hcover, fun p => ?_⟩
  apply grassmannian_existsUnique_selectedMatrix
  exact (coordinateGrassmannian_localized_selected_iff P (Submonoid.powers (g p)) (a p)).mpr
    (hbij p)

end FlagVarieties.Foundations.QuotientCharts
