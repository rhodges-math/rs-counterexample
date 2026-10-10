import RSCounterexample.FlagVarieties.Foundations.Flags.SelectedFlagChartOverlapIso
import RSCounterexample.FlagVarieties.Foundations.Schemes.SelectedFlagIncidenceChart
import Mathlib.AlgebraicGeometry.OpenImmersion

/-!
# Scheme overlaps of full-flag incidence charts

The overlap is the determinant open in the incidence chart.
Its coordinate transition is an isomorphism to the reverse overlap;
both resulting chart maps are open immersions over the original base.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory
universe u
variable (R : Type u) [CommRing R] {n : ℕ}
  (a b : (j : Fin (n+1)) → Fin (n-j.val) ↪ Fin n)

/-- The overlap of the charts `a` and `b` of the flag scheme, an open subscheme of the chart `a`. -/
def selectedFlagOverlapScheme : Scheme.{u} :=
  Spec (CommRingCat.of (SelectedFlagOverlapRing R a b))

/-- The open immersion of the overlap of the charts `a` and `b` into the chart `a`. -/
def selectedFlagOverlapInclusion :
    selectedFlagOverlapScheme R a b ⟶ selectedFlagIncidenceChart R a :=
  Spec.map (CommRingCat.ofHom (algebraMap
    (MvPolynomial (FlagChartVariable n) R ⧸ selectedFlagIncidenceIdeal R a)
    (SelectedFlagOverlapRing R a b)))

instance selectedFlagOverlapInclusion_open :
    IsOpenImmersion (selectedFlagOverlapInclusion R a b) := by
  unfold selectedFlagOverlapInclusion
  infer_instance

/-- The map from the overlap of the charts `a` and `b` to the chart `b`, given by the chart
transition. -/
def selectedFlagOverlapMap :
    selectedFlagOverlapScheme R a b ⟶ selectedFlagIncidenceChart R b :=
  Spec.map (CommRingCat.ofHom (selectedFlagOverlapCoordinates R a b).toRingHom)

/-- The overlap of the charts `a` and `b` is isomorphic to that of `b` and `a`. -/
def selectedFlagOverlapSchemeIso :
    selectedFlagOverlapScheme R a b ≅ selectedFlagOverlapScheme R b a :=
  Scheme.Spec.mapIso (selectedFlagOverlapAlgEquiv R a b).toRingEquiv.toCommRingCatIso.op

@[reassoc]
theorem selectedFlagOverlapSchemeIso_hom_inclusion :
    (selectedFlagOverlapSchemeIso R a b).hom ≫ selectedFlagOverlapInclusion R b a =
      selectedFlagOverlapMap R a b := by
  change Spec.map (CommRingCat.ofHom (selectedFlagOverlapLift R a b).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap _ (SelectedFlagOverlapRing R b a))) = _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro p
  exact selectedFlagOverlapLift_algebraMap R a b p

instance selectedFlagOverlapMap_open : IsOpenImmersion (selectedFlagOverlapMap R a b) := by
  rw [← selectedFlagOverlapSchemeIso_hom_inclusion]
  infer_instance

@[reassoc]
theorem selectedFlagOverlapMap_toSpec :
    selectedFlagOverlapMap R a b ≫ selectedFlagIncidenceChartToSpec R b =
      selectedFlagOverlapInclusion R a b ≫ selectedFlagIncidenceChartToSpec R a := by
  let fa := CommRingCat.ofHom (algebraMap R
    (MvPolynomial (FlagChartVariable n) R ⧸ selectedFlagIncidenceIdeal R a))
  let fb := CommRingCat.ofHom (algebraMap R
    (MvPolynomial (FlagChartVariable n) R ⧸ selectedFlagIncidenceIdeal R b))
  let ga := CommRingCat.ofHom (algebraMap
    (MvPolynomial (FlagChartVariable n) R ⧸ selectedFlagIncidenceIdeal R a)
    (SelectedFlagOverlapRing R a b))
  let gb := CommRingCat.ofHom (selectedFlagOverlapCoordinates R a b).toRingHom
  have h : fb ≫ gb = fa ≫ ga := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    exact (selectedFlagOverlapCoordinates R a b).commutes r
  exact (Spec.map_comp fb gb).symm.trans ((congrArg Spec.map h).trans (Spec.map_comp fa ga))

end FlagVarieties.Foundations.QuotientCharts
