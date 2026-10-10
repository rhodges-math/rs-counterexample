import RSCounterexample.FlagVarieties.Foundations.Schemes.SelectedChartSchemeStructure
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Cover.Open

/-! # Finite-type geometry of the selected quotient scheme -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory
universe u
variable (R : Type u) [CommRing R] (n d : ℕ)

instance selectedChartToSpec_locallyOfFiniteType :
    LocallyOfFiniteType (selectedChartToSpec R n d) := by
  unfold selectedChartToSpec
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  change (algebraMap R (MvPolynomial (Fin d × Fin (n-d)) R)).FiniteType
  rw [RingHom.finiteType_algebraMap]
  infer_instance

instance selectedChartSchemeToSpec_locallyOfFiniteType :
    LocallyOfFiniteType (selectedChartSchemeToSpec R n d) := by
  apply (IsZariskiLocalAtSource.iff_of_openCover (P := @LocallyOfFiniteType)
    (selectedChartGlueData R n d).openCover).mpr
  intro a
  change LocallyOfFiniteType
    (selectedChartSchemeChart R n d a.down ≫ selectedChartSchemeToSpec R n d)
  rw [selectedChartSchemeChart_toSpec]
  infer_instance

instance selectedChartScheme_compactSpace : CompactSpace (selectedChartScheme R n d) := by
  let C := (selectedChartGlueData R n d).openCover
  let : Finite C.I₀ := inferInstanceAs (Finite (ULift.{u} (Fin d ↪ Fin n)))
  let : ∀ a, CompactSpace (C.X a) := fun _ =>
    inferInstanceAs (CompactSpace (Spec (CommRingCat.of (MvPolynomial (Fin d × Fin (n-d)) R))))
  exact C.compactSpace

instance selectedChartSchemeToSpec_quasiCompact :
    QuasiCompact (selectedChartSchemeToSpec R n d) := inferInstance

instance selectedChartScheme_jacobsonSpace [IsJacobsonRing R] :
    JacobsonSpace (selectedChartScheme R n d) :=
  LocallyOfFiniteType.jacobsonSpace (selectedChartSchemeToSpec R n d)

end FlagVarieties.Foundations.QuotientCharts
