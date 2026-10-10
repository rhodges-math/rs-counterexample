import RSCounterexample.FlagVarieties.Foundations.Schemes.SelectedFlagChartSchemeStructure
import RSCounterexample.FlagVarieties.Foundations.Schemes.SelectedChartFiniteType

/-!
# Finite-type geometry of the complete flag scheme

The incidence chart is a quotient of a polynomial ring in finitely many
variables. Finitely many such affine charts cover the glued scheme.
These facts prove local finite type, quasi-compactness and, over a Jacobson
coefficient ring, the Jacobson property used in closed-point arguments.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory
universe u
variable (R : Type u) [CommRing R] {n : ℕ}

instance selectedFlagIncidenceChartToSpec_locallyOfFiniteType
    (a : (j : Fin (n+1)) → Fin (n-j.val) ↪ Fin n) :
    LocallyOfFiniteType (selectedFlagIncidenceChartToSpec R a) := by
  unfold selectedFlagIncidenceChartToSpec
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  change (algebraMap R
    (MvPolynomial (FlagChartVariable n) R ⧸ selectedFlagIncidenceIdeal R a)).FiniteType
  rw [RingHom.finiteType_algebraMap]
  infer_instance

variable (n)

instance selectedFlagChartSchemeToSpec_locallyOfFiniteType :
    LocallyOfFiniteType (selectedFlagChartSchemeToSpec R n) := by
  apply (IsZariskiLocalAtSource.iff_of_openCover (P := @LocallyOfFiniteType)
    (selectedFlagChartGlueData R n).openCover).mpr
  intro a
  change LocallyOfFiniteType
    (selectedFlagChartSchemeChart R n a.down ≫ selectedFlagChartSchemeToSpec R n)
  rw [selectedFlagChartSchemeChart_toSpec]
  infer_instance

instance selectedFlagChartScheme_compactSpace : CompactSpace (selectedFlagChartScheme R n) := by
  let C := (selectedFlagChartGlueData R n).openCover
  let : Finite C.I₀ :=
    inferInstanceAs (Finite (ULift.{u} ((j : Fin (n+1)) → Fin (n-j.val) ↪ Fin n)))
  let : ∀ a, CompactSpace (C.X a) := fun a =>
    inferInstanceAs (CompactSpace (Spec (CommRingCat.of
      (MvPolynomial (FlagChartVariable n) R ⧸ selectedFlagIncidenceIdeal R a.down))))
  exact C.compactSpace

instance selectedFlagChartSchemeToSpec_quasiCompact :
    QuasiCompact (selectedFlagChartSchemeToSpec R n) := inferInstance

instance selectedFlagChartScheme_jacobsonSpace [IsJacobsonRing R] :
    JacobsonSpace (selectedFlagChartScheme R n) :=
  LocallyOfFiniteType.jacobsonSpace (selectedFlagChartSchemeToSpec R n)

end FlagVarieties.Foundations.QuotientCharts
