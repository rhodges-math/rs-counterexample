import Schubert.FlagVarieties.Foundations.Flags.SelectedFlagTripleOverlapLift
import Schubert.FlagVarieties.Foundations.Schemes.SelectedFlagOverlapDiagonal
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Triple fiber products of the full-flag incidence charts

The affine tensor-product presentation realizes the previously constructed
ring maps as scheme morphisms on the categorical fiber product.
Both comparisons with the second and third incidence charts commute.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable (R : Type u) [CommRing R] {n : ℕ}
  (a b c : (j : Fin (n+1)) → Fin (n-j.val) ↪ Fin n)

/-- The triple overlap of the charts `a`, `b`, `c`, a fibre product over the chart `a`. -/
abbrev selectedFlagTripleOverlap : Scheme.{u} :=
  pullback (selectedFlagOverlapInclusion R a b) (selectedFlagOverlapInclusion R a c)

/-- The triple overlap is the spectrum of `SelectedFlagTripleOverlapRing`. -/
def selectedFlagTripleOverlapSpecIso : selectedFlagTripleOverlap R a b c ≅
    Spec (CommRingCat.of (SelectedFlagTripleOverlapRing R a b c)) :=
  pullbackSpecIso (MvPolynomial (FlagChartVariable n) R ⧸ selectedFlagIncidenceIdeal R a)
    (SelectedFlagOverlapRing R a b) (SelectedFlagOverlapRing R a c)

@[reassoc (attr := simp)]
theorem selectedFlagTripleOverlapSpecIso_inv_fst :
    (selectedFlagTripleOverlapSpecIso R a b c).inv ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (selectedFlagTripleOverlapLeft R a b c).toRingHom) :=
  pullbackSpecIso_inv_fst _ _ _

@[reassoc (attr := simp)]
theorem selectedFlagTripleOverlapSpecIso_inv_snd :
    (selectedFlagTripleOverlapSpecIso R a b c).inv ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (selectedFlagTripleOverlapRight R a b c).toRingHom) :=
  pullbackSpecIso_inv_snd _ _ _

/-- The map from the triple overlap of `(a, b, c)` to the overlap of the charts `b` and `c`. -/
def selectedFlagTripleOverlapMap :
    selectedFlagTripleOverlap R a b c ⟶ selectedFlagOverlapScheme R b c :=
  (selectedFlagTripleOverlapSpecIso R a b c).hom ≫
    Spec.map (CommRingCat.ofHom (selectedFlagTripleOverlapToSecondThird R a b c).toRingHom)

@[reassoc]
theorem selectedFlagTripleOverlapMap_first :
    selectedFlagTripleOverlapMap R a b c ≫ selectedFlagOverlapInclusion R b c =
      pullback.fst _ _ ≫ selectedFlagOverlapMap R a b := by
  have hs : Spec.map (CommRingCat.ofHom
      (selectedFlagTripleOverlapToSecondThird R a b c).toRingHom) ≫
      selectedFlagOverlapInclusion R b c =
      Spec.map (CommRingCat.ofHom (selectedFlagTripleOverlapLeft R a b c).toRingHom) ≫
        selectedFlagOverlapMap R a b :=
    spec_map_algHom_square R
      (IsScalarTower.toAlgHom R
        (MvPolynomial (FlagChartVariable n) R ⧸ selectedFlagIncidenceIdeal R b)
        (SelectedFlagOverlapRing R b c))
      (selectedFlagTripleOverlapToSecondThird R a b c) (selectedFlagOverlapCoordinates R a b)
      (selectedFlagTripleOverlapLeft R a b c) (selectedFlagTripleOverlapToSecondThird_first R a b c)
  rw [selectedFlagTripleOverlapMap, Category.assoc, hs, ← Category.assoc]
  exact congrArg (fun f => f ≫ selectedFlagOverlapMap R a b)
    (pullbackSpecIso_hom_fst (MvPolynomial (FlagChartVariable n) R ⧸ selectedFlagIncidenceIdeal R a)
      (SelectedFlagOverlapRing R a b) (SelectedFlagOverlapRing R a c))

@[reassoc]
theorem selectedFlagTripleOverlapMap_third :
    selectedFlagTripleOverlapMap R a b c ≫ selectedFlagOverlapMap R b c =
      pullback.snd _ _ ≫ selectedFlagOverlapMap R a c := by
  have hs : Spec.map (CommRingCat.ofHom
      (selectedFlagTripleOverlapToSecondThird R a b c).toRingHom) ≫
      selectedFlagOverlapMap R b c =
      Spec.map (CommRingCat.ofHom (selectedFlagTripleOverlapRight R a b c).toRingHom) ≫
        selectedFlagOverlapMap R a c :=
    spec_map_algHom_square R (selectedFlagOverlapCoordinates R b c)
      (selectedFlagTripleOverlapToSecondThird R a b c) (selectedFlagOverlapCoordinates R a c)
      (selectedFlagTripleOverlapRight R a b c)
      (selectedFlagTripleOverlapToSecondThird_third R a b c)
  rw [selectedFlagTripleOverlapMap, Category.assoc, hs, ← Category.assoc]
  exact congrArg (fun f => f ≫ selectedFlagOverlapMap R a c)
    (pullbackSpecIso_hom_snd (MvPolynomial (FlagChartVariable n) R ⧸ selectedFlagIncidenceIdeal R a)
      (SelectedFlagOverlapRing R a b) (SelectedFlagOverlapRing R a c))

end FlagVarieties.Foundations.QuotientCharts
