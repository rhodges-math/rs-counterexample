import RSCounterexample.FlagVarieties.Foundations.Schemes.SelectedUniversalTransition
import RSCounterexample.FlagVarieties.Foundations.Schemes.ModuleSheafLocalFrames

/-!
# The universal quotient on the selected-chart scheme

The global target is an image sheaf, constructed from the original
local quotients. Their compatibility has been proved on the full intersections.
It is a locally free finite-type quotient of the original labelled free source,
with explicit rank-d frames and the original quotient formula on every chart.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable (R : Type u) [CommRing R] (n d : ℕ)

/-- The original chart-range cover, with its index in the scheme universe. -/
abbrev selectedUniversalCoverOpen (a : ULift.{u} (Fin d ↪ Fin n)) :
    (selectedChartScheme R n d).Opens := selectedUniversalOpen R n d a.down

/-- The original local free target on this cover. -/
abbrev selectedUniversalCoverTarget (a : ULift.{u} (Fin d ↪ Fin n)) :
    (selectedUniversalCoverOpen R n d a).toScheme.Modules :=
  selectedUniversalLocalTarget R n d a.down

/-- The original split local quotient on this cover. -/
abbrev selectedUniversalCoverQuotient (a : ULift.{u} (Fin d ↪ Fin n)) :
    (coordinateFreeSheaf (selectedChartScheme R n d) n).restrict
      (selectedUniversalCoverOpen R n d a).ι ⟶ selectedUniversalCoverTarget R n d a :=
  selectedUniversalLocalQuotient R n d a.down

/-- All overlap compatibility is derived from the regular transitions. -/
theorem selectedUniversalCompatible :
    ModuleSheafGluing.Compatible (coordinateFreeSheaf (selectedChartScheme R n d) n)
      (selectedUniversalCoverOpen R n d) (selectedUniversalCoverTarget R n d)
      (selectedUniversalCoverQuotient R n d) := by
  apply ModuleSheafGluing.compatible_of_chart_restriction
  intro a b
  exact ⟨selectedUniversalTargetTransition R a.down b.down,
    selectedUniversalTargetTransition_comp R a.down b.down⟩

/-- The global quotient target, constructed as an image of sheaves. -/
def selectedUniversalQuotientSheaf : (selectedChartScheme R n d).Modules :=
  ModuleSheafGluing.gluedModule (coordinateFreeSheaf (selectedChartScheme R n d) n)
    (selectedUniversalCoverOpen R n d) (selectedUniversalCoverTarget R n d)
    (selectedUniversalCoverQuotient R n d)

/-- The universal quotient of the original labelled rank-n free sheaf. -/
def selectedUniversalQuotient :
    coordinateFreeSheaf (selectedChartScheme R n d) n ⟶ selectedUniversalQuotientSheaf R n d :=
  ModuleSheafGluing.gluedQuotient (coordinateFreeSheaf (selectedChartScheme R n d) n)
    (selectedUniversalCoverOpen R n d) (selectedUniversalCoverTarget R n d)
    (selectedUniversalCoverQuotient R n d)

instance selectedUniversalQuotient_epi : Epi (selectedUniversalQuotient R n d) := by
  unfold selectedUniversalQuotient
  infer_instance

/-- A rank-d frame on each original selected chart range. -/
def selectedUniversalQuotientFrame (a : Fin d ↪ Fin n) :
    (selectedUniversalQuotientSheaf R n d).restrict (selectedUniversalOpen R n d a).ι ≅
      coordinateFreeSheaf (selectedUniversalOpen R n d a).toScheme d :=
  ModuleSheafGluing.gluedChartIso (coordinateFreeSheaf (selectedChartScheme R n d) n)
    (selectedUniversalCoverOpen R n d) (selectedUniversalCoverTarget R n d)
    (selectedUniversalCoverQuotient R n d) (selectedUniversalCompatible R n d) ⟨a⟩

/-- The constructed quotient recovers the exact original local quotient map. -/
@[reassoc]
theorem selectedUniversalQuotient_chart (a : Fin d ↪ Fin n) :
    (Scheme.Modules.restrictFunctor (selectedUniversalOpen R n d a).ι).map
      (selectedUniversalQuotient R n d) ≫ (selectedUniversalQuotientFrame R n d a).hom =
    selectedUniversalLocalQuotient R n d a :=
  ModuleSheafGluing.gluedQuotient_chart (coordinateFreeSheaf (selectedChartScheme R n d) n)
    (selectedUniversalCoverOpen R n d) (selectedUniversalCoverTarget R n d)
    (selectedUniversalCoverQuotient R n d) (selectedUniversalCompatible R n d) ⟨a⟩

/-- Identifying the original source frame gives the identity-evaluated
matrix quotient transported along the polynomial-chart isomorphism. -/
theorem selectedUniversalQuotient_chart_formula (a : Fin d ↪ Fin n) :
    (coordinateRestrictFreeIso (selectedUniversalOpen R n d a).ι n).inv ≫
      (Scheme.Modules.restrictFunctor (selectedUniversalOpen R n d a).ι).map
        (selectedUniversalQuotient R n d) ≫ (selectedUniversalQuotientFrame R n d a).hom =
    selectedUniversalNormalizedQuotient R a := by
  rw [selectedUniversalQuotient_chart, selectedUniversalLocalQuotient_eq,
    Iso.inv_hom_id_assoc]

/-- Returning to the original polynomial chart recovers its
identity-evaluated quotient as an equality of sheaf morphisms. -/
theorem selectedUniversalQuotient_polynomial_formula (a : Fin d ↪ Fin n) :
    coordinateRestrictMap (selectedUniversalOpenIso R n d a).hom
      ((coordinateRestrictFreeIso (selectedUniversalOpen R n d a).ι n).inv ≫
        (Scheme.Modules.restrictFunctor (selectedUniversalOpen R n d a).ι).map
          (selectedUniversalQuotient R n d) ≫ (selectedUniversalQuotientFrame R n d a).hom) =
    selectedPresentationSheafMap R
      (CommRingCat.of (MvPolynomial (Fin d × Fin (n - d)) R)) a (AlgHom.id R _) := by
  rw [selectedUniversalQuotient_chart_formula]
  unfold selectedUniversalNormalizedQuotient
  rw [coordinateRestrictMap_comp_scheme]
  simp only [Iso.hom_inv_id, coordinateRestrictMap_id]

/-- Rank-d frames cover every point, including all degenerate rank/base cases. -/
theorem selectedUniversalQuotient_local_frames (x : selectedChartScheme R n d) :
    ∃ V : (selectedChartScheme R n d).Opens, x ∈ V ∧
      Nonempty ((selectedUniversalQuotientSheaf R n d).restrict V.ι ≅
        coordinateFreeSheaf V.toScheme d) := by
  obtain ⟨a, ha⟩ := selectedUniversalOpen_cover R n d x
  exact ⟨selectedUniversalOpen R n d a, ha, ⟨selectedUniversalQuotientFrame R n d a⟩⟩

private theorem selectedUniversalCover_covers (x : selectedChartScheme R n d) :
    ∃ a : ULift.{u} (Fin d ↪ Fin n), x ∈ selectedUniversalCoverOpen R n d a := by
  obtain ⟨a, ha⟩ := selectedUniversalOpen_cover R n d x
  exact ⟨⟨a⟩, ha⟩

instance selectedUniversalQuotientSheaf_isLocallyFree :
    (selectedUniversalQuotientSheaf R n d).IsLocallyFree :=
  ModuleSheafGluing.isLocallyFree_of_frames (selectedUniversalQuotientSheaf R n d)
    (selectedUniversalCoverOpen R n d) d (selectedUniversalCover_covers R n d)
    (fun a => selectedUniversalQuotientFrame R n d a.down)

instance selectedUniversalQuotientSheaf_isFiniteType :
    (selectedUniversalQuotientSheaf R n d).IsFiniteType :=
  ModuleSheafGluing.isFiniteType_of_frames (selectedUniversalQuotientSheaf R n d)
    (selectedUniversalCoverOpen R n d) d (selectedUniversalCover_covers R n d)
    (fun a => selectedUniversalQuotientFrame R n d a.down)

instance selectedUniversalQuotientSheaf_isQuasicoherent :
    (selectedUniversalQuotientSheaf R n d).IsQuasicoherent := by infer_instance

/-- Unconditional existence of the finite locally free quotient with
its original quotient maps on every selected chart. -/
theorem exists_selectedUniversalQuotient :
    ∃ (Q : (selectedChartScheme R n d).Modules)
      (q : coordinateFreeSheaf (selectedChartScheme R n d) n ⟶ Q),
      Epi q ∧ Q.IsLocallyFree ∧ Q.IsFiniteType ∧
      ∀ a : Fin d ↪ Fin n, ∃ e : Q.restrict (selectedUniversalOpen R n d a).ι ≅
        coordinateFreeSheaf (selectedUniversalOpen R n d a).toScheme d,
        (Scheme.Modules.restrictFunctor (selectedUniversalOpen R n d a).ι).map q ≫ e.hom =
          selectedUniversalLocalQuotient R n d a := by
  exact ⟨selectedUniversalQuotientSheaf R n d, selectedUniversalQuotient R n d,
    inferInstance, inferInstance, inferInstance,
    fun a => ⟨selectedUniversalQuotientFrame R n d a, selectedUniversalQuotient_chart R n d a⟩⟩

end FlagVarieties.Foundations.QuotientCharts
