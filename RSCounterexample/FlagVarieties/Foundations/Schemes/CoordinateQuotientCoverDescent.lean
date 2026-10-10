import RSCounterexample.FlagVarieties.Foundations.Schemes.ModuleSheafOpenCoverQuotient
import RSCounterexample.FlagVarieties.Foundations.Schemes.SelectedUniversalAffineCoverSource

/-!
# Global comparison from normalized coordinate quotient maps on a cover

The canonical free-source isomorphism is cancelled before applying descent.
Thus the hypotheses use the exact labelled source convention of the universal
quotient, while the proof descends morphisms of sheaves.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u v
variable {X : Scheme.{u}} {M N : X.Modules} {n : ℕ}

theorem pullback_map_eq_of_coordinate_source {Y : Scheme.{u}} (f : Y ⟶ X)
    (q : coordinateFreeSheaf X n ⟶ M) (r : coordinateFreeSheaf X n ⟶ N)
    (e : (Scheme.Modules.pullback f).obj M ≅ (Scheme.Modules.pullback f).obj N)
    (he : coordinatePullbackQuotient f q ≫ e.hom = coordinatePullbackQuotient f r) :
    (Scheme.Modules.pullback f).map q ≫ e.hom = (Scheme.Modules.pullback f).map r := by
  apply (cancel_epi (coordinatePullbackFreeIso f n).inv).mp
  simpa only [coordinatePullbackQuotient, Category.assoc] using he

/-- An isomorphism between two quotients `M`, `N` of the free sheaf `𝒪ⁿ`, glued from isomorphisms
over the members of an open cover that are compatible with the quotient maps. -/
def coordinateQuotientIsoOfCover (C : X.OpenCover.{v})
    (q : coordinateFreeSheaf X n ⟶ M) [Epi q]
    (r : coordinateFreeSheaf X n ⟶ N) [Epi r]
    (e : ∀ i, (Scheme.Modules.pullback (C.f i)).obj M ≅
      (Scheme.Modules.pullback (C.f i)).obj N)
    (he : ∀ i, coordinatePullbackQuotient (C.f i) q ≫ (e i).hom =
      coordinatePullbackQuotient (C.f i) r) : M ≅ N :=
  ModuleSheafGluing.quotientIsoOfPullbackCover C q r e
    (fun i => pullback_map_eq_of_coordinate_source (C.f i) q r (e i) (he i))

@[reassoc]
theorem coordinateQuotientIsoOfCover_source (C : X.OpenCover.{v})
    (q : coordinateFreeSheaf X n ⟶ M) [Epi q]
    (r : coordinateFreeSheaf X n ⟶ N) [Epi r]
    (e : ∀ i, (Scheme.Modules.pullback (C.f i)).obj M ≅
      (Scheme.Modules.pullback (C.f i)).obj N)
    (he : ∀ i, coordinatePullbackQuotient (C.f i) q ≫ (e i).hom =
      coordinatePullbackQuotient (C.f i) r) :
    q ≫ (coordinateQuotientIsoOfCover C q r e he).hom = r :=
  ModuleSheafGluing.quotientIsoOfPullbackCover_source C q r _ _

/-- The associated-sheaf map of the original quotient module is an epi. -/
instance coordinateQuotientSheafMap_epi (A : CommRingCat.{u}) {n d : ℕ}
    (P : Module.Grassmannian A (Fin n → A) d) : Epi (coordinateQuotientSheafMap A P) := by
  have : Epi (ModuleCat.ofHom P.toSubmodule.mkQ) :=
    (ModuleCat.epi_iff_surjective _).mpr P.toSubmodule.mkQ_surjective
  have : Epi (tilde.map (ModuleCat.ofHom P.toSubmodule.mkQ)) := by
    change Epi ((tilde.functor A).map (ModuleCat.ofHom P.toSubmodule.mkQ))
    infer_instance
  unfold coordinateQuotientSheafMap
  infer_instance

end FlagVarieties.Foundations.QuotientCharts
