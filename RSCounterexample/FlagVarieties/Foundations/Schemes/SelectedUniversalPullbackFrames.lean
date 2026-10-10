import RSCounterexample.FlagVarieties.Foundations.Schemes.SelectedUniversalPullbackCoherence

/-!
# Source-preserving pullback of quotient frames

The normalized source is the original coordinate free sheaf. All comparisons
below are the pullback composition, equality, and open-restriction
isomorphisms; the target module is arbitrary.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {X Y Z : Scheme.{u}} {n d : ℕ}

/-- Pullback of a quotient with the original labelled free source. -/
def coordinatePullbackQuotient (f : X ⟶ Y) {M : Y.Modules}
    (q : coordinateFreeSheaf Y n ⟶ M) :
    coordinateFreeSheaf X n ⟶ (Scheme.Modules.pullback f).obj M :=
  (coordinatePullbackFreeIso f n).inv ≫ (Scheme.Modules.pullback f).map q

instance coordinatePullbackQuotient_epi (f : X ⟶ Y) {M : Y.Modules}
    (q : coordinateFreeSheaf Y n ⟶ M) [Epi q] : Epi (coordinatePullbackQuotient f q) := by
  unfold coordinatePullbackQuotient
  infer_instance

/-- Arbitrary composite pullback preserves the original quotient source. -/
@[reassoc]
theorem coordinatePullbackQuotient_comp (f : X ⟶ Y) (g : Y ⟶ Z) {M : Z.Modules}
    (q : coordinateFreeSheaf Z n ⟶ M) :
    coordinatePullbackQuotient (f ≫ g) q ≫ (Scheme.Modules.pullbackComp f g).inv.app M =
      coordinatePullbackQuotient f (coordinatePullbackQuotient g q) := by
  apply (cancel_epi (coordinatePullbackFreeIso (f ≫ g) n).hom).mp
  conv_rhs => rw [← coordinatePullbackFreeIso_comp f g n]
  simp only [coordinatePullbackQuotient, Functor.map_comp, Category.assoc,
    Iso.hom_inv_id_assoc, Iso.hom_inv_id_map_assoc]
  exact (Scheme.Modules.pullbackComp f g).inv.naturality q

/-- Pull back a target frame through a further scheme morphism. -/
def coordinatePullbackFrameComp (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules)
    (e : (Scheme.Modules.pullback g).obj M ≅ coordinateFreeSheaf Y d) :
    (Scheme.Modules.pullback (f ≫ g)).obj M ≅ coordinateFreeSheaf X d :=
  ((Scheme.Modules.pullbackComp f g).app M).symm ≪≫
    (Scheme.Modules.pullback f).mapIso e ≪≫ coordinatePullbackFreeIso f d

/-- This frame transport retains the exact original local quotient formula. -/
theorem coordinatePullbackFrameComp_source (f : X ⟶ Y) (g : Y ⟶ Z) {M : Z.Modules}
    (q : coordinateFreeSheaf Z n ⟶ M)
    (e : (Scheme.Modules.pullback g).obj M ≅ coordinateFreeSheaf Y d)
    (t : coordinateFreeSheaf Y n ⟶ coordinateFreeSheaf Y d)
    (h : coordinatePullbackQuotient g q ≫ e.hom = t) :
    coordinatePullbackQuotient (f ≫ g) q ≫ (coordinatePullbackFrameComp f g M e).hom =
      coordinatePullbackMap f t := by
  change coordinatePullbackQuotient (f ≫ g) q ≫
    (Scheme.Modules.pullbackComp f g).inv.app M ≫
      (Scheme.Modules.pullback f).map e.hom ≫ (coordinatePullbackFreeIso f d).hom = _
  rw [coordinatePullbackQuotient_comp_assoc]
  simp only [coordinatePullbackQuotient, Category.assoc]
  unfold coordinatePullbackQuotient at h
  rw [← Functor.map_comp_assoc, h]
  rfl

/-- Equality of scheme maps preserves the normalized source comparison. -/
@[reassoc]
theorem coordinatePullbackQuotient_congr {f g : X ⟶ Y} (h : f = g) {M : Y.Modules}
    (q : coordinateFreeSheaf Y n ⟶ M) :
    coordinatePullbackQuotient f q ≫ (Scheme.Modules.pullbackCongr h).hom.app M =
      coordinatePullbackQuotient g q := by
  subst g
  simp [Scheme.Modules.pullbackCongr]

/-- The open-restriction/pullback comparison preserves the original source. -/
@[reassoc]
theorem coordinatePullbackQuotient_restrict (f : X ⟶ Y) [IsOpenImmersion f]
    {M : Y.Modules} (q : coordinateFreeSheaf Y n ⟶ M) :
    coordinatePullbackQuotient f q ≫ (Scheme.Modules.restrictFunctorIsoPullback f).inv.app M =
      (coordinateRestrictFreeIso f n).inv ≫ (Scheme.Modules.restrictFunctor f).map q := by
  unfold coordinatePullbackQuotient
  rw [← coordinateRestrictionIso_eq]
  simp only [coordinateRestrictionIso, Iso.trans_inv, Iso.app_inv, Category.assoc]
  rw [(Scheme.Modules.restrictFunctorIsoPullback f).inv.naturality]
  rfl

end FlagVarieties.Foundations.QuotientCharts
