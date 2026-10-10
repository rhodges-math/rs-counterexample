import RSCounterexample.FlagVarieties.Foundations.Schemes.SelectedSheafBaseChangeCoordinates

/-!
# Arbitrary affine base change of selected quotient sheaves

These are equalities of sheaf morphisms under geometric pullback along
`Spec.map`, using the canonical free-sheaf comparisons with the original
coordinate labels. Target transitions follow by cancelling the
pulled-back quotient epimorphism.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientCharts

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

variable (R : Type u) [CommRing R] (A B : CommRingCat.{u}) [Algebra R A] [Algebra R B]
  {n d : ℕ} (a b : Fin d ↪ Fin n)
  (f g : MvPolynomial (Fin d × Fin (n - d)) R →ₐ[R] A) (k : A →ₐ[R] B)

/-- Arbitrary affine pullback of the selected quotient, with both source
and target identified by their canonical labelled free-sheaf comparisons. -/
@[reassoc]
theorem selectedPresentationSheafMap_pullback :
    (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom k.toRingHom))).map
        (selectedPresentationSheafMap R A a f) ≫
      (coordinatePullbackIso (Spec.map (CommRingCat.ofHom k.toRingHom)) d).hom =
    (coordinatePullbackIso (Spec.map (CommRingCat.ofHom k.toRingHom)) n).hom ≫
      selectedPresentationSheafMap R B a (k.comp f) := by
  classical
  apply coordinateSheafMap_pullback
  intro i j
  have h := congrFun (selectedPresentationMap_map R a f k (Pi.single i 1)) j
  have hb : (fun l => k ((Pi.single i 1 : Fin n → A) l)) =
      (Pi.single i 1 : Fin n → B) := by
    ext l
    simp [Pi.single_apply]
  rw [hb] at h
  exact h

/-- Identifying both pulled-back free sheaves gives exactly the coefficient
base-changed selected quotient morphism. -/
theorem selectedPresentationSheafMap_pullback_conjugate :
    (coordinatePullbackIso (Spec.map (CommRingCat.ofHom k.toRingHom)) n).inv ≫
      (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom k.toRingHom))).map
        (selectedPresentationSheafMap R A a f) ≫
      (coordinatePullbackIso (Spec.map (CommRingCat.ofHom k.toRingHom)) d).hom =
    selectedPresentationSheafMap R B a (k.comp f) := by
  rw [selectedPresentationSheafMap_pullback, Iso.inv_hom_id_assoc]

/-- The canonical target transition commutes with geometric pullback.
The proof uses epi uniqueness of the sheaf quotient. -/
@[reassoc]
theorem selectedPresentationSheafTransition_pullback
    (he : selectedChartPoint R a f = selectedChartPoint R b g) :
    (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom k.toRingHom))).map
        (selectedPresentationSheafTransition R A a b f g he).hom ≫
      (coordinatePullbackIso (Spec.map (CommRingCat.ofHom k.toRingHom)) d).hom =
    (coordinatePullbackIso (Spec.map (CommRingCat.ofHom k.toRingHom)) d).hom ≫
      (selectedPresentationSheafTransition R B a b (k.comp f) (k.comp g)
        (selectedPresentation_point_map R a b f g k he)).hom := by
  apply (cancel_epi
    ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom k.toRingHom))).map
      (selectedPresentationSheafMap R A a f))).mp
  rw [← Functor.map_comp_assoc, selectedPresentationSheafTransition_comp,
    selectedPresentationSheafMap_pullback,
    selectedPresentationSheafMap_pullback_assoc, selectedPresentationSheafTransition_comp]

/-- The same transition compatibility, as an equality of sheaf isomorphisms. -/
theorem selectedPresentationSheafTransition_pullback_iso
    (he : selectedChartPoint R a f = selectedChartPoint R b g) :
    (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom k.toRingHom))).mapIso
        (selectedPresentationSheafTransition R A a b f g he) ≪≫
      coordinatePullbackIso (Spec.map (CommRingCat.ofHom k.toRingHom)) d =
    coordinatePullbackIso (Spec.map (CommRingCat.ofHom k.toRingHom)) d ≪≫
      selectedPresentationSheafTransition R B a b (k.comp f) (k.comp g)
        (selectedPresentation_point_map R a b f g k he) := by
  apply Iso.ext
  exact selectedPresentationSheafTransition_pullback R A B a b f g k he

end FlagVarieties.Foundations.QuotientCharts
