import Schubert.FlagVarieties.Foundations.Schemes.SelectedPresentationNaturality
import Schubert.FlagVarieties.Foundations.Schemes.AffineQuotientSheafPresentation

/-!
# Free quotient sheaves on the matrix charts

The ordered finite-coordinate module is identified with the free
sheaf using its original standard basis. Applying the associated-sheaf
functor to the chart quotient gives a split epimorphism. Changes
of quotient target give sheaf isomorphisms preserving that map.
-/

noncomputable section

namespace FlagVarieties.Foundations.QuotientCharts

open AlgebraicGeometry CategoryTheory

universe u

/-- Coordinate labels in the universe of the base scheme. -/
abbrev CoordinateIndex (n : ℕ) : Type u := ULift.{u} (Fin n)

/-- The original standard coordinate basis, with only the index universe lifted. -/
def coordinateFinsuppEquiv (A : CommRingCat.{u}) (n : ℕ) :
    (Fin n → A) ≃ₗ[A] (CoordinateIndex.{u} n →₀ A) :=
  (Pi.basisFun A (Fin n)).repr ≪≫ₗ Finsupp.domLCongr Equiv.ulift.symm

@[simp] theorem coordinateFinsuppEquiv_single (A : CommRingCat.{u}) {n : ℕ} (i : Fin n) :
    coordinateFinsuppEquiv A n (Pi.single i 1) = Finsupp.single ⟨i⟩ 1 := by
  classical
  rw [coordinateFinsuppEquiv, LinearEquiv.trans_apply,
    ← Pi.basisFun_apply A (Fin n) i, Module.Basis.repr_self, Finsupp.domLCongr_single]
  rfl

/-- The free module sheaf with the original finite coordinate labels. -/
abbrev coordinateFreeSheaf (X : Scheme.{u}) (n : ℕ) : X.Modules :=
  SheafOfModules.free (R := X.ringCatSheaf) (CoordinateIndex.{u} n)

/-- The canonical associated-sheaf identification with this labelled free sheaf. -/
def coordinateTildeFreeIso (A : CommRingCat.{u}) (n : ℕ) :
    tilde (ModuleCat.of A (Fin n → A)) ≅ coordinateFreeSheaf (Spec A) n :=
  (tilde.functor A).mapIso (coordinateFinsuppEquiv A n).toModuleIso ≪≫
    tildeFinsupp (CoordinateIndex.{u} n)

variable (R : Type u) [CommRing R] (A : CommRingCat.{u}) [Algebra R A]
  {n d : ℕ} (a b : Fin d ↪ Fin n)
  (f g : MvPolynomial (Fin d × Fin (n - d)) R →ₐ[R] A)

/-- A chart's quotient as a morphism of labelled free sheaves. -/
def selectedPresentationSheafMap :
    coordinateFreeSheaf (Spec A) n ⟶ coordinateFreeSheaf (Spec A) d :=
  (coordinateTildeFreeIso A n).inv ≫
    tilde.map (ModuleCat.ofHom (selectedPresentationMap R a f)) ≫
      (coordinateTildeFreeIso A d).hom

/-- The section uses the unchanged selected-coordinate inclusion. -/
def selectedPresentationSheafSection :
    coordinateFreeSheaf (Spec A) d ⟶ coordinateFreeSheaf (Spec A) n :=
  (coordinateTildeFreeIso A d).inv ≫
    tilde.map (ModuleCat.ofHom (coordinateInclusion (R := A) a)) ≫
      (coordinateTildeFreeIso A n).hom

theorem selectedPresentationSheafSection_comp :
    selectedPresentationSheafSection A a ≫ selectedPresentationSheafMap R A a f =
      𝟙 (coordinateFreeSheaf (Spec A) d) := by
  simp only [selectedPresentationSheafSection, selectedPresentationSheafMap,
    Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc (tilde.map _) (tilde.map _), ← tilde.map_comp,
    ← ModuleCat.ofHom_comp, selectedPresentationMap_section, ModuleCat.ofHom_id,
    tilde.map_id, Category.id_comp, Iso.inv_hom_id]

instance selectedPresentationSheafMap_epi : Epi (selectedPresentationSheafMap R A a f) := by
  let : Epi (tilde.map (ModuleCat.ofHom (selectedPresentationMap R a f))) :=
    QuotientPair.associated_map_epi _ (selectedPresentationMap_surjective R a f)
  unfold selectedPresentationSheafMap
  infer_instance

/-- The canonical change of quotient target as a sheaf isomorphism. -/
def selectedPresentationSheafTransition
    (he : selectedChartPoint R a f = selectedChartPoint R b g) :
    coordinateFreeSheaf (Spec A) d ≅ coordinateFreeSheaf (Spec A) d :=
  (coordinateTildeFreeIso A d).symm ≪≫
    (tilde.functor A).mapIso (selectedPresentationTransition R a b f g he).toModuleIso ≪≫
      coordinateTildeFreeIso A d

/-- The original ambient quotient map is preserved on the sheaf itself. -/
theorem selectedPresentationSheafTransition_comp
    (he : selectedChartPoint R a f = selectedChartPoint R b g) :
    selectedPresentationSheafMap R A a f ≫
        (selectedPresentationSheafTransition R A a b f g he).hom =
      selectedPresentationSheafMap R A b g := by
  simp only [selectedPresentationSheafMap, selectedPresentationSheafTransition,
    Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]
  change (coordinateTildeFreeIso A n).inv ≫
    tilde.map (ModuleCat.ofHom (selectedPresentationMap R a f)) ≫
      tilde.map (ModuleCat.ofHom (selectedPresentationTransition R a b f g he).toLinearMap) ≫
        (coordinateTildeFreeIso A d).hom = _
  rw [← Category.assoc (tilde.map _) (tilde.map _), ← tilde.map_comp,
    ← ModuleCat.ofHom_comp, selectedPresentationTransition_comp]

/-- Preserving the same quotient map forces uniqueness at sheaf level. -/
theorem selectedPresentationSheafTransition_unique
    (he : selectedChartPoint R a f = selectedChartPoint R b g)
    (t : coordinateFreeSheaf (Spec A) d ⟶ coordinateFreeSheaf (Spec A) d)
    (ht : selectedPresentationSheafMap R A a f ≫ t = selectedPresentationSheafMap R A b g) :
    (selectedPresentationSheafTransition R A a b f g he).hom = t := by
  apply (cancel_epi (selectedPresentationSheafMap R A a f)).mp
  exact (selectedPresentationSheafTransition_comp R A a b f g he).trans ht.symm

@[simp] theorem selectedPresentationSheafTransition_refl :
    selectedPresentationSheafTransition R A a a f f rfl =
      Iso.refl (coordinateFreeSheaf (Spec A) d) := by
  apply Iso.ext
  apply selectedPresentationSheafTransition_unique
  exact Category.comp_id _

/-- The sheaf transitions satisfy the triple-overlap identity. -/
theorem selectedPresentationSheafTransition_trans (c : Fin d ↪ Fin n)
    (h : MvPolynomial (Fin d × Fin (n - d)) R →ₐ[R] A)
    (he : selectedChartPoint R a f = selectedChartPoint R b g)
    (he' : selectedChartPoint R b g = selectedChartPoint R c h) :
    selectedPresentationSheafTransition R A a b f g he ≪≫
        selectedPresentationSheafTransition R A b c g h he' =
      selectedPresentationSheafTransition R A a c f h (he.trans he') := by
  apply Iso.ext
  apply (cancel_epi (selectedPresentationSheafMap R A a f)).mp
  simp only [Iso.trans_hom, ← Category.assoc, selectedPresentationSheafTransition_comp]

end FlagVarieties.Foundations.QuotientCharts
