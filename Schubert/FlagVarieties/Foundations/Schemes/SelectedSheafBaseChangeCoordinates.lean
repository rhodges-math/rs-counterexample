import Schubert.FlagVarieties.Foundations.Schemes.SelectedSheafBaseChangeScalar

/-!
# Geometric pullback of original coordinate module maps

The proof expands each original generator into scalar multiples of the
original target generators, then applies sheaf pullback to that finite
sum. The comparison is Mathlib's canonical labelled free-sheaf comparison.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientCharts

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

variable (A : CommRingCat.{u}) {n d : ℕ}

/-- A linear map in the original coordinates, transported through the
canonical associated-sheaf/free-sheaf identifications. -/
def coordinateSheafMap (L : (Fin n → A) →ₗ[A] (Fin d → A)) :
    coordinateFreeSheaf (Spec A) n ⟶ coordinateFreeSheaf (Spec A) d :=
  (coordinateTildeFreeIso A n).inv ≫ tilde.map (ModuleCat.ofHom L) ≫
    (coordinateTildeFreeIso A d).hom

/-- Decomposition of a column, using the original coordinate labels. -/
theorem coordinate_column_sum (L : (Fin n → A) →ₗ[A] (Fin d → A)) (i : Fin n) :
    L.comp (LinearMap.single A (fun _ : Fin n => A) i) =
      ∑ j : Fin d, (LinearMap.single A (fun _ : Fin d => A) j).comp
        (scalarLinear A (L (Pi.single i 1) j)) := by
  classical
  apply LinearMap.ext_ring
  ext j
  simp [scalarLinear, LinearMap.comp_apply, LinearMap.single_apply]

/-- A generator's image as a sum of scalar maps followed by labelled
free summand inclusions. -/
theorem coordinateSheafMap_generator_sum
    (L : (Fin n → A) →ₗ[A] (Fin d → A)) (i : Fin n) :
    SheafOfModules.ιFree (⟨i⟩ : CoordinateIndex.{u} n) ≫ coordinateSheafMap A L =
      ∑ j : Fin d, affineScalarSheafMap A (L (Pi.single i 1) j) ≫
        SheafOfModules.ιFree (⟨j⟩ : CoordinateIndex.{u} d) := by
  classical
  rw [← coordinateTildeFreeIso_generator]
  simp only [coordinateSheafMap, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc, ← tilde.map_comp, ← ModuleCat.ofHom_comp, coordinate_column_sum]
  have hs : ModuleCat.ofHom (∑ j : Fin d,
      (LinearMap.single A (fun _ : Fin d => A) j).comp
        (scalarLinear A (L (Pi.single i 1) j))) =
      ∑ j : Fin d, ModuleCat.ofHom
        ((LinearMap.single A (fun _ : Fin d => A) j).comp
          (scalarLinear A (L (Pi.single i 1) j))) := by
    apply ModuleCat.hom_ext
    simp
  rw [hs]
  change (tilde.functor A).map (∑ j : Fin d, _) ≫ _ = _
  rw [Functor.map_sum, Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro j _
  rw [ModuleCat.ofHom_comp, Functor.map_comp, Category.assoc]
  change affineScalarSheafMap A (L (Pi.single i 1) j) ≫
    tilde.map (ModuleCat.ofHom (LinearMap.single A (fun _ : Fin d => A) j)) ≫
      (coordinateTildeFreeIso A d).hom = _
  rw [coordinateTildeFreeIso_generator]

variable {A} {B : CommRingCat.{u}} (k : A ⟶ B)
  (L : (Fin n → A) →ₗ[A] (Fin d → A))
  (L' : (Fin n → B) →ₗ[B] (Fin d → B))

/-- Geometric pullback naturality of a coordinate sheaf map, when its
original column coefficients are carried along the specified ring map. -/
theorem coordinateSheafMap_pullback
    (h : ∀ (i : Fin n) (j : Fin d), k (L (Pi.single i 1) j) = L' (Pi.single i 1) j) :
    (Scheme.Modules.pullback (Spec.map k)).map (coordinateSheafMap A L) ≫
      (coordinatePullbackIso (Spec.map k) d).hom =
    (coordinatePullbackIso (Spec.map k) n).hom ≫ coordinateSheafMap B L' := by
  classical
  apply Cofan.IsColimit.hom_ext
    (isColimitCofanMkObjOfIsColimit (Scheme.Modules.pullback (Spec.map k)) _ _
      (SheafOfModules.isColimitFreeCofan
        (R := (Spec A).ringCatSheaf) (CoordinateIndex.{u} n)))
  intro i
  rcases i with ⟨i⟩
  change (Scheme.Modules.pullback (Spec.map k)).map
      (SheafOfModules.ιFree (⟨i⟩ : CoordinateIndex.{u} n)) ≫
      (Scheme.Modules.pullback (Spec.map k)).map (coordinateSheafMap A L) ≫
        (coordinatePullbackIso (Spec.map k) d).hom =
    (Scheme.Modules.pullback (Spec.map k)).map
      (SheafOfModules.ιFree (⟨i⟩ : CoordinateIndex.{u} n)) ≫
      (coordinatePullbackIso (Spec.map k) n).hom ≫ coordinateSheafMap B L'
  rw [coordinatePullbackIso_generator_assoc]
  rw [← Functor.map_comp_assoc, coordinateSheafMap_generator_sum]
  rw [Functor.map_sum, Preadditive.sum_comp]
  rw [coordinateSheafMap_generator_sum, Preadditive.comp_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Functor.map_comp, Category.assoc, coordinatePullbackIso_generator,
    ← Category.assoc, affineScalarSheafMap_pullback, h, Category.assoc]

end FlagVarieties.Foundations.QuotientCharts
