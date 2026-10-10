import RSCounterexample.FlagVarieties.Foundations.Schemes.SelectedPresentationSheaf

/-!
# Original coordinate generators under the free-sheaf comparison

The comparison with a free sheaf respects each original summand map, not
merely its abstract isomorphism class. These identities are used to compare
matrix quotient maps after scheme restriction and base change.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientCharts

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

variable (A : CommRingCat.{u})

/-- The associated-sheaf coproduct comparison retains each labelled summand. -/
theorem tildeFinsupp_generator (I : Type u) (i : I) :
    tilde.map (ModuleCat.ofHom (Finsupp.lsingle i : A →ₗ[A] (I →₀ A))) ≫
        (tildeFinsupp I).hom = SheafOfModules.ιFree i := by
  classical
  let H : IsColimit ((tilde.functor A).mapCocone (ModuleCat.finsuppCocone A A I)) :=
    isColimitOfPreserves (tilde.functor A) (ModuleCat.finsuppCoconeIsColimit A A I)
  let e : (Discrete.functor fun (_ : I) => ModuleCat.of A A) ⋙ tilde.functor A ≅
      Discrete.functor fun _ => SheafOfModules.unit (Spec A).ringCatSheaf :=
    Discrete.natIso (fun _ => tildeSelf)
  exact ((IsColimit.precomposeHomEquiv e.symm _).symm H).comp_coconePointUniqueUpToIso_hom
    (coproductIsCoproduct _) (Discrete.mk i)

/-- The original coordinate inclusion is sent to the identically labelled free summand. -/
theorem coordinateTildeFreeIso_generator {n : ℕ} (i : Fin n) :
    tilde.map (ModuleCat.ofHom (LinearMap.single A (fun _ : Fin n => A) i)) ≫
        (coordinateTildeFreeIso A n).hom = SheafOfModules.ιFree (⟨i⟩ : CoordinateIndex.{u} n) := by
  have he : (coordinateFinsuppEquiv A n).toLinearMap.comp
      (LinearMap.single A (fun _ : Fin n => A) i) =
        (Finsupp.lsingle ⟨i⟩ : A →ₗ[A] (CoordinateIndex.{u} n →₀ A)) := by
    apply LinearMap.ext_ring
    exact coordinateFinsuppEquiv_single A i
  change tilde.map (ModuleCat.ofHom (LinearMap.single A (fun _ : Fin n => A) i)) ≫
    tilde.map (ModuleCat.ofHom (coordinateFinsuppEquiv A n).toLinearMap) ≫
      (tildeFinsupp (CoordinateIndex.{u} n)).hom = _
  rw [← Category.assoc, ← tilde.map_comp, ← ModuleCat.ofHom_comp, he]
  exact tildeFinsupp_generator A _ _

/-- The original quotient image of each ambient generator is preserved as a full sheaf map. -/
theorem selectedPresentationSheafMap_generator
    (R : Type u) [CommRing R] [Algebra R A] {n d : ℕ} (a : Fin d ↪ Fin n)
    (f : MvPolynomial (Fin d × Fin (n - d)) R →ₐ[R] A) (i : Fin n) :
    SheafOfModules.ιFree (⟨i⟩ : CoordinateIndex.{u} n) ≫
        selectedPresentationSheafMap R A a f =
      tilde.map (ModuleCat.ofHom ((selectedPresentationMap R a f).comp
        (LinearMap.single A (fun _ : Fin n => A) i))) ≫
          (coordinateTildeFreeIso A d).hom := by
  rw [← coordinateTildeFreeIso_generator]
  simp only [selectedPresentationSheafMap, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc, ← tilde.map_comp, ← ModuleCat.ofHom_comp]

end FlagVarieties.Foundations.QuotientCharts
