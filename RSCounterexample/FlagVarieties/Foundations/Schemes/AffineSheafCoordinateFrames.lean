import RSCounterexample.FlagVarieties.Foundations.Schemes.AffineSheafLocalFiniteFree
import RSCounterexample.FlagVarieties.Foundations.Schemes.ModuleSheafLocalFrames
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Sections of finite coordinate frames

Evaluation preserves finite biproducts. Consequently a finite free sheaf
has the expected finite free module of sections on every open, including
the zero-rank case. No surjectivity on sections is assumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u

/-- Evaluate the finite coproduct of copies of the structure sheaf. -/
def coordinateFreeSectionIso {X : Scheme.{u}} (U : X.Opens) (d : ℕ) :
    ModuleCat.of Γ(X, U) Γ(coordinateFreeSheaf X d, U) ≅
      ModuleCat.of Γ(X, U) (CoordinateIndex.{u} d → Γ(X, U)) := by
  let F := SheafOfModules.evaluation X.ringCatSheaf (op U)
  haveI : F.Additive := inferInstanceAs
    (SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation _ (op U)).Additive
  let f := fun _ : CoordinateIndex.{u} d => SheafOfModules.unit X.ringCatSheaf
  letI : HasBiproduct f := HasBiproduct.of_hasProduct f
  letI : HasBiproduct (F.obj ∘ f) := HasBiproduct.of_hasProduct _
  letI : PreservesBiproduct f F := preservesBiproduct_of_preservesProduct F
  exact F.mapIso (biproduct.isoCoproduct f).symm ≪≫
    Functor.mapBiproduct F f ≪≫ biproduct.isoProduct (F.obj ∘ f) ≪≫
      ModuleCat.piIsoPi (F.obj ∘ f)

/-- The section frame keeps the original finite coordinate labels. -/
def coordinateFreeSectionEquiv {X : Scheme.{u}} (U : X.Opens) (d : ℕ) :
    Γ(coordinateFreeSheaf X d, U) ≃ₗ[Γ(X, U)] (Fin d → Γ(X, U)) :=
  (coordinateFreeSectionIso U d).toLinearEquiv ≪≫ₗ
    LinearEquiv.funCongrLeft Γ(X, U) Γ(X, U) Equiv.ulift.symm

/-- Evaluate a local coordinate frame on its terminal open. -/
def overCoordinateSectionFrame {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) (d : ℕ)
    (e : M.over U ≅
      SheafOfModules.free (R := X.ringCatSheaf.over U) (CoordinateIndex.{u} d)) :
    Γ(M, U) ≃ₗ[Γ(X, U)] (Fin d → Γ(X, U)) :=
  ((SheafOfModules.evaluation _ (op (Over.mk (𝟙 U)))).mapIso
    (e ≪≫ (ModuleSheafGluing.coordinateOverFreeIso U d).symm)).toLinearEquiv ≪≫ₗ
      coordinateFreeSectionEquiv U d

end FlagVarieties.Foundations.QuotientCharts
