import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# A common-source image for gluing quotient module sheaves

The object constructed here is the image of a morphism to a product of
module sheaves. Its local comparison is an isomorphism when the local quotient
maps have the same kernels on the chart in question. The overlap module derives
this sectionwise kernel condition from transition isomorphisms.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.ModuleSheafGluing

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

variable {X : Scheme.{u}} {I : Type u}

/-- A mono of module sheaves is injective on every open's sections. -/
theorem mono_app_injective {M N : X.Modules} (f : M ⟶ N) [Mono f] (W : X.Opens) :
    Function.Injective (f.app W) := by
  let F : X.Modules ⥤ ModuleCat.{u} (X.ringCatSheaf.obj.obj (.op W)) :=
    SheafOfModules.evaluation X.ringCatSheaf (.op W)
  have : PreservesLimitsOfSize.{u, u} F :=
    inferInstanceAs (PreservesLimitsOfSize.{u, u}
      (SheafOfModules.evaluation.{u} X.ringCatSheaf (.op W)))
  have : Mono (F.map f) := inferInstance
  exact (ModuleCat.mono_iff_injective (F.map f)).mp this

/-- Sections of a product of module sheaves are determined by their projections. -/
theorem product_app_ext (P : I → X.Modules) (W : X.Opens)
    (x y : Γ(∏ᶜ P, W))
    (h : ∀ i, (Pi.π P i).app W x = (Pi.π P i).app W y) : x = y := by
  let F : X.Modules ⥤ ModuleCat.{u} (X.ringCatSheaf.obj.obj (.op W)) :=
    SheafOfModules.evaluation X.ringCatSheaf (.op W)
  have : PreservesLimitsOfSize.{u, u} F :=
    inferInstanceAs (PreservesLimitsOfSize.{u, u}
      (SheafOfModules.evaluation.{u} X.ringCatSheaf (.op W)))
  exact Concrete.isLimit_ext _ (isLimitOfPreserves F (limit.isLimit (Discrete.functor P)))
    x y (fun i => h i.as)

variable (E : X.Modules) (P : I → X.Modules) (t : ∀ i, E ⟶ P i)

/-- The simultaneous sheaf map to all local pushforwards. -/
def familyMap : E ⟶ ∏ᶜ P := Pi.lift t

/-- The global module sheaf, defined as a categorical image rather than by gluing data. -/
def quotientImage : X.Modules := image (familyMap E P t)

/-- The canonical epimorphism from the original global source. -/
def quotientMap : E ⟶ quotientImage E P t := factorThruImage (familyMap E P t)

instance quotientMap_epi : Epi (quotientMap E P t) := by
  unfold quotientMap
  infer_instance

/-- The comparison to the `i`-th pushed-forward local quotient. -/
def quotientComponent (i : I) : quotientImage E P t ⟶ P i :=
  image.ι (familyMap E P t) ≫ Pi.π P i

@[reassoc (attr := simp)]
theorem quotientMap_component (i : I) :
    quotientMap E P t ≫ quotientComponent E P t i = t i := by
  simp [quotientMap, quotientComponent, familyMap]

/-- A section killed by every component is killed by the image quotient. -/
theorem quotientMap_app_eq_zero (W : X.Opens) (x : Γ(E, W))
    (h : ∀ i, (t i).app W x = 0) : (quotientMap E P t).app W x = 0 := by
  apply mono_app_injective (image.ι (familyMap E P t)) W
  rw [map_zero]
  change ((quotientMap E P t ≫ image.ι (familyMap E P t)).app W) x = 0
  rw [show quotientMap E P t ≫ image.ι (familyMap E P t) = familyMap E P t from image.fac _]
  apply product_app_ext P W
  intro i
  rw [map_zero]
  change ((familyMap E P t ≫ Pi.π P i).app W) x = 0
  simpa [familyMap] using h i

variable (U : X.Opens) (i : I)

/-- The restriction of the global comparison to a chart. -/
def localComponent : (quotientImage E P t).restrict U.ι ⟶ (P i).restrict U.ι :=
  (Scheme.Modules.restrictFunctor U.ι).map (quotientComponent E P t i)

@[reassoc (attr := simp)]
theorem restrict_quotientMap_component :
    (Scheme.Modules.restrictFunctor U.ι).map (quotientMap E P t) ≫
      localComponent E P t U i = (Scheme.Modules.restrictFunctor U.ι).map (t i) := by
  rw [localComponent, ← Functor.map_comp, quotientMap_component]

/-- Kernel agreement on the subopens of a chart makes the global quotient
annihilate the kernel of that chart's quotient. -/
theorem local_kernel_quotientMap_eq_zero
    (h : ∀ (W : X.Opens), W ≤ U → ∀ x : Γ(E, W),
      (t i).app W x = 0 → ∀ j, (t j).app W x = 0) :
    kernel.ι ((Scheme.Modules.restrictFunctor U.ι).map (t i)) ≫
      (Scheme.Modules.restrictFunctor U.ι).map (quotientMap E P t) = 0 := by
  apply Scheme.Modules.hom_ext
  intro V
  ext x
  change (quotientMap E P t).app (U.ι ''ᵁ V)
    ((kernel.ι ((Scheme.Modules.restrictFunctor U.ι).map (t i))).app V x) = 0
  apply quotientMap_app_eq_zero
  apply h (U.ι ''ᵁ V)
  · exact le_trans (Scheme.Hom.image_mono U.ι le_top) (by simp)
  · have hk := congrArg (fun f => (f.app V) x)
      (kernel.condition ((Scheme.Modules.restrictFunctor U.ι).map (t i)))
    exact hk

/-- The inverse local comparison is descended through the local epi. -/
def localInverse
    [Epi ((Scheme.Modules.restrictFunctor U.ι).map (t i))]
    (h : ∀ (W : X.Opens), W ≤ U → ∀ x : Γ(E, W),
      (t i).app W x = 0 → ∀ j, (t j).app W x = 0) :
    (P i).restrict U.ι ⟶ (quotientImage E P t).restrict U.ι :=
  Abelian.epiDesc ((Scheme.Modules.restrictFunctor U.ι).map (t i))
    ((Scheme.Modules.restrictFunctor U.ι).map (quotientMap E P t))
    (local_kernel_quotientMap_eq_zero E P t U i h)

@[reassoc (attr := simp)]
theorem local_map_inverse
    [Epi ((Scheme.Modules.restrictFunctor U.ι).map (t i))]
    (h : ∀ (W : X.Opens), W ≤ U → ∀ x : Γ(E, W),
      (t i).app W x = 0 → ∀ j, (t j).app W x = 0) :
    (Scheme.Modules.restrictFunctor U.ι).map (t i) ≫ localInverse E P t U i h =
      (Scheme.Modules.restrictFunctor U.ι).map (quotientMap E P t) := by
  apply Abelian.comp_epiDesc

/-- The image restricts to the local quotient. No global-section
surjectivity is used; only the local epimorphism is needed. -/
def localIso
    [Epi ((Scheme.Modules.restrictFunctor U.ι).map (t i))]
    (h : ∀ (W : X.Opens), W ≤ U → ∀ x : Γ(E, W),
      (t i).app W x = 0 → ∀ j, (t j).app W x = 0) :
    (quotientImage E P t).restrict U.ι ≅ (P i).restrict U.ι where
  hom := localComponent E P t U i
  inv := localInverse E P t U i h
  hom_inv_id := by
    apply (cancel_epi ((Scheme.Modules.restrictFunctor U.ι).map (quotientMap E P t))).mp
    simp only [← Category.assoc, restrict_quotientMap_component, local_map_inverse,
      Category.comp_id]
  inv_hom_id := by
    apply (cancel_epi ((Scheme.Modules.restrictFunctor U.ι).map (t i))).mp
    simp only [← Category.assoc, local_map_inverse, restrict_quotientMap_component,
      Category.comp_id]

end FlagVarieties.Foundations.ModuleSheafGluing
