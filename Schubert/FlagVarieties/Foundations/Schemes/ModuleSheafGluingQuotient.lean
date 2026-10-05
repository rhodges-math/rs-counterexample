import Schubert.FlagVarieties.Foundations.Schemes.ModuleSheafGluingOverlap
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free

/-!
# Gluing common-source quotient module sheaves

Starting with local module sheaves and epimorphisms from the restriction
of a single global source, commuting overlap isomorphisms construct a
global quotient. Its restrictions are canonically identified with the original
local targets, and the original quotient maps are recovered literally.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.ModuleSheafGluing

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

variable {X : Scheme.{u}} {I : Type u} (E : X.Modules) (U : I → X.Opens)
  (Q : ∀ i, (U i).toScheme.Modules) (q : ∀ i, E.restrict (U i).ι ⟶ Q i)

/-- The constructed global module sheaf: the image of the canonical
common-source map to the product of chart pushforwards. -/
def gluedModule : X.Modules :=
  quotientImage E (chartPushforward U Q) (chartAdjoint E U Q q)

/-- The global quotient of the given source sheaf. -/
def gluedQuotient : E ⟶ gluedModule E U Q q :=
  quotientMap E (chartPushforward U Q) (chartAdjoint E U Q q)

instance gluedQuotient_epi : Epi (gluedQuotient E U Q q) := by
  unfold gluedQuotient
  infer_instance

variable [∀ i, Epi (q i)] (h : Compatible E U Q q)

/-- The restriction of the constructed module is isomorphic to the
original local module, by overlap compatibility and the restriction counit. -/
def gluedChartIso (i : I) : (gluedModule E U Q q).restrict (U i).ι ≅ Q i :=
  localIso E (chartPushforward U Q) (chartAdjoint E U Q q) (U i) i
    (compatible_kernel E U Q q h i) ≪≫
      (Scheme.Modules.restrictFunctorAdjCounitIso (U i).ι).app (Q i)

/-- The local comparison recovers the original quotient, on the
restriction of the original source. -/
@[reassoc (attr := simp)]
theorem gluedQuotient_chart (i : I) :
    (Scheme.Modules.restrictFunctor (U i).ι).map (gluedQuotient E U Q q) ≫
      (gluedChartIso E U Q q h i).hom = q i := by
  change (Scheme.Modules.restrictFunctor (U i).ι).map
      (quotientMap E (chartPushforward U Q) (chartAdjoint E U Q q)) ≫
    localComponent E (chartPushforward U Q) (chartAdjoint E U Q q) (U i) i ≫
      (Scheme.Modules.restrictAdjunction (U i).ι).counit.app (Q i) = q i
  rw [← Category.assoc, restrict_quotientMap_component, chartAdjoint_counit]

/-- Local target frames induce local frames of the global
quotient, of any rank. -/
def gluedChartFrame {D : Type u}
    (frame : ∀ i, Q i ≅ SheafOfModules.free (R := (U i).toScheme.ringCatSheaf) D)
    (i : I) :
    (gluedModule E U Q q).restrict (U i).ι ≅
      SheafOfModules.free (R := (U i).toScheme.ringCatSheaf) D :=
  gluedChartIso E U Q q h i ≪≫ frame i

include h

/-- An open cover and local free targets give local freeness of the
constructed quotient, with the same arbitrary finite rank (including zero). -/
theorem glued_locally_free_frames (d : ℕ)
    (hcover : ∀ x : X, ∃ i, x ∈ U i)
    (frame : ∀ i, Q i ≅
      SheafOfModules.free (R := (U i).toScheme.ringCatSheaf) (ULift.{u} (Fin d))) :
    ∀ x : X, ∃ V : X.Opens, x ∈ V ∧
      Nonempty ((gluedModule E U Q q).restrict V.ι ≅
        SheafOfModules.free (R := V.toScheme.ringCatSheaf) (ULift.{u} (Fin d))) := by
  intro x
  obtain ⟨i, hi⟩ := hcover x
  exact ⟨U i, hi, ⟨gluedChartFrame E U Q q h frame i⟩⟩

/-- Existence of a global quotient with all prescribed local quotient
maps. The global module, quotient and comparison isomorphisms are constructed. -/
theorem exists_global_quotient :
    ∃ (M : X.Modules) (p : E ⟶ M), Epi p ∧
      ∀ i, ∃ e : M.restrict (U i).ι ≅ Q i,
        (Scheme.Modules.restrictFunctor (U i).ι).map p ≫ e.hom = q i := by
  exact ⟨gluedModule E U Q q, gluedQuotient E U Q q, inferInstance,
    fun i => ⟨gluedChartIso E U Q q h i, gluedQuotient_chart E U Q q h i⟩⟩

end FlagVarieties.Foundations.ModuleSheafGluing
