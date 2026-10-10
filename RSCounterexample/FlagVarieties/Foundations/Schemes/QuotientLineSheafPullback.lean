import RSCounterexample.FlagVarieties.Foundations.Schemes.QuotientLineSheafIsomorphism
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-!
# Pullbacks of ordered quotient line sheaves

The pulled-back quotient uses Mathlib's sheaf pullback functor
and canonical coproduct comparison. Local line frames pull back
through the canonical restriction and composition isomorphisms.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientPair

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

variable {X Y : Scheme.{u}} (f : Y ⟶ X)

/-- Preimage of opens is final, since it sends the terminal open to the terminal open. -/
instance quotientPullbackOpens_final : (Opens.map f.base).Final where
  out V := by
    let T : StructuredArrow V (Opens.map f.base) :=
      StructuredArrow.mk (Y := ⊤) (homOfLE (by simp))
    let (i : StructuredArrow V (Opens.map f.base)) : Unique (i ⟶ T) :=
      ⟨⟨StructuredArrow.homMk (homOfLE le_top)⟩,
        fun _ => StructuredArrow.hom_ext _ _ (Subsingleton.elim _ _)⟩
    exact isConnected_of_isTerminal _ (CategoryTheory.Limits.IsTerminal.ofUnique T)

/-- The canonical unit-sheaf comparison for the sheaf pullback. -/
def quotientPullbackUnitIso :
    (Scheme.Modules.pullback f).obj (unitSheaf X) ≅ unitSheaf Y :=
  @asIso (SheafOfModules.{u} Y.ringCatSheaf) _ _ _
    (SheafOfModules.pullbackObjUnitToUnit (F := Opens.map f.base) f.toRingCatSheafHom) inferInstance

/-- The canonical pullback comparison fixes each of the two original summand labels. -/
def quotientPullbackFreeIso :
    (Scheme.Modules.pullback f).obj (orderedFreeSheaf X) ≅ orderedFreeSheaf Y :=
  SheafOfModules.pullbackObjFreeIso f.toRingCatSheafHom QuotientPairIndex.{u}

@[reassoc] theorem quotientPullbackFreeIso_generator (i : QuotientPairIndex.{u}) :
    (Scheme.Modules.pullback f).map (orderedFreeInclusion X i) ≫
        (quotientPullbackFreeIso f).hom =
      (quotientPullbackUnitIso f).hom ≫ orderedFreeInclusion Y i :=
  SheafOfModules.pullback_map_ιFree_comp_pullbackObjFreeIso_hom f.toRingCatSheafHom i

/-- The pulled-back ordered quotient, with its source canonically identified. -/
def quotientLinePullback {N : X.Modules} (q : orderedFreeSheaf X ⟶ N) :
    orderedFreeSheaf Y ⟶ (Scheme.Modules.pullback f).obj N :=
  (quotientPullbackFreeIso f).inv ≫ (Scheme.Modules.pullback f).map q

instance quotientLinePullback_epi {N : X.Modules} (q : orderedFreeSheaf X ⟶ N) [Epi q] :
    Epi (quotientLinePullback f q) := by
  unfold quotientLinePullback
  infer_instance

/-- Local line-sheaf triviality is preserved by arbitrary scheme pullback. -/
theorem locally_trivial_sheaf_pullback (N : X.Modules)
    (hline : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Nonempty (N.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))) :
    ∀ y : Y, ∃ V : Y.Opens, y ∈ V ∧
      Nonempty (((Scheme.Modules.pullback f).obj N).over V ≅
        SheafOfModules.unit (Y.ringCatSheaf.over V)) := by
  intro y
  obtain ⟨U, hyU, ⟨e⟩⟩ := hline (f y)
  let V := f ⁻¹ᵁ U
  let g : V.toScheme ⟶ U.toScheme := f.resLE U V le_rfl
  have hg : g ≫ U.ι = V.ι ≫ f := f.resLE_comp_ι le_rfl
  let er : ((Scheme.Modules.pullback f).obj N).restrict V.ι ≅ unitSheaf V.toScheme :=
    (Scheme.Modules.restrictFunctorIsoPullback V.ι).app _ ≪≫
      (Scheme.Modules.pullbackComp V.ι f).app N ≪≫
      (Scheme.Modules.pullbackCongr hg.symm).app N ≪≫
      ((Scheme.Modules.pullbackComp g U.ι).app N).symm ≪≫
      (Scheme.Modules.pullback g).mapIso
          ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app N).symm ≪≫
      (Scheme.Modules.pullback g).mapIso (overFrameToRestrict N U e) ≪≫
      quotientPullbackUnitIso g
  exact ⟨V, hyU, ⟨restrictFrameToOver _ V er⟩⟩

end FlagVarieties.Foundations.QuotientPair
