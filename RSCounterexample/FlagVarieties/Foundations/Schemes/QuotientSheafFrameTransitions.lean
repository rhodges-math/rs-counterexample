import RSCounterexample.FlagVarieties.Foundations.Schemes.QuotientSheafOrderedSections

/-!
# Sheaf frame coordinates and their common-unit transitions

The two coefficients are the images of the original two quotient
sections in a local sheaf frame. Restricting the sheaf frame
restricts those coefficients. Two such frames on an intersection differ
by a common unit of its ring of sections.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientPair

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u v

variable {X : Scheme.{u}} {N : X.Modules}

/-- Evaluation of a sheaf frame commutes with restriction to a smaller open. -/
theorem overSheafSectionFrame_restrict {U V : X.Opens} (h : V ≤ U)
    (e : N.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) (m : Γ(N, U)) :
    overSheafSectionFrame N V (restrictOverSheafFrame N h e)
        (N.presheaf.map (homOfLE h).op m) =
      X.presheaf.map (homOfLE h).op (overSheafSectionFrame N U e m) := by
  let j : Over.mk (homOfLE h) ⟶ Over.mk (𝟙 U) :=
    Over.homMk (homOfLE h) (Category.comp_id _)
  exact PresheafOfModules.naturality_apply e.hom.val j.op m

/-- The ring of the open subscheme restricts exactly as the ambient structure sheaf does. -/
theorem topIso_inv_restrict {U V : X.Opens} (h : V ≤ U) (a : Γ(X, U)) :
    (X.homOfLE h).appTop (U.topIso.inv a) =
      V.topIso.inv (X.presheaf.map (homOfLE h).op a) := by
  change ((U.topIso.inv ≫ (X.homOfLE h).appTop) a) =
    ((X.presheaf.map (homOfLE h).op ≫ V.topIso.inv) a)
  congr 1
  simp only [Scheme.homOfLE_appTop, Scheme.Opens.topIso_inv, ← Functor.map_comp]
  rfl

/-- The coefficient in a local sheaf frame, over the open-scheme ring. -/
def framedQuotientCoefficient (q : orderedFreeSheaf X ⟶ N) (U : X.Opens)
    (e : N.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (i : QuotientPairIndex.{u}) : RingOn U :=
  U.topIso.inv (overSheafSectionFrame N U e (orderedQuotientSection q U i))

theorem framedQuotientCoefficient_restrict (q : orderedFreeSheaf X ⟶ N)
    {U V : X.Opens} (h : V ≤ U)
    (e : N.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (i : QuotientPairIndex.{u}) :
    (X.homOfLE h).appTop (framedQuotientCoefficient q U e i) =
      framedQuotientCoefficient q V (restrictOverSheafFrame N h e) i := by
  unfold framedQuotientCoefficient
  rw [topIso_inv_restrict, ← overSheafSectionFrame_restrict,
    orderedQuotientSection_restrict]

theorem framedQuotientCoefficient_coprime [N.IsQuasicoherent]
    (q : orderedFreeSheaf X ⟶ N) [Epi q] (U : X.Opens) (hU : IsAffineOpen U)
    (e : N.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    IsCoprime (framedQuotientCoefficient q U e ⟨0⟩)
      (framedQuotientCoefficient q U e ⟨1⟩) :=
  (orderedQuotientSection_coprime q U hU (overSheafSectionFrame N U e)).map U.topIso.inv.hom

/-- Common-unit overlap compatibility follows from two frames of the same section module. -/
theorem sheafFrames_overlap_common_unit (q : orderedFreeSheaf X ⟶ N)
    {U V : X.Opens}
    (e : N.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (e' : N.over V ≅ SheafOfModules.unit (X.ringCatSheaf.over V)) :
    ∃ unit : (RingOn (U ⊓ V))ˣ,
      (X.homOfLE (inf_le_left : U ⊓ V ≤ U)).appTop (framedQuotientCoefficient q U e ⟨0⟩) =
        (unit : RingOn (U ⊓ V)) *
          (X.homOfLE (inf_le_right : U ⊓ V ≤ V)).appTop
            (framedQuotientCoefficient q V e' ⟨0⟩) ∧
      (X.homOfLE (inf_le_left : U ⊓ V ≤ U)).appTop (framedQuotientCoefficient q U e ⟨1⟩) =
        (unit : RingOn (U ⊓ V)) *
          (X.homOfLE (inf_le_right : U ⊓ V ≤ V)).appTop
            (framedQuotientCoefficient q V e' ⟨1⟩) := by
  obtain ⟨unit, h0, h1⟩ := quotient_frame_change_pair
    (overSheafSectionFrame N (U ⊓ V) (restrictOverSheafFrame N inf_le_right e'))
    (overSheafSectionFrame N (U ⊓ V) (restrictOverSheafFrame N inf_le_left e))
    (orderedQuotientSection q (U ⊓ V) ⟨0⟩) (orderedQuotientSection q (U ⊓ V) ⟨1⟩)
  refine ⟨Units.map (U ⊓ V).topIso.inv.hom unit, ?_, ?_⟩
  · rw [framedQuotientCoefficient_restrict, framedQuotientCoefficient_restrict]
    change (U ⊓ V).topIso.inv _ =
      (U ⊓ V).topIso.inv (unit : Γ(X, U ⊓ V)) * (U ⊓ V).topIso.inv _
    rw [← map_mul]
    exact congrArg (U ⊓ V).topIso.inv h0
  · rw [framedQuotientCoefficient_restrict, framedQuotientCoefficient_restrict]
    change (U ⊓ V).topIso.inv _ =
      (U ⊓ V).topIso.inv (unit : Γ(X, U ⊓ V)) * (U ⊓ V).topIso.inv _
    rw [← map_mul]
    exact congrArg (U ⊓ V).topIso.inv h1

end FlagVarieties.Foundations.QuotientPair
