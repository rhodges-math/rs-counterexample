import RSCounterexample.FlagVarieties.Foundations.Schemes.QuotientLineSheafGlobal

/-!
# Invariance under an isomorphism of quotient line sheaves

The isomorphism is required to commute with the original ordered free
source. Its restriction transports sheaf frames and preserves
both original generator sections. The global projective morphism is
therefore unchanged.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientPair

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

variable {X : Scheme.{u}} {N N' : X.Modules}
  (q : orderedFreeSheaf X ⟶ N) (q' : orderedFreeSheaf X ⟶ N')
  (t : N ≅ N') (hq : q ≫ t.hom = q')

include hq in
/-- A commuting quotient isomorphism preserves each original ordered section. -/
theorem orderedQuotientSection_isomorphism (U : X.Opens) (i : QuotientPairIndex.{u}) :
    t.hom.app U (orderedQuotientSection q U i) = orderedQuotientSection q' U i := by
  change ((orderedFreeInclusion X i ≫ q) ≫ t.hom).app U (1 : Γ(X, U)) = _
  rw [Category.assoc, hq]
  rfl

/-- Restricting and evaluating a transported sheaf frame applies the original isomorphism. -/
theorem overSheafSectionFrame_isomorphism (U : X.Opens)
    (e : N'.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) (m : Γ(N, U)) :
    overSheafSectionFrame N U ((SheafOfModules.overFunctor X.ringCatSheaf U).mapIso t ≪≫ e) m =
      overSheafSectionFrame N' U e (t.hom.app U m) := rfl

include hq

theorem framedQuotientCoefficient_isomorphism (U : X.Opens)
    (e : N'.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) (i : QuotientPairIndex.{u}) :
    framedQuotientCoefficient q U
      ((SheafOfModules.overFunctor X.ringCatSheaf U).mapIso t ≪≫ e) i =
      framedQuotientCoefficient q' U e i := by
  unfold framedQuotientCoefficient
  rw [overSheafSectionFrame_isomorphism, orderedQuotientSection_isomorphism q q' t hq]

variable {A : Type u} [CommRing A] [Epi q] [Epi q']
  (hline : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
    Nonempty (N.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)))
  (hline' : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
    Nonempty (N'.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)))

/-- The global scheme morphism depends only on the isomorphism class of the ordered quotient. -/
theorem fromQuotientLineSheaf_isomorphism (φ : A →+* Γ(X, ⊤)) :
    fromQuotientLineSheaf q hline φ = fromQuotientLineSheaf q' hline' φ := by
  let D := chooseAffineSheafFrameCover N' hline'
  apply (X.openCoverOfIsOpenCover D.opens D.isOpenCover).hom_ext
  intro x
  change (D.opens x).ι ≫ _ = (D.opens x).ι ≫ _
  rw [fromQuotientLineSheaf_local_formula q hline φ (D.opens x) (D.affine x)
      ((SheafOfModules.overFunctor X.ringCatSheaf (D.opens x)).mapIso t ≪≫ D.frame x),
    fromQuotientLineSheaf_local_formula q' hline' φ (D.opens x) (D.affine x) (D.frame x)]
  congr 1 <;> exact framedQuotientCoefficient_isomorphism q q' t hq _ _ _

theorem fromQuotientLineSheafOver_isomorphism (b : X ⟶ Spec (CommRingCat.of A)) :
    fromQuotientLineSheafOver q hline b = fromQuotientLineSheafOver q' hline' b :=
  fromQuotientLineSheaf_isomorphism q q' t hq hline hline' (quotientLineBaseCoefficients b)

end FlagVarieties.Foundations.QuotientPair
