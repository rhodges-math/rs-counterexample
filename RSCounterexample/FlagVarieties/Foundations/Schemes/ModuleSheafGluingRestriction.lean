import RSCounterexample.FlagVarieties.Foundations.Schemes.ModuleSheafGluingQuotient

/-!
# Supplying overlap transitions on the open subschemes

The over-site formulation used to compare sections is equivalent to the
scheme-module restriction formulation. This transports the transition
isomorphism and its common-source identity through Mathlib's canonical site
equivalence; it introduces no coordinate or section equations as extra inputs.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.ModuleSheafGluing

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

variable {X : Scheme.{u}} {E M N : X.Modules}

/-- Restriction to a subopen factors canonically through restriction to its
containing chart. -/
def restrictionThroughChart {V W : X.Opens} (h : W ≤ V) :
    Scheme.Modules.restrictFunctor W.ι ≅
      Scheme.Modules.restrictFunctor V.ι ⋙
        Scheme.Modules.restrictFunctor (X.homOfLE h) :=
  Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι h).symm ≪≫
    Scheme.Modules.restrictFunctorComp (X.homOfLE h) V.ι

/-- On a subopen of its source, an open pushforward is the original
module restricted to that subopen. -/
def pushforwardOnSubopenIso {V W : X.Opens} (h : W ≤ V) (Q : V.toScheme.Modules) :
    ((Scheme.Modules.pushforward V.ι).obj Q).restrict W.ι ≅
      Q.restrict (X.homOfLE h) :=
  (restrictionThroughChart h).app _ ≪≫
    (Scheme.Modules.restrictFunctor (X.homOfLE h)).mapIso
      ((Scheme.Modules.restrictFunctorAdjCounitIso V.ι).app Q)

/-- Transport a restriction isomorphism to the equivalent over site. -/
def restrictionIsoToOver (W : X.Opens) (e : M.restrict W.ι ≅ N.restrict W.ι) :
    M.over W ≅ N.over W :=
  (Scheme.Modules.overEquiv W).fullyFaithfulFunctor.preimageIso
    ((Scheme.Modules.overFunctorEquiv W).app M ≪≫ e ≪≫
      ((Scheme.Modules.overFunctorEquiv W).app N).symm)

/-- The canonical site comparison preserves the common-source identity. -/
theorem restrictionIsoToOver_source (W : X.Opens)
    (f : E ⟶ M) (g : E ⟶ N) (e : M.restrict W.ι ≅ N.restrict W.ι)
    (h : (Scheme.Modules.restrictFunctor W.ι).map f ≫ e.hom =
      (Scheme.Modules.restrictFunctor W.ι).map g) :
    f.over W ≫ (restrictionIsoToOver W e).hom = g.over W := by
  apply (Scheme.Modules.overEquiv W).functor.map_injective
  simp only [Functor.map_comp, restrictionIsoToOver,
    Functor.FullyFaithful.preimageIso_hom, Functor.FullyFaithful.map_preimage,
    Iso.trans_hom, Iso.symm_hom]
  change (Scheme.Modules.overEquiv W).functor.map (f.over W) ≫
    ((Scheme.Modules.overFunctorEquiv W).hom.app M ≫ e.hom ≫
      (Scheme.Modules.overFunctorEquiv W).inv.app N) =
        (Scheme.Modules.overEquiv W).functor.map (g.over W)
  have hf : (Scheme.Modules.overEquiv W).functor.map (f.over W) ≫
      (Scheme.Modules.overFunctorEquiv W).hom.app M =
    (Scheme.Modules.overFunctorEquiv W).hom.app E ≫
      (Scheme.Modules.restrictFunctor W.ι).map f :=
    (Scheme.Modules.overFunctorEquiv W).hom.naturality f
  have hg : (Scheme.Modules.overEquiv W).functor.map (g.over W) ≫
      (Scheme.Modules.overFunctorEquiv W).hom.app N =
    (Scheme.Modules.overFunctorEquiv W).hom.app E ≫
      (Scheme.Modules.restrictFunctor W.ι).map g :=
    (Scheme.Modules.overFunctorEquiv W).hom.naturality g
  rw [← Category.assoc, ← Category.assoc, hf]
  simp only [Category.assoc]
  rw [← Category.assoc ((Scheme.Modules.restrictFunctor W.ι).map f) e.hom
    ((Scheme.Modules.overFunctorEquiv W).inv.app N), h,
    ← Category.assoc, ← hg]
  simp

variable {I : Type u} (E : X.Modules) (U : I → X.Opens)
  (Q : ∀ i, (U i).toScheme.Modules) (q : ∀ i, E.restrict (U i).ι ⟶ Q i)

/-- The canonical pushforward comparison recovers the restriction of the
original local quotient on each subopen of its chart. -/
@[reassoc]
theorem chartAdjoint_subopen (i : I) {W : X.Opens} (hW : W ≤ U i) :
    (Scheme.Modules.restrictFunctor W.ι).map (chartAdjoint E U Q q i) ≫
      (pushforwardOnSubopenIso hW (Q i)).hom =
    (restrictionThroughChart hW).hom.app E ≫
      (Scheme.Modules.restrictFunctor (X.homOfLE hW)).map (q i) := by
  change (Scheme.Modules.restrictFunctor W.ι).map (chartAdjoint E U Q q i) ≫
    (restrictionThroughChart hW).hom.app (chartPushforward U Q i) ≫
      (Scheme.Modules.restrictFunctor (X.homOfLE hW)).map
        ((Scheme.Modules.restrictAdjunction (U i).ι).counit.app (Q i)) = _
  rw [← Category.assoc, (restrictionThroughChart hW).hom.naturality]
  simp only [Functor.comp_map, Category.assoc, ← Functor.map_comp, chartAdjoint_counit]

/-- Transitions on the full intersection open subschemes provide the
overlap hypothesis of the global quotient construction. -/
theorem compatible_of_restriction
    (h : ∀ i j, ∃ e :
      (chartPushforward U Q i).restrict (U i ⊓ U j).ι ≅
        (chartPushforward U Q j).restrict (U i ⊓ U j).ι,
      (Scheme.Modules.restrictFunctor (U i ⊓ U j).ι).map (chartAdjoint E U Q q i) ≫
        e.hom =
      (Scheme.Modules.restrictFunctor (U i ⊓ U j).ι).map (chartAdjoint E U Q q j)) :
    Compatible E U Q q := by
  intro i j
  obtain ⟨e, he⟩ := h i j
  exact ⟨restrictionIsoToOver (U i ⊓ U j) e,
    restrictionIsoToOver_source _ _ _ _ he⟩

/-- It suffices to give transitions between the original local targets on the
intersection subscheme, preserving their maps from the canonically identified
restriction of the single global source. -/
theorem compatible_of_chart_restriction
    (h : ∀ i j, ∃ e :
      (Q i).restrict (X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i)) ≅
        (Q j).restrict (X.homOfLE (inf_le_right : U i ⊓ U j ≤ U j)),
      (restrictionThroughChart (inf_le_left : U i ⊓ U j ≤ U i)).hom.app E ≫
        (Scheme.Modules.restrictFunctor (X.homOfLE inf_le_left)).map (q i) ≫ e.hom =
      (restrictionThroughChart (inf_le_right : U i ⊓ U j ≤ U j)).hom.app E ≫
        (Scheme.Modules.restrictFunctor (X.homOfLE inf_le_right)).map (q j)) :
    Compatible E U Q q := by
  apply compatible_of_restriction
  intro i j
  obtain ⟨e, he⟩ := h i j
  let ei := pushforwardOnSubopenIso (inf_le_left : U i ⊓ U j ≤ U i) (Q i)
  let ej := pushforwardOnSubopenIso (inf_le_right : U i ⊓ U j ≤ U j) (Q j)
  refine ⟨ei ≪≫ e ≪≫ ej.symm, ?_⟩
  apply (cancel_mono ej.hom).mp
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]
  change (Scheme.Modules.restrictFunctor (U i ⊓ U j).ι).map
      (chartAdjoint E U Q q i) ≫ ei.hom ≫ e.hom =
    (Scheme.Modules.restrictFunctor (U i ⊓ U j).ι).map
      (chartAdjoint E U Q q j) ≫ ej.hom
  rw [← Category.assoc, chartAdjoint_subopen, chartAdjoint_subopen]
  simpa only [Category.assoc] using he

end FlagVarieties.Foundations.ModuleSheafGluing
