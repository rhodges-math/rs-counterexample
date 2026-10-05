import Schubert.FlagVarieties.Foundations.Schemes.ProjectiveLineGluingData

/-!
# Gluing ordered-pair morphisms on a source open cover

The supplied local pairs define a unique morphism to the projective-line
scheme. Their common-unit relations imply equality of full morphisms on overlaps.
There is no assumed global pair and no quotient-line universal property.
-/

noncomputable section

namespace FlagVarieties.Foundations.ProjectiveLine.OpenPairData

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u v

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {ι : Type v}
  {U : ι → X.Opens} (D : OpenPairData U) (φ : R →+* Γ(X, ⊤))
  (hU : IsOpenCover U)

set_option backward.isDefEq.respectTransparency false in
/-- Descent compatibility on the categorical pullback of two covering inclusions. -/
theorem localMap_pullback (i j : ι) :
    pullback.fst (U i).ι (U j).ι ≫ D.localMap φ i =
      pullback.snd (U i).ι (U j).ι ≫ D.localMap φ j := by
  rw [← cancel_epi (isPullback_opens_inf (U i) (U j)).isoPullback.hom]
  simpa only [IsPullback.isoPullback_hom_fst_assoc,
    IsPullback.isoPullback_hom_snd_assoc] using D.localMap_overlap φ i j

/-- The scheme morphism obtained by descent of the locally coprime ordered pairs. -/
def glue : X ⟶ scheme R :=
  (X.openCoverOfIsOpenCover U hU).glueMorphisms (D.localMap φ) (D.localMap_pullback φ)

/-- Restriction to each covering open recovers the supplied ordered-pair morphism. -/
@[reassoc] theorem restrict_glue (i : ι) :
    (U i).ι ≫ D.glue φ hU =
      fromPair (coefficientsOn φ (U i)) (D.delta i) (D.epsilon i) (D.coprime i) :=
  (X.openCoverOfIsOpenCover U hU).ι_glueMorphisms (D.localMap φ)
    (D.localMap_pullback φ) i

/-- The glued map is the only scheme morphism with these local restrictions. -/
theorem glue_unique (f : X ⟶ scheme R)
    (hf : ∀ i, (U i).ι ≫ f = D.localMap φ i) : f = D.glue φ hU := by
  apply (X.openCoverOfIsOpenCover U hU).hom_ext
  intro i
  exact (hf i).trans (D.restrict_glue φ hU i).symm

include hU in
theorem existsUnique_glued :
    ∃! f : X ⟶ scheme R, ∀ i, (U i).ι ≫ f = D.localMap φ i := by
  refine ⟨D.glue φ hU, fun i => D.restrict_glue φ hU i, ?_⟩
  exact fun f hf => D.glue_unique φ hU f hf

set_option backward.isDefEq.respectTransparency false in
/-- Descent preserves the structural morphism associated with the single coefficient hom. -/
@[reassoc] theorem glue_toSpec :
    D.glue φ hU ≫ toSpec R = X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ) := by
  apply (X.openCoverOfIsOpenCover U hU).hom_ext
  intro i
  change (U i).ι ≫ D.glue φ hU ≫ toSpec R =
    (U i).ι ≫ X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ)
  rw [D.restrict_glue_assoc, fromPair_toSpec, ← Category.assoc,
    Scheme.toSpecΓ_naturality]
  simp only [coefficientsOn, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  rfl

end FlagVarieties.Foundations.ProjectiveLine.OpenPairData
