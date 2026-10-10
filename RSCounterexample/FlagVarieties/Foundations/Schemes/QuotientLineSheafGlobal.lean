import RSCounterexample.FlagVarieties.Foundations.Schemes.QuotientSheafProjectiveGluing

/-!
# Global quotient-line morphism: uniqueness, independence, and the base

The gluing construction is characterized by its formula for the original
two quotient sections in every affine local sheaf frame. This gives
independence from arbitrary affine frame covers. A base morphism
`X → Spec A` supplies the coefficient homomorphism and the construction is
proved to lie over that same base morphism.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientPair

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u v

variable {A : Type u} [CommRing A] {X : Scheme.{u}} {N : X.Modules}
  (q : orderedFreeSheaf X ⟶ N) [Epi q]
  (hline : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
    Nonempty (N.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)))
  (φ : A →+* Γ(X, ⊤))

/-- The global quotient-line map agrees with gluing on any affine frame cover. -/
theorem fromQuotientLineSheaf_eq_fromSheafFrames [N.IsQuasicoherent]
    {ι : Type v} {U : ι → X.Opens} (hAffine : ∀ i, IsAffineOpen (U i))
    (frames : ∀ i, N.over (U i) ≅ SheafOfModules.unit (X.ringCatSheaf.over (U i)))
    (hU : IsOpenCover U) :
    fromQuotientLineSheaf q hline φ = fromSheafFrames q hAffine frames φ hU := by
  unfold fromQuotientLineSheaf
  apply fromSheafFrames_cover_independent

/-- The formula in all affine local frames uniquely determines the scheme morphism. -/
theorem fromQuotientLineSheaf_unique (g : X ⟶ ProjectiveLine.scheme A)
    (hg : ∀ (V : X.Opens) (hV : IsAffineOpen V)
      (e : N.over V ≅ SheafOfModules.unit (X.ringCatSheaf.over V)),
      V.ι ≫ g = ProjectiveLine.fromPair (ProjectiveLine.coefficientsOn φ V)
        (framedQuotientCoefficient q V e ⟨0⟩) (framedQuotientCoefficient q V e ⟨1⟩)
        (lineSheaf_frame_coprime q hline V hV e)) :
    g = fromQuotientLineSheaf q hline φ := by
  let D := chooseAffineSheafFrameCover N hline
  apply (X.openCoverOfIsOpenCover D.opens D.isOpenCover).hom_ext
  intro x
  exact (hg (D.opens x) (D.affine x) (D.frame x)).trans
    (fromQuotientLineSheaf_local_formula q hline φ (D.opens x) (D.affine x) (D.frame x)).symm

/-- The coefficients induced by a structural morphism to the affine base. -/
def quotientLineBaseCoefficients (b : X ⟶ Spec (CommRingCat.of A)) :
    A →+* Γ(X, ⊤) :=
  b.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom

/-- The base morphism is recovered from the induced coefficient homomorphism. -/
theorem quotientLineBaseCoefficients_toSpec (b : X ⟶ Spec (CommRingCat.of A)) :
    X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (quotientLineBaseCoefficients b)) = b := by
  change X.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ b.appTop) = b
  rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
    toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

/-- The global quotient-line map relative to a base scheme morphism. -/
def fromQuotientLineSheafOver (b : X ⟶ Spec (CommRingCat.of A)) :
    X ⟶ ProjectiveLine.scheme A :=
  fromQuotientLineSheaf q hline (quotientLineBaseCoefficients b)

@[reassoc] theorem fromQuotientLineSheafOver_toSpec (b : X ⟶ Spec (CommRingCat.of A)) :
    fromQuotientLineSheafOver q hline b ≫ ProjectiveLine.toSpec A = b := by
  rw [fromQuotientLineSheafOver, fromQuotientLineSheaf_toSpec,
    quotientLineBaseCoefficients_toSpec]

/-- Every affine local frame has the ordered quotient-section formula over the given base. -/
@[reassoc] theorem fromQuotientLineSheafOver_local_formula
    (b : X ⟶ Spec (CommRingCat.of A)) (V : X.Opens) (hV : IsAffineOpen V)
    (e : N.over V ≅ SheafOfModules.unit (X.ringCatSheaf.over V)) :
    V.ι ≫ fromQuotientLineSheafOver q hline b =
      ProjectiveLine.fromPair (ProjectiveLine.coefficientsOn (quotientLineBaseCoefficients b) V)
        (framedQuotientCoefficient q V e ⟨0⟩) (framedQuotientCoefficient q V e ⟨1⟩)
        (lineSheaf_frame_coprime q hline V hV e) :=
  fromQuotientLineSheaf_local_formula q hline (quotientLineBaseCoefficients b) V hV e

end FlagVarieties.Foundations.QuotientPair
