import RSCounterexample.FlagVarieties.Foundations.Schemes.AffineQuotientSheafPresentation
import RSCounterexample.FlagVarieties.Foundations.Schemes.AffineQuotientCompatibility

/-!
# Affine quotient morphisms on sheaf-trivializing charts

An isomorphism of the quotient sheaf with the structure sheaf
induces a frame of its affine sections. Finite projectivity and stalk
rank one are consequences, and supply the existing Proj constructor.
This is the local step on a sheaf-trivializing affine chart; it does not
assert global triviality of a line bundle or choose a frame cover.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientPair

open AlgebraicGeometry CategoryTheory TensorProduct

universe u

variable {R : CommRingCat.{u}} {L : (Spec R).Modules}

/-- A sheaf trivialization induces a frame of its affine section module. -/
def sheafGlobalFrame (e : L ≅ SheafOfModules.unit (Spec R).ringCatSheaf) :
    sheafGlobalModule L ≃ₗ[R] R :=
  (moduleSpecΓFunctor.mapIso (e ≪≫ tildeSelf.symm)).toLinearEquiv ≪≫ₗ
    (tilde.isoTop (ModuleCat.of R R)).toLinearEquiv.symm

theorem sheafGlobal_finite_of_frame (e : L ≅ SheafOfModules.unit (Spec R).ringCatSheaf) :
    Module.Finite R (sheafGlobalModule L) :=
  Module.Finite.equiv (sheafGlobalFrame e).symm

theorem sheafGlobal_projective_of_frame (e : L ≅ SheafOfModules.unit (Spec R).ringCatSheaf) :
    Module.Projective R (sheafGlobalModule L) :=
  Module.Projective.of_equiv (sheafGlobalFrame e).symm

theorem sheafGlobal_rank_one_of_frame
    (e : L ≅ SheafOfModules.unit (Spec R).ringCatSheaf) (p : PrimeSpectrum R) :
    Module.rankAtStalk (sheafGlobalModule L) p = 1 := by
  let : Nontrivial R := p.nontrivial
  rw [Module.rankAtStalk_eq_of_equiv (sheafGlobalFrame e), Module.rankAtStalk_self]
  rfl

variable {X : Scheme.{u}} (f : Spec R ⟶ X) [IsOpenImmersion f] {N : X.Modules}

/-- On a sheaf-trivializing affine chart, the quotient gives a Proj morphism. -/
def fromAffineQuotientSheafFrame [N.IsQuasicoherent]
    (e : N.restrict f ≅ SheafOfModules.unit (Spec R).ringCatSheaf)
    (q : orderedFreeSheaf X ⟶ N) [Epi q] : Spec R ⟶ ProjectiveLine.scheme R := by
  let := sheafGlobal_finite_of_frame e
  let := sheafGlobal_projective_of_frame e
  exact fromFiniteProjectivePair (sheafGlobalModule (N.restrict f))
    (sheafGlobal_rank_one_of_frame e) (affineQuotientSectionPair f q)
    (affineQuotientSectionPair_surjective f q)

theorem fromAffineQuotientSheafFrame_toSpec [N.IsQuasicoherent]
    (e : N.restrict f ≅ SheafOfModules.unit (Spec R).ringCatSheaf)
    (q : orderedFreeSheaf X ⟶ N) [Epi q] :
    fromAffineQuotientSheafFrame f e q ≫ ProjectiveLine.toSpec R = 𝟙 (Spec R) := by
  let := sheafGlobal_finite_of_frame e
  let := sheafGlobal_projective_of_frame e
  unfold fromAffineQuotientSheafFrame
  apply fromFiniteProjectivePair_toSpec

/-- The resulting scheme morphism is independent of the chosen sheaf trivialization. -/
theorem fromAffineQuotientSheafFrame_independent [N.IsQuasicoherent]
    (e e' : N.restrict f ≅ SheafOfModules.unit (Spec R).ringCatSheaf)
    (q : orderedFreeSheaf X ⟶ N) [Epi q] :
    fromAffineQuotientSheafFrame f e q = fromAffineQuotientSheafFrame f e' q := by
  rfl

end FlagVarieties.Foundations.QuotientPair
