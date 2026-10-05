import Schubert.FlagVarieties.Foundations.Schemes.GeneralLinearFlag
import Schubert.FlagVarieties.Foundations.Schemes.GeneralLinearGrassmannianAffine
import Schubert.FlagVarieties.Foundations.Schemes.SelectedFlagAffineRingClassification

/-! Affine test points of the varying general-linear flag product. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B] (n : ℕ)

/-- The `B`-point `(g, P)` of `GLₙ ×_R Flₙ` given by an `R`-algebra map `k : 𝒪(GLₙ) → B` and a flag
`P` of `Bⁿ`. -/
def generalLinearFlagOfAffine
    (k : TauCeti.GeneralLinear.CoordinateRing R n →ₐ[R] B)
    (P : RingFlag B (Fin n → B) n) :
    Spec (CommRingCat.of B) ⟶ generalLinearFlagProduct R n :=
  pullback.lift (generalLinearGroupPoint R B n k)
    (simultaneousFlagRelativeMorphism R P)
    ((generalLinearGroupPoint_toSpec R B n k).trans
      (simultaneousFlagRelativeMorphism_toSpec R P).symm)

@[reassoc] theorem generalLinearFlagOfAffine_group
    (k : TauCeti.GeneralLinear.CoordinateRing R n →ₐ[R] B)
    (P : RingFlag B (Fin n → B) n) :
    generalLinearFlagOfAffine R B n k P ≫ generalLinearFlagGroup R n =
      generalLinearGroupPoint R B n k :=
  pullback.lift_fst _ _ _

@[reassoc] theorem generalLinearFlagOfAffine_point
    (k : TauCeti.GeneralLinear.CoordinateRing R n →ₐ[R] B)
    (P : RingFlag B (Fin n → B) n) :
    generalLinearFlagOfAffine R B n k P ≫ generalLinearFlagPoint R n =
      simultaneousFlagRelativeMorphism R P :=
  pullback.lift_snd _ _ _

@[reassoc] theorem generalLinearFlagOfAffine_coordinate
    (k : TauCeti.GeneralLinear.CoordinateRing R n →ₐ[R] B)
    (P : RingFlag B (Fin n → B) n) :
    generalLinearFlagOfAffine R B n k P ≫ generalLinearFlagCoordinateMap R n =
      Spec.map (CommRingCat.ofHom k.toRingHom) := by
  change (generalLinearFlagOfAffine R B n k P ≫ generalLinearFlagGroup R n) ≫
    (TauCeti.GeneralLinear.groupSchemeSpecIso R n).hom = _
  rw [generalLinearFlagOfAffine_group]
  unfold generalLinearGroupPoint
  simp

/-- At the point `(g, P)`, the pullback of the universal step-`j` quotient along the projection to
`Flₙ` is its pullback along the classifying morphism of `P`. -/
def generalLinearFlagAffineTargetIso
    (k : TauCeti.GeneralLinear.CoordinateRing R n →ₐ[R] B)
    (P : RingFlag B (Fin n → B) n) (j : Fin (n+1)) :
    (Scheme.Modules.pullback (generalLinearFlagOfAffine R B n k P)).obj
      ((Scheme.Modules.pullback (generalLinearFlagPoint R n)).obj
        (selectedFlagUniversalTarget R n j)) ≅
      (Scheme.Modules.pullback (simultaneousFlagRelativeMorphism R P)).obj
        (selectedFlagUniversalTarget R n j) :=
  (Scheme.Modules.pullbackComp (generalLinearFlagOfAffine R B n k P)
    (generalLinearFlagPoint R n)).app (selectedFlagUniversalTarget R n j) ≪≫
    (Scheme.Modules.pullbackCongr
      (generalLinearFlagOfAffine_point R B n k P)).app
        (selectedFlagUniversalTarget R n j)

@[reassoc] theorem generalLinearFlagAffineTargetIso_source
    (k : TauCeti.GeneralLinear.CoordinateRing R n →ₐ[R] B)
    (P : RingFlag B (Fin n → B) n) (j : Fin (n+1)) :
    coordinatePullbackQuotient (generalLinearFlagOfAffine R B n k P)
      (coordinatePullbackQuotient (generalLinearFlagPoint R n)
        (selectedFlagUniversalQuotient R n j)) ≫
      (generalLinearFlagAffineTargetIso R B n k P j).hom =
    coordinatePullbackQuotient (simultaneousFlagRelativeMorphism R P)
      (selectedFlagUniversalQuotient R n j) := by
  unfold generalLinearFlagAffineTargetIso
  simp only [Iso.trans_hom, Iso.app_hom]
  rw [← Category.assoc, coordinatePullbackQuotient_comp_hom]
  rw [coordinatePullbackQuotient_congr]

@[reassoc] theorem generalLinearFlagAffineQuotient_source
    (k : TauCeti.GeneralLinear.CoordinateRing R n →ₐ[R] B)
    (P : RingFlag B (Fin n → B) n) (j : Fin (n+1)) :
    coordinatePullbackQuotient (generalLinearFlagOfAffine R B n k P)
        ((generalLinearFlagFamily R n).quotient j) ≫
      (generalLinearFlagAffineTargetIso R B n k P j).hom =
    (constantMatrixSpecIso (CommRingCat.of B)
      (generalLinearMatrixAt R B n k)
      (generalLinearMatrixAt_isUnit R B n k)).inv ≫
      coordinatePullbackQuotient (simultaneousFlagRelativeMorphism R P)
        (selectedFlagUniversalQuotient R n j) := by
  change coordinatePullbackQuotient (generalLinearFlagOfAffine R B n k P)
      ((constantMatrixSheafIso (TauCeti.GeneralLinear.CoordinateRing R n)
        (generalLinearFlagCoordinateMap R n)
        (TauCeti.GeneralLinear.localizedGenericMatrix R n)
        (generalLinearGrassmannianMatrix_isUnit R n)).inv ≫
        coordinatePullbackQuotient (generalLinearFlagPoint R n)
          (selectedFlagUniversalQuotient R n j)) ≫ _ = _
  rw [coordinatePullbackQuotient_constantMatrix_inv]
  rw [Category.assoc, generalLinearFlagAffineTargetIso_source]
  rw [generalLinearFlagOfAffine_coordinate]
  rw [generalLinearMatrixIso_at]

end FlagVarieties.Foundations.QuotientCharts
