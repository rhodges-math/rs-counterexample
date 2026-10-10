import RSCounterexample.FlagVarieties.Foundations.Schemes.GeneralLinearGrassmannian
import RSCounterexample.FlagVarieties.Foundations.Schemes.ConstantMatrixSheafAffine

/-! Affine test points of the varying general-linear product. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B] (n d : ℕ)

/-- The invertible matrix of the `B`-point of `GLₙ` given by an `R`-algebra map `k : 𝒪(GLₙ) → B`. -/
def generalLinearMatrixAt
    (k : TauCeti.GeneralLinear.CoordinateRing R n →ₐ[R] B) :
    Matrix (Fin n) (Fin n) B :=
  (TauCeti.GeneralLinear.localizedGenericMatrix R n).map k.toRingHom

theorem generalLinearMatrixAt_isUnit
    (k : TauCeti.GeneralLinear.CoordinateRing R n →ₐ[R] B) :
    IsUnit (generalLinearMatrixAt R B n k) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  change IsUnit (((TauCeti.GeneralLinear.localizedGenericMatrix R n).map k).det)
  rw [← AlgHom.mapMatrix_apply, ← AlgHom.map_det]
  exact (TauCeti.GeneralLinear.isUnit_det_localizedGenericMatrix R n).map k

theorem generalLinearMatrixIso_at
    (k : TauCeti.GeneralLinear.CoordinateRing R n →ₐ[R] B) :
    constantMatrixSheafIso (TauCeti.GeneralLinear.CoordinateRing R n)
      (Spec.map (CommRingCat.ofHom k.toRingHom))
      (TauCeti.GeneralLinear.localizedGenericMatrix R n)
      (generalLinearGrassmannianMatrix_isUnit R n) =
    constantMatrixSpecIso (CommRingCat.of B) (generalLinearMatrixAt R B n k)
      (generalLinearMatrixAt_isUnit R B n k) := by
  letI : Algebra (TauCeti.GeneralLinear.CoordinateRing R n) B := k.toAlgebra
  have hk : algebraMap (TauCeti.GeneralLinear.CoordinateRing R n) B = k.toRingHom := rfl
  apply Iso.ext
  simpa only [hk, generalLinearMatrixAt] using
    (constantMatrixSheafIso_specMap_hom
      (TauCeti.GeneralLinear.CoordinateRing R n)
      (TauCeti.GeneralLinear.localizedGenericMatrix R n)
      (generalLinearGrassmannianMatrix_isUnit R n) B)

/-- The `B`-point of `GLₙ` given by an `R`-algebra map `k : 𝒪(GLₙ) → B`. -/
def generalLinearGroupPoint
    (k : TauCeti.GeneralLinear.CoordinateRing R n →ₐ[R] B) :
    Spec (CommRingCat.of B) ⟶ (TauCeti.GeneralLinear.groupScheme R n).X.left :=
  Spec.map (CommRingCat.ofHom k.toRingHom) ≫
    (TauCeti.GeneralLinear.groupSchemeSpecIso R n).inv

@[reassoc] theorem generalLinearGroupPoint_toSpec
    (k : TauCeti.GeneralLinear.CoordinateRing R n →ₐ[R] B) :
    generalLinearGroupPoint R B n k ≫
        (TauCeti.GeneralLinear.groupScheme R n).X.hom =
      Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
  unfold generalLinearGroupPoint
  rw [TauCeti.GeneralLinear.groupScheme_X_hom]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact k.commutes r

/-- The `B`-point `(g, P)` of `GLₙ ×_R Gr` given by an `R`-algebra map `k : 𝒪(GLₙ) → B` and a point
`P` of the Grassmannian of `Bⁿ`. -/
def generalLinearGrassmannianOfAffine
    (k : TauCeti.GeneralLinear.CoordinateRing R n →ₐ[R] B)
    (P : Module.Grassmannian B (Fin n → B) d) :
    Spec (CommRingCat.of B) ⟶ generalLinearGrassmannianProduct R n d :=
  pullback.lift (generalLinearGroupPoint R B n k)
    (selectedQuotientMorphism R P)
    ((generalLinearGroupPoint_toSpec R B n k).trans
      (selectedQuotientMorphism_toSpec (R := R) (P := P)).symm)

@[reassoc] theorem generalLinearGrassmannianOfAffine_group
    (k : TauCeti.GeneralLinear.CoordinateRing R n →ₐ[R] B)
    (P : Module.Grassmannian B (Fin n → B) d) :
    generalLinearGrassmannianOfAffine R B n d k P ≫
      generalLinearGrassmannianGroup R n d = generalLinearGroupPoint R B n k :=
  pullback.lift_fst _ _ _

@[reassoc] theorem generalLinearGrassmannianOfAffine_point
    (k : TauCeti.GeneralLinear.CoordinateRing R n →ₐ[R] B)
    (P : Module.Grassmannian B (Fin n → B) d) :
    generalLinearGrassmannianOfAffine R B n d k P ≫
      generalLinearGrassmannianPoint R n d = selectedQuotientMorphism R P :=
  pullback.lift_snd _ _ _

@[reassoc] theorem generalLinearGrassmannianOfAffine_coordinate
    (k : TauCeti.GeneralLinear.CoordinateRing R n →ₐ[R] B)
    (P : Module.Grassmannian B (Fin n → B) d) :
    generalLinearGrassmannianOfAffine R B n d k P ≫
      generalLinearGrassmannianCoordinateMap R n d =
        Spec.map (CommRingCat.ofHom k.toRingHom) := by
  change (generalLinearGrassmannianOfAffine R B n d k P ≫
    generalLinearGrassmannianGroup R n d) ≫
      (TauCeti.GeneralLinear.groupSchemeSpecIso R n).hom = _
  rw [generalLinearGrassmannianOfAffine_group]
  unfold generalLinearGroupPoint
  simp

/-- Compare the doubly pulled universal target with the original affine
coordinate quotient, through the product projection and composition. -/
def generalLinearGrassmannianAffineTargetIso
    (k : TauCeti.GeneralLinear.CoordinateRing R n →ₐ[R] B)
    (P : Module.Grassmannian B (Fin n → B) d) :
    (Scheme.Modules.pullback (generalLinearGrassmannianOfAffine R B n d k P)).obj
      ((Scheme.Modules.pullback (generalLinearGrassmannianPoint R n d)).obj
        (selectedUniversalQuotientSheaf R n d)) ≅
      coordinateQuotientSheaf (CommRingCat.of B) P :=
  (Scheme.Modules.pullbackComp (generalLinearGrassmannianOfAffine R B n d k P)
    (generalLinearGrassmannianPoint R n d)).app
      (selectedUniversalQuotientSheaf R n d) ≪≫
    (Scheme.Modules.pullbackCongr
      (generalLinearGrassmannianOfAffine_point R B n d k P)).app
        (selectedUniversalQuotientSheaf R n d) ≪≫
      selectedUniversalAffineQuotientIso R B P

@[reassoc] theorem generalLinearGrassmannianAffineTargetIso_source
    (k : TauCeti.GeneralLinear.CoordinateRing R n →ₐ[R] B)
    (P : Module.Grassmannian B (Fin n → B) d) :
    coordinatePullbackQuotient (generalLinearGrassmannianOfAffine R B n d k P)
      (coordinatePullbackQuotient (generalLinearGrassmannianPoint R n d)
        (selectedUniversalQuotient R n d)) ≫
        (generalLinearGrassmannianAffineTargetIso R B n d k P).hom =
      coordinateQuotientSheafMap (CommRingCat.of B) P := by
  unfold generalLinearGrassmannianAffineTargetIso
  simp only [Iso.trans_hom, Iso.app_hom]
  rw [← Category.assoc, coordinatePullbackQuotient_comp_hom]
  rw [← Category.assoc, coordinatePullbackQuotient_congr]
  exact selectedUniversalAffineQuotientIso_source R B P

/-- The varying matrix acts on the original affine quotient source after
the canonical target comparison. -/
@[reassoc] theorem generalLinearGrassmannianAffineQuotient_source
    (k : TauCeti.GeneralLinear.CoordinateRing R n →ₐ[R] B)
    (P : Module.Grassmannian B (Fin n → B) d) :
    coordinatePullbackQuotient (generalLinearGrassmannianOfAffine R B n d k P)
        (generalLinearGrassmannianQuotient R n d) ≫
      (generalLinearGrassmannianAffineTargetIso R B n d k P).hom =
    (constantMatrixSpecIso (CommRingCat.of B)
      (generalLinearMatrixAt R B n k)
      (generalLinearMatrixAt_isUnit R B n k)).inv ≫
      coordinateQuotientSheafMap (CommRingCat.of B) P := by
  unfold generalLinearGrassmannianQuotient
  rw [coordinatePullbackQuotient_constantMatrix_inv]
  rw [Category.assoc, generalLinearGrassmannianAffineTargetIso_source]
  rw [generalLinearGrassmannianOfAffine_coordinate]
  change (constantMatrixSheafIso (TauCeti.GeneralLinear.CoordinateRing R n)
    (Spec.map (CommRingCat.ofHom k.toRingHom))
    (TauCeti.GeneralLinear.localizedGenericMatrix R n)
    (generalLinearGrassmannianMatrix_isUnit R n)).inv ≫
      coordinateQuotientSheafMap (CommRingCat.of B) P = _
  rw [generalLinearMatrixIso_at]

end FlagVarieties.Foundations.QuotientCharts
