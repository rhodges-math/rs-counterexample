import RSCounterexample.FlagVarieties.Foundations.Schemes.SelectedTripleOverlapCoordinates
import RSCounterexample.FlagVarieties.Foundations.Schemes.SelectedChartOverlapDiagonal
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Scheme maps on triple chart intersections

The source is the categorical fiber product of the two determinant opens.
Its affine tensor-product presentation carries the proved regular map
into the second/third overlap. Both chart-comparison squares commute as
scheme morphisms, not merely on field-valued points.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace FlagVarieties.Foundations.QuotientCharts

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

variable (R : Type u) [CommRing R]

/-- A commuting algebra square gives a commuting square of affine schemes. -/
theorem spec_map_algHom_square
    {P S T A : Type u} [CommRing P] [CommRing S] [CommRing T] [CommRing A]
    [Algebra R P] [Algebra R S] [Algebra R T] [Algebra R A]
    (f : P →ₐ[R] S) (g : S →ₐ[R] A) (f' : P →ₐ[R] T) (g' : T →ₐ[R] A)
    (h : g.comp f = g'.comp f') :
    Spec.map (CommRingCat.ofHom g.toRingHom) ≫ Spec.map (CommRingCat.ofHom f.toRingHom) =
      Spec.map (CommRingCat.ofHom g'.toRingHom) ≫ Spec.map (CommRingCat.ofHom f'.toRingHom) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun q : P →ₐ[R] A => Spec.map (CommRingCat.ofHom q.toRingHom)) h

variable {n d : ℕ} (a b c : Fin d ↪ Fin n)

/-- The triple intersection, formed over its first affine chart. -/
abbrev selectedTripleOverlap : Scheme.{u} :=
  pullback (selectedChartOverlapInclusion R a b) (selectedChartOverlapInclusion R a c)

/-- Its canonical affine tensor-product presentation. -/
def selectedTripleOverlapSpecIso : selectedTripleOverlap R a b c ≅
    Spec (CommRingCat.of (selectedTripleOverlapRing R a b c)) :=
  pullbackSpecIso (MvPolynomial (Fin d × Fin (n - d)) R)
    (Localization.Away (selectedPolynomialBlock R a b).det)
    (Localization.Away (selectedPolynomialBlock R a c).det)

@[reassoc (attr := simp)] theorem selectedTripleOverlapSpecIso_inv_fst :
    (selectedTripleOverlapSpecIso R a b c).inv ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (selectedTripleOverlapLeft R a b c).toRingHom) :=
  pullbackSpecIso_inv_fst _ _ _

@[reassoc (attr := simp)] theorem selectedTripleOverlapSpecIso_inv_snd :
    (selectedTripleOverlapSpecIso R a b c).inv ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (selectedTripleOverlapRight R a b c).toRingHom) :=
  pullbackSpecIso_inv_snd _ _ _

/-- The scheme map into the overlap of the second and third charts. -/
def selectedTripleOverlapToSecondThird : selectedTripleOverlap R a b c ⟶
    Spec (CommRingCat.of (Localization.Away (selectedPolynomialBlock R b c).det)) :=
  (selectedTripleOverlapSpecIso R a b c).hom ≫
    Spec.map (CommRingCat.ofHom (selectedTripleOverlapLift R a b c).toRingHom)

/-- The new overlap point has the expected second-chart coordinates. -/
@[reassoc] theorem selectedTripleOverlapToSecondThird_first :
    selectedTripleOverlapToSecondThird R a b c ≫ selectedChartOverlapInclusion R b c =
      pullback.fst _ _ ≫ selectedChartOverlapMap R a b := by
  have hs : Spec.map (CommRingCat.ofHom (selectedTripleOverlapLift R a b c).toRingHom) ≫
      selectedChartOverlapInclusion R b c =
      Spec.map (CommRingCat.ofHom (selectedTripleOverlapLeft R a b c).toRingHom) ≫
        selectedChartOverlapMap R a b := by
    apply spec_map_algHom_square R
      (IsScalarTower.toAlgHom R (MvPolynomial (Fin d × Fin (n - d)) R)
        (Localization.Away (selectedPolynomialBlock R b c).det))
      (selectedTripleOverlapLift R a b c)
      (matrixOverlapCoordinates R (selectedPolynomialBlock R a b) (remainingPolynomialBlock R a b))
      (selectedTripleOverlapLeft R a b c)
    apply AlgHom.ext
    intro p
    exact (selectedTripleOverlapLift_algebraMap R a b c p).trans
      (DFunLike.congr_fun (selectedTripleOverlapSecond_eq R a b c) p)
  rw [selectedTripleOverlapToSecondThird, Category.assoc, hs, ← Category.assoc]
  exact congrArg (fun f => f ≫ selectedChartOverlapMap R a b)
    (pullbackSpecIso_hom_fst (MvPolynomial (Fin d × Fin (n - d)) R)
      (Localization.Away (selectedPolynomialBlock R a b).det)
      (Localization.Away (selectedPolynomialBlock R a c).det))

/-- The two regular paths to the third chart agree on the fiber product. -/
@[reassoc] theorem selectedTripleOverlapToSecondThird_third :
    selectedTripleOverlapToSecondThird R a b c ≫ selectedChartOverlapMap R b c =
      pullback.snd _ _ ≫ selectedChartOverlapMap R a c := by
  have hs : Spec.map (CommRingCat.ofHom (selectedTripleOverlapLift R a b c).toRingHom) ≫
      selectedChartOverlapMap R b c =
      Spec.map (CommRingCat.ofHom (selectedTripleOverlapRight R a b c).toRingHom) ≫
        selectedChartOverlapMap R a c := by
    exact spec_map_algHom_square R
      (matrixOverlapCoordinates R (selectedPolynomialBlock R b c) (remainingPolynomialBlock R b c))
      (selectedTripleOverlapLift R a b c)
      (matrixOverlapCoordinates R (selectedPolynomialBlock R a c) (remainingPolynomialBlock R a c))
      (selectedTripleOverlapRight R a b c)
      (selectedTripleOverlapLift_coordinates R a b c)
  rw [selectedTripleOverlapToSecondThird, Category.assoc, hs, ← Category.assoc]
  exact congrArg (fun f => f ≫ selectedChartOverlapMap R a c)
    (pullbackSpecIso_hom_snd (MvPolynomial (Fin d × Fin (n - d)) R)
      (Localization.Away (selectedPolynomialBlock R a b).det)
      (Localization.Away (selectedPolynomialBlock R a c).det))

end FlagVarieties.Foundations.QuotientCharts
