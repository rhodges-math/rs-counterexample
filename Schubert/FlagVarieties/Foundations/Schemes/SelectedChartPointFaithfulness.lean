import Schubert.FlagVarieties.Foundations.Schemes.SelectedChartPointMaps

/-!+# The glued charts identify exactly the same presented quotients

The converse to presentation independence uses the categorical
intersection of two charts. Equality of scheme maps supplies a map into the
determinant localization; fullness of `Spec` recovers its ring map. Thus no
additional quotient identifications arise from gluing.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientCharts

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

theorem spec_preimage_comp_eq
    {P S A : Type u} [CommRing P] [CommRing S] [CommRing A]
    (q : P →+* S) (f : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of S))
    (r : P →+* A)
    (h : f ≫ Spec.map (CommRingCat.ofHom q) = Spec.map (CommRingCat.ofHom r)) :
    (Spec.preimage f).hom.comp q = r := by
  have hs : Spec.map (CommRingCat.ofHom q ≫ Spec.preimage f) =
      Spec.map (CommRingCat.ofHom r) := by
    rw [Spec.map_comp, Spec.map_preimage]
    exact h
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective hs)

variable (R : Type u) [CommRing R] {n d : ℕ} (a b : Fin d ↪ Fin n)

/-- The specified determinant overlap is the categorical chart intersection. -/
theorem selectedChartScheme_overlap_lift {X : Scheme.{u}}
    (f g : X ⟶ Spec (CommRingCat.of (MvPolynomial (Fin d × Fin (n - d)) R)))
    (h : f ≫ selectedChartSchemeChart R n d a =
      g ≫ selectedChartSchemeChart R n d b) :
    ∃ l : X ⟶ Spec (CommRingCat.of (Localization.Away (selectedPolynomialBlock R a b).det)),
      l ≫ selectedChartOverlapInclusion R a b = f ∧
      l ≫ selectedChartOverlapMap R a b = g := by
  let D := selectedChartGlueData R n d
  let s : PullbackCone (D.ι (ULift.up a)) (D.ι (ULift.up b)) := PullbackCone.mk f g h
  let H := D.vPullbackConeIsLimit (ULift.up a) (ULift.up b)
  refine ⟨H.lift s, H.fac s WalkingCospan.left, ?_⟩
  have hs := H.fac s WalkingCospan.right
  change H.lift s ≫ ((selectedChartOverlapIso R a b).hom ≫
    selectedChartOverlapInclusion R b a) = g at hs
  rw [selectedChartOverlapIso_hom_inclusion] at hs
  exact hs

variable {A : Type u} [CommRing A] [Algebra R A]

/-- Equal affine maps into the glued scheme have exactly equal quotients. -/
theorem selectedChartPoint_quotient_eq_of_map_eq
    (f g : MvPolynomial (Fin d × Fin (n - d)) R →ₐ[R] A)
    (h : selectedChartPointMap R a f = selectedChartPointMap R b g) :
    selectedChartPoint R a f = selectedChartPoint R b g := by
  obtain ⟨l, hl, hr⟩ := selectedChartScheme_overlap_lift R a b
    (Spec.map (CommRingCat.ofHom f.toRingHom))
    (Spec.map (CommRingCat.ofHom g.toRingHom)) h
  have hleft := spec_preimage_comp_eq
    (algebraMap (MvPolynomial (Fin d × Fin (n - d)) R)
      (Localization.Away (selectedPolynomialBlock R a b).det)) l f.toRingHom hl
  have hright := spec_preimage_comp_eq
    (matrixOverlapCoordinates R (selectedPolynomialBlock R a b)
      (remainingPolynomialBlock R a b)).toRingHom l g.toRingHom hr
  let q : Localization.Away (selectedPolynomialBlock R a b).det →ₐ[R] A :=
    { (Spec.preimage l).hom with
      commutes' := fun r => by
        rw [IsScalarTower.algebraMap_apply R (MvPolynomial (Fin d × Fin (n - d)) R)
          (Localization.Away (selectedPolynomialBlock R a b).det)]
        exact (RingHom.congr_fun hleft (algebraMap R _ r)).trans (f.commutes r) }
  have hq : q.comp (IsScalarTower.toAlgHom R (MvPolynomial (Fin d × Fin (n - d)) R)
      (Localization.Away (selectedPolynomialBlock R a b).det)) = f := by
    apply AlgHom.toRingHom_injective
    exact hleft
  have hu : IsUnit (f (selectedPolynomialBlock R a b).det) := by
    have hh := (IsLocalization.Away.algebraMap_isUnit (selectedPolynomialBlock R a b).det).map q
    exact (DFunLike.congr_fun hq (selectedPolynomialBlock R a b).det) ▸ hh
  have ht : selectedChartTransitionHom R a b f hu = g := by
    have ht' := selectedChartTransitionHom_restriction R a b q
      (show IsUnit ((q.comp (IsScalarTower.toAlgHom R
        (MvPolynomial (Fin d × Fin (n - d)) R)
        (Localization.Away (selectedPolynomialBlock R a b).det)))
          (selectedPolynomialBlock R a b).det) from by rw [hq]; exact hu)
    have ht'' : selectedChartTransitionHom R a b f hu =
        q.comp (matrixOverlapCoordinates R (selectedPolynomialBlock R a b)
          (remainingPolynomialBlock R a b)) := by
      simpa only [hq] using ht'
    exact ht''.trans (AlgHom.toRingHom_injective hright)
  have hp := selectedChartTransitionHom_represents R a b f hu _
    (selectedChartPoint_presented R a f)
  rw [ht] at hp
  apply (grassmannianTransportEquiv (selectedCoordinateEquiv (R := A) b)).injective
  exact hp.symm.trans (selectedChartPoint_presented R b g)

/-- The gluing relation on normalized affine presentations is precisely quotient equality. -/
theorem selectedChartPointMap_eq_iff_quotient_eq
    (f g : MvPolynomial (Fin d × Fin (n - d)) R →ₐ[R] A) :
    selectedChartPointMap R a f = selectedChartPointMap R b g ↔
      selectedChartPoint R a f = selectedChartPoint R b g :=
  ⟨selectedChartPoint_quotient_eq_of_map_eq R a b f g,
    selectedChartPointMap_eq_of_quotient_eq R a b f g⟩

end FlagVarieties.Foundations.QuotientCharts
