import Schubert.FlagVarieties.Foundations.Schemes.SelectedChartOverlapCompatibility

/-! # Naturality and joint applicability of regular chart transitions -/

noncomputable section

namespace FlagVarieties.Foundations.QuotientCharts

universe u

variable (R : Type u) [CommRing R] {n d : ℕ} (a b c : Fin d ↪ Fin n)
  {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- A map out of the determinant localization is the lift of its restriction. -/
theorem awayLiftAlgHom_restriction {P : Type u} [CommRing P] [Algebra R P] (x : P)
    (f : Localization.Away x →ₐ[R] A)
    (h : IsUnit ((f.comp (IsScalarTower.toAlgHom R P (Localization.Away x))) x)) :
    (IsLocalization.Away.liftAlgHom x h : Localization.Away x →ₐ[R] A) = f := by
  apply AlgHom.toRingHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers x)
  apply RingHom.ext
  intro p
  simp

theorem selectedChartTransitionHom_restriction
    (f : Localization.Away (selectedPolynomialBlock R a b).det →ₐ[R] A)
    (h : IsUnit ((f.comp (IsScalarTower.toAlgHom R
      (MvPolynomial (Fin d × Fin (n - d)) R)
      (Localization.Away (selectedPolynomialBlock R a b).det)))
        (selectedPolynomialBlock R a b).det)) :
    selectedChartTransitionHom R a b
      (f.comp (IsScalarTower.toAlgHom R (MvPolynomial (Fin d × Fin (n - d)) R)
        (Localization.Away (selectedPolynomialBlock R a b).det))) h =
      f.comp (matrixOverlapCoordinates R (selectedPolynomialBlock R a b)
        (remainingPolynomialBlock R a b)) := by
  unfold selectedChartTransitionHom
  rw [awayLiftAlgHom_restriction]

/-- Applicability of two charts for the same quotient implies their mutual overlap. -/
theorem selectedChartTransitionHom_joint_unit
    (f : MvPolynomial (Fin d × Fin (n - d)) R →ₐ[R] A)
    (hab : IsUnit (f (selectedPolynomialBlock R a b).det))
    (hac : IsUnit (f (selectedPolynomialBlock R a c).det)) :
    IsUnit (selectedChartTransitionHom R a b f hab (selectedPolynomialBlock R b c).det) := by
  apply (selectedPolynomialBlock_open_iff R b c _ (selectedChartPoint R a f)
    (selectedChartTransitionHom_represents R a b f hab _ (selectedChartPoint_presented R a f))).mpr
  exact (selectedPolynomialBlock_open_iff R a c f _ (selectedChartPoint_presented R a f)).mp hac

/-- Localization lifts commute with arbitrary homomorphisms of base algebras. -/
theorem awayLiftAlgHom_comp {P : Type u} [CommRing P] [Algebra R P] (x : P)
    (f : P →ₐ[R] A) (g : A →ₐ[R] B) (h : IsUnit (f x))
    (hg : IsUnit ((g.comp f) x)) :
    (IsLocalization.Away.liftAlgHom x hg : Localization.Away x →ₐ[R] B) =
      g.comp (IsLocalization.Away.liftAlgHom x h : Localization.Away x →ₐ[R] A) := by
  apply AlgHom.toRingHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers x)
  apply RingHom.ext
  intro p
  simp

theorem selectedChartTransitionHom_comp
    (f : MvPolynomial (Fin d × Fin (n - d)) R →ₐ[R] A) (g : A →ₐ[R] B)
    (h : IsUnit (f (selectedPolynomialBlock R a b).det))
    (hg : IsUnit ((g.comp f) (selectedPolynomialBlock R a b).det)) :
    selectedChartTransitionHom R a b (g.comp f) hg =
      g.comp (selectedChartTransitionHom R a b f h) := by
  unfold selectedChartTransitionHom
  rw [awayLiftAlgHom_comp R _ f g h hg, AlgHom.comp_assoc]

end FlagVarieties.Foundations.QuotientCharts
