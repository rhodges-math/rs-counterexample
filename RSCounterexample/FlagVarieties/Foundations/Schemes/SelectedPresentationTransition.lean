import RSCounterexample.FlagVarieties.Foundations.Schemes.SelectedPresentationMap

/-!
# Target transitions for selected quotient presentations

Equality of the quotient points produces a unique identification
of their free targets. It preserves every vector of the original source;
the inverse and triple-overlap laws follow from this property.
-/

noncomputable section

namespace FlagVarieties.Foundations.QuotientCharts

universe u

variable (R : Type u) [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
  {n d : ℕ} (a b c : Fin d ↪ Fin n)
  (f g h : MvPolynomial (Fin d × Fin (n - d)) R →ₐ[R] A)

/-- The target change attached to two presentations of one quotient. -/
def selectedPresentationTransition (he : selectedChartPoint R a f = selectedChartPoint R b g) :
    (Fin d → A) ≃ₗ[A] (Fin d → A) :=
  quotientPresentationEquiv (selectedPresentationMap R a f) (selectedPresentationMap R b g)
    (selectedPresentationMap_surjective R a f) (selectedPresentationMap_surjective R b g)
    (by rw [selectedPresentationMap_ker, selectedPresentationMap_ker, he])

/-- This transition retains each original ambient quotient vector. -/
@[simp] theorem selectedPresentationTransition_apply
    (he : selectedChartPoint R a f = selectedChartPoint R b g) (v : Fin n → A) :
    selectedPresentationTransition R a b f g he (selectedPresentationMap R a f v) =
      selectedPresentationMap R b g v :=
  quotientPresentationEquiv_apply _ _ _ _ _ v

theorem selectedPresentationTransition_comp
    (he : selectedChartPoint R a f = selectedChartPoint R b g) :
    (selectedPresentationTransition R a b f g he).toLinearMap.comp
        (selectedPresentationMap R a f) = selectedPresentationMap R b g :=
  quotientPresentationEquiv_comp _ _ _ _ _

/-- The unchanged selected-coordinate section computes the full transition. -/
theorem selectedPresentationTransition_eq_comp
    (he : selectedChartPoint R a f = selectedChartPoint R b g) :
    (selectedPresentationTransition R a b f g he).toLinearMap =
      (selectedPresentationMap R b g).comp (coordinateInclusion a) := by
  apply LinearMap.ext
  intro v
  have hs := LinearMap.congr_fun (selectedPresentationMap_section R a f) v
  calc
    selectedPresentationTransition R a b f g he v =
        selectedPresentationTransition R a b f g he
          (selectedPresentationMap R a f (coordinateInclusion a v)) := congrArg _ hs.symm
    _ = selectedPresentationMap R b g (coordinateInclusion a v) :=
      selectedPresentationTransition_apply R a b f g he _

theorem selectedPresentationTransition_unique
    (he : selectedChartPoint R a f = selectedChartPoint R b g)
    (t : (Fin d → A) →ₗ[A] (Fin d → A))
    (ht : t.comp (selectedPresentationMap R a f) = selectedPresentationMap R b g) :
    (selectedPresentationTransition R a b f g he).toLinearMap = t :=
  quotientPresentationEquiv_unique _ _ _ _ _ t ht

@[simp] theorem selectedPresentationTransition_refl :
    selectedPresentationTransition R a a f f rfl = LinearEquiv.refl A (Fin d → A) :=
  quotientPresentationEquiv_refl _ _

theorem selectedPresentationTransition_symm
    (he : selectedChartPoint R a f = selectedChartPoint R b g) :
    (selectedPresentationTransition R a b f g he).symm =
      selectedPresentationTransition R b a g f he.symm :=
  quotientPresentationEquiv_symm _ _ _ _ _

theorem selectedPresentationTransition_trans
    (he : selectedChartPoint R a f = selectedChartPoint R b g)
    (he' : selectedChartPoint R b g = selectedChartPoint R c h) :
    (selectedPresentationTransition R a b f g he).trans
        (selectedPresentationTransition R b c g h he') =
      selectedPresentationTransition R a c f h (he.trans he') :=
  quotientPresentationEquiv_trans _ _ _ _ _ _ _ _

/-- The regular determinant-open transition has exactly the same quotient point. -/
theorem selectedChartPoint_transition
    (hab : IsUnit (f (selectedPolynomialBlock R a b).det)) :
    selectedChartPoint R a f =
      selectedChartPoint R b (selectedChartTransitionHom R a b f hab) := by
  apply (grassmannianTransportEquiv (selectedCoordinateEquiv (R := A) b)).injective
  exact (selectedChartTransitionHom_represents R a b f hab _
    (selectedChartPoint_presented R a f)).symm.trans
      (selectedChartPoint_presented R b _)

/-- The overlap carries a canonical invertible change of free quotient target. -/
def selectedRegularPresentationTransition
    (hab : IsUnit (f (selectedPolynomialBlock R a b).det)) :
    (Fin d → A) ≃ₗ[A] (Fin d → A) :=
  selectedPresentationTransition R a b f (selectedChartTransitionHom R a b f hab)
    (selectedChartPoint_transition R a b f hab)

@[simp] theorem selectedRegularPresentationTransition_apply
    (hab : IsUnit (f (selectedPolynomialBlock R a b).det)) (v : Fin n → A) :
    selectedRegularPresentationTransition R a b f hab (selectedPresentationMap R a f v) =
      selectedPresentationMap R b (selectedChartTransitionHom R a b f hab) v :=
  selectedPresentationTransition_apply R a b f _ _ v

end FlagVarieties.Foundations.QuotientCharts
