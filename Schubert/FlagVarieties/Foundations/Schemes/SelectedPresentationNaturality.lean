import Schubert.FlagVarieties.Foundations.Schemes.SelectedPresentationTransition
import Schubert.FlagVarieties.Foundations.Flags.CoordinateSelectedPointNaturality

/-!
# Arbitrary scalar changes of the quotient maps

The maps and their target transitions retain the original ambient and
selected coordinates under every algebra homomorphism. No injectivity,
flatness or reducedness assumption is imposed on the scalar change.
-/

noncomputable section

namespace FlagVarieties.Foundations.QuotientCharts

universe u

variable (R : Type u) [CommRing R] {A B : Type u} [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] {n d : ℕ} (a b : Fin d ↪ Fin n)
  (f g : MvPolynomial (Fin d × Fin (n - d)) R →ₐ[R] A)

/-- Explicit evaluation in the original, unrelabelled ambient coordinates. -/
theorem selectedPresentationMap_apply (v : Fin n → A) (i : Fin d) :
    selectedPresentationMap R a f v i = v (a i) +
      ∑ j : Fin (n - d), f (MvPolynomial.X (i, j)) *
        v (coordinateCompletion a (Sum.inr j)) := by
  simp [selectedPresentationMap, normalizedMap_apply, Matrix.toLin'_apply,
    Matrix.mulVec, dotProduct]

/-- Entrywise scalar change commutes with the entire quotient map. -/
theorem selectedPresentationMap_map (k : A →ₐ[R] B) (v : Fin n → A) :
    (fun i => k (selectedPresentationMap R a f v i)) =
      selectedPresentationMap R a (k.comp f) (fun i => k (v i)) := by
  ext i
  simp [selectedPresentationMap_apply, map_sum]

/-- Equality of presented quotient points persists under any scalar change. -/
theorem selectedPresentation_point_map (k : A →ₐ[R] B)
    (he : selectedChartPoint R a f = selectedChartPoint R b g) :
    selectedChartPoint R a (k.comp f) = selectedChartPoint R b (k.comp g) := by
  let : Algebra A B := k.toAlgebra
  rw [← selectedChartPoint_baseChange R k a f, ← selectedChartPoint_baseChange R k b g, he]

/-- Canonical changes of target commute with arbitrary scalar changes. -/
theorem selectedPresentationTransition_map (k : A →ₐ[R] B)
    (he : selectedChartPoint R a f = selectedChartPoint R b g) (v : Fin d → A) :
    (fun i => k (selectedPresentationTransition R a b f g he v i)) =
      selectedPresentationTransition R a b (k.comp f) (k.comp g)
        (selectedPresentation_point_map R a b f g k he) (fun i => k (v i)) := by
  obtain ⟨w, rfl⟩ := selectedPresentationMap_surjective R a f v
  rw [selectedPresentationTransition_apply,
    selectedPresentationMap_map R a f k w,
    selectedPresentationTransition_apply, selectedPresentationMap_map]

end FlagVarieties.Foundations.QuotientCharts
