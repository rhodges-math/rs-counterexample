import Schubert.FlagVarieties.Foundations.Flags.SelectedChartIncidence
import Mathlib.Algebra.MvPolynomial.Rename

/-!
# Polynomial equations for flag incidence on quotient charts

Each equation is a basis entry of the second quotient minus its forced
factorization through the first. The variables are the two original chart
matrices, in disjoint summands. Evaluation of these polynomials
detects inclusion of the chart kernels over every coefficient algebra.
-/

noncomputable section
namespace FlagVarieties.Foundations.QuotientCharts
universe u
variable (R : Type u) [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
  {n d e : ℕ} (a : Fin d ↪ Fin n) (b : Fin e ↪ Fin n)

theorem selectedPresentationMap_selected_sum
    (g : MvPolynomial (Fin e × Fin (n-e)) R →ₐ[R] A)
    (v : Fin d → A) (i : Fin e) :
    selectedPresentationMap R b g (coordinateInclusion a v) i =
      ∑ t : Fin d, selectedPresentationMap R b g (Pi.single (a t) 1) i * v t := by
  classical
  have h := congrFun (LinearMap.toMatrix'_mulVec
    ((selectedPresentationMap R b g).comp (coordinateInclusion a)) v) i
  simpa only [Matrix.mulVec, dotProduct, LinearMap.toMatrix'_apply,
    LinearMap.comp_apply, coordinateInclusion_basis] using h.symm

theorem selectedChartPoint_le_iff_polynomial_entries
    (f : MvPolynomial (Fin d × Fin (n-d)) R →ₐ[R] A)
    (g : MvPolynomial (Fin e × Fin (n-e)) R →ₐ[R] A) :
    (selectedChartPoint R a f).toSubmodule ≤ (selectedChartPoint R b g).toSubmodule ↔
      ∀ (i : Fin e) (j : Fin n),
        selectedPresentationMap R b g (Pi.single j 1) i -
          ∑ t : Fin d, selectedPresentationMap R b g (Pi.single (a t) 1) i *
            selectedPresentationMap R a f (Pi.single j 1) t = 0 := by
  simp only [selectedChartPoint_le_iff_entries, selectedPresentationMap_selected_sum]

/-- One equation in the joint polynomial parameter ring. -/
def selectedIncidencePolynomial (i : Fin e) (j : Fin n) :
    MvPolynomial ((Fin d × Fin (n-d)) ⊕ (Fin e × Fin (n-e))) R :=
  selectedPresentationMap R b (MvPolynomial.rename Sum.inr) (Pi.single j 1) i -
    ∑ t : Fin d,
      selectedPresentationMap R b (MvPolynomial.rename Sum.inr) (Pi.single (a t) 1) i *
        selectedPresentationMap R a (MvPolynomial.rename Sum.inl) (Pi.single j 1) t

theorem selectedPresentationMap_map_basis
    {B : Type u} [CommRing B] [Algebra R B]
    (f : MvPolynomial (Fin d × Fin (n-d)) R →ₐ[R] A)
    (k : A →ₐ[R] B) (i : Fin d) (j : Fin n) :
    k (selectedPresentationMap R a f (Pi.single j 1) i) =
      selectedPresentationMap R a (k.comp f) (Pi.single j 1) i := by
  classical
  have h := congrFun (selectedPresentationMap_map R a f k (Pi.single j 1)) i
  have hv : (fun t : Fin n => k ((Pi.single j (1 : A) : Fin n → A) t)) =
      (Pi.single j (1 : B) : Fin n → B) := by
    ext t
    simp [Pi.single_apply]
  rw [hv] at h
  exact h

/-- Evaluation of an incidence equation is the corresponding quotient entry. -/
theorem selectedIncidencePolynomial_eval
    (k : MvPolynomial ((Fin d × Fin (n-d)) ⊕ (Fin e × Fin (n-e))) R →ₐ[R] A)
    (i : Fin e) (j : Fin n) :
    k (selectedIncidencePolynomial R a b i j) =
      selectedPresentationMap R b (k.comp (MvPolynomial.rename Sum.inr)) (Pi.single j 1) i -
        ∑ t : Fin d,
          selectedPresentationMap R b (k.comp (MvPolynomial.rename Sum.inr))
              (Pi.single (a t) 1) i *
            selectedPresentationMap R a (k.comp (MvPolynomial.rename Sum.inl))
              (Pi.single j 1) t := by
  simp only [selectedIncidencePolynomial, map_sub, map_sum, map_mul,
    selectedPresentationMap_map_basis]

/-- The equations are sufficient and necessary over every coefficient algebra. -/
theorem selectedIncidencePolynomial_vanish_iff
    (k : MvPolynomial ((Fin d × Fin (n-d)) ⊕ (Fin e × Fin (n-e))) R →ₐ[R] A) :
    (∀ (i : Fin e) (j : Fin n), k (selectedIncidencePolynomial R a b i j) = 0) ↔
      (selectedChartPoint R a (k.comp (MvPolynomial.rename Sum.inl))).toSubmodule ≤
        (selectedChartPoint R b (k.comp (MvPolynomial.rename Sum.inr))).toSubmodule := by
  simp only [selectedIncidencePolynomial_eval, selectedChartPoint_le_iff_polynomial_entries]

end FlagVarieties.Foundations.QuotientCharts
