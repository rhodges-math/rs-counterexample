import RSCounterexample.FlagVarieties.Foundations.Flags.SelectedChartIncidence

/-!
# The two endpoint kernels of a full flag chart

The rank-n selected quotient has zero kernel and the rank-zero quotient
has the whole ambient module as kernel. These assertions hold over every
commutative coefficient algebra, including the zero ring and n=0.
-/

noncomputable section
namespace FlagVarieties.Foundations.QuotientCharts
universe u
variable (R : Type u) [CommRing R] {A : Type u} [CommRing A] [Algebra R A] {n : ℕ}

theorem selectedChartPoint_full_bottom (a : Fin n ↪ Fin n)
    (f : MvPolynomial (Fin n × Fin (n-n)) R →ₐ[R] A) :
    (selectedChartPoint R a f).toSubmodule = ⊥ := by
  classical
  rw [← selectedPresentationMap_ker, LinearMap.ker_eq_bot]
  intro v w h
  funext j
  obtain ⟨i, rfl⟩ := (Finite.surjective_of_injective a.injective) j
  have hi := congrFun h i
  let : IsEmpty (Fin (n-n)) := ⟨fun j => by have := j.isLt; omega⟩
  simpa only [selectedPresentationMap_apply, Finset.univ_eq_empty, Finset.sum_empty,
    add_zero] using hi

theorem selectedChartPoint_zero_top (a : Fin 0 ↪ Fin n)
    (f : MvPolynomial (Fin 0 × Fin (n-0)) R →ₐ[R] A) :
    (selectedChartPoint R a f).toSubmodule = ⊤ := by
  rw [← selectedPresentationMap_ker, LinearMap.ker_eq_top]
  apply LinearMap.ext
  intro v
  exact Subsingleton.elim _ _

end FlagVarieties.Foundations.QuotientCharts
