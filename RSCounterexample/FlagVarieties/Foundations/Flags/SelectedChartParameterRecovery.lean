import RSCounterexample.FlagVarieties.Foundations.Schemes.SelectedChartOverlapReturn

/-! # Unique selected polynomial parameters of a quotient -/

noncomputable section
namespace FlagVarieties.Foundations.QuotientCharts
universe u
variable (R : Type u) [CommRing R] {n d : ℕ}
  (a : Fin d ↪ Fin n) {A : Type u} [CommRing A] [Algebra R A]

theorem selectedChartPoint_injective : Function.Injective (selectedChartPoint R a (A := A)) := by
  intro f g h
  apply (matrixEvaluationEquiv R d (n-d) A).injective
  apply matrixGrassmannianChartEquiv.injective
  apply Subtype.ext
  rw [selectedChartPoint_presented, selectedChartPoint_presented, h]

/-- A selected basis of the quotient determines exactly one parameter map. -/
theorem selectedChartPoint_existsUnique
    (P : Module.Grassmannian A (Fin n → A) d)
    (ha : Function.Bijective (P.toSubmodule.mkQ.comp (coordinateInclusion a))) :
    ∃! f : MvPolynomial (Fin d × Fin (n-d)) R →ₐ[R] A, selectedChartPoint R a f = P := by
  obtain ⟨C, hC, _⟩ := grassmannian_existsUnique_selectedMatrix P a ha
  let f := (matrixEvaluationEquiv R d (n-d) A).symm C
  have hf : selectedChartPoint R a f = P := by
    apply (grassmannianTransportEquiv (selectedCoordinateEquiv (R := A) a)).injective
    change grassmannianTransport (selectedChartPoint R a f) (selectedCoordinateEquiv a) =
      grassmannianTransport P (selectedCoordinateEquiv a)
    rw [← selectedChartPoint_presented]
    simpa only [f, Equiv.apply_symm_apply] using hC
  refine ⟨f, hf, ?_⟩
  intro g hg
  exact selectedChartPoint_injective R a (hg.trans hf.symm)

end FlagVarieties.Foundations.QuotientCharts
