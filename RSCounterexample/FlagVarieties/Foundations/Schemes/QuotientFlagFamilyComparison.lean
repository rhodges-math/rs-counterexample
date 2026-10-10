import RSCounterexample.FlagVarieties.Foundations.Schemes.QuotientFlagFamily

/-! # Source-preserving step comparisons automatically respect the flag chain -/

noncomputable section
namespace FlagVarieties.Foundations.QuotientCharts.QuotientFlagFamily
open AlgebraicGeometry CategoryTheory
universe u
variable {X : Scheme.{u}} {n : ℕ} (F G : QuotientFlagFamily X n)

/-- Compatibility of the adjacent arrows follows from their original common source.
It is not a further assumption on a family of quotient comparisons. -/
theorem transition_natural_of_source
    (e : ∀ j, F.target j ⟶ G.target j)
    (he : ∀ j, F.quotient j ≫ e j = G.quotient j) (j : Fin n) :
    F.transition j ≫ e j.succ = e j.castSucc ≫ G.transition j := by
  let : Epi (F.quotient j.castSucc) := F.quotient_epi j.castSucc
  apply (cancel_epi (F.quotient j.castSucc)).mp
  rw [← Category.assoc, F.transition_source, he j.succ,
    ← Category.assoc, he j.castSucc, G.transition_source]

/-- A morphism of quotient targets is uniquely determined by its source equation. -/
theorem step_comparison_unique (j : Fin (n+1))
    (e f : F.target j ⟶ G.target j)
    (he : F.quotient j ≫ e = G.quotient j)
    (hf : F.quotient j ≫ f = G.quotient j) : e = f := by
  let : Epi (F.quotient j) := F.quotient_epi j
  exact (cancel_epi (F.quotient j)).mp (he.trans hf.symm)

end FlagVarieties.Foundations.QuotientCharts.QuotientFlagFamily
