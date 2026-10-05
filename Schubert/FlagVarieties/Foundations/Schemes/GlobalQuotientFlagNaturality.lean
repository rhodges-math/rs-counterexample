import Schubert.FlagVarieties.Foundations.Schemes.GlobalQuotientFlagClassification

/-! # Arbitrary pullback naturality of full flag classification -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory
universe u
variable (R : Type u) [CommRing R] {X : Scheme.{u}} {n : ℕ}
  (b : X ⟶ Spec (CommRingCat.of R)) (F : QuotientFlagFamily X n)

theorem globalQuotientFlagUniversalIso_unique (j : Fin (n+1))
    (e : (Scheme.Modules.pullback (globalQuotientFlagMorphism R b F)).obj
      (selectedFlagUniversalTarget R n j) ≅ F.target j)
    (he : coordinatePullbackQuotient (globalQuotientFlagMorphism R b F)
      (selectedFlagUniversalQuotient R n j) ≫ e.hom = F.quotient j) :
    e = globalQuotientFlagUniversalIso R b F j := by
  apply Iso.ext
  apply (cancel_epi (coordinatePullbackQuotient (globalQuotientFlagMorphism R b F)
    (selectedFlagUniversalQuotient R n j))).mp
  exact he.trans (globalQuotientFlagUniversalIso_source R b F j).symm

theorem globalQuotientFlagMorphism_pullback {Y : Scheme.{u}} (g : Y ⟶ X) :
    g ≫ globalQuotientFlagMorphism R b F =
      globalQuotientFlagMorphism R (g ≫ b) (F.pullback g) := by
  apply globalQuotientFlagMorphism_unique R (g ≫ b) (F.pullback g)
    (g ≫ globalQuotientFlagMorphism R b F)
    (by rw [Category.assoc, globalQuotientFlagMorphism_toSpec])
    (fun j => coordinateQuotientComparisonPullback g (globalQuotientFlagMorphism R b F)
      (globalQuotientFlagUniversalIso R b F j))
  intro j
  exact coordinateQuotientComparisonPullback_source g
    (globalQuotientFlagMorphism R b F) (selectedFlagUniversalQuotient R n j) (F.quotient j)
    (globalQuotientFlagUniversalIso R b F j) (globalQuotientFlagUniversalIso_source R b F j)

theorem globalQuotientFlagMorphism_targetIso (G : QuotientFlagFamily X n)
    (e : ∀ j, F.target j ≅ G.target j)
    (he : ∀ j, F.quotient j ≫ (e j).hom = G.quotient j) :
    globalQuotientFlagMorphism R b F = globalQuotientFlagMorphism R b G := by
  apply globalQuotientFlagMorphism_unique R b G (globalQuotientFlagMorphism R b F)
    (globalQuotientFlagMorphism_toSpec R b F)
    (fun j => globalQuotientFlagUniversalIso R b F j ≪≫ e j)
  intro j
  simp only [Iso.trans_hom]
  rw [← Category.assoc, globalQuotientFlagUniversalIso_source, he j]

end FlagVarieties.Foundations.QuotientCharts
