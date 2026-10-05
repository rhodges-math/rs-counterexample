import Schubert.FlagVarieties.Foundations.Schemes.SelectedTripleOverlapMaps
import Mathlib.AlgebraicGeometry.Gluing

/-!
# Scheme gluing data for the selected quotient charts

The pairwise overlaps and triple fiber products are schemes. Their
maps satisfy the categorical cocycle, so Mathlib's scheme-gluing theorem
applies. The functor of the glued scheme is identified with the quotient
Grassmannian in `Schemes/SelectedAffineClassification.lean`, and its universal
quotient is constructed in `Schemes/SelectedUniversalQuotient.lean`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace FlagVarieties.Foundations.QuotientCharts

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

variable (R : Type u) [CommRing R] {n d : ℕ} (a b c : Fin d ↪ Fin n)

@[reassoc] theorem selectedChartOverlapIso_hom_inclusion :
    (selectedChartOverlapIso R a b).hom ≫ selectedChartOverlapInclusion R b a =
      selectedChartOverlapMap R a b :=
  selectedChartOverlapIso_hom_chart R a b

@[reassoc (attr := simp)] theorem selectedChartOverlapIso_reverse_map :
    (selectedChartOverlapIso R a b).hom ≫ selectedChartOverlapMap R b a =
      selectedChartOverlapInclusion R a b := by
  rw [← selectedChartOverlapIso_hom_chart, ← Category.assoc, selectedChartOverlapIso_reverse,
    Category.id_comp]
  rfl

/-- The cyclic change of first chart on a triple intersection. -/
def selectedTripleOverlapTransition :
    selectedTripleOverlap R a b c ⟶ selectedTripleOverlap R b c a :=
  pullback.lift (selectedTripleOverlapToSecondThird R a b c)
    (pullback.fst _ _ ≫ (selectedChartOverlapIso R a b).hom) (by
      rw [Category.assoc, selectedChartOverlapIso_hom_inclusion]
      exact selectedTripleOverlapToSecondThird_first R a b c)

@[reassoc (attr := simp)] theorem selectedTripleOverlapTransition_snd :
    selectedTripleOverlapTransition R a b c ≫ pullback.snd _ _ =
      pullback.fst _ _ ≫ (selectedChartOverlapIso R a b).hom :=
  pullback.lift_snd _ _ _

@[reassoc] theorem selectedTripleOverlapTransition_third :
    selectedTripleOverlapTransition R a b c ≫ pullback.fst _ _ ≫ selectedChartOverlapMap R b c =
      pullback.snd _ _ ≫ selectedChartOverlapMap R a c := by
  unfold selectedTripleOverlapTransition
  rw [pullback.lift_fst_assoc]
  exact selectedTripleOverlapToSecondThird_third R a b c

/-- The cyclic triple transition is the identity after three changes of chart. -/
theorem selectedTripleOverlapTransition_cocycle :
    selectedTripleOverlapTransition R a b c ≫ selectedTripleOverlapTransition R b c a ≫
      selectedTripleOverlapTransition R c a b = 𝟙 _ := by
  apply (cancel_mono (pullback.snd (selectedChartOverlapInclusion R a b)
    (selectedChartOverlapInclusion R a c) ≫ selectedChartOverlapInclusion R a c)).mp
  simp only [Category.id_comp, Category.assoc]
  rw [selectedTripleOverlapTransition_snd_assoc]
  rw [selectedChartOverlapIso_hom_inclusion]
  rw [selectedTripleOverlapTransition_third]
  rw [selectedTripleOverlapTransition_snd_assoc, selectedChartOverlapIso_reverse_map]
  exact pullback.condition

variable (n d)

/-- Scheme gluing data using every selected-coordinate chart and its determinant overlaps. -/
def selectedChartGlueData : Scheme.GlueData.{u} where
  J := ULift.{u} (Fin d ↪ Fin n)
  U _ := Spec (CommRingCat.of (MvPolynomial (Fin d × Fin (n - d)) R))
  V ij := Spec (CommRingCat.of
    (Localization.Away (selectedPolynomialBlock R ij.1.down ij.2.down).det))
  f i j := selectedChartOverlapInclusion R i.down j.down
  t i j := (selectedChartOverlapIso R i.down j.down).hom
  t_id i := selectedChartOverlapIso_self R i.down
  t' i j k := selectedTripleOverlapTransition R i.down j.down k.down
  t_fac i j k := selectedTripleOverlapTransition_snd R i.down j.down k.down
  cocycle i j k := selectedTripleOverlapTransition_cocycle R i.down j.down k.down
  f_open i j := selectedChartOverlapInclusion_open R i.down j.down

/-- The scheme obtained by gluing the normalized quotient charts. -/
def selectedChartScheme : Scheme.{u} := (selectedChartGlueData R n d).glued

/-- The canonical open chart maps into the glued scheme. -/
def selectedChartSchemeChart (a : Fin d ↪ Fin n) :
    Spec (CommRingCat.of (MvPolynomial (Fin d × Fin (n - d)) R)) ⟶
      selectedChartScheme R n d := (selectedChartGlueData R n d).ι ⟨a⟩

instance selectedChartSchemeChart_open (a : Fin d ↪ Fin n) :
    IsOpenImmersion (selectedChartSchemeChart R n d a) := by
  unfold selectedChartSchemeChart
  infer_instance

theorem selectedChartSchemeChart_jointly_surjective (x : selectedChartScheme R n d) :
    ∃ (a : Fin d ↪ Fin n)
      (y : Spec (CommRingCat.of (MvPolynomial (Fin d × Fin (n - d)) R))),
      selectedChartSchemeChart R n d a y = x := by
  obtain ⟨a, y, hy⟩ := (selectedChartGlueData R n d).ι_jointly_surjective x
  exact ⟨a.down, y, hy⟩

end FlagVarieties.Foundations.QuotientCharts
