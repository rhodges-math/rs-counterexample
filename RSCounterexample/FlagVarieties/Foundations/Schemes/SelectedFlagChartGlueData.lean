import RSCounterexample.FlagVarieties.Foundations.Schemes.SelectedFlagTripleOverlapMaps
import Mathlib.AlgebraicGeometry.Gluing

/-!
# Gluing the full-flag incidence charts

The charts are the incidence quotient schemes, and their overlaps
are the simultaneous determinant opens. Triple fiber-product maps
satisfy the categorical cocycle. The resulting scheme and its open charts
are constructed here. Flag families are classified in
`Schemes/SelectedFlagAffineRingClassification.lean` (affine sources) and
`Schemes/GlobalQuotientFlagDescent.lean` (arbitrary schemes).
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable (R : Type u) [CommRing R] {n : ℕ}
  (a b c : (j : Fin (n+1)) → Fin (n-j.val) ↪ Fin n)

@[reassoc (attr := simp)]
theorem selectedFlagOverlapSchemeIso_reverse_map :
    (selectedFlagOverlapSchemeIso R a b).hom ≫ selectedFlagOverlapMap R b a =
      selectedFlagOverlapInclusion R a b := by
  rw [← selectedFlagOverlapSchemeIso_hom_inclusion, ← Category.assoc,
    selectedFlagOverlapSchemeIso_reverse, Category.id_comp]

/-- The transition `(a, b, c) ⟶ (b, c, a)` between triple overlaps, part of the gluing data of the
flag scheme. -/
def selectedFlagTripleOverlapTransition :
    selectedFlagTripleOverlap R a b c ⟶ selectedFlagTripleOverlap R b c a :=
  pullback.lift (selectedFlagTripleOverlapMap R a b c)
    (pullback.fst _ _ ≫ (selectedFlagOverlapSchemeIso R a b).hom) (by
      rw [Category.assoc, selectedFlagOverlapSchemeIso_hom_inclusion]
      exact selectedFlagTripleOverlapMap_first R a b c)

@[reassoc (attr := simp)]
theorem selectedFlagTripleOverlapTransition_snd :
    selectedFlagTripleOverlapTransition R a b c ≫ pullback.snd _ _ =
      pullback.fst _ _ ≫ (selectedFlagOverlapSchemeIso R a b).hom :=
  pullback.lift_snd _ _ _

@[reassoc]
theorem selectedFlagTripleOverlapTransition_third :
    selectedFlagTripleOverlapTransition R a b c ≫ pullback.fst _ _ ≫ selectedFlagOverlapMap R b c =
      pullback.snd _ _ ≫ selectedFlagOverlapMap R a c := by
  unfold selectedFlagTripleOverlapTransition
  rw [pullback.lift_fst_assoc]
  exact selectedFlagTripleOverlapMap_third R a b c

theorem selectedFlagTripleOverlapTransition_cocycle :
    selectedFlagTripleOverlapTransition R a b c ≫ selectedFlagTripleOverlapTransition R b c a ≫
      selectedFlagTripleOverlapTransition R c a b = 𝟙 _ := by
  apply (cancel_mono (pullback.snd (selectedFlagOverlapInclusion R a b)
    (selectedFlagOverlapInclusion R a c) ≫ selectedFlagOverlapInclusion R a c)).mp
  simp only [Category.id_comp, Category.assoc]
  rw [selectedFlagTripleOverlapTransition_snd_assoc]
  rw [selectedFlagOverlapSchemeIso_hom_inclusion]
  rw [selectedFlagTripleOverlapTransition_third]
  rw [selectedFlagTripleOverlapTransition_snd_assoc, selectedFlagOverlapSchemeIso_reverse_map]
  exact pullback.condition

variable (n)

/-- Gluing data with all selected full-flag incidence charts. -/
def selectedFlagChartGlueData : Scheme.GlueData.{u} where
  J := ULift.{u} ((j : Fin (n+1)) → Fin (n-j.val) ↪ Fin n)
  U i := selectedFlagIncidenceChart R i.down
  V ij := selectedFlagOverlapScheme R ij.1.down ij.2.down
  f i j := selectedFlagOverlapInclusion R i.down j.down
  t i j := (selectedFlagOverlapSchemeIso R i.down j.down).hom
  t_id i := selectedFlagOverlapSchemeIso_self R i.down
  t' i j k := selectedFlagTripleOverlapTransition R i.down j.down k.down
  t_fac i j k := selectedFlagTripleOverlapTransition_snd R i.down j.down k.down
  cocycle i j k := selectedFlagTripleOverlapTransition_cocycle R i.down j.down k.down
  f_open i j := selectedFlagOverlapInclusion_open R i.down j.down

/-- The scheme obtained by gluing the full-flag incidence charts. -/
def selectedFlagChartScheme : Scheme.{u} := (selectedFlagChartGlueData R n).glued

/-- The open immersion of the chart `a` into the flag scheme. -/
def selectedFlagChartSchemeChart
    (a : (j : Fin (n+1)) → Fin (n-j.val) ↪ Fin n) :
    selectedFlagIncidenceChart R a ⟶ selectedFlagChartScheme R n :=
  (selectedFlagChartGlueData R n).ι ⟨a⟩

instance selectedFlagChartSchemeChart_open
    (a : (j : Fin (n+1)) → Fin (n-j.val) ↪ Fin n) :
    IsOpenImmersion (selectedFlagChartSchemeChart R n a) := by
  unfold selectedFlagChartSchemeChart
  infer_instance

end FlagVarieties.Foundations.QuotientCharts
