import RSCounterexample.FlagVarieties.Foundations.Schemes.SelectedFlagMorphismCover
import RSCounterexample.FlagVarieties.Foundations.Schemes.SelectedFlagChartPointFaithfulness

/-!
# The original quotient projections detect affine flag morphisms

Both maps receive derived principal presentation covers. On every
intersection, scalar extension gives two joint affine presentations. Their
quotient projections detect equality by the original Grassmannian theorem.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TensorProduct
universe u
variable (R : Type u) [CommRing R] {A : Type u} [CommRing A] [Algebra R A] {n : ℕ}

theorem selectedFlagChartPointMap_eq_of_projections_eq
    (a b : (j : Fin (n+1)) → Fin (n-j.val) ↪ Fin n)
    (k l : MvPolynomial (FlagChartVariable n) R →ₐ[R] A)
    (hk : selectedFlagIncidenceIdeal R a ≤ RingHom.ker k.toRingHom)
    (hl : selectedFlagIncidenceIdeal R b ≤ RingHom.ker l.toRingHom)
    (h : ∀ j, selectedFlagChartPointMap R a k hk ≫ selectedFlagChartSchemeStep R n j =
      selectedFlagChartPointMap R b l hl ≫ selectedFlagChartSchemeStep R n j) :
    selectedFlagChartPointMap R a k hk = selectedFlagChartPointMap R b l hl := by
  apply selectedFlagChartPointMap_eq_of_steps_eq
  intro j
  have hj := h j
  rw [selectedFlagChartPointMap_step, selectedFlagChartPointMap_step] at hj
  exact selectedChartPoint_quotient_eq_of_map_eq R (a j) (b j) _ _ hj

variable {R}

theorem SelectedFlagMorphismCover.overlap_eq_of_projections_eq
    {F G : Spec (CommRingCat.of A) ⟶ selectedFlagChartScheme R n}
    (D : SelectedFlagMorphismCover F) (E : SelectedFlagMorphismCover G)
    (h : ∀ j, F ≫ selectedFlagChartSchemeStep R n j = G ≫ selectedFlagChartSchemeStep R n j)
    (i : D.index) (l : E.index) :
    pullback.fst (D.schemeCover.f i) (E.schemeCover.f l) ≫ D.chartMap i =
      pullback.snd (D.schemeCover.f i) (E.schemeCover.f l) ≫ E.chartMap l := by
  have hp (j : Fin (n+1)) :
      (pullback.fst (D.schemeCover.f i) (E.schemeCover.f l) ≫ D.chartMap i) ≫
        selectedFlagChartSchemeStep R n j =
      (pullback.snd (D.schemeCover.f i) (E.schemeCover.f l) ≫ E.chartMap l) ≫
        selectedFlagChartSchemeStep R n j := by
    rw [← D.restriction i, ← E.restriction l]
    simp only [Category.assoc]
    rw [h j, pullback.condition_assoc]
  let S := Localization.Away (D.element i)
  let T := Localization.Away (E.element l)
  let g : S →ₐ[A] S ⊗[A] T := Algebra.TensorProduct.includeLeft
  let q : T →ₐ[A] S ⊗[A] T := Algebra.TensorProduct.includeRight
  have hf : (pullbackSpecIso A S T).inv ≫
      pullback.fst (D.schemeCover.f i) (E.schemeCover.f l) =
        Spec.map (CommRingCat.ofHom g.toRingHom) := by
    exact pullbackSpecIso_inv_fst A S T
  have hs : (pullbackSpecIso A S T).inv ≫
      pullback.snd (D.schemeCover.f i) (E.schemeCover.f l) =
        Spec.map (CommRingCat.ofHom q.toRingHom) := by
    exact pullbackSpecIso_inv_snd A S T
  have he (j : Fin (n+1)) := congrArg
    (fun f => (pullbackSpecIso A S T).inv ≫ f) (hp j)
  apply (cancel_epi (pullbackSpecIso A S T).inv).mp
  rw [← Category.assoc, ← Category.assoc, hf, hs]
  change Spec.map (CommRingCat.ofHom (g.restrictScalars R).toRingHom) ≫
      selectedFlagChartPointMap R (D.selection i) (D.evaluation i) (D.incidence i) =
    Spec.map (CommRingCat.ofHom (q.restrictScalars R).toRingHom) ≫
      selectedFlagChartPointMap R (E.selection l) (E.evaluation l) (E.incidence l)
  rw [selectedFlagChartPointMap_comp, selectedFlagChartPointMap_comp]
  apply selectedFlagChartPointMap_eq_of_projections_eq
  intro j
  have hj := he j
  simp only [← Category.assoc, hf, hs] at hj
  change (Spec.map (CommRingCat.ofHom (g.restrictScalars R).toRingHom) ≫
      selectedFlagChartPointMap R (D.selection i) (D.evaluation i) (D.incidence i)) ≫
        selectedFlagChartSchemeStep R n j =
    (Spec.map (CommRingCat.ofHom (q.restrictScalars R).toRingHom) ≫
      selectedFlagChartPointMap R (E.selection l) (E.evaluation l) (E.incidence l)) ≫
        selectedFlagChartSchemeStep R n j at hj
  rw [selectedFlagChartPointMap_comp, selectedFlagChartPointMap_comp] at hj
  exact hj

/-- No extra flag-map identifications remain after checking every quotient projection. -/
theorem selectedFlagAffineMorphism_eq_of_projections_eq
    (F G : Spec (CommRingCat.of A) ⟶ selectedFlagChartScheme R n)
    (hF : F ≫ selectedFlagChartSchemeToSpec R n =
      Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (hG : G ≫ selectedFlagChartSchemeToSpec R n =
      Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (h : ∀ j, F ≫ selectedFlagChartSchemeStep R n j = G ≫ selectedFlagChartSchemeStep R n j) :
    F = G := by
  let D := selectedFlagMorphismCover F hF
  let E := selectedFlagMorphismCover G hG
  apply D.schemeCover.hom_ext
  intro i
  rw [D.restriction i]
  apply Scheme.Cover.hom_ext (E.schemeCover.pullback₁ (D.schemeCover.f i))
  intro l
  change pullback.fst (D.schemeCover.f i) (E.schemeCover.f l) ≫ D.chartMap i =
    pullback.fst (D.schemeCover.f i) (E.schemeCover.f l) ≫ D.schemeCover.f i ≫ G
  rw [pullback.condition_assoc, E.restriction l]
  exact D.overlap_eq_of_projections_eq E h i l

end FlagVarieties.Foundations.QuotientCharts
