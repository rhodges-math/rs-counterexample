import RSCounterexample.FlagVarieties.Foundations.Schemes.SelectedMorphismCover

/-!
# Finite principal presentations of an incoming Grassmannian morphism

The unit-ideal property of the derived principal cover supplies a finite
subcover. Its evaluations and factorization equations are retained literally.
No global quotient or descent assertion is a premise.
-/

noncomputable section

namespace FlagVarieties.Foundations.QuotientCharts

open AlgebraicGeometry CategoryTheory

universe u

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] {n d : ℕ}
  {F : Spec (CommRingCat.of A) ⟶ selectedChartScheme R n d}

namespace SelectedMorphismCover

/-- Retain selected presentations along a family still generating the unit ideal. -/
def reindex (D : SelectedMorphismCover F) {J : Type u} (p : J → D.index)
    (h : Ideal.span (Set.range (fun j => D.element (p j))) = ⊤) :
    SelectedMorphismCover F where
  index := J
  element j := D.element (p j)
  selection j := D.selection (p j)
  span_top := h
  evaluation j := D.evaluation (p j)
  factors j := D.factors (p j)

/-- A finite subfamily suffices, including when the spectrum is empty. -/
theorem exists_finite_refinement (D : SelectedMorphismCover F) :
    ∃ E : SelectedMorphismCover F, Finite E.index := by
  classical
  obtain ⟨T, hT, hspan⟩ := (Ideal.span_eq_top_iff_finite (Set.range D.element)).mp
    D.span_top
  have hex (t : T) : ∃ i, D.element i = (t : A) := hT t.property
  let p (t : T) := Classical.choose (hex t)
  have hp (t : T) : D.element (p t) = (t : A) := Classical.choose_spec (hex t)
  have hrange : Set.range (fun t : T => D.element (p t)) = (T : Set A) := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      change D.element (p t) ∈ (T : Set A)
      rw [hp t]
      exact t.property
    · intro hx
      exact ⟨⟨x, hx⟩, hp ⟨x, hx⟩⟩
  have hcover : Ideal.span (Set.range (fun t : T => D.element (p t))) = ⊤ := by
    rw [hrange]
    exact hspan
  exact ⟨D.reindex p hcover, inferInstanceAs (Finite T)⟩

end SelectedMorphismCover

/-- Every incoming map over the coefficient base has a finite principal presentation cover. -/
theorem selectedMorphism_finite_cover_exists
    (F : Spec (CommRingCat.of A) ⟶ selectedChartScheme R n d)
    (hF : F ≫ selectedChartSchemeToSpec R n d =
      Spec.map (CommRingCat.ofHom (algebraMap R A))) :
    ∃ D : SelectedMorphismCover F, Finite D.index :=
  (selectedMorphismCover F hF).exists_finite_refinement

/-- A finite cover chosen from the local presentations of the map. -/
def selectedMorphismFiniteCover
    (F : Spec (CommRingCat.of A) ⟶ selectedChartScheme R n d)
    (hF : F ≫ selectedChartSchemeToSpec R n d =
      Spec.map (CommRingCat.ofHom (algebraMap R A))) : SelectedMorphismCover F :=
  (selectedMorphism_finite_cover_exists F hF).choose

instance selectedMorphismFiniteCover_finite
    (F : Spec (CommRingCat.of A) ⟶ selectedChartScheme R n d)
    (hF : F ≫ selectedChartSchemeToSpec R n d =
      Spec.map (CommRingCat.ofHom (algebraMap R A))) :
    Finite (selectedMorphismFiniteCover F hF).index :=
  (selectedMorphism_finite_cover_exists F hF).choose_spec

end FlagVarieties.Foundations.QuotientCharts
