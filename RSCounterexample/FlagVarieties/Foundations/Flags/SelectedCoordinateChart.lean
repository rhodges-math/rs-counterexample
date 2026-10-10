import RSCounterexample.FlagVarieties.Foundations.Flags.CoordinateSelection
import RSCounterexample.FlagVarieties.Foundations.Flags.GrassmannianChart
import RSCounterexample.FlagVarieties.Foundations.Flags.GrassmannianTransport

/-!
# Normalizing a selected-coordinate quotient

A coordinate injection is completed to an ordering of all ambient coordinates.
The completion only orders the unselected coordinates. Transport by this
ordering identifies the selected quotient map with the normalized
Grassmannian chart condition, and hence gives a unique matrix presentation.
-/

noncomputable section

namespace FlagVarieties.Foundations.QuotientCharts

variable {R : Type*} [CommRing R] {n d : ℕ}

/-- Complete selected coordinates by an ordering of their complement. -/
def coordinateCompletion (a : Fin d ↪ Fin n) : Fin d ⊕ Fin (n - d) ≃ Fin n := by
  classical
  let b : ↥((Set.range a)ᶜ : Set (Fin n)) ≃ Fin (n - d) :=
    Fintype.equivFinOfCardEq (by
      rw [Fintype.card_compl_set, Fintype.card_range, Fintype.card_fin, Fintype.card_fin])
  exact ((Equiv.ofInjective a a.injective).sumCongr b.symm).trans
    (Equiv.Set.sumCompl (Set.range a))

@[simp] theorem coordinateCompletion_inl (a : Fin d ↪ Fin n) (i : Fin d) :
    coordinateCompletion a (Sum.inl i) = a i := by
  classical
  simp [coordinateCompletion]

/-- Selected coordinates first, followed by the complementary coordinates. -/
def selectedCoordinateEquiv (a : Fin d ↪ Fin n) :
    (Fin n → R) ≃ₗ[R] ((Fin d → R) × (Fin (n - d) → R)) :=
  (LinearEquiv.piCongrLeft R (fun _ : Fin n => R) (coordinateCompletion a)).symm.trans
    (LinearEquiv.sumArrowLequivProdArrow (Fin d) (Fin (n - d)) R R)

@[simp] theorem selectedCoordinateEquiv_fst (a : Fin d ↪ Fin n)
    (v : Fin n → R) (i : Fin d) :
    (selectedCoordinateEquiv a v).1 i = v (a i) := by
  simp [selectedCoordinateEquiv, LinearEquiv.piCongrLeft, LinearEquiv.piCongrLeft']

@[simp] theorem selectedCoordinateEquiv_snd (a : Fin d ↪ Fin n)
    (v : Fin n → R) (j : Fin (n - d)) :
    (selectedCoordinateEquiv a v).2 j = v (coordinateCompletion a (Sum.inr j)) := rfl

/-- The original inclusion is precisely the first-coordinate inclusion
after changing ambient coordinates. -/
theorem selectedCoordinateEquiv_inclusion (a : Fin d ↪ Fin n) :
    (selectedCoordinateEquiv (R := R) a).toLinearMap.comp (coordinateInclusion a) =
      LinearMap.inl R (Fin d → R) (Fin (n - d) → R) := by
  classical
  apply (Pi.basisFun R (Fin d)).ext
  intro i
  simp only [LinearMap.comp_apply, Pi.basisFun_apply, coordinateInclusion_basis]
  apply Prod.ext
  · ext j
    simp [Pi.single_apply, a.injective.eq_iff]
  · ext j
    have hne : coordinateCompletion a (Sum.inr j) ≠ a i := by
      rw [← coordinateCompletion_inl a i]
      exact fun h => Sum.inr_ne_inl ((coordinateCompletion a).injective h)
    simp [hne]

/-- The quotient equivalence intertwines selected coordinate maps. -/
theorem selectedQuotientMap_transport (P : Submodule R (Fin n → R))
    (a : Fin d ↪ Fin n) :
    (Submodule.Quotient.equiv P _ (selectedCoordinateEquiv a) rfl).toLinearMap.comp
        (P.mkQ.comp (coordinateInclusion a)) =
      firstCoordinates (P.map (selectedCoordinateEquiv a).toLinearMap) := by
  have he := selectedCoordinateEquiv_inclusion (R := R) a
  apply LinearMap.ext
  intro v
  change Submodule.Quotient.mk (selectedCoordinateEquiv a (coordinateInclusion a v)) =
    Submodule.Quotient.mk (v, 0)
  exact congrArg Submodule.Quotient.mk (LinearMap.congr_fun he v)

/-- Applicability is exactly bijectivity of the original selected map. -/
theorem selectedCoordinate_chartCondition_iff (P : Submodule R (Fin n → R))
    (a : Fin d ↪ Fin n) :
    ChartCondition (P.map (selectedCoordinateEquiv a).toLinearMap) ↔
      Function.Bijective (P.mkQ.comp (coordinateInclusion a)) := by
  rw [ChartCondition, ← selectedQuotientMap_transport]
  change Function.Bijective ((Submodule.Quotient.equiv P _ (selectedCoordinateEquiv a) rfl) ∘
    (P.mkQ.comp (coordinateInclusion a))) ↔ _
  exact (Submodule.Quotient.equiv P _ (selectedCoordinateEquiv a) rfl).bijective.of_comp_iff' _

/-- Every applicable coordinate selection gives a unique normalized matrix
for the transported Grassmannian point. -/
theorem grassmannian_existsUnique_selectedMatrix
    (P : Module.Grassmannian R (Fin n → R) d) (a : Fin d ↪ Fin n)
    (ha : Function.Bijective (P.toSubmodule.mkQ.comp (coordinateInclusion a))) :
    ∃! C : Matrix (Fin d) (Fin (n - d)) R,
      (matrixGrassmannianChartEquiv C).val =
        grassmannianTransport P (selectedCoordinateEquiv a) := by
  let Q : GrassmannianChart R d (n - d) :=
    ⟨grassmannianTransport P (selectedCoordinateEquiv a),
      (selectedCoordinate_chartCondition_iff P.toSubmodule a).mpr ha⟩
  refine ⟨matrixGrassmannianChartEquiv.symm Q, ?_, ?_⟩
  · exact congrArg Subtype.val (matrixGrassmannianChartEquiv.apply_symm_apply Q)
  · intro C hC
    apply matrixGrassmannianChartEquiv.injective
    apply Subtype.ext
    exact hC.trans (congrArg Subtype.val (matrixGrassmannianChartEquiv.apply_symm_apply Q)).symm

/-- Every quotient over a local ring belongs to one of these charts. -/
theorem grassmannian_exists_selectedMatrix_local [IsLocalRing R]
    (P : Module.Grassmannian R (Fin n → R) d) :
    ∃ (a : Fin d ↪ Fin n) (C : Matrix (Fin d) (Fin (n - d)) R),
      (matrixGrassmannianChartEquiv C).val =
        grassmannianTransport P (selectedCoordinateEquiv a) := by
  obtain ⟨a, ha⟩ := grassmannian_exists_bijective_selectedMap_local P
  obtain ⟨C, hC, _⟩ := grassmannian_existsUnique_selectedMatrix P a ha
  exact ⟨a, C, hC⟩

end FlagVarieties.Foundations.QuotientCharts
