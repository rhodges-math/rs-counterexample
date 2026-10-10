import RSCounterexample.FlagVarieties.Foundations.Schemes.SelectedChartPointFaithfulness
import RSCounterexample.FlagVarieties.Foundations.Flags.LocalizedCoordinateChart
import Mathlib.AlgebraicGeometry.Cover.Open

/-!
# Finite-projective quotients have selected affine chart covers

Every quotient in the coordinate Grassmannian admits a principal cover with
normalized matrix presentations. The data below record those
presentations, and their existence is derived from the quotient itself.
The cover can be empty over the zero ring. No global quotient basis is assumed.
-/

noncomputable section

namespace FlagVarieties.Foundations.QuotientCharts

open AlgebraicGeometry CategoryTheory

universe u

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
  {n d : ℕ} (P : Module.Grassmannian A (Fin n → A) d)

/-- Principal-open normalized presentations of a fixed quotient. -/
structure SelectedQuotientCover where
  /-- The index set of the cover. -/
  index : Type u
  /-- The functions `fᵢ` whose basic open sets `D(fᵢ)` cover `Spec A`. -/
  element : index → A
  /-- The chart in which the quotient is presented on `D(fᵢ)`. -/
  selection : index → (Fin d ↪ Fin n)
  span_top : Ideal.span (Set.range element) = ⊤
  /-- The chart coordinates of the quotient on `D(fᵢ)`. -/
  evaluation : ∀ i, MvPolynomial (Fin d × Fin (n - d)) R →ₐ[R]
    Localization.Away (element i)
  represents : ∀ i, selectedChartPoint R (selection i) (evaluation i) =
    coordinateGrassmannianBaseChange (Localization.Away (element i)) P

/-- The quotient itself supplies all local presentation data. -/
theorem selectedQuotientCover_nonempty : Nonempty (SelectedQuotientCover R A P) := by
  classical
  obtain ⟨s, a, g, hcover, hm⟩ := grassmannian_exists_selectedMatrix_finiteOpenCover P
  choose C hC using fun i => (hm i).exists
  refine ⟨{
    index := s
    element := g
    selection := a
    span_top := PrimeSpectrum.iSup_basicOpen_eq_top_iff.mp hcover
    evaluation := fun i => (matrixEvaluationEquiv R d (n - d) (Localization.Away (g i))).symm (C i)
    represents := ?_ }⟩
  intro i
  unfold selectedChartPoint
  rw [Equiv.apply_symm_apply, hC i, grassmannianTransport_symm]

/-- A fixed choice of derived presentations, used only to construct the global map. -/
def selectedQuotientCover : SelectedQuotientCover R A P :=
  Classical.choice (selectedQuotientCover_nonempty R A P)

namespace SelectedQuotientCover

variable {R A P} (D : SelectedQuotientCover R A P)

/-- The covering domains are spectra of the corresponding localizations. -/
abbrev schemeCover : (Spec (CommRingCat.of A)).OpenCover :=
  (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of A) D.element D.span_top).openCover

/-- Each derived normalized quotient presentation gives a scheme map. -/
def chartMap (i : D.index) : Spec (CommRingCat.of (Localization.Away (D.element i))) ⟶
    selectedChartScheme R n d :=
  selectedChartPointMap R (D.selection i) (D.evaluation i)

end SelectedQuotientCover

variable {A} {B : Type u} [CommRing B] [Algebra R B]
  (a : Fin d ↪ Fin n)

/-- Pullback of a presented affine point is composition of its polynomial evaluation. -/
@[reassoc] theorem selectedChartPointMap_comp
    (f : MvPolynomial (Fin d × Fin (n - d)) R →ₐ[R] A) (g : A →ₐ[R] B) :
    Spec.map (CommRingCat.ofHom g.toRingHom) ≫ selectedChartPointMap R a f =
      selectedChartPointMap R a (g.comp f) := by
  unfold selectedChartPointMap
  rw [← Category.assoc, spec_map_algHom_comp]

/-- An algebra map gives a morphism over its coefficient-ring map. -/
theorem spec_map_algHom_toSpec
    {S : Type u} [CommRing S] [Algebra R S] (f : S →ₐ[R] A) :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R S)) =
        Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact f.comp_algebraMap

/-- The affine presentation map lies over the original coefficient ring. -/
@[reassoc] theorem selectedChartPointMap_toSpec
    (f : MvPolynomial (Fin d × Fin (n - d)) R →ₐ[R] A) :
    selectedChartPointMap R a f ≫ selectedChartSchemeToSpec R n d =
      Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
  rw [selectedChartPointMap, Category.assoc, selectedChartSchemeChart_toSpec]
  exact spec_map_algHom_toSpec R f

end FlagVarieties.Foundations.QuotientCharts
