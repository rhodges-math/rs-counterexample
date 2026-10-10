import RSCounterexample.FlagVarieties.Foundations.Schemes.SelectedMorphismCoverCompatibility
import RSCounterexample.FlagVarieties.Foundations.Flags.FiniteLocalKernelDescent
import RSCounterexample.FlagVarieties.Foundations.Flags.CoordinateLocalizationKernels

/-!
# Descent of the local kernels of an incoming scheme map

Local quotient equality over a double localization supplies the required
power-clearing condition. On a finite presentation cover, the intersection
of the inverse-image kernels therefore has exactly the prescribed
localizations. Projectivity and the rank of its quotient, which make this
submodule a Grassmannian point, are supplied in
`Schemes/SelectedMorphismQuotient.lean` via `grassmannianOfPrincipalQuotientFrames`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientCharts.SelectedMorphismCover

open AlgebraicGeometry CategoryTheory

universe u

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] {n d : ℕ}
  {F : Spec (CommRingCat.of A) ⟶ selectedChartScheme R n d}
  (D : SelectedMorphismCover F)

/-- The kernel obtained by imposing all the derived local quotient equations. -/
def kernel : Submodule A (Fin n → A) :=
  ⨅ i, ((selectedChartPoint R (D.selection i) (D.evaluation i)).toSubmodule.restrictScalars A).comap
    (coordinateScalarMap (Localization.Away (D.element i)) n)

/-- Overlap compatibility clears a power of the first principal element in the second kernel. -/
theorem kernel_pow_compatibility (i j : D.index) (v : Fin n → A)
    (hv : coordinateScalarMap (Localization.Away (D.element i)) n v ∈
      (selectedChartPoint R (D.selection i) (D.evaluation i)).toSubmodule) :
    ∃ k : ℕ, coordinateScalarMap (Localization.Away (D.element j)) n (D.element i ^ k • v) ∈
      (selectedChartPoint R (D.selection j) (D.evaluation j)).toSubmodule := by
  let S := Localization.Away (D.element j)
  let T := Localization.Away (algebraMap A S (D.element i))
  have hu : IsUnit (algebraMap A T (D.element i)) := by
    rw [IsScalarTower.algebraMap_apply A S T]
    exact IsLocalization.Away.algebraMap_isUnit (algebraMap A S (D.element i))
  let g : Localization.Away (D.element i) →ₐ[A] T :=
    IsLocalization.Away.liftAlgHom (D.element i)
      (f := IsScalarTower.toAlgHom A A T) hu
  let h : S →ₐ[A] T := IsScalarTower.toAlgHom A S T
  have heq := D.quotient_after_maps_eq D i j g h
  let : Algebra (Localization.Away (D.element i)) T := g.toAlgebra
  have hi : coordinateScalarMap T n
        (coordinateScalarMap (Localization.Away (D.element i)) n v) ∈
      (selectedChartPoint R (D.selection i)
        ((g.restrictScalars R).comp (D.evaluation i))).toSubmodule := by
    rw [← selectedChartPoint_baseChange R (g.restrictScalars R)]
    exact coordinateScalarMap_mem_baseChange T _ hv
  have hvec : coordinateScalarMap T n
        (coordinateScalarMap (Localization.Away (D.element i)) n v) =
      coordinateScalarMap T n (coordinateScalarMap S n v) := by
    ext p
    simp only [coordinateScalarMap_apply]
    change g (algebraMap A (Localization.Away (D.element i)) (v p)) =
      algebraMap S T (algebraMap A S (v p))
    rw [g.commutes]
    exact IsScalarTower.algebraMap_apply A S T (v p)
  rw [hvec, heq] at hi
  have hj : coordinateScalarMap T n (coordinateScalarMap S n v) ∈
      (coordinateGrassmannianBaseChange T
        (selectedChartPoint R (D.selection j) (D.evaluation j))).toSubmodule := by
    rw [selectedChartPoint_baseChange_tower R]
    exact hi
  obtain ⟨k, hk⟩ := (coordinateScalarMap_mem_away_baseChange_iff
    (algebraMap A S (D.element i))
    (selectedChartPoint R (D.selection j) (D.evaluation j))
    (coordinateScalarMap S n v)).mp hj
  refine ⟨k, ?_⟩
  convert hk using 1
  ext p
  simp [coordinateScalarMap_apply, Pi.smul_apply, Algebra.smul_def, S]

/-- On every member of the finite cover, the descended kernel is exactly the original local
kernel. -/
theorem kernel_localized_eq [Finite D.index] (i : D.index) :
    D.kernel.localized' (Localization.Away (D.element i)) (.powers (D.element i))
        (coordinateScalarMap (Localization.Away (D.element i)) n) =
      (selectedChartPoint R (D.selection i) (D.evaluation i)).toSubmodule := by
  let := Fintype.ofFinite D.index
  exact finite_local_kernels_descend D.element
    (fun j => Localization.Away (D.element j))
    (fun j => Fin n → Localization.Away (D.element j))
    (fun j => coordinateScalarMap (Localization.Away (D.element j)) n)
    (fun j => (selectedChartPoint R (D.selection j) (D.evaluation j)).toSubmodule)
    D.kernel_pow_compatibility i

end FlagVarieties.Foundations.QuotientCharts.SelectedMorphismCover
