import RSCounterexample.FlagVarieties.Foundations.Flags.QuotientChart
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# The normalized matrix chart of the Grassmannian

The coefficient maps from `QuotientChart` parametrize the subtype of
Mathlib's quotient-convention Grassmannian on which the selected coordinate
images form a basis. The quotient is finite projective of the required
stalk rank. No open immersion or chart-cover assertion is assumed here.
-/

namespace FlagVarieties.Foundations.QuotientCharts

variable {R : Type*} [CommRing R] {d c : ℕ}

/-- A normalized matrix determines a Grassmannian point. -/
noncomputable def normalizedGrassmannian (C : (Fin c → R) →ₗ[R] (Fin d → R)) :
    Module.Grassmannian R ((Fin d → R) × (Fin c → R)) d where
  toSubmodule := LinearMap.ker (normalizedMap C)
  finite_quotient := Module.Finite.equiv (normalizedQuotientEquiv C).symm
  projective_quotient := Module.Projective.of_equiv (normalizedQuotientEquiv C).symm
  rankAtStalk_eq p := by
    let := p.nontrivial
    rw [congrFun (Module.rankAtStalk_eq_of_equiv (normalizedQuotientEquiv C)) p]
    rw [Module.rankAtStalk_pi (fun _ : Fin d => R) p]
    simp [finsum_eq_sum_of_fintype]

@[simp] theorem normalizedGrassmannian_submodule (C : (Fin c → R) →ₗ[R] (Fin d → R)) :
    (normalizedGrassmannian C).toSubmodule = LinearMap.ker (normalizedMap C) := rfl

/-- The chart condition is on the selected-coordinate map into the
quotient of an existing Grassmannian point. -/
def GrassmannianChart (R : Type*) [CommRing R] (d c : ℕ) :=
  {P : Module.Grassmannian R ((Fin d → R) × (Fin c → R)) d // ChartCondition P.toSubmodule}

/-- Every chart point has a unique coefficient map and conversely. -/
noncomputable def grassmannianChartEquiv :
    ((Fin c → R) →ₗ[R] (Fin d → R)) ≃ GrassmannianChart R d c where
  toFun C := ⟨normalizedGrassmannian C, normalizedMap_chartCondition C⟩
  invFun P := coefficients P.val.toSubmodule P.property
  left_inv C := coefficients_normalizedMap C _
  right_inv P := by
    apply Subtype.ext
    apply Module.Grassmannian.ext
    exact normalizedMap_coefficients_ker P.val.toSubmodule P.property

/-- Affine matrix parameters for the normalized chart, with explicit row
and column indexing. Scheme representability is a further theorem. -/
noncomputable def matrixGrassmannianChartEquiv :
    Matrix (Fin d) (Fin c) R ≃ GrassmannianChart R d c :=
  (Matrix.toLin' : Matrix (Fin d) (Fin c) R ≃ₗ[R] ((Fin c → R) →ₗ[R] (Fin d → R))).toEquiv.trans
    grassmannianChartEquiv

@[simp] theorem matrixGrassmannianChartEquiv_submodule (C : Matrix (Fin d) (Fin c) R) :
    (matrixGrassmannianChartEquiv C).val.toSubmodule =
      LinearMap.ker (normalizedMap (Matrix.toLin' C)) := rfl

end FlagVarieties.Foundations.QuotientCharts
