import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Elementary upper-triangular operations for Bruhat elimination

The transvection at `(i,j)` with `i<j` adds a later row to an earlier
row on the left, or an earlier column to a later column on the right.
Both operations preserve the upper Borel group.
-/

namespace FlagVarieties.Foundations.TypeA

open Matrix

variable {n : ℕ} {K : Type*} [Field K]

theorem upper_transvection {i j : Fin n} (hij : i < j) (c : K) :
    (Matrix.transvection i j c).IsUpperTriangular := by
  intro a b hba
  have hab : a ≠ b := ne_of_gt hba
  have hcross : ¬(i = a ∧ j = b) := by
    rintro ⟨rfl, rfl⟩
    exact (not_lt_of_ge hij.le) hba
  simp [Matrix.transvection, hab, hcross]

theorem upper_transvection_det {i j : Fin n} (hij : i < j) (c : K) :
    (Matrix.transvection i j c).det = 1 := by
  classical
  exact Matrix.det_transvection_of_ne i j (ne_of_lt hij) c

theorem upper_transvection_isUnit {i j : Fin n} (hij : i < j) (c : K) :
    IsUnit (Matrix.transvection i j c) := by
  classical
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  rw [upper_transvection_det hij]
  exact isUnit_one

end FlagVarieties.Foundations.TypeA
