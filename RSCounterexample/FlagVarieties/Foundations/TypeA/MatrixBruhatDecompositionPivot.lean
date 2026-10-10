import RSCounterexample.FlagVarieties.Foundations.TypeA.MatrixBruhatDecompositionElementary

/-!
# One-step upper-triangular pivot elimination

At a nonzero entry `(r,c)`, an upper-triangular column operation clears
a chosen entry to its right in row `r`.  An upper-triangular row operation
clears a chosen entry above it in column `c`.  The lemmas record the
unchanged columns and rows needed to iterate these steps.
-/

namespace FlagVarieties.Foundations.TypeA

open Matrix

variable {n : ℕ} {K : Type*} [Field K]

/-- The column operation adding `-(A r j / A r c)` times column `c` to column `j`; it clears the
entry `(r, j)` using the pivot `(r, c)`. -/
def rightPivotEliminator (A : Matrix (Fin n) (Fin n) K)
    (r c j : Fin n) : Matrix (Fin n) (Fin n) K :=
  Matrix.transvection c j (-(A r j / A r c))

/-- The row operation adding `-(A i c / A r c)` times row `r` to row `i`; it clears the entry
`(i, c)` using the pivot `(r, c)`. -/
def leftPivotEliminator (A : Matrix (Fin n) (Fin n) K)
    (r c i : Fin n) : Matrix (Fin n) (Fin n) K :=
  Matrix.transvection i r (-(A i c / A r c))

theorem rightPivotEliminator_upper (A : Matrix (Fin n) (Fin n) K)
    (r c j : Fin n) (hcj : c < j) :
    (rightPivotEliminator A r c j).IsUpperTriangular :=
  upper_transvection hcj _

theorem leftPivotEliminator_upper (A : Matrix (Fin n) (Fin n) K)
    (r c i : Fin n) (hir : i < r) :
    (leftPivotEliminator A r c i).IsUpperTriangular :=
  upper_transvection hir _

theorem rightPivotEliminator_isUnit (A : Matrix (Fin n) (Fin n) K)
    (r c j : Fin n) (hcj : c < j) :
    IsUnit (rightPivotEliminator A r c j) :=
  upper_transvection_isUnit hcj _

theorem leftPivotEliminator_isUnit (A : Matrix (Fin n) (Fin n) K)
    (r c i : Fin n) (hir : i < r) :
    IsUnit (leftPivotEliminator A r c i) :=
  upper_transvection_isUnit hir _

theorem rightPivotEliminator_clear (A : Matrix (Fin n) (Fin n) K)
    (r c j : Fin n) (hp : A r c ≠ 0) :
    (A * rightPivotEliminator A r c j) r j = 0 := by
  classical
  simp only [rightPivotEliminator, Matrix.mul_transvection_apply_same]
  field_simp
  ring

theorem leftPivotEliminator_clear (A : Matrix (Fin n) (Fin n) K)
    (r c i : Fin n) (hp : A r c ≠ 0) :
    (leftPivotEliminator A r c i * A) i c = 0 := by
  classical
  simp only [leftPivotEliminator, Matrix.transvection_mul_apply_same]
  field_simp
  ring

theorem rightPivotEliminator_other_column (A : Matrix (Fin n) (Fin n) K)
    (r c j : Fin n) (t : Fin n) (ht : t ≠ j) :
    ∀ i, (A * rightPivotEliminator A r c j) i t = A i t := by
  classical
  intro i
  exact Matrix.mul_transvection_apply_of_ne c j i t ht _ A

theorem leftPivotEliminator_other_row (A : Matrix (Fin n) (Fin n) K)
    (r c i : Fin n) (t : Fin n) (ht : t ≠ i) :
    ∀ j, (leftPivotEliminator A r c i * A) t j = A t j := by
  classical
  intro j
  exact Matrix.transvection_mul_apply_of_ne i r t j ht _ A

end FlagVarieties.Foundations.TypeA
