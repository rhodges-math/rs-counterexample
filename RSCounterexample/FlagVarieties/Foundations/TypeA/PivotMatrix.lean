import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Partial-permutation matrices

`FlagVarieties.Foundations.pivotMatrix q` is the `0/1` matrix with a `1` in row `q c` of each
column `c` (the column-to-row convention).
-/

namespace FlagVarieties.Foundations

variable {K I J : Type*} [Field K] [Fintype I] [Fintype J]
  [DecidableEq I] [DecidableEq J]

/-- A partial-permutation matrix, with the column-to-row convention. -/
def pivotMatrix (q : J → I) : Matrix I J K := fun i c => if q c = i then 1 else 0

end FlagVarieties.Foundations
