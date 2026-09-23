import Schubert.Algebra.Basic
import Mathlib.GroupTheory.Perm.Fin

/-! # Finite permutations and descents -/

namespace Schubert

abbrev FinPermutation (n : ℕ) := Equiv.Perm (Fin n)

namespace FinPermutation

variable {n : ℕ}

/-- A descent at position `i`; the existential position is its successor.
The final position consequently cannot be a descent. -/
def HasDescent (w : FinPermutation n) (i : Fin n) : Prop :=
  ∃ j : Fin n, j.1 = i.1 + 1 ∧ w j < w i

/-- The descent positions of a finite permutation. -/
def descentSet (w : FinPermutation n) : Set (Fin n) :=
  {i | w.HasDescent i}

/-- A permutation is Grassmannian when it has exactly one descent. -/
def IsGrassmannian (w : FinPermutation n) : Prop :=
  ∃! i : Fin n, w.HasDescent i

/-- A permutation is bigrassmannian when it and its inverse are Grassmannian. -/
def IsBigrassmannian (w : FinPermutation n) : Prop :=
  w.IsGrassmannian ∧ IsGrassmannian (w.symm : FinPermutation n)

/-- Inversions, represented by ordered pairs of positions. -/
def inversionSet (w : FinPermutation n) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun p ↦ p.1 < p.2 ∧ w p.2 < w p.1

/-- Coxeter length in type `A`, defined as the number of inversions. -/
def length (w : FinPermutation n) : ℕ :=
  w.inversionSet.card

@[simp]
theorem mem_inversionSet_iff (w : FinPermutation n) (i j : Fin n) :
    (i, j) ∈ w.inversionSet ↔ i < j ∧ w j < w i := by
  simp [inversionSet]

end FinPermutation

end Schubert
