import Schubert.TypeA.Permutations.Bruhat

/-! # Rothe diagrams and southeast corners -/

namespace Schubert

namespace FinPermutation

variable {n : ℕ}

/-- A cell `(i,j)` lies in the Rothe diagram when it is left of the permutation
matrix entry in row `i` and above the entry in column `j`. -/
def IsRotheCell (w : FinPermutation n) (i j : Fin n) : Prop :=
  j < w i ∧ i < w.symm j

/-- Natural-number version, useful for testing the southern and eastern
neighbors at the boundary of the diagram. -/
def IsRotheCellNat (w : FinPermutation n) (i j : ℕ) : Prop :=
  ∃ hi : i < n, ∃ hj : j < n,
    w.IsRotheCell ⟨i, hi⟩ ⟨j, hj⟩

/-- A southeast corner of the Rothe diagram. -/
def IsEssentialCorner (w : FinPermutation n) (i j : Fin n) : Prop :=
  w.IsRotheCell i j ∧
    ¬ w.IsRotheCellNat (i.1 + 1) j.1 ∧
    ¬ w.IsRotheCellNat i.1 (j.1 + 1)

/-- The essential diagram corners of a permutation. -/
def diagramEssentialSet (w : FinPermutation n) : Set (Fin n × Fin n) :=
  {p | w.IsEssentialCorner p.1 p.2}

theorem isRotheCellNat_of_isRotheCell (w : FinPermutation n) {i j : Fin n}
    (h : w.IsRotheCell i j) : w.IsRotheCellNat i.1 j.1 :=
  ⟨i.2, j.2, h⟩

end FinPermutation

end Schubert
