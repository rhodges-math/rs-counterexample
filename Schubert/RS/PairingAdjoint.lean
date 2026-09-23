import Schubert.RS.Pairing
import Schubert.RS.KeyAction

/-! Adjoint operators for the exact key–atom pairing used in the paper. -/

namespace Schubert.RS

open FinPermutation
noncomputable section
variable {n : ℕ}

def mirrorAdjacent (i : AdjacentPosition n) : AdjacentPosition n where
  left := i.right.rev
  hasRight := by
    have h := i.hasRight
    simp only [Fin.rev, AdjacentPosition.right_val]
    omega

@[simp] theorem mirrorAdjacent_left (i : AdjacentPosition n) :
    (mirrorAdjacent i).left = i.right.rev := rfl

@[simp] theorem mirrorAdjacent_right (i : AdjacentPosition n) :
    (mirrorAdjacent i).right = i.left.rev := by
  apply Fin.ext
  have h := i.hasRight
  simp only [AdjacentPosition.right_val, mirrorAdjacent_left, Fin.rev,
    AdjacentPosition.right_val]
  omega

@[simp] theorem mirrorAdjacent_involutive (i : AdjacentPosition n) :
    mirrorAdjacent (mirrorAdjacent i) = i := by
  apply AdjacentPosition.ext
  simp

theorem adjacentTransposition_mirror (i : AdjacentPosition n) (k : Fin n) :
    adjacentTransposition (mirrorAdjacent i) k.rev = (adjacentTransposition i k).rev := by
  by_cases hl : k = i.left <;> by_cases hr : k = i.right <;>
    simp_all [adjacentTransposition, Equiv.swap_apply_def]

theorem reverseNegWeight_swap (i : AdjacentPosition n) (a : Weight n) :
    reverseNegWeight (weightSwap (mirrorAdjacent i) a) =
      weightSwap i (reverseNegWeight a) := by
  ext k
  change -a (adjacentTransposition (mirrorAdjacent i) k.rev) =
    -a (adjacentTransposition i k).rev
  rw [adjacentTransposition_mirror]

theorem reverseNeg_laurentSwap (i : AdjacentPosition n) (p : Laurent n) :
    reverseNeg (laurentSwap (mirrorAdjacent i) p) = laurentSwap i (reverseNeg p) := by
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => simp [hp, hq]
  | single a z => simp [reverseNegWeight_swap]

theorem reverseNeg_isobaric_identity (i : AdjacentPosition n) (g : Polynomial n) :
    (1 - AddMonoidAlgebra.single (positiveRoot i.left i.right) 1) *
      reverseNeg (toLaurent (isobaric (mirrorAdjacent i) g)) =
      laurentSwap i (reverseNeg (toLaurent g)) -
        AddMonoidAlgebra.single (positiveRoot i.left i.right) 1 *
          reverseNeg (toLaurent g) := by
  have h := congrArg reverseNeg (isobaric_laurent_identity (mirrorAdjacent i) g)
  simpa only [map_mul, map_sub, map_one, reverseNeg_single,
    reverseNegWeight_positiveRoot, mirrorAdjacent_left, mirrorAdjacent_right,
    Fin.rev_rev, reverseNeg_laurentSwap] using h

/-- The precise reflected-index adjointness in the manuscript's convention. -/
theorem keyAtomPairing_isobaric (i : AdjacentPosition n) (f g : Polynomial n) :
    keyAtomPairing (isobaric i f) g =
      keyAtomPairing f (isobaric (mirrorAdjacent i) g) := by
  exact constantTerm_isobaric_adjoint_weyl i _ _ _ _
    (isobaric_laurent_identity i f) (reverseNeg_isobaric_identity i g)

theorem keyAtomPairing_sub_left (f g h : Polynomial n) :
    keyAtomPairing (f - g) h = keyAtomPairing f h - keyAtomPairing g h := by
  simp [keyAtomPairing, sub_mul]

theorem keyAtomPairing_sub_right (f g h : Polynomial n) :
    keyAtomPairing f (g - h) = keyAtomPairing f g - keyAtomPairing f h := by
  simp [keyAtomPairing, mul_sub, sub_mul]

theorem keyAtomPairing_atomOperator (i : AdjacentPosition n) (f g : Polynomial n) :
    keyAtomPairing (atomOperator i f) g =
      keyAtomPairing f (atomOperator (mirrorAdjacent i) g) := by
  rw [atomOperator, atomOperator, keyAtomPairing_sub_left, keyAtomPairing_sub_right,
    keyAtomPairing_isobaric]

/-- The exact sorting step used in key–atom orthogonality. All operators
here are the already constructed polynomial operators, with no pairing
recursion assumed as an input. -/
theorem keyAtomPairing_key_atom_ascent (a u : Composition n) (i : AdjacentPosition n)
    (hu : u i.left < u i.right) :
    keyAtomPairing (key a) (atom u) =
      if a (mirrorAdjacent i).right < a (mirrorAdjacent i).left then
        keyAtomPairing (key (swapComposition a (mirrorAdjacent i)))
          (atom (swapComposition u i)) -
        keyAtomPairing (key a) (atom (swapComposition u i)) else 0 := by
  rw [atom_any_ascent u i hu]
  rw [← mirrorAdjacent_involutive i, ← keyAtomPairing_atomOperator]
  simp only [mirrorAdjacent_involutive]
  rw [atomOperator, keyAtomPairing_sub_left, isobaric_key]
  split_ifs <;> simp

end
end Schubert.RS
