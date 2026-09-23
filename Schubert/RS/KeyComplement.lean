import Schubert.RS.PairingAdjoint
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors

/-! The rectangle-complement identity in the paper's coefficient-duality proof. -/

namespace Schubert.RS

open FinPermutation
noncomputable section
variable {n : ℕ}

def rectangleMonomial (w : ℕ) : Laurent n :=
  AddMonoidAlgebra.single (fun _ => (w : ℤ)) 1

def reverseComplement (w : ℕ) (a : Composition n) : Composition n :=
  fun j => w - a j.rev

@[simp] theorem laurentSwap_rectangleMonomial (i : AdjacentPosition n) (w : ℕ) :
    laurentSwap i (rectangleMonomial w) = rectangleMonomial w := by
  rw [rectangleMonomial, laurentSwap_single]
  rfl

theorem positiveRoot_ne_zero (i j : Fin n) (h : i ≠ j) : positiveRoot i j ≠ 0 := by
  intro he
  have hz := congrFun he i
  simp [positiveRoot, Pi.single_apply, h] at hz

theorem simpleWeyl_ne_zero (i : AdjacentPosition n) :
    (1 : Laurent n) - AddMonoidAlgebra.single (positiveRoot i.left i.right) 1 ≠ 0 := by
  intro h
  have hz := congrArg (fun p : Laurent n => p.coeff 0) h
  simp [positiveRoot_ne_zero i.left i.right i.left_ne_right] at hz

theorem reverseComplement_swap (w : ℕ) (a : Composition n) (i : AdjacentPosition n) :
    swapComposition (reverseComplement w a) (mirrorAdjacent i) =
      reverseComplement w (swapComposition a i) := by
  funext k
  have h := adjacentTransposition_mirror (mirrorAdjacent i) k
  simp only [mirrorAdjacent_involutive] at h
  exact congrArg (fun j => w - a j) h.symm

theorem reverseComplement_antitone (w : ℕ) (a : Composition n) (ha : Antitone a) :
    Antitone (reverseComplement w a) := by
  intro i j hij
  exact Nat.sub_le_sub_left (ha (Fin.rev_le_rev.mpr hij)) w

theorem compositionMonomial_toLaurent (a : Composition n) :
    toLaurent (compositionMonomial a) =
      AddMonoidAlgebra.single (fun i => (a i : ℤ)) 1 := by
  rw [compositionMonomial, toLaurent_monomial]
  rfl

theorem reverseComplement_monomial (w : ℕ) (a : Composition n) (ha : ∀ i, a i ≤ w) :
    toLaurent (compositionMonomial (reverseComplement w a)) =
      rectangleMonomial w * reverseNeg (toLaurent (compositionMonomial a)) := by
  rw [compositionMonomial_toLaurent, compositionMonomial_toLaurent,
    reverseNeg_single, rectangleMonomial, AddMonoidAlgebra.single_mul_single]
  simp only [mul_one]
  apply congrArg (fun v : Weight n => AddMonoidAlgebra.single v (1 : ℤ))
  ext i
  change ((w - a i.rev : ℕ) : ℤ) = (w : ℤ) + -(a i.rev : ℤ)
  rw [Nat.cast_sub (ha i.rev)]
  ring

/-- The rectangle shift commutes with the reflected isobaric operation. -/
theorem reverseComplement_isobaric (w : ℕ) (i : AdjacentPosition n)
    (f g : Polynomial n)
    (h : toLaurent f = rectangleMonomial w * reverseNeg (toLaurent g)) :
    toLaurent (isobaric (mirrorAdjacent i) f) =
      rectangleMonomial w * reverseNeg (toLaurent (isobaric i g)) := by
  apply mul_left_cancel₀ (simpleWeyl_ne_zero (mirrorAdjacent i))
  have hc := reverseNeg_isobaric_identity (mirrorAdjacent i) g
  simp only [mirrorAdjacent_involutive] at hc
  rw [isobaric_laurent_identity, h, map_mul, laurentSwap_rectangleMonomial]
  calc
    _ = rectangleMonomial w *
      (laurentSwap (mirrorAdjacent i) (reverseNeg (toLaurent g)) -
        AddMonoidAlgebra.single
          (positiveRoot (mirrorAdjacent i).left (mirrorAdjacent i).right) 1 *
            reverseNeg (toLaurent g)) := by ring
    _ = _ := by rw [← hc]; ring

/-- This is the key complement identity needed to convert constant-term
orthogonality to the coefficient functional in the manuscript. -/
theorem key_reverseComplement (w : ℕ) (a : Composition n) (ha : ∀ i, a i ≤ w) :
    toLaurent (key (reverseComplement w a)) =
      rectangleMonomial w * reverseNeg (toLaurent (key a)) := by
  induction a using (measure sortingMeasure).wf.induction with
  | h a ih =>
    by_cases hs : (ascentSet a).Nonempty
    · let i := firstAscent a hs
      have hi : a i.left < a i.right := firstAscent_lt a hs
      have hci : reverseComplement w a (mirrorAdjacent i).left <
          reverseComplement w a (mirrorAdjacent i).right := by
        simp only [reverseComplement, mirrorAdjacent_left, mirrorAdjacent_right, Fin.rev_rev]
        have hla := ha i.left
        have hra := ha i.right
        omega
      have hb : ∀ j, swapComposition a i j ≤ w := fun j => ha (adjacentTransposition i j)
      rw [key_any_ascent _ (mirrorAdjacent i) hci, reverseComplement_swap, key_ascent a hs]
      exact reverseComplement_isobaric w i _ _
        (ih _ (sortingMeasure_swap_lt a i hi) hb)
    · have hd := antitone_of_no_ascent a hs
      rw [key_of_antitone _ (reverseComplement_antitone w a hd), key_of_no_ascent a hs]
      exact reverseComplement_monomial w a ha

end
end Schubert.RS
