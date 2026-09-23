import Schubert.RS.Representation.FlagFinite
import Schubert.RS.PresentationCharacter
import Mathlib.Data.Fin.Tuple.Sort

namespace Schubert.RS.Representation
noncomputable section
open scoped BigOperators

/-- Canonical descending sort, with original-index order resolving ties. -/
def compositionPermutation {n : ℕ} (u : Composition n) : Equiv.Perm (Fin n) :=
  Tuple.sort (α := OrderDual ℕ) u

def dominantComposition {n : ℕ} (u : Composition n) : Composition n :=
  fun i => u (compositionPermutation u i)

theorem dominantComposition_antitone {n : ℕ} (u : Composition n) :
    Antitone (dominantComposition u) := by
  intro i j hij
  exact Tuple.monotone_sort (α := OrderDual ℕ) (fun i => u i) hij

theorem compositionPermutation_ties {n : ℕ} (u : Composition n) (i j : Fin n)
    (hij : i < j) (he : dominantComposition u i = dominantComposition u j) :
    compositionPermutation u i < compositionPermutation u j :=
  ((Tuple.eq_sort_iff (α := OrderDual ℕ)).mp (rfl : compositionPermutation u = Tuple.sort (α := OrderDual ℕ) u)).2 i j hij he

/-- Inverse of suffix sums on antitone weights. Recursion includes rank zero;
for a nonempty tuple the first column multiplicity is the first entry minus
the total number of columns belonging to the remaining rows. -/
def columnsOfWeight : {n : ℕ} → Composition n → ColumnShape n
  | 0, _ => Fin.elim0
  | n+1, v =>
    let tail := columnsOfWeight (fun i : Fin n => v i.succ)
    Fin.cons (v 0 - ∑ i, tail i) tail

theorem shapeWeight_cons_zero {n : ℕ} (a : ℕ) (m : ColumnShape n) :
    shapeWeight (Fin.cons a m) 0 = a + ∑ i, m i := by
  simp [shapeWeight, Fin.sum_univ_succ]

theorem shapeWeight_cons_succ {n : ℕ} (a : ℕ) (m : ColumnShape n) (i : Fin n) :
    shapeWeight (Fin.cons a m) i.succ = shapeWeight m i := by
  simp [shapeWeight, Fin.sum_univ_succ]

theorem shapeWeight_columnsOfWeight {n : ℕ} (v : Composition n) (hv : Antitone v) :
    shapeWeight (columnsOfWeight v) = v := by
  induction n with
  | zero => exact Subsingleton.elim _ _
  | succ n ih =>
    let tail : Composition n := fun i => v i.succ
    have ht : Antitone tail := fun i j hij => hv (Fin.succ_le_succ_iff.mpr hij)
    have he := ih tail ht
    have hle : ∑ i, columnsOfWeight tail i ≤ v 0 := by
      cases n with
      | zero => simp
      | succ n =>
        have hh := congrFun he 0
        simp only [shapeWeight, Fin.zero_le, if_true] at hh
        rw [hh]
        exact hv (Fin.zero_le _)
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change shapeWeight (Fin.cons (v 0 - ∑ i, columnsOfWeight tail i) (columnsOfWeight tail)) 0 = v 0
      rw [shapeWeight_cons_zero, Nat.sub_add_cancel hle]
    · change shapeWeight (Fin.cons (v 0 - ∑ i, columnsOfWeight tail i) (columnsOfWeight tail)) j.succ = v j.succ
      rw [shapeWeight_cons_succ, he]

def compositionShape {n : ℕ} (u : Composition n) : ColumnShape n :=
  columnsOfWeight (dominantComposition u)

theorem compositionShape_weight {n : ℕ} (u : Composition n) :
    shapeWeight (compositionShape u) = dominantComposition u :=
  shapeWeight_columnsOfWeight _ (dominantComposition_antitone u)

theorem composition_extremalWeight {n : ℕ} (u : Composition n) :
    extremalWeight (compositionShape u) (compositionPermutation u) = u := by
  funext i
  simp [extremalWeight, compositionShape_weight, dominantComposition]

/-- Actual concrete cyclic module, indexed by every weak composition.
Its identification with the irreducible highest-weight Demazure construction
remains a separate theorem, not a premise embedded in this definition. -/
abbrev compositionFlag {n : ℕ} (u : Composition n) :=
  flagDemazure (compositionShape u) (compositionPermutation u)

def compositionFlagTorus {n : ℕ} (u : Composition n) :
    DiagonalTorus n →* Module.End ℂ (compositionFlag u) :=
  flagTorus (compositionShape u) (compositionPermutation u)

def compositionFlagGenerator {n : ℕ} (u : Composition n) : compositionFlag u :=
  flagGenerator (compositionShape u) (compositionPermutation u)

theorem compositionFlagGenerator_weight {n : ℕ} (u : Composition n) (t : DiagonalTorus n) :
    compositionFlagTorus u t (compositionFlagGenerator u) =
      integerWeightScalar (fun i => (u i : ℤ)) t • compositionFlagGenerator u := by
  have h := flagGenerator_weight (compositionShape u) (compositionPermutation u) t
  rw [composition_extremalWeight] at h
  exact h

theorem compositionFlagGenerator_ne_zero {n : ℕ} (u : Composition n) :
    compositionFlagGenerator u ≠ 0 := flagGenerator_ne_zero _ _

/-- The Joseph-Polo presentation property specialized to the composition flag module. -/
def CompositionFlagJosephPolo {n : ℕ} (u : Composition n) : Prop :=
  HasJosephPoloPresentation u (compositionFlagTorus u) (compositionFlagGenerator u)

/-- The Demazure character property specialized to the composition flag module. -/
def CompositionFlagDemazureCharacter {n : ℕ} (u : Composition n) : Prop :=
  HasDemazureCharacter u (compositionFlagTorus u)



theorem compositionPermutation_of_antitone {n : ℕ} (u : Composition n) (hu : Antitone u) :
    compositionPermutation u = Equiv.refl _ := by
  apply (Tuple.sort_eq_refl_iff_monotone (α := OrderDual ℕ)).mpr
  exact hu

theorem dominantComposition_unique {n : ℕ} (u : Composition n) (w : Equiv.Perm (Fin n))
    (hw : Antitone (u ∘ w)) : u ∘ w = dominantComposition u :=
  Tuple.unique_antitone hw (dominantComposition_antitone u)

theorem columnsOfWeight_zero (n : ℕ) : columnsOfWeight (0 : Composition n) = 0 := by
  induction n with
  | zero => exact Subsingleton.elim _ _
  | succ n ih =>
    change (Fin.cons (0 - ∑ i, columnsOfWeight (0 : Composition n) i) (columnsOfWeight (0 : Composition n)) : Composition (n+1)) = 0
    rw [ih]
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem compositionPermutation_zero (n : ℕ) :
    compositionPermutation (0 : Composition n) = Equiv.refl _ :=
  compositionPermutation_of_antitone _ (fun _ _ _ => le_rfl)

theorem compositionShape_zero (n : ℕ) : compositionShape (0 : Composition n) = 0 := by
  exact columnsOfWeight_zero n

theorem compositionPermutation_rank_zero (u : Composition 0) :
    compositionPermutation u = Equiv.refl _ := Subsingleton.elim _ _

theorem compositionPermutation_rank_one (u : Composition 1) :
    compositionPermutation u = Equiv.refl _ := Subsingleton.elim _ _

theorem compositionShape_rank_one (u : Composition 1) : compositionShape u = u := by
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  simp [compositionShape, columnsOfWeight, dominantComposition, compositionPermutation_rank_one]

theorem compositionFlag_seed_zero (n : ℕ) :
    extremalFlag (compositionShape (0 : Composition n)) (compositionPermutation 0) = 1 := by
  rw [compositionShape_zero]
  simp [extremalFlag, highestFlag, rowRename]

theorem compositionFlag_degree {n : ℕ} (u : Composition n) :
    flagDegree (compositionShape u) = ∑ i, u i := by
  rw [← extremalWeight_sum (compositionShape u) (compositionPermutation u), composition_extremalWeight]

end
end Schubert.RS.Representation


