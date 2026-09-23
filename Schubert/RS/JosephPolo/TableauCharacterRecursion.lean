import Schubert.RS.JosephPolo.ColumnStringCharacters
import Schubert.RS.JosephPolo.StringSelection

namespace Schubert.RS.Representation
noncomputable section
open FinPermutation
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem flagString_character_recursion {n d L : ℕ} {h : Fin d → Fin n}
    {i : AdjacentPosition n} {T : Fin (L+1) → (j : Fin d) → FlagMinorRowSet (h j)}
    (hT : IsFlagDefiningString h i L T)
    (hW : IsColumnWeightString i L (fun k => flagTupleWeight h (T k)))
    (w : FinPermutation n) (hw : w.symm i.right < w.symm i.left) :
    isobaric i (∑ k, if HasFlagDefiningChain h (T k) (w.leftAdjacentSwap i)
      then compositionMonomial (flagTupleWeight h (T k)) else 0) =
    ∑ k, if HasFlagDefiningChain h (T k) w
      then compositionMonomial (flagTupleWeight h (T k)) else 0 := by
  have htarget := hT.descent_iff_head w hw
  rcases hT.trichotomy (w.leftAdjacentSwap i) with he | hh | hf
  · have h0 := he 0
    simp only [he,htarget,h0,ite_false,Finset.sum_const_zero,isobaric_zero]
  · have h0 := (hh 0).mpr rfl
    simp only [hh,htarget,h0,ite_true]
    simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    exact hW.character.symm
  · have h0 := hf 0
    simp only [hf,htarget,h0,ite_true]
    exact hW.character_fixed

/-- The generating polynomial of exactly the tuples with a defining chain.
It has no representation-theoretic character assertion in its definition. -/
def flagTableauCharacter {n d : ℕ} (h : Fin d → Fin n) (w : FinPermutation n) :
    RS.Polynomial n :=
  ∑ T : (j : Fin d) → FlagMinorRowSet (h j),
    if HasFlagDefiningChain h T w then compositionMonomial (flagTupleWeight h T) else 0

theorem flagTableauCharacter_eq_sum_strings {n d : ℕ} (h : Fin d → Fin n)
    (i : AdjacentPosition n) (w : FinPermutation n) :
    let S := flagStringPartition i d h
    flagTableauCharacter h w = ∑ a : S.Index, ∑ k : Fin (S.length a+1),
      if HasFlagDefiningChain h (S.position ⟨a,k⟩) w
        then compositionMonomial (flagTupleWeight h (S.position ⟨a,k⟩)) else 0 := by
  let S := flagStringPartition i d h
  let f := fun T : (j : Fin d) → FlagMinorRowSet (h j) =>
    if HasFlagDefiningChain h T w then compositionMonomial (flagTupleWeight h T) else 0
  change (∑ T, f T) = ∑ a : S.Index, ∑ k : Fin (S.length a+1), f (S.position ⟨a,k⟩)
  exact ((Fintype.sum_equiv S.position (fun x => f (S.position x)) f (fun _ => rfl)).symm).trans
    (Fintype.sum_sigma (fun x => f (S.position x)))

theorem isobaric_finite_sum {n : ℕ} (i : AdjacentPosition n)
    {J : Type*} [Fintype J] (f : J → RS.Polynomial n) :
    isobaric i (∑ j, f j) = ∑ j, isobaric i (f j) := by
  let p : RS.Polynomial n →+ RS.Polynomial n :=
    { toFun := isobaric i, map_zero' := isobaric_zero i, map_add' := isobaric_add i }
  exact map_sum p f Finset.univ

/-- The combinatorial isobaric recursion, valid for every ordered column
sequence and every inverse descent of its ambient Bruhat bound. -/
theorem flagTableauCharacter_recursion {n d : ℕ} (h : Fin d → Fin n)
    (i : AdjacentPosition n) (w : FinPermutation n)
    (hw : w.symm i.right < w.symm i.left) :
    isobaric i (flagTableauCharacter h (w.leftAdjacentSwap i)) =
      flagTableauCharacter h w := by
  rw [flagTableauCharacter_eq_sum_strings h i (w.leftAdjacentSwap i),
    flagTableauCharacter_eq_sum_strings h i w,isobaric_finite_sum]
  apply Finset.sum_congr rfl
  intro a _
  exact flagString_character_recursion (flagStringPartition_good i d h a)
    (flagStringPartition_weight i d h a) w hw

end
end Schubert.RS.Representation
