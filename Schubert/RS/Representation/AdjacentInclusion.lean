import Schubert.RS.Representation.ExtremalStrings

namespace Schubert.RS.Representation
noncomputable section
open scoped BigOperators
open FinPermutation

theorem stringDegree_add_shapeWeight {n : ℕ} (m : ColumnShape n) (a b : Fin n) (hba : b<a) :
    stringDegree m a b + shapeWeight m a = shapeWeight m b := by
  unfold stringDegree shapeWeight
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases ha : a ≤ k
  · have hb : b ≤ k := le_trans hba.le ha
    simp [activeMinor, ha, hb, not_lt.mpr ha]
  · by_cases hb : b ≤ k <;> simp [activeMinor, ha, hb, lt_of_not_ge ha]

theorem stringDegree_eq_weight_sub {n : ℕ} (m : ColumnShape n) (a b : Fin n) (hba : b<a) :
    stringDegree m a b = shapeWeight m b - shapeWeight m a := by
  have h := stringDegree_add_shapeWeight m a b hba
  omega

theorem extremalFlag_swap_iter_weight {n : ℕ} (m : ColumnShape n) (w : Equiv.Perm (Fin n))
    (a b : Fin n) (hu : extremalWeight m w a < extremalWeight m w b) :
    ∃ c : ℂ, c ≠ 0 ∧ rowRename (Equiv.swap a b) (extremalFlag m w) =
      c • derivationIter (matrixUnitDerivation a b)
        (extremalWeight m w b - extremalWeight m w a) (extremalFlag m w) := by
  have hba : w.symm b < w.symm a := by
    by_contra h
    exact (not_lt_of_ge (shapeWeight_antitone m (le_of_not_gt h))) hu
  simpa only [stringDegree_eq_weight_sub m _ _ hba, extremalWeight] using extremalFlag_swap_iter m w a b hu

theorem compositionShape_perm {n : ℕ} (u : Composition n) (v : Equiv.Perm (Fin n)) :
    compositionShape (u ∘ v) = compositionShape u := by
  unfold compositionShape
  congr 1
  exact Tuple.comp_perm_comp_sort_eq_comp_sort (α := OrderDual ℕ)

theorem extremalWeight_swap_mul {n : ℕ} (m : ColumnShape n) (w : Equiv.Perm (Fin n))
    (a b : Fin n) : extremalWeight m (Equiv.swap a b * w) = extremalWeight m w ∘ Equiv.swap a b := by
  funext i
  rfl

theorem compositionFlag_swap_eq {n : ℕ} (u : Composition n) (a b : Fin n) :
    compositionFlag (u ∘ Equiv.swap a b) =
      flagDemazure (compositionShape u) (Equiv.swap a b * compositionPermutation u) := by
  have hshape := compositionShape_perm u (Equiv.swap a b)
  have hw : extremalWeight (compositionShape u) (compositionPermutation (u ∘ Equiv.swap a b)) =
      extremalWeight (compositionShape u) (Equiv.swap a b * compositionPermutation u) := by
    rw [extremalWeight_swap_mul, composition_extremalWeight]
    rw [← hshape]
    exact composition_extremalWeight _
  change flagDemazure (compositionShape (u ∘ Equiv.swap a b)) (compositionPermutation (u ∘ Equiv.swap a b)) = _
  rw [hshape]
  exact flagDemazure_eq_of_weight_eq _ _ _ hw

theorem compositionFlag_swap_le {n : ℕ} (u : Composition n) (r : PositiveRoot n)
    (hu : u r.val.1 < u r.val.2) :
    compositionFlag (u ∘ Equiv.swap r.val.1 r.val.2) ≤ compositionFlag u := by
  rw [compositionFlag_swap_eq]
  apply upperCyclic_le_of_seed_mem
  change rowRename (Equiv.swap r.val.1 r.val.2 * compositionPermutation u) (highestFlag (compositionShape u)) ∈ _
  rw [rowRename_mul]
  apply extremalFlag_swap_mem
  rwa [composition_extremalWeight]

theorem compositionFlag_adjacent_le {n : ℕ} (u : Composition n) (i : AdjacentPosition n)
    (hu : u i.left < u i.right) : compositionFlag (swapComposition u i) ≤ compositionFlag u :=
  compositionFlag_swap_le u ⟨(i.left,i.right), i.left_lt_right⟩ hu

/-- The actual distinguished neighboring seed belongs to the original cyclic
module; no JP, PBW, character, or saturation statement is used. -/
theorem adjacentFlagGenerator_mem {n : ℕ} (u : Composition n) (i : AdjacentPosition n)
    (hu : u i.left < u i.right) :
    (compositionFlagGenerator (swapComposition u i)).val ∈ compositionFlag u :=
  compositionFlag_adjacent_le u i hu (compositionFlagGenerator (swapComposition u i)).property

end
end Schubert.RS.Representation
