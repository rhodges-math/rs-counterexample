import Schubert.TypeA.Permutations.AdjacentTranspositions
import Schubert.TypeA.Permutations.EssentialBigrassmannian
import Mathlib.Data.Fin.Rev

/-!
# Inversion length and adjacent swaps

An adjacent descent is removed by a right adjacent swap.  We prove directly
that this decreases inversion number by exactly one, using the involution on
ordered pairs induced by the adjacent transposition.
-/

namespace Schubert

namespace FinPermutation

variable {n : ℕ}

/-- An adjacent transposition preserves the order of an increasing pair
unless that pair is exactly the exchanged adjacent pair. -/
theorem adjacentTransposition_lt_of_lt_of_ne_pair
    (a : AdjacentPosition n) (x y : Fin n)
    (hxy : x < y) (hne : (x, y) ≠ (a.left, a.right)) :
    adjacentTransposition a x < adjacentTransposition a y := by
  by_cases hxl : x = a.left
  · subst x
    by_cases hyr : y = a.right
    · exact (hne (Prod.ext rfl hyr)).elim
    · have hry : a.right < y := by
        change a.left.1 + 1 < y.1
        change a.left.1 < y.1 at hxy
        have hneval : y.1 ≠ a.left.1 + 1 := by
          intro h
          exact hyr (Fin.ext h)
        omega
      have hyl : y ≠ a.left := hxy.ne'
      rw [adjacentTransposition, Equiv.swap_apply_left,
        Equiv.swap_apply_of_ne_of_ne hyl hyr]
      exact hry
  · by_cases hxr : x = a.right
    · subst x
      have hyl : y ≠ a.left := (a.left_lt_right.trans hxy).ne'
      have hyr : y ≠ a.right := hxy.ne'
      rw [adjacentTransposition, Equiv.swap_apply_right,
        Equiv.swap_apply_of_ne_of_ne hyl hyr]
      exact a.left_lt_right.trans hxy
    · by_cases hyl : y = a.left
      · subst y
        have hxl' : x ≠ a.left := hxy.ne
        have hxr' : x ≠ a.right := by
          intro hx
          subst x
          exact (not_lt_of_ge a.left_lt_right.le) hxy
        rw [adjacentTransposition,
          Equiv.swap_apply_of_ne_of_ne hxl' hxr',
          Equiv.swap_apply_left]
        exact hxy.trans a.left_lt_right
      · by_cases hyr : y = a.right
        · subst y
          have hxlval : x < a.left := by
            change x.1 < a.left.1
            change x.1 < a.left.1 + 1 at hxy
            have hneval : x.1 ≠ a.left.1 := by
              intro h
              exact hxl (Fin.ext h)
            omega
          rw [adjacentTransposition,
            Equiv.swap_apply_of_ne_of_ne hxl hxr,
            Equiv.swap_apply_right]
          exact hxlval
        · rw [adjacentTransposition,
            Equiv.swap_apply_of_ne_of_ne hxl hxr,
            Equiv.swap_apply_of_ne_of_ne hyl hyr]
          exact hxy

/-- Simultaneously exchange both entries of an ordered pair. -/
def adjacentPairSwap (a : AdjacentPosition n) :
    Fin n × Fin n ≃ Fin n × Fin n :=
  (adjacentTransposition a).prodCongr (adjacentTransposition a)

@[simp] theorem adjacentPairSwap_apply
    (a : AdjacentPosition n) (p : Fin n × Fin n) :
    adjacentPairSwap a p =
      (adjacentTransposition a p.1, adjacentTransposition a p.2) :=
  rfl

@[simp] theorem adjacentPairSwap_involutive
    (a : AdjacentPosition n) (p : Fin n × Fin n) :
    adjacentPairSwap a (adjacentPairSwap a p) = p := by
  rcases p with ⟨x, y⟩
  simp [adjacentPairSwap, adjacentTransposition]

@[simp] theorem adjacentPairSwap_adjacentPair
    (a : AdjacentPosition n) :
    adjacentPairSwap a (a.left, a.right) = (a.right, a.left) := by
  simp [adjacentPairSwap, adjacentTransposition]

private theorem swapped_inversion_not_adjacentPair
    (w : FinPermutation n) (a : AdjacentPosition n)
    (hdescent : w.HasDescent a.left) {p : Fin n × Fin n}
    (hp : p ∈ (w.rightAdjacentSwap a).inversionSet) :
    p ≠ (a.left, a.right) := by
  intro hpair
  rcases p with ⟨x, y⟩
  simp only [Prod.mk.injEq] at hpair
  rcases hpair with ⟨rfl, rfl⟩
  rw [mem_inversionSet_iff] at hp
  have hdesc := (hasDescent_left_iff w a).mp hdescent
  simp only [rightAdjacentSwap_apply_left,
    rightAdjacentSwap_apply_right] at hp
  exact (not_lt_of_ge hdesc.le) hp.2

/-- The pair involution sends every inversion after removing an adjacent
descent to an old inversion different from the removed adjacent pair. -/
theorem adjacentPairSwap_mem_erase_inversionSet
    (w : FinPermutation n) (a : AdjacentPosition n)
    (hdescent : w.HasDescent a.left) {p : Fin n × Fin n}
    (hp : p ∈ (w.rightAdjacentSwap a).inversionSet) :
    adjacentPairSwap a p ∈ w.inversionSet.erase (a.left, a.right) := by
  rw [Finset.mem_erase]
  have hpdata := (mem_inversionSet_iff (w.rightAdjacentSwap a) p.1 p.2).mp hp
  have hpne := swapped_inversion_not_adjacentPair w a hdescent hp
  constructor
  · intro himage
    have := congrArg (adjacentPairSwap a) himage
    rw [adjacentPairSwap_involutive,
      adjacentPairSwap_adjacentPair] at this
    have horder : p.1 < p.2 := hpdata.1
    rw [this] at horder
    exact (not_lt_of_ge a.left_lt_right.le) horder
  · rw [mem_inversionSet_iff]
    refine ⟨adjacentTransposition_lt_of_lt_of_ne_pair
      a p.1 p.2 hpdata.1 hpne, ?_⟩
    simpa [rightAdjacentSwap, adjacentPairSwap_apply] using hpdata.2

/-- Conversely, every old inversion except the adjacent descent pulls back
to an inversion after the swap. -/
theorem adjacentPairSwap_mem_swapped_inversionSet
    (w : FinPermutation n) (a : AdjacentPosition n)
    {p : Fin n × Fin n}
    (hp : p ∈ w.inversionSet.erase (a.left, a.right)) :
    adjacentPairSwap a p ∈ (w.rightAdjacentSwap a).inversionSet := by
  rw [Finset.mem_erase] at hp
  rw [mem_inversionSet_iff]
  refine ⟨adjacentTransposition_lt_of_lt_of_ne_pair a p.1 p.2
    ((mem_inversionSet_iff w p.1 p.2).mp hp.2).1 hp.1, ?_⟩
  have hvalue := ((mem_inversionSet_iff w p.1 p.2).mp hp.2).2
  simpa [rightAdjacentSwap, adjacentPairSwap_apply,
    adjacentTransposition] using hvalue

/-- Removing an adjacent descent removes exactly one inversion. -/
theorem inversionSet_card_rightAdjacentSwap_of_descent
    (w : FinPermutation n) (a : AdjacentPosition n)
    (hdescent : w.HasDescent a.left) :
    (w.rightAdjacentSwap a).inversionSet.card =
      w.inversionSet.card - 1 := by
  classical
  calc
    (w.rightAdjacentSwap a).inversionSet.card =
        (w.inversionSet.erase (a.left, a.right)).card := by
      apply Finset.card_bij
        (fun p _ => adjacentPairSwap a p)
      · intro p hp
        exact adjacentPairSwap_mem_erase_inversionSet w a hdescent hp
      · intro p₁ hp₁ p₂ hp₂ heq
        exact (adjacentPairSwap a).injective heq
      · intro p hp
        refine ⟨adjacentPairSwap a p,
          adjacentPairSwap_mem_swapped_inversionSet w a hp, ?_⟩
        exact adjacentPairSwap_involutive a p
    _ = w.inversionSet.card - 1 := by
      apply Finset.card_erase_of_mem
      rw [mem_inversionSet_iff]
      exact ⟨a.left_lt_right,
        (hasDescent_left_iff w a).mp hdescent⟩

/-- Coxeter length drops by one at every adjacent right descent. -/
theorem length_rightAdjacentSwap_of_descent
    (w : FinPermutation n) (a : AdjacentPosition n)
    (hdescent : w.HasDescent a.left) :
    (w.rightAdjacentSwap a).length + 1 = w.length := by
  unfold length
  rw [inversionSet_card_rightAdjacentSwap_of_descent w a hdescent]
  have hpos : 0 < w.inversionSet.card := by
    have hmem : (a.left, a.right) ∈ w.inversionSet := by
      rw [mem_inversionSet_iff]
      exact ⟨a.left_lt_right,
        (hasDescent_left_iff w a).mp hdescent⟩
    exact Finset.card_pos.mpr ⟨_, hmem⟩
  omega

@[simp] theorem rightAdjacentSwap_involutive
    (w : FinPermutation n) (a : AdjacentPosition n) :
    (w.rightAdjacentSwap a).rightAdjacentSwap a = w := by
  ext x
  simp [rightAdjacentSwap, adjacentTransposition]

theorem swapped_hasDescent_of_ascent
    (w : FinPermutation n) (a : AdjacentPosition n)
    (hascent : w a.left < w a.right) :
    (w.rightAdjacentSwap a).HasDescent a.left := by
  rw [hasDescent_left_iff]
  simpa using hascent

/-- An adjacent ascent raises inversion length by exactly one. -/
theorem length_rightAdjacentSwap_of_ascent
    (w : FinPermutation n) (a : AdjacentPosition n)
    (hascent : w a.left < w a.right) :
    w.length + 1 = (w.rightAdjacentSwap a).length := by
  have hdrop := length_rightAdjacentSwap_of_descent
    (w.rightAdjacentSwap a) a
    (swapped_hasDescent_of_ascent w a hascent)
  simpa using hdrop

/-- At an adjacent pair, a permutation has either a descent or an ascent. -/
theorem descent_or_ascent
    (w : FinPermutation n) (a : AdjacentPosition n) :
    w.HasDescent a.left ∨ w a.left < w a.right := by
  rcases lt_or_gt_of_ne (w.injective.ne a.left_ne_right) with h | h
  · exact Or.inr h
  · exact Or.inl ((hasDescent_left_iff w a).mpr h)

/-- Apply a word of adjacent transpositions by successive right swaps. -/
def applyRightAdjacentWord
    (word : List (AdjacentPosition n)) (w : FinPermutation n) :
    FinPermutation n :=
  word.foldl rightAdjacentSwap w

@[simp] theorem applyRightAdjacentWord_nil (w : FinPermutation n) :
    applyRightAdjacentWord [] w = w :=
  rfl

@[simp] theorem applyRightAdjacentWord_cons
    (a : AdjacentPosition n) (word : List (AdjacentPosition n))
    (w : FinPermutation n) :
    applyRightAdjacentWord (a :: word) w =
      applyRightAdjacentWord word (w.rightAdjacentSwap a) :=
  rfl

theorem applyRightAdjacentWord_append
    (u v : List (AdjacentPosition n)) (w : FinPermutation n) :
    applyRightAdjacentWord (u ++ v) w =
      applyRightAdjacentWord v (applyRightAdjacentWord u w) := by
  simp [applyRightAdjacentWord, List.foldl_append]

/-- A word whose every adjacent swap lies strictly to the right of `k`
leaves the entry at position `k` fixed. -/
theorem applyRightAdjacentWord_apply_of_forall_lt_left
    (word : List (AdjacentPosition n)) (w : FinPermutation n) (k : Fin n)
    (hletters : ∀ a ∈ word, k < a.left) :
    applyRightAdjacentWord word w k = w k := by
  induction word generalizing w with
  | nil => rfl
  | cons a tail ih =>
      rw [applyRightAdjacentWord_cons, ih]
      · apply rightAdjacentSwap_apply_of_ne
        · exact (hletters a (by simp)).ne
        · exact (hletters a (by simp)).trans a.left_lt_right |>.ne
      · intro b hb
        exact hletters b (by simp [hb])

/-- In inverse-wire coordinates, swaps lying strictly to the right of `k`
leave the wire initially occupying `k` at `k`. -/
theorem applyRightAdjacentWord_symm_apply_apply_of_forall_lt_left
    (word : List (AdjacentPosition n)) (w : FinPermutation n) (k : Fin n)
    (hletters : ∀ a ∈ word, k < a.left) :
    (applyRightAdjacentWord word w).symm (w k) = k := by
  apply (applyRightAdjacentWord word w).injective
  rw [Equiv.apply_symm_apply,
    applyRightAdjacentWord_apply_of_forall_lt_left word w k hletters]

/-- No adjacent word can lower inversion length by more than its number of
letters. -/
theorem length_le_word_length_add_result
    (word : List (AdjacentPosition n)) (w : FinPermutation n) :
    w.length ≤ word.length + (applyRightAdjacentWord word w).length := by
  induction word generalizing w with
  | nil => simp
  | cons a word ih =>
      rw [applyRightAdjacentWord_cons, List.length_cons]
      have hrest := ih (w.rightAdjacentSwap a)
      rcases descent_or_ascent w a with hdescent | hascent
      · have hdrop := length_rightAdjacentSwap_of_descent w a hdescent
        omega
      · have hrise := length_rightAdjacentSwap_of_ascent w a hascent
        omega

/-- Every letter of a descending word is a descent at the stage where it is
applied. -/
def IsDescendingWord :
    FinPermutation n → List (AdjacentPosition n) → Prop
  | _, [] => True
  | w, a :: word =>
      w.HasDescent a.left ∧ IsDescendingWord (w.rightAdjacentSwap a) word

/-- A descending word lowers inversion length by exactly its number of
letters. -/
theorem length_applyRightAdjacentWord_of_isDescending
    (word : List (AdjacentPosition n)) (w : FinPermutation n)
    (h : IsDescendingWord w word) :
    word.length + (applyRightAdjacentWord word w).length = w.length := by
  induction word generalizing w with
  | nil => simp
  | cons a word ih =>
      rcases h with ⟨hdescent, hrest⟩
      change (word.length + 1) +
        (applyRightAdjacentWord word (w.rightAdjacentSwap a)).length =
          w.length
      have hi := ih (w.rightAdjacentSwap a) hrest
      have hdrop := length_rightAdjacentSwap_of_descent w a hdescent
      omega

/-- A word achieving the maximal possible length drop is necessarily
descending at every step. -/
theorem isDescendingWord_of_length_eq
    (word : List (AdjacentPosition n)) (w : FinPermutation n)
    (hlength : word.length + (applyRightAdjacentWord word w).length =
      w.length) :
    IsDescendingWord w word := by
  induction word generalizing w with
  | nil => trivial
  | cons a word ih =>
      rw [applyRightAdjacentWord_cons, List.length_cons] at hlength
      rcases descent_or_ascent w a with hdescent | hascent
      · refine ⟨hdescent, ih (w.rightAdjacentSwap a) ?_⟩
        have hdrop := length_rightAdjacentSwap_of_descent w a hdescent
        omega
      · have hrise := length_rightAdjacentSwap_of_ascent w a hascent
        have hbound := length_le_word_length_add_result word
          (w.rightAdjacentSwap a)
        omega

@[simp] theorem length_refl (n : ℕ) :
    length (Equiv.refl (Fin n) : FinPermutation n) = 0 := by
  unfold length
  apply Finset.card_eq_zero.mpr
  rw [Finset.eq_empty_iff_forall_notMem]
  intro p hp
  rw [mem_inversionSet_iff] at hp
  exact (not_lt_of_ge hp.1.le) hp.2

/-- A finite permutation has no inversions exactly when it is the identity. -/
theorem eq_refl_of_length_eq_zero (w : FinPermutation n)
    (hzero : w.length = 0) : w = Equiv.refl (Fin n) := by
  by_contra hne
  obtain ⟨i, j, hj, hdescent⟩ := exists_descent_of_ne_refl w hne
  have hinv : (i, j) ∈ w.inversionSet := by
    rw [mem_inversionSet_iff]
    have hij : i < j := by
      change i.1 < j.1
      omega
    exact ⟨hij, hdescent⟩
  have hpos : 0 < w.length := by
    exact Finset.card_pos.mpr ⟨(i, j), hinv⟩
  omega

/-- Every permutation admits a word of exactly its inversion length which
sorts it to the identity.  Thus the inversion statistic is the Coxeter word
length for the adjacent generators. -/
theorem exists_reducedWord_to_refl (w : FinPermutation n) :
    ∃ word : List (AdjacentPosition n),
      applyRightAdjacentWord word w = Equiv.refl (Fin n) ∧
        word.length = w.length := by
  generalize hm : w.length = m
  induction m using Nat.strong_induction_on generalizing w with
  | h m ih =>
      by_cases hw : w = Equiv.refl (Fin n)
      · subst w
        refine ⟨[], rfl, ?_⟩
        simpa [length_refl] using hm
      · obtain ⟨i, hi⟩ := exists_descent_of_ne_refl w hw
        rcases hi with ⟨j, hj, hdesc⟩
        let a : AdjacentPosition n :=
          { left := i
            hasRight := by
              rw [← hj]
              exact j.isLt }
        have ha : w.HasDescent a.left := ⟨j, hj, hdesc⟩
        have hdrop := length_rightAdjacentSwap_of_descent w a ha
        have hlt : (w.rightAdjacentSwap a).length < m := by
          omega
        obtain ⟨word, hword, hwordLength⟩ :=
          ih (w.rightAdjacentSwap a).length hlt
            (w.rightAdjacentSwap a) rfl
        refine ⟨a :: word, hword, ?_⟩
        simp only [List.length_cons]
        omega

/-- A chosen reduced sorting word, extracted from the proved existence
theorem rather than postulated. -/
noncomputable def reducedWordToRefl (w : FinPermutation n) :
    List (AdjacentPosition n) :=
  Classical.choose (exists_reducedWord_to_refl w)

@[simp] theorem apply_reducedWordToRefl (w : FinPermutation n) :
    applyRightAdjacentWord (reducedWordToRefl w) w =
      Equiv.refl (Fin n) :=
  (Classical.choose_spec (exists_reducedWord_to_refl w)).1

@[simp] theorem length_reducedWordToRefl (w : FinPermutation n) :
    (reducedWordToRefl w).length = w.length :=
  (Classical.choose_spec (exists_reducedWord_to_refl w)).2

/-- Send an inversion of the inverse permutation to the corresponding
inversion of the original permutation. -/
def inverseInversionPair (w : FinPermutation n) (p : Fin n × Fin n) :
    Fin n × Fin n :=
  (w.symm p.2, w.symm p.1)

/-- Inversion number is invariant under inversion of a permutation. -/
theorem length_symm (w : FinPermutation n) :
    length (w.symm : FinPermutation n) = w.length := by
  unfold length
  apply Finset.card_bij (fun p _ => inverseInversionPair w p)
  · intro p hp
    rw [mem_inversionSet_iff] at hp ⊢
    exact ⟨hp.2, by simpa [inverseInversionPair] using hp.1⟩
  · intro p₁ hp₁ p₂ hp₂ heq
    change (w.symm p₁.2, w.symm p₁.1) =
      (w.symm p₂.2, w.symm p₂.1) at heq
    apply Prod.ext
    · exact w.symm.injective (congrArg Prod.snd heq)
    · exact w.symm.injective (congrArg Prod.fst heq)
  · intro p hp
    refine ⟨(w p.2, w p.1), ?_, ?_⟩
    · rw [mem_inversionSet_iff] at hp ⊢
      exact ⟨hp.2, by simpa using hp.1⟩
    · simp [inverseInversionPair]

/-- All strictly ordered pairs of positions. -/
def increasingPairs (n : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun p => p.1 < p.2

/-- Increasing position pairs on which the values are also increasing. -/
def noninversionSet (w : FinPermutation n) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun p => p.1 < p.2 ∧ w p.1 < w p.2

theorem inversionSet_union_noninversionSet (w : FinPermutation n) :
    w.inversionSet ∪ noninversionSet w = increasingPairs n := by
  ext p
  rw [Finset.mem_union, mem_inversionSet_iff]
  simp only [noninversionSet, increasingPairs, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro (h | h) <;> exact h.1
  · intro h
    rcases lt_or_gt_of_ne (w.injective.ne h.ne) with hv | hv
    · exact Or.inr ⟨h, hv⟩
    · exact Or.inl ⟨h, hv⟩

theorem inversionSet_disjoint_noninversionSet (w : FinPermutation n) :
    Disjoint w.inversionSet (noninversionSet w) := by
  rw [Finset.disjoint_left]
  intro p hp hq
  rw [mem_inversionSet_iff] at hp
  simp only [noninversionSet, Finset.mem_filter,
    Finset.mem_univ, true_and] at hq
  exact (not_lt_of_ge hp.2.le) hq.2

theorem increasingPairs_card (w : FinPermutation n) :
    (increasingPairs n).card =
      w.inversionSet.card + (noninversionSet w).card := by
  calc
    (increasingPairs n).card =
        (w.inversionSet ∪ noninversionSet w).card := by
      rw [inversionSet_union_noninversionSet]
    _ = w.inversionSet.card + (noninversionSet w).card :=
      Finset.card_union_of_disjoint
        (inversionSet_disjoint_noninversionSet w)

/-- Composing on the right with the longest permutation exchanges inversions
and noninversions. -/
theorem inversionSet_trans_revPerm (w : FinPermutation n) :
    inversionSet (w.trans (Fin.revPerm : FinPermutation n)) =
      noninversionSet w := by
  ext p
  rw [mem_inversionSet_iff]
  simp only [Equiv.trans_apply, Fin.revPerm_apply, Fin.rev_lt_rev,
    noninversionSet, Finset.mem_filter, Finset.mem_univ, true_and]

theorem inversionSet_revPerm :
    inversionSet (Fin.revPerm : FinPermutation n) = increasingPairs n := by
  ext p
  rw [mem_inversionSet_iff]
  simp only [Fin.revPerm_apply, Fin.rev_lt_rev,
    increasingPairs, Finset.mem_filter, Finset.mem_univ, true_and]
  tauto

/-- The relative permutation carrying the longest element to `w` has the
complementary inversion length. -/
theorem length_longestRelative_add (w : FinPermutation n) :
    length ((Fin.revPerm : FinPermutation n).trans
        (w.symm : FinPermutation n)) + w.length =
      length (Fin.revPerm : FinPermutation n) := by
  have hinv : length (((Fin.revPerm : FinPermutation n).trans
      (w.symm : FinPermutation n)).symm : FinPermutation n) =
      length ((Fin.revPerm : FinPermutation n).trans
        (w.symm : FinPermutation n)) :=
    length_symm _
  have hsymm : (((Fin.revPerm : FinPermutation n).trans
      (w.symm : FinPermutation n)).symm : FinPermutation n) =
      w.trans (Fin.revPerm : FinPermutation n) := by
    ext i
    simp
  rw [← hinv, hsymm]
  unfold length
  rw [inversionSet_trans_revPerm, inversionSet_revPerm]
  have hpartition := increasingPairs_card w
  omega

/-- Applying an adjacent word to an arbitrary starting permutation is the
same as first applying it to the identity and then composing with the start. -/
theorem applyRightAdjacentWord_eq_trans
    (word : List (AdjacentPosition n)) (w : FinPermutation n) :
    applyRightAdjacentWord word w =
      (applyRightAdjacentWord word (Equiv.refl (Fin n))).trans w := by
  induction word generalizing w with
  | nil => rfl
  | cons a word ih =>
      calc
        applyRightAdjacentWord (a :: word) w =
            applyRightAdjacentWord word (w.rightAdjacentSwap a) := rfl
        _ = (applyRightAdjacentWord word (Equiv.refl (Fin n))).trans
            (w.rightAdjacentSwap a) := ih _
        _ = ((applyRightAdjacentWord word (Equiv.refl (Fin n))).trans
              (rightAdjacentSwap (Equiv.refl (Fin n) : FinPermutation n) a)).trans w := by
                ext x
                rfl
        _ = (applyRightAdjacentWord word
              (rightAdjacentSwap (Equiv.refl (Fin n) : FinPermutation n) a)).trans w := by
                rw [ih (rightAdjacentSwap
                  (Equiv.refl (Fin n) : FinPermutation n) a)]
        _ = (applyRightAdjacentWord (a :: word)
              (Equiv.refl (Fin n))).trans w := rfl

/-- Reversing a word of adjacent transpositions inverts the permutation
obtained by applying that word to the identity. -/
theorem applyRightAdjacentWord_reverse_refl
    (word : List (AdjacentPosition n)) :
    applyRightAdjacentWord word.reverse (Equiv.refl (Fin n)) =
      (applyRightAdjacentWord word (Equiv.refl (Fin n))).symm := by
  induction word with
  | nil => rfl
  | cons a tail ih =>
      rw [List.reverse_cons, applyRightAdjacentWord_append]
      simp only [applyRightAdjacentWord_cons, applyRightAdjacentWord_nil]
      rw [ih]
      rw [applyRightAdjacentWord_eq_trans tail
        (rightAdjacentSwap (Equiv.refl (Fin n)) a)]
      ext x
      rfl

/-- If a word sorts `g` to the identity, its product from the identity is
`g⁻¹`. -/
theorem applyRightAdjacentWord_refl_eq_symm_of_eq_refl
    {word : List (AdjacentPosition n)} {g : FinPermutation n}
    (hword : applyRightAdjacentWord word g = Equiv.refl (Fin n)) :
    applyRightAdjacentWord word (Equiv.refl (Fin n)) =
      (g.symm : FinPermutation n) := by
  rw [applyRightAdjacentWord_eq_trans] at hword
  apply Equiv.ext
  intro x
  have hx := DFunLike.congr_fun hword x
  apply g.injective
  simpa using hx

/-- If a word sorts a permutation to the identity, its reversed word sorts
the inverse permutation to the identity. -/
theorem applyRightAdjacentWord_reverse_symm_eq_refl_of_eq_refl
    {word : List (AdjacentPosition n)} {g : FinPermutation n}
    (hword : applyRightAdjacentWord word g = Equiv.refl (Fin n)) :
    applyRightAdjacentWord word.reverse (g.symm : FinPermutation n) =
      Equiv.refl (Fin n) := by
  rw [applyRightAdjacentWord_eq_trans,
    applyRightAdjacentWord_reverse_refl,
    applyRightAdjacentWord_refl_eq_symm_of_eq_refl hword]
  ext x
  simp

/-- Inversion length is subadditive under permutation composition.  The
proof realizes the left factor by the reverse of its canonical sorting word
and applies the universal word-length bound from the right factor. -/
theorem length_trans_le (left right : FinPermutation n) :
    length (left.trans right : FinPermutation n) ≤
      left.length + right.length := by
  let sorting := reducedWordToRefl left
  have hproductSorting :
      applyRightAdjacentWord sorting (Equiv.refl (Fin n)) =
        (left.symm : FinPermutation n) :=
    applyRightAdjacentWord_refl_eq_symm_of_eq_refl
      (apply_reducedWordToRefl left)
  have happly :
      applyRightAdjacentWord sorting (left.trans right) = right := by
    rw [applyRightAdjacentWord_eq_trans, hproductSorting]
    ext x
    simp
  have hbound := length_le_word_length_add_result
    sorting (left.trans right)
  rw [happly, length_reducedWordToRefl] at hbound
  exact hbound

/-- A canonical reduced word descending from the longest permutation to
`w`, constructed by sorting the relative permutation. -/
noncomputable def reducedWordFromLongest (w : FinPermutation n) :
    List (AdjacentPosition n) :=
  reducedWordToRefl
    ((Fin.revPerm : FinPermutation n).trans (w.symm : FinPermutation n))

@[simp] theorem apply_reducedWordFromLongest (w : FinPermutation n) :
    applyRightAdjacentWord (reducedWordFromLongest w)
      (Fin.revPerm : FinPermutation n) = w := by
  let g : FinPermutation n :=
    (Fin.revPerm : FinPermutation n).trans (w.symm : FinPermutation n)
  have hsort : applyRightAdjacentWord (reducedWordFromLongest w) g =
      Equiv.refl (Fin n) := by
    exact apply_reducedWordToRefl g
  have hproduct :=
    applyRightAdjacentWord_refl_eq_symm_of_eq_refl hsort
  rw [applyRightAdjacentWord_eq_trans]
  rw [hproduct]
  ext x
  simp [g]

@[simp] theorem length_reducedWordFromLongest (w : FinPermutation n) :
    (reducedWordFromLongest w).length + w.length =
      length (Fin.revPerm : FinPermutation n) := by
  rw [reducedWordFromLongest, length_reducedWordToRefl]
  exact length_longestRelative_add w

theorem isDescendingWord_reducedWordFromLongest (w : FinPermutation n) :
    IsDescendingWord (Fin.revPerm : FinPermutation n)
      (reducedWordFromLongest w) := by
  apply isDescendingWord_of_length_eq
  rw [apply_reducedWordFromLongest]
  exact length_reducedWordFromLongest w

end FinPermutation

end Schubert
