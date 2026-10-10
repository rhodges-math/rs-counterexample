import RSCounterexample.Demazure.Representation.FlagChoice
import RSCounterexample.Demazure.JosephPolo.FlagModulePresentation
import RSCounterexample.Demazure.TorusCharacterTransport

/-!
# Demazure modules along cosets of the stabilizer

For the dominant weight `λ = shapeWeight m` and a permutation `w`, the Demazure module
`D_w(λ) = flagDemazure m w` depends only on the extremal weight `w · λ = extremalWeight m w`.
It is REL's `compositionFlag (w · λ)`, so the Demazure character formula holds for every `w`,
not only for the shortest coset representatives.

We also introduce the shortest coset representatives `W^λ` (`IsMinCosetRep`) and show that a
permutation outside `W^λ` has a smaller permutation, in Bruhat order, with the same extremal
weight.
-/

open Schubert

namespace Demazure.SchubertUnions

open FlagModule FinPermutation

variable {n : ℕ}

theorem columnsOfWeight_shapeWeight : ∀ {n : ℕ} (m : ColumnShape n),
    columnsOfWeight (shapeWeight m) = m
  | 0, _ => Subsingleton.elim _ _
  | n + 1, m => by
    rw [← Fin.cons_self_tail m]
    have htail : (fun i : Fin n => shapeWeight (Fin.cons (m 0) (Fin.tail m) : ColumnShape (n+1))
        i.succ) = shapeWeight (Fin.tail m) :=
      funext fun i => shapeWeight_cons_succ (m 0) (Fin.tail m) i
    rw [columnsOfWeight]
    rw [htail, columnsOfWeight_shapeWeight (Fin.tail m), shapeWeight_cons_zero]
    simp

/-- The action `σ · λ = λ ∘ σ⁻¹` of a permutation on a composition. -/
def permAct (σ : Equiv.Perm (Fin n)) (dom : Composition n) : Composition n :=
  fun i => dom (σ.symm i)

theorem extremalWeight_eq_permAct (m : ColumnShape n) (w : Equiv.Perm (Fin n)) :
    extremalWeight m w = permAct w (shapeWeight m) := rfl

theorem dominantComposition_extremalWeight (m : ColumnShape n) (w : Equiv.Perm (Fin n)) :
    dominantComposition (extremalWeight m w) = shapeWeight m := by
  have h : Antitone (extremalWeight m w ∘ w) := by
    intro i j hij
    simpa [extremalWeight] using shapeWeight_antitone m hij
  rw [← dominantComposition_unique _ w h]
  funext i
  simp [extremalWeight]

theorem compositionShape_extremalWeight (m : ColumnShape n) (w : Equiv.Perm (Fin n)) :
    compositionShape (extremalWeight m w) = m := by
  rw [compositionShape, dominantComposition_extremalWeight, columnsOfWeight_shapeWeight]

/-- `D_w(λ)` is REL's composition flag module of its extremal weight. -/
theorem flagDemazure_eq_compositionFlag (m : ColumnShape n) (w : Equiv.Perm (Fin n)) :
    flagDemazure m w = compositionFlag (extremalWeight m w) := by
  change flagDemazure m w = flagDemazure (compositionShape (extremalWeight m w))
    (compositionPermutation (extremalWeight m w))
  have hshape := compositionShape_extremalWeight m w
  have hwt := composition_extremalWeight (extremalWeight m w)
  rw [hshape] at hwt ⊢
  exact flagDemazure_eq_of_weight_eq m w _ hwt.symm

/-- The Demazure character formula for every Demazure module `D_w(λ)`. -/
theorem flagDemazure_hasTorusCharacter (m : ColumnShape n) (w : Equiv.Perm (Fin n)) :
    HasTorusCharacter (flagTorus m w) (key (extremalWeight m w)) :=
  HasTorusCharacter.of_equiv (compositionFlagJosephPolo_and_character (extremalWeight m w)).2
    (LinearEquiv.ofEq _ _ (flagDemazure_eq_compositionFlag m w).symm) fun _ _ => rfl

/-! ### Shortest coset representatives -/

/-- `σ` is the shortest element of its coset `σ · Stab(λ)`: it is increasing on each block of
equal entries of `λ`. -/
def IsMinCosetRep (dom : Composition n) (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ i j, i < j → dom i = dom j → σ i < σ j

theorem exists_adjacent_descent (σ : Equiv.Perm (Fin n)) {i j : Fin n} (hij : i < j)
    (hσ : σ j < σ i) :
    ∃ p : AdjacentPosition n, i ≤ p.left ∧ p.right ≤ j ∧ σ p.right < σ p.left := by
  obtain ⟨d, hd⟩ : ∃ d, j.val = i.val + 1 + d :=
    ⟨j.val - i.val - 1, by rw [Fin.lt_def] at hij; omega⟩
  induction d generalizing i with
  | zero =>
    let a : AdjacentPosition n := ⟨i, by omega⟩
    have hal : a.left = i := rfl
    have har : a.right = j := Fin.ext (by rw [AdjacentPosition.right_val, hal]; omega)
    exact ⟨a, le_of_eq hal.symm, le_of_eq har, by rw [har, hal]; exact hσ⟩
  | succ d ih =>
    let a : AdjacentPosition n := ⟨i, by omega⟩
    have hal : a.left = i := rfl
    have harv : a.right.val = i.val + 1 := by rw [AdjacentPosition.right_val, hal]
    by_cases h : σ a.right < σ a.left
    · exact ⟨a, le_of_eq hal.symm, by rw [Fin.le_def]; omega, h⟩
    · have hlt : σ a.left < σ a.right :=
        lt_of_le_of_ne (not_lt.mp h) (fun e => a.left_ne_right (σ.injective e))
      have hr : a.right < j := by rw [Fin.lt_def]; omega
      rw [hal] at hlt
      obtain ⟨p, hp1, hp2, hp3⟩ := ih hr (lt_trans hσ hlt) (by omega)
      refine ⟨p, ?_, hp2, hp3⟩
      rw [Fin.le_def] at hp1 ⊢
      omega

/-- A permutation outside `W^λ` lies strictly above a permutation with the same extremal
weight. -/
theorem exists_lt_extremalWeight_eq (m : ColumnShape n) (σ : FinPermutation n)
    (hσ : ¬ IsMinCosetRep (shapeWeight m) σ) :
    ∃ τ, τ <ᴮ σ ∧ extremalWeight m τ = extremalWeight m σ := by
  simp only [IsMinCosetRep, not_forall] at hσ
  obtain ⟨i, j, hij, heq, hnot⟩ := hσ
  have hσji : σ j < σ i :=
    lt_of_le_of_ne (not_lt.mp hnot) (fun e => (ne_of_lt hij) (σ.injective e).symm)
  obtain ⟨p, hip, hpj, hdesc⟩ := exists_adjacent_descent σ hij hσji
  have hblock : shapeWeight m p.left = shapeWeight m p.right := by
    apply le_antisymm
    · calc shapeWeight m p.left ≤ shapeWeight m i := shapeWeight_antitone m hip
        _ = shapeWeight m j := heq
        _ ≤ shapeWeight m p.right := shapeWeight_antitone m hpj
    · exact shapeWeight_antitone m (le_of_lt p.left_lt_right)
  have hD : σ.HasDescent p.left := (hasDescent_left_iff σ p).mpr hdesc
  refine ⟨σ.rightAdjacentSwap p, rightAdjacentSwap_lt_of_descent σ p hD, ?_⟩
  funext k
  simp only [extremalWeight, rightAdjacentSwap, adjacentTransposition, Equiv.symm_trans_apply,
    Equiv.symm_swap]
  by_cases hl : σ.symm k = p.left
  · rw [hl, Equiv.swap_apply_left, hblock]
  · by_cases hr : σ.symm k = p.right
    · rw [hr, Equiv.swap_apply_right, hblock]
    · rw [Equiv.swap_apply_of_ne_of_ne hl hr]

end Demazure.SchubertUnions
