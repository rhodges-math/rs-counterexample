import RSCounterexample.FlagVarieties.Foundations.TypeA.MatrixBruhatDecompositionMinor

/-!
# Ordered insertion of a deleted pivot index

The equivalence puts `Fin n` into the complement of a chosen index and
reserves the right summand for that index.  Its left summand is strictly
order preserving; this is the order fact needed when extending upper
triangular matrices over the deleted column.
-/

namespace FlagVarieties.Foundations.TypeA

variable {n : ℕ}

/-- The map `Fin n ⊕ Unit → Fin (n + 1)` sending `Fin n` in order onto the complement of `p` and the
extra point to `p`. -/
def insertIndex (p : Fin (n + 1)) : Fin n ⊕ Unit → Fin (n + 1)
  | .inl i => p.succAbove i
  | .inr _ => p

theorem insertIndex_injective (p : Fin (n + 1)) :
    Function.Injective (insertIndex p) := by
  intro a b h
  cases a with
  | inl i =>
      cases b with
      | inl j =>
          congr 1
          exact p.succAbove_right_injective (by simpa [insertIndex] using h)
      | inr u =>
          cases u
          exact (p.succAbove_ne i (by simp [insertIndex] at h)).elim
  | inr u =>
      cases u
      cases b with
      | inl j =>
          exact (p.ne_succAbove j (by simp [insertIndex] at h)).elim
      | inr v => cases v; rfl

theorem insertIndex_surjective (p : Fin (n + 1)) :
    Function.Surjective (insertIndex p) := by
  intro x
  by_cases hx : x = p
  · exact ⟨Sum.inr (), by simpa [insertIndex] using hx.symm⟩
  · obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq hx
    exact ⟨Sum.inl i, by simpa [insertIndex] using hi⟩

/-- `insertIndex p` as an equivalence. -/
noncomputable def insertIndexEquiv (p : Fin (n + 1)) :
    Fin n ⊕ Unit ≃ Fin (n + 1) :=
  Equiv.ofBijective (insertIndex p)
    ⟨insertIndex_injective p, insertIndex_surjective p⟩

@[simp] theorem insertIndexEquiv_inl (p : Fin (n + 1)) (i : Fin n) :
    insertIndexEquiv p (.inl i) = p.succAbove i := rfl

@[simp] theorem insertIndexEquiv_inr (p : Fin (n + 1)) (u : Unit) :
    insertIndexEquiv p (.inr u) = p := rfl

@[simp] theorem insertIndexEquiv_symm_inl (p : Fin (n + 1)) (i : Fin n) :
    (insertIndexEquiv p).symm (p.succAbove i) = .inl i := by
  simpa only [insertIndexEquiv_inl] using
    (insertIndexEquiv p).symm_apply_apply (Sum.inl i)

@[simp] theorem insertIndexEquiv_symm_inr (p : Fin (n + 1)) :
    (insertIndexEquiv p).symm p = .inr () := by
  simpa only [insertIndexEquiv_inr] using
    (insertIndexEquiv p).symm_apply_apply (Sum.inr ())

theorem insertIndexEquiv_inl_strictMono (p : Fin (n + 1)) :
    StrictMono (fun i : Fin n => insertIndexEquiv p (.inl i)) :=
  Fin.strictMono_succAbove p

end FlagVarieties.Foundations.TypeA
