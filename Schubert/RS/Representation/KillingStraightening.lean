import Schubert.RS.Representation.KillingWordFiltration

namespace Schubert.RS.Representation
noncomputable section

private theorem count_expansion {n : ℕ} (order roots : List (PositiveRoot n))
    (horder : order.Nodup) (r : PositiveRoot n) :
    (order.flatMap fun s => List.replicate (roots.count s) s).count r =
      if r ∈ order then roots.count r else 0 := by
  classical
  induction order with
  | nil => simp
  | cons s order ih =>
    have hs := List.nodup_cons.mp horder
    by_cases hrs : r = s
    · subst s
      simp [List.flatMap_cons, ih hs.2, hs.1]
    · have hval : s.val ≠ r.val := fun h => hrs (Subtype.ext h.symm)
      simp [List.flatMap_cons, ih hs.2, List.count_replicate, hrs, hval]

/-- Canonical words are formed by collecting equal roots in the given order. -/
def countWord {n : ℕ} (order : RootOrdering n) (roots : List (PositiveRoot n)) :
    List (PositiveRoot n) :=
  order.roots.flatMap fun r => List.replicate (roots.count r) r

theorem countWord_perm {n : ℕ} (order : RootOrdering n) (roots : List (PositiveRoot n)) :
    roots.Perm (countWord order roots) := by
  classical
  apply List.perm_iff_count.mpr
  intro r
  rw [countWord, count_expansion _ _ order.nodup, if_pos (order.complete r)]

theorem rootWord_countWord {n : ℕ} (order : RootOrdering n) (roots : List (PositiveRoot n)) :
    rootWord (countWord order roots) = orderedRootMonomial order (fun r => roots.count r) := by
  rw [orderedRootMonomial_eq]
  unfold countWord rootWord
  induction order.roots with
  | nil => simp
  | cons r rs ih => simp [ih]

abbrev KillingPowers {n : ℕ} (u : Fin n → ℕ) (powers : PositiveRoot n → ℕ) : Prop :=
  ∀ r, 0 < powers r → u r.val.2 ≤ u r.val.1

/-- Ordered nonempty monomials supported entirely on the killing roots. -/
def orderedKillingSpan {n : ℕ} (u : Fin n → ℕ) (order : RootOrdering n) :
    Submodule ℂ (Enveloping n) :=
  Submodule.span ℂ {a | ∃ powers : PositiveRoot n → ℕ,
    KillingPowers u powers ∧ (∃ r, 0 < powers r) ∧ a = orderedRootMonomial order powers}

/-- Straightening in the killing subalgebra is proved by strict word-length
induction. Permuting to the count-word introduces only shorter nonempty
killing words, so no constant term can appear. -/
theorem killingWord_mem_orderedSpan {n : ℕ} (u : Fin n → ℕ) (order : RootOrdering n)
    (roots : List (PositiveRoot n)) (hk : IsKillingWord u roots) (hn : 0 < roots.length) :
    rootWord roots ∈ orderedKillingSpan u order := by
  classical
  have hc : rootWord (countWord order roots) ∈ orderedKillingSpan u order := by
    rw [rootWord_countWord]
    apply Submodule.subset_span
    refine ⟨fun r => roots.count r, ?_, ?_, rfl⟩
    · intro r hr
      exact hk r (List.count_pos_iff.mp hr)
    · cases roots with
      | nil => simp at hn
      | cons r roots => exact ⟨r, List.count_pos_iff.mpr (List.mem_cons_self ..)⟩
  have hlower : shorterKillingSpan u roots.length ≤ orderedKillingSpan u order := by
    apply Submodule.span_le.mpr
    rintro a ⟨shorter, hs, hpos, hlt, rfl⟩
    exact killingWord_mem_orderedSpan u order shorter hs hpos
  have hd := hlower (killingWord_perm_difference u (countWord_perm order roots) hk)
  simpa only [sub_add_cancel] using (orderedKillingSpan u order).add_mem hd hc
termination_by roots.length

theorem killingOperator_mul_word_straightens {n : ℕ} (u : Fin n → ℕ)
    (order : RootOrdering n) (r : PositiveRoot n) (hr : u r.val.2 ≤ u r.val.1)
    (roots : List (PositiveRoot n)) (hk : IsKillingWord u roots) :
    rootWord roots * rootOperator r ∈ orderedKillingSpan u order := by
  have hw : IsKillingWord u (roots ++ [r]) := by
    intro s hs
    rcases List.mem_append.mp hs with hs | hs
    · exact hk s hs
    · simpa using List.mem_singleton.mp hs ▸ hr
  have := killingWord_mem_orderedSpan u order (roots ++ [r]) hw (by simp)
  simpa [rootWord] using this

end
end Schubert.RS.Representation
