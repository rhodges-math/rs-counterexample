import Schubert.RS.HallRowEquivalence
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-! Weak height words and their complete multiplicity vectors are equivalent. -/

namespace Schubert.RS.HallLattice
noncomputable section

def heightMultiset {k y : ℕ} (r : WeakHeights k y) : Sym (Fin (y+1)) k :=
  ⟨(List.ofFn r.val : Multiset (Fin (y+1))), by simp⟩

theorem heightMultiset_injective (k y : ℕ) : Function.Injective (@heightMultiset k y) := by
  intro r q h
  have hp : (List.ofFn r.val).Perm (List.ofFn q.val) :=
    Multiset.coe_eq_coe.mp (congrArg Subtype.val h)
  have hs (r : WeakHeights k y) : (List.ofFn r.val).SortedLE := by
    apply List.sortedLE_ofFn_iff.mpr
    intro i j hij
    exact r.property hij
  apply Subtype.ext
  exact List.ofFn_injective (hp.eq_of_sortedLE (hs r) (hs q))

theorem heightMultiset_surjective (k y : ℕ) : Function.Surjective (@heightMultiset k y) := by
  intro m
  let l := (m : Multiset (Fin (y+1))).sort
  have hl : l.length = k := by simp [l]
  let r : Fin k → Fin (y+1) := fun q => l.get ⟨q.val, by rw [hl]; exact q.isLt⟩
  have hr : Monotone (fun q => (r q).val) := by
    have hs : l.SortedLE := (Multiset.pairwise_sort _ _).sortedLE
    intro i j hij
    exact hs.monotone_get (show (⟨i.val, by rw [hl]; exact i.isLt⟩ : Fin l.length) ≤
      ⟨j.val, by rw [hl]; exact j.isLt⟩ from hij)
  have he : List.ofFn r = l := by
    apply List.ext_getElem
    · simp [hl]
    · intro a ha hb
      simp only [List.getElem_ofFn]
      rfl
  refine ⟨⟨r, hr⟩, ?_⟩
  apply Sym.ext
  change (List.ofFn r : Multiset (Fin (y+1))) = m
  rw [he]
  exact Multiset.sort_eq _ _

def heightMultisetEquiv (k y : ℕ) : WeakHeights k y ≃ Sym (Fin (y+1)) k :=
  Equiv.ofBijective heightMultiset ⟨heightMultiset_injective k y, heightMultiset_surjective k y⟩

def heightMultiplicityEquiv (k y : ℕ) :
    WeakHeights k y ≃ {e : Fin (y+1) → ℕ // ∑ h, e h = k} :=
  (heightMultisetEquiv k y).trans (Sym.equivNatSumOfFintype (Fin (y+1)) k)

theorem heightMultiplicity_apply {k y : ℕ} (r : WeakHeights k y) (h : Fin (y+1)) :
    (heightMultiplicityEquiv k y r).val h = (List.ofFn r.val).count h := by
  simp only [heightMultiplicityEquiv, Equiv.trans_apply, Sym.coe_equivNatSumOfFintype_apply_apply]
  change (List.ofFn r.val : Multiset (Fin (y+1))).count h = (List.ofFn r.val).count h
  exact Multiset.coe_count _ _

theorem heightMultiplicity_weight {R : Type*} [CommMonoid R] {k y : ℕ}
    (slot : Fin (y+1) → R) (r : WeakHeights k y) :
    (∏ q, slot (r.val q)) = ∏ h, slot h ^ (heightMultiplicityEquiv k y r).val h := by
  classical
  simp_rw [heightMultiplicity_apply]
  rw [← List.prod_ofFn]
  change (List.ofFn (slot ∘ r.val)).prod = _
  rw [← List.map_ofFn]
  rw [Finset.prod_list_map_count]
  apply Finset.prod_subset (Finset.subset_univ _)
  intro h _ hn
  have hh : (List.ofFn r.val).count h = 0 := List.count_eq_zero_of_not_mem
    (fun hm => hn (List.mem_toFinset.mpr hm))
  simp only [hh, pow_zero]

end
end Schubert.RS.HallLattice
