import Schubert.RS.Family.MarkedSelections
import Schubert.RS.Family.SourceSelections

/-! All paired target selections, allowing the two source classes to have
different sizes. Balance is an exact bijection, with no omitted terms. -/

namespace Schubert.RS.Family
noncomputable section
variable {m p q : ℕ}

def balancedTermSelection (t : BalancedPairedTerm m p q) : MarkedSelection m p q where
  early := t.val.2.1.val.1 \ t.val.1
  late := t.val.2.1.val.2
  marked := t.val.1
  early_disjoint_marked := Finset.sdiff_disjoint
  late_disjoint_marked := t.property.2.1
  first_degree := by
    have he : (t.val.2.1.val.1 \ t.val.1).card+t.val.1.card=t.val.2.1.val.1.card := by
      rw [← Finset.card_union_of_disjoint Finset.sdiff_disjoint,
        Finset.sdiff_union_of_subset t.property.1]
    rw [he]
    exact t.val.2.1.property.1
  first_early_bound := by
    rw [← Finset.card_union_of_disjoint Finset.sdiff_disjoint,
      Finset.sdiff_union_of_subset t.property.1]
    exact t.val.2.1.property.2
  second_early_bound := by
    have h := t.val.2.2.property.2
    rw [t.property.2.2.1,Finset.card_compl,Fintype.card_fin] at h
    exact h

def selectionFirstChoice (c : MarkedSelection m p q) : PairedChoice m p :=
  ⟨(c.early ∪ c.marked,c.late),by
    rw [Finset.card_union_of_disjoint c.early_disjoint_marked]
    exact ⟨c.first_degree,c.first_early_bound⟩⟩

def selectionSecondChoice (hp : 0<p) (hq : 0<q) (h : p+q=m+1)
    (c : MarkedSelection m p q) : PairedChoice m q :=
  ⟨(c.earlyᶜ,(c.late ∪ c.marked)ᶜ),by
    simp only [Finset.card_compl,Fintype.card_fin,
      Finset.card_union_of_disjoint c.late_disjoint_marked]
    have he : c.early.card≤m := by simpa using Finset.card_le_univ c.early
    have hl : c.late.card+c.marked.card≤m := by
      rw [← Finset.card_union_of_disjoint c.late_disjoint_marked]
      simpa using Finset.card_le_univ (c.late ∪ c.marked)
    have hd := c.first_degree
    have hb := c.second_early_bound
    constructor <;> omega⟩

def selectionBalancedTerm (hp : 0<p) (hq : 0<q) (h : p+q=m+1)
    (c : MarkedSelection m p q) : BalancedPairedTerm m p q :=
  ⟨(c.marked,selectionFirstChoice c,selectionSecondChoice hp hq h c),by
    change c.marked ⊆ c.early ∪ c.marked ∧ Disjoint c.late c.marked ∧
      c.earlyᶜ=((c.early ∪ c.marked) \ c.marked)ᶜ ∧ _
    rw [disjoint_union_sdiff _ _ c.early_disjoint_marked]
    exact ⟨Finset.subset_union_right,c.late_disjoint_marked,rfl,rfl⟩⟩

theorem balancedTermSelection_selection (hp : 0<p) (hq : 0<q) (h : p+q=m+1)
    (c : MarkedSelection m p q) : balancedTermSelection (selectionBalancedTerm hp hq h c)=c := by
  apply MarkedSelection.ext
  · exact disjoint_union_sdiff _ _ c.early_disjoint_marked
  · rfl
  · rfl

theorem selectionBalancedTerm_term (hp : 0<p) (hq : 0<q) (h : p+q=m+1)
    (t : BalancedPairedTerm m p q) : selectionBalancedTerm hp hq h (balancedTermSelection t)=t := by
  apply Subtype.ext
  refine Prod.ext rfl ?_
  apply Prod.ext
  · apply Subtype.ext
    exact Prod.ext (Finset.sdiff_union_of_subset t.property.1) rfl
  · apply Subtype.ext
    exact Prod.ext t.property.2.2.1.symm t.property.2.2.2.symm

def pairedSelectionEquiv (hp : 0<p) (hq : 0<q) (h : p+q=m+1) :
    BalancedPairedTerm m p q ≃ MarkedSelection m p q where
  toFun := balancedTermSelection
  invFun := selectionBalancedTerm hp hq h
  left_inv := selectionBalancedTerm_term hp hq h
  right_inv := balancedTermSelection_selection hp hq h

theorem marked_pair_signed_sum (hp : 0<p) (hq : 0<q) (h : p+q=m+1) :
    ∑ t : BalancedPairedTerm m p q,(-1 : ℤ)^t.val.1.card =
      2*(Nat.choose m (p-1) : ℤ)*Nat.choose m p-m*(Nat.choose (m-1) (p-1) : ℤ)^2 := by
  rw [← (pairedSelectionEquiv hp hq h).symm.sum_comp (fun t => (-1 : ℤ)^t.val.1.card)]
  exact marked_selection_signed_sum hp h

end
end Schubert.RS.Family
