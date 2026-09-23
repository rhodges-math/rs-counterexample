import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Direct zero/one-marked-pair count. A marked pair uses both sources' early
slot and neither late slot. Unmarked slots are divided between the sources.
Only finite subsets, cardinalities, and explicit bijections occur here. -/

namespace Schubert.RS.Family
noncomputable section
variable {m p q : ℕ}

/-- At unmarked pairs the first source chooses early subset `early` and late
subset `late`. At marked pairs both sources choose early and neither chooses late. -/
structure MarkedSelection (m p q : ℕ) where
  early : Finset (Fin m)
  late : Finset (Fin m)
  marked : Finset (Fin m)
  early_disjoint_marked : Disjoint early marked
  late_disjoint_marked : Disjoint late marked
  first_degree : early.card + marked.card + late.card = 2 * p - 1
  first_early_bound : early.card + marked.card ≤ p
  second_early_bound : m - early.card ≤ q

/-- Total early usage, counted across both sources, is m plus the number
of marked pairs. The first summand is source A; the second is source B. -/
theorem MarkedSelection.early_usage (c : MarkedSelection m p q) :
    (c.early.card+c.marked.card)+(m-c.early.card)=m+c.marked.card := by
  have he : c.early.card≤m := by simpa using Finset.card_le_univ c.early
  omega

theorem MarkedSelection.marked_card_le_one {m p q : ℕ}
    (c : MarkedSelection m p q) (h : p + q = m + 1) : c.marked.card ≤ 1 := by
  have he := c.early_usage
  have ha := c.first_early_bound
  have hb := c.second_early_bound
  omega

@[ext] theorem MarkedSelection.ext {m p q : ℕ} {c d : MarkedSelection m p q}
    (he : c.early = d.early) (hl : c.late = d.late) (hf : c.marked = d.marked) : c = d := by
  cases c
  cases d
  cases he
  cases hl
  cases hf
  rfl

instance {m p q : ℕ} : Fintype (MarkedSelection m p q) :=
  Fintype.ofInjective (fun c => (c.early, c.late, c.marked)) (by
    intro c d h
    exact MarkedSelection.ext (congrArg (fun x => x.1) h)
      (congrArg (fun x => x.2.1) h) (congrArg (fun x => x.2.2) h))

abbrev FixedSizeSubset (α : Type*) (k : ℕ) := {s : Finset α // s.card = k}

/-- The two possible early/late usage patterns when no pair is marked. -/
abbrev UnmarkedChoices (m p : ℕ) :=
  (FixedSizeSubset (Fin m) (p - 1) × FixedSizeSubset (Fin m) p) ⊕
    (FixedSizeSubset (Fin m) p × FixedSizeSubset (Fin m) (p - 1))

/-- Choose the marked pair, then two subsets of the remaining labeled pairs. -/
abbrev OneMarkedChoices (m p : ℕ) :=
  (e : Fin m) × (FixedSizeSubset {i : Fin m // i ≠ e} (p - 1) ×
    FixedSizeSubset {i : Fin m // i ≠ e} (p - 1))

theorem card_unmarkedChoices (m p : ℕ) :
    Fintype.card (UnmarkedChoices m p) = 2 * Nat.choose m (p - 1) * Nat.choose m p := by
  simp only [UnmarkedChoices, Fintype.card_sum, Fintype.card_prod,
    FixedSizeSubset, Fintype.card_finset_len, Fintype.card_fin]
  ring

theorem card_oneMarkedChoices (m p : ℕ) :
    Fintype.card (OneMarkedChoices m p) = m * Nat.choose (m - 1) (p - 1) ^ 2 := by
  have hc (e : Fin m) : Fintype.card {i : Fin m // i ≠ e} = m - 1 := by
    simp [Fintype.card_subtype_compl]
  simp only [OneMarkedChoices, Fintype.card_sigma, Fintype.card_prod,
    FixedSizeSubset, Fintype.card_finset_len, hc]
  simp [pow_two]

theorem unmarked_sizes (hp : 0 < p) (h : p+q=m+1)
    (c : MarkedSelection m p q) (hz : c.marked.card=0) :
    (c.early.card=p-1 ∧ c.late.card=p) ∨
      (c.early.card=p ∧ c.late.card=p-1) := by
  have he : c.early.card ≤ m := by simpa using Finset.card_le_univ c.early
  have hd := c.first_degree
  have ha := c.first_early_bound
  have hb := c.second_early_bound
  omega

theorem oneMarked_sizes (hp : 0 < p) (h : p+q=m+1)
    (c : MarkedSelection m p q) (hz : c.marked.card=1) :
    c.early.card=p-1 ∧ c.late.card=p-1 := by
  have he : c.early.card ≤ m := by simpa using Finset.card_le_univ c.early
  have hd := c.first_degree
  have ha := c.first_early_bound
  have hb := c.second_early_bound
  omega

abbrev UnmarkedSelection (m p q : ℕ) := {c : MarkedSelection m p q // c.marked=∅}
abbrev OneMarkedSelection (m p q : ℕ) := {c : MarkedSelection m p q // c.marked.card=1}

def unmarkedOfChoice (hp : 0 < p) (h : p+q=m+1) : UnmarkedChoices m p → UnmarkedSelection m p q
  | .inl (e,l) => ⟨{
      early := e.val, late := l.val, marked := ∅
      early_disjoint_marked := Finset.disjoint_empty_right _
      late_disjoint_marked := Finset.disjoint_empty_right _
      first_degree := by simp only [Finset.card_empty,e.property,l.property]; omega
      first_early_bound := by simp only [Finset.card_empty,e.property]; omega
      second_early_bound := by rw [e.property]; omega }, rfl⟩
  | .inr (e,l) => ⟨{
      early := e.val, late := l.val, marked := ∅
      early_disjoint_marked := Finset.disjoint_empty_right _
      late_disjoint_marked := Finset.disjoint_empty_right _
      first_degree := by simp only [Finset.card_empty,e.property,l.property]; omega
      first_early_bound := by simp only [Finset.card_empty,e.property]; omega
      second_early_bound := by rw [e.property]; omega }, rfl⟩

theorem unmarkedOfChoice_injective (hp : 0 < p) (h : p+q=m+1) :
    Function.Injective (unmarkedOfChoice hp h) := by
  intro x y hxy
  have he := congrArg (fun c : UnmarkedSelection m p q => c.val.early) hxy
  have hl := congrArg (fun c : UnmarkedSelection m p q => c.val.late) hxy
  cases x with
  | inl x =>
    cases y with
    | inl y => exact congrArg Sum.inl (Prod.ext (Subtype.ext he) (Subtype.ext hl))
    | inr y =>
      have hc := congrArg Finset.card he
      change x.1.val.card=y.1.val.card at hc
      rw [x.1.property,y.1.property] at hc
      omega
  | inr x =>
    cases y with
    | inl y =>
      have hc := congrArg Finset.card he
      change x.1.val.card=y.1.val.card at hc
      rw [x.1.property,y.1.property] at hc
      omega
    | inr y => exact congrArg Sum.inr (Prod.ext (Subtype.ext he) (Subtype.ext hl))

theorem unmarkedOfChoice_surjective (hp : 0 < p) (h : p+q=m+1) :
    Function.Surjective (unmarkedOfChoice hp h) := by
  intro c
  have hz : c.val.marked.card=0 := by rw [c.property]; rfl
  rcases unmarked_sizes hp h c.val hz with ⟨he,hl⟩ | ⟨he,hl⟩
  · refine ⟨.inl (⟨c.val.early,he⟩,⟨c.val.late,hl⟩),?_⟩
    apply Subtype.ext
    exact MarkedSelection.ext rfl rfl c.property.symm
  · refine ⟨.inr (⟨c.val.early,he⟩,⟨c.val.late,hl⟩),?_⟩
    apply Subtype.ext
    exact MarkedSelection.ext rfl rfl c.property.symm

def unmarkedEquiv (hp : 0 < p) (h : p+q=m+1) : UnmarkedChoices m p ≃ UnmarkedSelection m p q :=
  Equiv.ofBijective (unmarkedOfChoice hp h)
    ⟨unmarkedOfChoice_injective hp h,unmarkedOfChoice_surjective hp h⟩

def oneMarkedOfChoice (hp : 0 < p) (h : p+q=m+1) (s : OneMarkedChoices m p) : OneMarkedSelection m p q :=
  ⟨{
    early := s.2.1.val.map (Function.Embedding.subtype _)
    late := s.2.2.val.map (Function.Embedding.subtype _)
    marked := {s.1}
    early_disjoint_marked := by
      apply Finset.disjoint_singleton_right.mpr
      exact Finset.notMem_map_subtype_of_not_property _ (by simp)
    late_disjoint_marked := by
      apply Finset.disjoint_singleton_right.mpr
      exact Finset.notMem_map_subtype_of_not_property _ (by simp)
    first_degree := by simp only [Finset.card_map,Finset.card_singleton,s.2.1.property,s.2.2.property]; omega
    first_early_bound := by simp only [Finset.card_map,Finset.card_singleton,s.2.1.property]; omega
    second_early_bound := by simp only [Finset.card_map,s.2.1.property]; omega }, by simp⟩

theorem oneMarkedOfChoice_injective (hp : 0 < p) (h : p+q=m+1) :
    Function.Injective (oneMarkedOfChoice hp h) := by
  rintro ⟨e,x⟩ ⟨f,y⟩ hxy
  have hf := congrArg (fun c : OneMarkedSelection m p q => c.val.marked) hxy
  have hef : e=f := Finset.singleton_injective hf
  subst f
  have he := congrArg (fun c : OneMarkedSelection m p q => c.val.early) hxy
  have hl := congrArg (fun c : OneMarkedSelection m p q => c.val.late) hxy
  have hxe : x.1=y.1 := Subtype.ext (Finset.map_injective _ he)
  have hxl : x.2=y.2 := Subtype.ext (Finset.map_injective _ hl)
  have hxy := Prod.ext hxe hxl
  cases hxy
  rfl

theorem oneMarkedOfChoice_surjective (hp : 0 < p) (h : p+q=m+1) :
    Function.Surjective (oneMarkedOfChoice hp h) := by
  intro c
  obtain ⟨e,hf⟩ := Finset.card_eq_one.mp c.property
  have he : e ∉ c.val.early :=
    Finset.disjoint_singleton_right.mp (hf ▸ c.val.early_disjoint_marked)
  have hl : e ∉ c.val.late :=
    Finset.disjoint_singleton_right.mp (hf ▸ c.val.late_disjoint_marked)
  have hpe : ∀ x ∈ c.val.early, x ≠ e := fun x hx hxe => he (hxe ▸ hx)
  have hpl : ∀ x ∈ c.val.late, x ≠ e := fun x hx hxe => hl (hxe ▸ hx)
  obtain ⟨hce,hcl⟩ := oneMarked_sizes hp h c.val c.property
  have hmapE := Finset.subtype_map_of_mem hpe
  have hmapL := Finset.subtype_map_of_mem hpl
  have hcardE : (c.val.early.subtype (· ≠ e)).card=p-1 := by
    rw [← Finset.card_map (Function.Embedding.subtype (· ≠ e)),hmapE,hce]
  have hcardL : (c.val.late.subtype (· ≠ e)).card=p-1 := by
    rw [← Finset.card_map (Function.Embedding.subtype (· ≠ e)),hmapL,hcl]
  refine ⟨⟨e,(⟨_,hcardE⟩,⟨_,hcardL⟩)⟩,?_⟩
  apply Subtype.ext
  exact MarkedSelection.ext hmapE hmapL hf.symm

def oneMarkedEquiv (hp : 0 < p) (h : p+q=m+1) : OneMarkedChoices m p ≃ OneMarkedSelection m p q :=
  Equiv.ofBijective (oneMarkedOfChoice hp h) ⟨oneMarkedOfChoice_injective hp h,oneMarkedOfChoice_surjective hp h⟩

theorem unmarked_selection_count (hp : 0 < p) (h : p+q=m+1) :
    Fintype.card (UnmarkedSelection m p q) = 2 * Nat.choose m (p-1) * Nat.choose m p := by
  rw [← Fintype.card_congr (unmarkedEquiv hp h),card_unmarkedChoices]

theorem one_marked_selection_count (hp : 0 < p) (h : p+q=m+1) :
    Fintype.card (OneMarkedSelection m p q) = m * Nat.choose (m-1) (p-1)^2 := by
  rw [← Fintype.card_congr (oneMarkedEquiv hp h),card_oneMarkedChoices]

theorem marked_card_one_iff (h : p+q=m+1) (c : MarkedSelection m p q) :
    c.marked.card=1 ↔ c.marked ≠ ∅ := by
  have hb := c.marked_card_le_one h
  constructor
  · intro hz he
    rw [he] at hz
    simp at hz
  · intro hz
    have hn : c.marked.card ≠ 0 := fun hn => hz (Finset.card_eq_zero.mp hn)
    omega

def markedSelectionEquiv (h : p+q=m+1) : UnmarkedSelection m p q ⊕ OneMarkedSelection m p q ≃ MarkedSelection m p q :=
  (Equiv.sumCongr (Equiv.refl (UnmarkedSelection m p q))
    (Equiv.subtypeEquivRight (marked_card_one_iff h))).trans
    (Equiv.sumCompl (fun c : MarkedSelection m p q => c.marked=∅))

theorem marked_selection_signed_sum (hp : 0 < p) (h : p+q=m+1) :
    ∑ c : MarkedSelection m p q, (-1 : ℤ)^c.marked.card =
      2*(Nat.choose m (p-1) : ℤ)*Nat.choose m p -
        m*(Nat.choose (m-1) (p-1) : ℤ)^2 := by
  have hv (c : UnmarkedSelection m p q) : (-1 : ℤ)^c.val.marked.card=1 := by simp [c.property]
  have he (c : OneMarkedSelection m p q) : (-1 : ℤ)^c.val.marked.card = -1 := by rw [c.property,pow_one]
  rw [← (markedSelectionEquiv h).sum_comp (fun c => (-1 : ℤ)^c.marked.card),Fintype.sum_sum_type]
  change (∑ c : UnmarkedSelection m p q, (-1 : ℤ)^c.val.marked.card) +
    (∑ c : OneMarkedSelection m p q, (-1 : ℤ)^c.val.marked.card) = _
  simp only [hv,he,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [unmarked_selection_count hp h,one_marked_selection_count hp h]
  push_cast
  ring

end
end Schubert.RS.Family
