import Schubert.RS.Representation.KillingCommutators

namespace Schubert.RS.Representation
noncomputable section

def rootWord {n : ℕ} (roots : List (PositiveRoot n)) : Enveloping n :=
  (roots.map rootOperator).prod

@[simp] theorem rootWord_nil {n : ℕ} : rootWord ([] : List (PositiveRoot n)) = 1 := rfl
@[simp] theorem rootWord_cons {n : ℕ} (r : PositiveRoot n) (roots : List (PositiveRoot n)) :
    rootWord (r :: roots) = rootOperator r * rootWord roots := rfl

abbrev IsKillingWord {n : ℕ} (u : Fin n → ℕ) (roots : List (PositiveRoot n)) : Prop :=
  ∀ r ∈ roots, u r.val.2 ≤ u r.val.1

/-- Strictly shorter NONEMPTY killing words. Excluding the empty word keeps
straightening in the augmentation ideal. -/
def shorterKillingSpan {n : ℕ} (u : Fin n → ℕ) (d : ℕ) : Submodule ℂ (Enveloping n) :=
  Submodule.span ℂ {a | ∃ roots : List (PositiveRoot n),
    IsKillingWord u roots ∧ 0 < roots.length ∧ roots.length < d ∧ a = rootWord roots}

theorem shorterKillingSpan_left {n : ℕ} (u : Fin n → ℕ) (d : ℕ)
    (r : PositiveRoot n) (hr : u r.val.2 ≤ u r.val.1)
    {a : Enveloping n} (ha : a ∈ shorterKillingSpan u d) :
    rootOperator r * a ∈ shorterKillingSpan u (d + 1) := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨roots, hk, hn, hd, rfl⟩ := ha
    apply Submodule.subset_span
    refine ⟨r :: roots, ?_, by simp, by simpa using Nat.add_lt_add_right hd 1, rfl⟩
    intro s hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact hr
    · exact hk s hs
  | zero => simp
  | add a b ha hb ia ib => simpa only [mul_add] using (shorterKillingSpan u (d + 1)).add_mem ia ib
  | smul c a ha ia =>
    rw [mul_smul_comm]
    exact (shorterKillingSpan u (d + 1)).smul_mem c ia

theorem killingOperatorSpan_mul_word {n : ℕ} (u : Fin n → ℕ)
    (roots : List (PositiveRoot n)) (hk : IsKillingWord u roots)
    {a : Enveloping n} (ha : a ∈ killingOperatorSpan u) :
    a * rootWord roots ∈ shorterKillingSpan u (roots.length + 2) := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨r, hr, rfl⟩ := ha
    apply Submodule.subset_span
    refine ⟨r :: roots, ?_, by simp, by simp, rfl⟩
    intro s hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact hr
    · exact hk s hs
  | zero => simp
  | add a b ha hb ia ib => simpa only [add_mul] using (shorterKillingSpan u _).add_mem ia ib
  | smul c a ha ia =>
    rw [smul_mul_assoc]
    exact (shorterKillingSpan u _).smul_mem c ia

/-- Exchanging generators changes the product only by strictly shorter
nonempty killing words. This is proved by permutation induction, using the
actual type-A commutator relations, not an assumed straightening theorem. -/
theorem killingWord_perm_difference {n : ℕ} (u : Fin n → ℕ)
    {roots other : List (PositiveRoot n)} (hp : roots.Perm other)
    (hk : IsKillingWord u roots) :
    rootWord roots - rootWord other ∈ shorterKillingSpan u roots.length := by
  revert hk
  induction hp with
  | nil => intro _; simp
  | @cons r roots other hp ih =>
    intro hk
    have hr := hk r (List.mem_cons_self ..)
    have htail : IsKillingWord u roots := fun s hs => hk s (List.mem_cons_of_mem r hs)
    have hh := shorterKillingSpan_left u roots.length r hr (ih htail)
    simpa only [rootWord_cons, mul_sub, List.length_cons] using hh
  | swap r s roots =>
    intro hk
    have hr := hk r (by simp)
    have hs := hk s (by simp)
    have htail : IsKillingWord u roots := fun t ht => hk t (by simp [ht])
    have hh := killingOperatorSpan_mul_word u roots htail (killing_commutator_mem u s r hs hr)
    simpa only [rootWord_cons, List.length_cons, sub_mul, mul_assoc, Nat.add_assoc] using hh
  | @trans roots middle other hp hq ihp ihq =>
    intro hk
    have hm : IsKillingWord u middle := fun r hr => hk r (hp.mem_iff.mpr hr)
    have h₁ := ihp hk
    have h₂ := ihq hm
    rw [← hp.length_eq] at h₂
    have hh := (shorterKillingSpan u roots.length).add_mem h₁ h₂
    convert hh using 1 <;> abel

end
end Schubert.RS.Representation
