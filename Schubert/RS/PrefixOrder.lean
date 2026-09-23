import Schubert.RS.RootWeights
import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Data.Fin.Rev

/-! Prefix order and its extremal-permutation bound for the dominant pairing. -/

namespace Schubert.RS
noncomputable section
variable {n : ℕ}

def PrefixLE (v w : Weight n) : Prop := ∀ k, prefixWeight v k ≤ prefixWeight w k

theorem prefixWeight_injective : Function.Injective (prefixWeight (n := n)) := by
  intro v w h
  funext j
  have hs := congrFun h j.succ
  have hp := congrFun h j.castSucc
  rw [prefixWeight_succ, prefixWeight_succ] at hs
  omega

theorem PrefixLE.refl (v : Weight n) : PrefixLE v v := fun _ => le_rfl

theorem PrefixLE.trans {u v w : Weight n} (huv : PrefixLE u v) (hvw : PrefixLE v w) :
    PrefixLE u w := fun k => le_trans (huv k) (hvw k)

theorem PrefixLE.antisymm {v w : Weight n} (hvw : PrefixLE v w) (hwv : PrefixLE w v) : v = w :=
  prefixWeight_injective (funext fun k => le_antisymm (hvw k) (hwv k))

theorem prefixLE_add_rootWeight (w : Weight n) (d : Fin (n-1) →₀ ℕ) :
    PrefixLE w (w + rootWeight d) := by
  intro k
  rw [prefixWeight_add, prefixWeight_rootWeight]
  unfold extendedRootDegree
  split_ifs <;> omega

/-- The increasing rearrangement is minimal in prefix order among all
permutations. The proof is the ordinary rearrangement inequality with a
prefix indicator; repeated entries require no strictness assumption. -/
theorem prefixLE_monotone_permutation (v : Weight n) (hv : Monotone v)
    (σ : Equiv.Perm (Fin n)) : PrefixLE v (fun i => v (σ i)) := by
  intro k
  let f : Fin n → ℤ := fun i => if i.val < k.val then 1 else 0
  have hfg : Antivary f v := by
    intro i j hij
    have hlt : i < j := by
      by_contra hn
      have hh := hv (le_of_not_gt hn)
      omega
    have hval : i.val < j.val := hlt
    dsimp [f]
    split_ifs <;> omega
  have h := hfg.sum_mul_le_sum_mul_comp_perm (σ := σ)
  simpa only [f, ite_mul, one_mul, zero_mul, ← Finset.sum_filter, prefixWeight] using h

theorem prefixLE_reverse_dominant (u : Composition n) (hu : Antitone u)
    (σ : Equiv.Perm (Fin n)) :
    PrefixLE (fun i => (u i.rev : ℤ)) (fun i => (u (σ i) : ℤ)) := by
  let r : Equiv.Perm (Fin n) :=
    { toFun := Fin.rev
      invFun := Fin.rev
      left_inv := Fin.rev_rev
      right_inv := Fin.rev_rev }
  have hm : Monotone (fun i : Fin n => (u i.rev : ℤ)) := by
    intro i j hij
    have hh : j.rev ≤ i.rev := by simpa using hij
    change (u i.rev : ℤ) ≤ (u j.rev : ℤ)
    exact_mod_cast hu hh
  have h := prefixLE_monotone_permutation (fun i => (u i.rev : ℤ)) hm (σ.trans r)
  simpa [r] using h

end
end Schubert.RS
