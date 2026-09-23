import Schubert.RS.RootDegrees

/-! Convert nonnegative simple-root coordinates back to ordinary torus weights. -/

namespace Schubert.RS
noncomputable section
variable {n : ℕ}

/-- Discrete difference of the simple-root prefix coordinates, with zero
boundary values. This works also in ranks zero and one. -/
def rootWeight (d : Fin (n-1) →₀ ℕ) (j : Fin n) : ℤ :=
  (if h : j.val < n-1 then (d ⟨j.val, h⟩ : ℤ) else 0) -
    (if h : 0 < j.val then (d ⟨j.val-1, by omega⟩ : ℤ) else 0)

@[simp] theorem rootWeight_zero : rootWeight (0 : Fin (n-1) →₀ ℕ) = 0 := by
  funext j
  simp [rootWeight]

theorem rootWeight_add (d e : Fin (n-1) →₀ ℕ) :
    rootWeight (d+e) = rootWeight d + rootWeight e := by
  funext j
  simp only [rootWeight, Finsupp.add_apply, Nat.cast_add, Pi.add_apply]
  split_ifs <;> ring

def rootWeightHom : (Fin (n-1) →₀ ℕ) →+ Weight n where
  toFun := rootWeight
  map_zero' := rootWeight_zero
  map_add' := rootWeight_add

theorem rootWeight_nsmul (r : ℕ) (d : Fin (n-1) →₀ ℕ) :
    rootWeight (r • d) = r • rootWeight d := rootWeightHom.map_nsmul r d

/-- Root intervals and ordinary matrix-root weights agree, including roots
touching the first or last coordinate. -/
theorem rootWeight_rootDegree (a b : Fin n) (hab : a < b) :
    rootWeight (rootDegree a b) = positiveRoot a b := by
  funext j
  have hij : a.val < b.val := hab
  have ha := a.isLt
  have hb := b.isLt
  have hj := j.isLt
  simp only [rootWeight, rootDegree_apply, positiveRoot, Pi.sub_apply, Pi.single_apply]
  split_ifs <;> simp_all [Fin.ext_iff] <;> omega

theorem prefixWeight_zero (w : Weight n) : prefixWeight w 0 = 0 := by
  simp [prefixWeight]

theorem prefixWeight_succ (w : Weight n) (j : Fin n) :
    prefixWeight w j.succ = prefixWeight w j.castSucc + w j := by
  classical
  have he : Finset.univ.filter (fun i : Fin n => i.val < j.succ.val) =
      insert j (Finset.univ.filter (fun i : Fin n => i.val < j.castSucc.val)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Fin.val_succ, Fin.val_castSucc, Fin.ext_iff]
    omega
  have hn : j ∉ Finset.univ.filter (fun i : Fin n => i.val < j.castSucc.val) := by simp
  unfold prefixWeight
  rw [he, Finset.sum_insert hn, add_comm]

theorem prefixWeight_discrete (v : Fin (n+1) → ℤ) (k : Fin (n+1)) :
    prefixWeight (fun j : Fin n => v j.succ - v j.castSucc) k = v k - v 0 := by
  induction k using Fin.induction with
  | zero => simp [prefixWeight_zero]
  | succ j ih =>
    rw [prefixWeight_succ, ih]
    ring

def extendedRootDegree (d : Fin (n-1) →₀ ℕ) (k : Fin (n+1)) : ℤ :=
  if h : 0 < k.val ∧ k.val < n then (d ⟨k.val-1, by omega⟩ : ℤ) else 0

theorem rootWeight_discrete (d : Fin (n-1) →₀ ℕ) :
    rootWeight d = fun j : Fin n => extendedRootDegree d j.succ - extendedRootDegree d j.castSucc := by
  funext j
  simp only [rootWeight, extendedRootDegree, Fin.val_succ, Fin.val_castSucc]
  split_ifs <;> simp_all <;> omega

theorem prefixWeight_rootWeight (d : Fin (n-1) →₀ ℕ) (k : Fin (n+1)) :
    prefixWeight (rootWeight d) k = extendedRootDegree d k := by
  rw [rootWeight_discrete, prefixWeight_discrete]
  simp [extendedRootDegree]

theorem prefixWeight_rootWeight_cut (d : Fin (n-1) →₀ ℕ) (k : Fin (n-1)) :
    prefixWeight (rootWeight d) ⟨k.val+1, by omega⟩ = (d k : ℤ) := by
  rw [prefixWeight_rootWeight]
  have hk : k.val + 1 < n := by have h := k.isLt; omega
  simp [extendedRootDegree, hk]

theorem rootWeight_injective : Function.Injective (rootWeight (n := n)) := by
  intro d e h
  ext k
  have he := congrArg (fun w => prefixWeight w ⟨k.val+1, by omega⟩) h
  rw [prefixWeight_rootWeight_cut, prefixWeight_rootWeight_cut] at he
  exact_mod_cast he

theorem rootWeight_sum_zero (d : Fin (n-1) →₀ ℕ) : ∑ i, rootWeight d i = 0 := by
  have h := prefixWeight_rootWeight d (Fin.last n)
  simpa [prefixWeight, extendedRootDegree] using h

namespace Counterexample

theorem rootWeight_coefficientBox : rootWeight coefficientBox = targetDifference := by decide

end Counterexample

end
end Schubert.RS
