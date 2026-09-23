import Schubert.RS.JosephPolo.Heisenberg

/-! Mixed annihilators for a three-root subsystem. The proof is a finite
induction, not an appeal to a highest-weight presentation. -/

namespace Schubert.RS.Representation
noncomputable section
set_option maxHeartbeats 1200000

/-- Two simple-root bounds force every mixed B,C monomial of total
degree m+p+1 to vanish, even after an arbitrary A power on the right. -/
theorem heisenberg_mixed_annihilator {X : Type*} [AddCommGroup X] [Module ℂ X]
    (A B C : Module.End ℂ X) (hBA : B*A=A*B+C)
    (hAC : Commute A C) (hBC : Commute B C)
    (m p : ℕ) (x : X) (hA : (A^(m+1)) x=0) (hB : (B^(p+1)) x=0)
    (d : ℕ) (hd : d ≤ m+p+1) (j : ℕ) :
    (B^(m+p+1-d)) ((C^d) ((A^j) x))=0 := by
  induction d generalizing j with
  | zero =>
    simp only [Nat.sub_zero, pow_zero, Module.End.one_apply]
    by_cases hj : j ≤ m
    · have hz := heisenberg_pow_kills_after_pow A B C hBA hBC (p+1) j x hB
      have he : m+p+1 = (m-j)+(p+1+j) := by omega
      rw [he, pow_add, Module.End.mul_apply, hz, map_zero]
    · have he : j = (j-(m+1))+(m+1) := by omega
      have hz : (A^j) x=0 := by
        rw [he, pow_add, Module.End.mul_apply, hA, map_zero]
      rw [hz, map_zero]
  | succ d ih =>
    have hd' : d ≤ m+p+1 := by omega
    let k := m+p+1-(d+1)
    have hk : k+1=m+p+1-d := by dsimp [k]; omega
    have hz (l : ℕ) : (B^(k+1)) ((C^d) ((A^l) x))=0 := by
      rw [hk]
      exact ih hd' l
    have hc : A ((C^d) ((A^j) x)) = (C^d) ((A^(j+1)) x) := by
      rw [pow_succ', Module.End.mul_apply]
      exact congrArg (fun D : Module.End ℂ X => D ((A^j) x)) ((hAC.pow_right d).eq)
    have h := congrArg (fun D : Module.End ℂ X => D ((C^d) ((A^j) x)))
      (central_commutator_pow_mul A B C hBA hBC k)
    change (B^(k+1)) (A ((C^d) ((A^j) x))) =
      A ((B^(k+1)) ((C^d) ((A^j) x))) +
        (k+1) • ((B^k) (C ((C^d) ((A^j) x)))) at h
    rw [hc, hz (j+1), hz j, map_zero, zero_add] at h
    have hz' : ((k+1 : ℕ) : ℂ) • ((B^k) ((C^(d+1)) ((A^j) x)))=0 := by
      simpa only [Nat.cast_smul_eq_nsmul, pow_succ', Module.End.mul_apply] using h.symm
    exact (smul_eq_zero.mp hz').resolve_left (by exact_mod_cast Nat.succ_ne_zero k)

theorem heisenberg_central_power_kills {X : Type*} [AddCommGroup X] [Module ℂ X]
    (A B C : Module.End ℂ X) (hBA : B*A=A*B+C)
    (hAC : Commute A C) (hBC : Commute B C)
    (m p : ℕ) (x : X) (hA : (A^(m+1)) x=0) (hB : (B^(p+1)) x=0) :
    (C^(m+p+1)) x=0 := by
  simpa using heisenberg_mixed_annihilator A B C hBA hAC hBC m p x hA hB
    (m+p+1) le_rfl 0

/-- The relation needed when a lowering operator differentiates the
long-root power in the Joseph--Polo left ideal. -/
theorem heisenberg_central_boundary_kills {X : Type*} [AddCommGroup X] [Module ℂ X]
    (A B C : Module.End ℂ X) (hBA : B*A=A*B+C)
    (hAC : Commute A C) (hBC : Commute B C)
    (m p : ℕ) (x : X) (hA : (A^(m+1)) x=0) (hB : (B^(p+1)) x=0) :
    (C^(m+p)) (B x)=0 := by
  have h := heisenberg_mixed_annihilator A B C hBA hAC hBC m p x hA hB
    (m+p) (by omega) 0
  have he : m+p+1-(m+p)=1 := by omega
  rw [he, pow_one, pow_zero, Module.End.one_apply] at h
  rw [← Module.End.mul_apply, (hBC.pow_right (m+p)).eq, Module.End.mul_apply] at h
  exact h

end
end Schubert.RS.Representation
