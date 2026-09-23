import Schubert.RS.Representation.KillingCommutators
import Mathlib.Tactic.NoncommRing

/-! Three-root identities used to transport the defining annihilators.
These are identities in actual associative rings and their modules; there
is no character or presentation hypothesis. -/

namespace Schubert.RS.Representation
noncomputable section
set_option maxHeartbeats 800000

theorem central_commutator_mul_pow {R : Type*} [Ring R] (A B C : R)
    (hBA : B * A = A * B + C) (hAC : Commute A C) (k : ℕ) :
    B * A ^ (k + 1) = A ^ (k + 1) * B + (k + 1) • (A ^ k * C) := by
  induction k with
  | zero => simpa using hBA
  | succ k ih =>
    calc
      B * A ^ (k+1+1) = (B * A ^ (k+1)) * A := by rw [pow_succ, mul_assoc]
      _ = (A ^ (k+1) * B + (k+1) • (A^k*C)) * A := by rw [ih]
      _ = A ^ (k+1) * (A*B+C) + (k+1) • (A^(k+1)*C) := by
        rw [add_mul, smul_mul_assoc, mul_assoc, hBA]
        congr 1
        congr 1
        rw [mul_assoc, ← hAC.eq, ← mul_assoc, ← pow_succ]
      _ = A ^ (k+1+1) * B + (k+1+1) • (A^(k+1)*C) := by
        rw [mul_add, ← mul_assoc, ← pow_succ]
        simp only [add_nsmul, one_nsmul]
        abel

theorem central_commutator_pow_mul {R : Type*} [Ring R] (A B C : R)
    (hBA : B*A=A*B+C) (hBC : Commute B C) (k : ℕ) :
    B^(k+1)*A = A*B^(k+1) + (k+1) • (B^k*C) := by
  have hAB : A*B=B*A+(-C) := by rw [hBA]; abel
  have h := central_commutator_mul_pow B A (-C) hAB hBC.neg_right k
  simp only [mul_neg, smul_neg] at h
  rw [h]
  abel

theorem central_commutator_neg_orientation {R : Type*} [Ring R] (A B C : R)
    (h : A*B=B*A+C) : B*(-A)=(-A)*B+C := by
  rw [mul_neg, neg_mul, h]
  abel

/-- Commuting across m copies of A can increase the required B exponent
by at most m. The centrality requirement is explicit. -/
theorem heisenberg_pow_kills_after_pow {X : Type*} [AddCommGroup X] [Module ℂ X]
    (A B C : Module.End ℂ X) (hBA : B*A=A*B+C) (hBC : Commute B C)
    (q m : ℕ) (x : X) (hB : (B^q) x=0) : (B^(q+m)) ((A^m) x)=0 := by
  induction m with
  | zero => simpa using hB
  | succ m ih =>
    have h := congrArg (fun D : Module.End ℂ X => D ((A^m) x))
      (central_commutator_pow_mul A B C hBA hBC (q+m))
    have hc : (B^(q+m)) (C ((A^m) x))=0 := by
      rw [← Module.End.mul_apply, (hBC.pow_left (q+m)).eq,
        Module.End.mul_apply, ih, map_zero]
    have hb : (B^(q+m+1)) ((A^m) x)=0 := by
      rw [pow_succ', Module.End.mul_apply, ih, map_zero]
    change (B^(q+m+1)) (A ((A^m) x)) =
      A ((B^(q+m+1)) ((A^m) x)) + (q+m+1) • ((B^(q+m)) (C ((A^m) x))) at h
    rw [hb, hc, map_zero, smul_zero, add_zero] at h
    simpa only [pow_succ', Module.End.mul_apply, Nat.add_assoc] using h

theorem heisenberg_pow_of_linear_killing {X : Type*} [AddCommGroup X] [Module ℂ X]
    (A B C : Module.End ℂ X) (hBA : B*A=A*B+C)
    (hAC : Commute A C) (hBC : Commute B C)
    (m p : ℕ) (x : X) (hB : B x=0) (hC : (C^p) x=0) :
    (B^p) ((A^m) x)=0 := by
  induction m generalizing p x with
  | zero =>
    cases p with
    | zero => simpa using hC
    | succ p => simp only [pow_zero, Module.End.one_apply, pow_succ,
        Module.End.mul_apply, hB, map_zero]
  | succ m ih =>
    cases p with
    | zero => simpa using congrArg (A^(m+1)) hC
    | succ p =>
      have hb := ih (p+1) x hB hC
      have hcB : B (C x)=0 := by
        rw [← Module.End.mul_apply, hBC.eq, Module.End.mul_apply, hB, map_zero]
      have hcC : (C^p) (C x)=0 := by
        simpa only [pow_succ, Module.End.mul_apply] using hC
      have hc := ih p (C x) hcB hcC
      have hcomm : C ((A^m) x)=(A^m) (C x) :=
        congrArg (fun D : Module.End ℂ X => D x) ((hAC.pow_left m).eq.symm)
      have h := congrArg (fun D : Module.End ℂ X => D ((A^m) x))
        (central_commutator_pow_mul A B C hBA hBC p)
      change (B^(p+1)) (A ((A^m) x)) =
        A ((B^(p+1)) ((A^m) x)) + (p+1) • ((B^p) (C ((A^m) x))) at h
      rw [hb, hcomm, hc, map_zero, smul_zero, add_zero] at h
      simpa only [pow_succ', Module.End.mul_apply] using h

/-- If A kills x after m+1 steps and B kills x after p steps, then the
central commutator kills the top A-string vector after p steps. -/
theorem heisenberg_top_annihilator {X : Type*} [AddCommGroup X] [Module ℂ X]
    (A B C : Module.End ℂ X) (hBA : B*A = A*B+C)
    (hAC : Commute A C) (hBC : Commute B C) (p m : ℕ) (x : X)
    (hA : (A^(m+1)) x = 0) (hB : (B^p) x = 0) :
    (A^m) ((C^p) x) = 0 := by
  induction p generalizing m x with
  | zero => simpa using congrArg (A^m) hB
  | succ p ih =>
    have hA' : (A^(m+2)) x = 0 := by
      rw [show m+2=(m+1)+1 by omega, pow_succ', Module.End.mul_apply, hA, map_zero]
    have hBA' := congrArg (fun D : Module.End ℂ X => D x)
      (central_commutator_mul_pow A B C hBA hAC (m+1))
    have hCA : (A^(m+1)) (C x) = 0 := by
      rw [← Module.End.mul_apply, (hAC.pow_left (m+1)).eq, Module.End.mul_apply, hA, map_zero]
    have hAB : (A^(m+2)) (B x) = 0 := by
      simpa only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply,
        hA', hCA, map_zero, smul_zero, add_zero] using hBA'.symm
    have hBB : (B^p) (B x) = 0 := by
      simpa only [pow_succ, Module.End.mul_apply] using hB
    have hstep := ih (m+1) (B x) hAB hBB
    have htop : (A^(m+1)) ((C^p) x) = 0 := by
      rw [← Module.End.mul_apply, ((hAC.pow_left (m+1)).pow_right p).eq,
        Module.End.mul_apply, hA, map_zero]
    have h := congrArg (fun D : Module.End ℂ X => D ((C^p) x))
      (central_commutator_mul_pow A B C hBA hAC m)
    have hcomm : B ((C^p) x) = (C^p) (B x) := by
      exact congrArg (fun D : Module.End ℂ X => D x) ((hBC.pow_right p).eq)
    have hz : (m+1) • ((A^m) ((C^(p+1)) x)) = 0 := by
      change B ((A^(m+1)) ((C^p) x)) =
        (A^(m+1)) (B ((C^p) x)) + (m+1) • ((A^m) (C ((C^p) x))) at h
      rw [htop, map_zero, hcomm, hstep, zero_add] at h
      simpa only [pow_succ', Module.End.mul_apply] using h.symm
    have hz' : ((m+1 : ℕ) : ℂ) • ((A^m) ((C^(p+1)) x)) = 0 := by
      simpa only [Nat.cast_smul_eq_nsmul] using hz
    exact (smul_eq_zero.mp hz').resolve_left (by exact_mod_cast Nat.succ_ne_zero m)

/-- The two annihilating exponents exchange at the top of an A-string.
The disjunction is exactly the two cases introduced by truncated natural
subtraction in the Joseph--Polo exponents. -/
theorem heisenberg_top_two_bounds {X : Type*} [AddCommGroup X] [Module ℂ X]
    (A B C : Module.End ℂ X) (hBA : B*A=A*B+C)
    (hAC : Commute A C) (hBC : Commute B C)
    (m p q : ℕ) (hpq : q=p+m ∨ p=1) (x : X)
    (hA : (A^(m+1)) x=0) (hB : (B^p) x=0) (hC : (C^q) x=0) :
    (B^q) ((A^m) x)=0 ∧ (C^p) ((A^m) x)=0 := by
  constructor
  · rcases hpq with hq | hp
    · rw [hq]
      exact heisenberg_pow_kills_after_pow A B C hBA hBC p m x hB
    · have hb : B x=0 := by simpa [hp] using hB
      exact heisenberg_pow_of_linear_killing A B C hBA hAC hBC m q x hb hC
  · rw [← Module.End.mul_apply, ((hAC.pow_left m).pow_right p).eq.symm,
      Module.End.mul_apply]
    exact heisenberg_top_annihilator A B C hBA hAC hBC p m x hA hB

theorem neg_end_pow_apply {X : Type*} [AddCommGroup X] [Module ℂ X]
    (A : Module.End ℂ X) (m : ℕ) (x : X) :
    ((-A)^m) x = (-1 : ℂ)^m • ((A^m) x) := by
  induction m with
  | zero => simp
  | succ m ih =>
    simp only [pow_succ', Module.End.mul_apply, LinearMap.neg_apply,
      ih, map_smul, neg_one_mul, neg_smul, smul_neg]

end
end Schubert.RS.Representation
