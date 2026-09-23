import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-! The exact binomial factorization and strict sign criterion, using signed
integer differences even when p or q equals one. -/

namespace Schubert.RS.Family
noncomputable section
variable {m p q : ℕ}

def coefficientValue (m p : ℕ) : ℤ :=
  2*(Nat.choose m (p-1) : ℤ)*Nat.choose m p - m*(Nat.choose (m-1) (p-1) : ℤ)^2

theorem binomial_left (hp : 0 < p) (hq : 0 < q) (h : p+q=m+1) :
    (Nat.choose m (p-1) : ℤ)*q = m*Nat.choose (m-1) (p-1) := by
  have hm : m-1+1=m := by omega
  have ht : m-(p-1)=q := by omega
  have he := Nat.choose_mul_succ_eq (m-1) (p-1)
  rw [hm,ht] at he
  have hz : (Nat.choose (m-1) (p-1) : ℤ)*m = (Nat.choose m (p-1) : ℤ)*q := by
    exact_mod_cast he
  rw [← hz,mul_comm]

theorem binomial_right (hp : 0 < p) (hq : 0 < q) (h : p+q=m+1) :
    (Nat.choose m p : ℤ)*p = m*Nat.choose (m-1) (p-1) := by
  have hm : m-1+1=m := by omega
  have hp' : p-1+1=p := by omega
  have he := Nat.add_one_mul_choose_eq (m-1) (p-1)
  rw [hm,hp'] at he
  exact_mod_cast he.symm

theorem coefficientValue_scaled (hp : 0 < p) (hq : 0 < q) (h : p+q=m+1) :
    (p : ℤ)*q*coefficientValue m p =
      m*(Nat.choose (m-1) (p-1) : ℤ)^2*(2-((p : ℤ)-2)*((q : ℤ)-2)) := by
  have hz : (p : ℤ)+q=m+1 := by exact_mod_cast h
  have hi : (2*m : ℤ)-p*q=2-((p : ℤ)-2)*((q : ℤ)-2) := by nlinarith
  calc
    (p : ℤ)*q*coefficientValue m p =
      2*((Nat.choose m (p-1) : ℤ)*q)*((Nat.choose m p : ℤ)*p) -
        (p : ℤ)*q*m*(Nat.choose (m-1) (p-1) : ℤ)^2 := by unfold coefficientValue; ring
    _ = m*(Nat.choose (m-1) (p-1) : ℤ)^2*((2*m : ℤ)-p*q) := by
      rw [binomial_left hp hq h,binomial_right hp hq h]
      ring
    _ = _ := by rw [hi]

theorem coefficientValue_factorization (hp : 0 < p) (hq : 0 < q) (h : p+q=m+1) :
    (coefficientValue m p : ℚ) =
      (m : ℚ)/((p : ℚ)*q)*(Nat.choose (m-1) (p-1) : ℚ)^2*
        (2-((p : ℚ)-2)*((q : ℚ)-2)) := by
  have he : (p : ℚ)*q*(coefficientValue m p : ℚ) =
      m*(Nat.choose (m-1) (p-1) : ℚ)^2*(2-((p : ℚ)-2)*((q : ℚ)-2)) := by
    exact_mod_cast coefficientValue_scaled hp hq h
  have hp' : (p : ℚ) ≠ 0 := by positivity
  have hq' : (q : ℚ) ≠ 0 := by positivity
  field_simp
  nlinarith [he]

theorem coefficientValue_negative_iff (hp : 0 < p) (hq : 0 < q) (h : p+q=m+1) :
    coefficientValue m p < 0 ↔ 2 < ((p : ℤ)-2)*((q : ℤ)-2) := by
  have hm : 0 < m := by omega
  have hc : 0 < Nat.choose (m-1) (p-1) := Nat.choose_pos (by omega)
  have hpq : 0 < (p : ℤ)*q := by positivity
  have hmc : 0 < (m : ℤ)*(Nat.choose (m-1) (p-1) : ℤ)^2 := by positivity
  have hl : (p : ℤ)*q*coefficientValue m p < 0 ↔ coefficientValue m p < 0 := by
    simp [mul_neg_iff,hpq,not_lt_of_ge hpq.le]
  have hr : (m : ℤ)*(Nat.choose (m-1) (p-1) : ℤ)^2*
      (2-((p : ℤ)-2)*((q : ℤ)-2)) < 0 ↔
      (2-((p : ℤ)-2)*((q : ℤ)-2)) < 0 := by
    simp [mul_neg_iff,hmc,not_lt_of_ge hmc.le]
  rw [← hl,coefficientValue_scaled hp hq h,hr]
  omega

end
end Schubert.RS.Family
