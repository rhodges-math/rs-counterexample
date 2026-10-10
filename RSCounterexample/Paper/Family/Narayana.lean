import RSCounterexample.Paper.Family.Sign
import Mathlib.Data.Nat.GCD.Basic

/-!
# Narayana numbers and the family coefficient

The Narayana number `N(r, k) = (1/r)·C(r, k)·C(r, k-1)` (`1 ≤ k ≤ r`) is defined as a natural
number, with the exact division proved (`narayana_dvd`). For `p + q = m + 1` the paper's
identity `N(p+q-1, p) = ((p+q-1)/(pq))·C(p+q-2, p-1)²` is `narayana_family`, and the
Narayana form of the family coefficient in (1.6),
`coefficientValue m p = N(m, p)·(2 - (p-2)(q-2))`, is `coefficientValue_eq_narayana`.
-/

namespace Schubert.RS.Family

/-- The Narayana number `N(r, k) = (1/r)·C(r, k)·C(r, k-1)`. The division is exact for
`1 ≤ k ≤ r` (`narayana_dvd`). -/
def narayana (r k : ℕ) : ℕ := r.choose k * r.choose (k - 1) / r

/-- `r` divides `C(r, k)·C(r, k-1)` for `1 ≤ k ≤ r`. With `r = n + 1` and `k = j + 1`,
`C(n+1, j+1)·C(n+1, j)·(n+2) = (n+1)·C(n, j)·C(n+2, j+1)`, and `n + 1` is coprime to `n + 2`. -/
theorem narayana_dvd {r k : ℕ} (hk : 1 ≤ k) (hkr : k ≤ r) :
    r ∣ r.choose k * r.choose (k - 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := ⟨r - 1, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  have h1 := Nat.add_one_mul_choose_eq n j
  have h2 := Nat.choose_mul_succ_eq n j
  obtain ⟨t, ht⟩ : ∃ t, n + 1 - j = t := ⟨_, rfl⟩
  rw [ht] at h2
  have hsum : n + 2 = (j + 1) + t := by omega
  have hmul : (n + 1).choose (j + 1) * (n + 1).choose j * (n + 2) =
      (n + 1) * (n.choose j * ((n + 1).choose j + (n + 1).choose (j + 1))) := by
    calc (n + 1).choose (j + 1) * (n + 1).choose j * (n + 2)
        = ((n + 1).choose (j + 1) * (j + 1)) * (n + 1).choose j +
            ((n + 1).choose j * t) * (n + 1).choose (j + 1) := by rw [hsum]; ring
      _ = ((n + 1) * n.choose j) * (n + 1).choose j +
            (n.choose j * (n + 1)) * (n + 1).choose (j + 1) := by rw [h1, h2]
      _ = (n + 1) * (n.choose j * ((n + 1).choose j + (n + 1).choose (j + 1))) := by ring
  have hcop : Nat.Coprime (n + 1) (n + 2) :=
    Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)
  exact hcop.dvd_of_dvd_mul_right ⟨_, hmul⟩

/-- `r·N(r, k) = C(r, k)·C(r, k-1)` for `1 ≤ k ≤ r`. -/
theorem mul_narayana {r k : ℕ} (hk : 1 ≤ k) (hkr : k ≤ r) :
    r * narayana r k = r.choose k * r.choose (k - 1) :=
  Nat.mul_div_cancel' (narayana_dvd hk hkr)

/-- The Narayana number as the rational number `(1/r)·C(r, k)·C(r, k-1)`. -/
theorem narayana_eq_rat {r k : ℕ} (hk : 1 ≤ k) (hkr : k ≤ r) :
    (narayana r k : ℚ) = (1 / (r : ℚ)) * r.choose k * r.choose (k - 1) := by
  have hr : (r : ℚ) ≠ 0 := by exact_mod_cast (show r ≠ 0 by omega)
  have h : (r : ℚ) * narayana r k = r.choose k * r.choose (k - 1) := by
    exact_mod_cast mul_narayana hk hkr
  rw [mul_assoc, ← h]
  field_simp

theorem narayana_pos {r k : ℕ} (hk : 1 ≤ k) (hkr : k ≤ r) : 0 < narayana r k := by
  have h := mul_narayana hk hkr
  have hc : 0 < r.choose k * r.choose (k - 1) :=
    Nat.mul_pos (Nat.choose_pos hkr) (Nat.choose_pos (by omega))
  rcases Nat.eq_zero_or_pos (narayana r k) with h0 | h0
  · rw [h0, mul_zero] at h
    omega
  · exact h0

/-- `N(p+q-1, p) = ((p+q-1)/(pq))·C(p+q-2, p-1)²`, cleared of denominators
(`m = p + q - 1`). -/
theorem narayana_family {m p q : ℕ} (hp : 0 < p) (hq : 0 < q) (h : p + q = m + 1) :
    (p : ℤ) * q * narayana m p = m * ((m - 1).choose (p - 1) : ℤ) ^ 2 := by
  have hm : (m : ℤ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hN : (m : ℤ) * narayana m p = (m.choose p : ℤ) * m.choose (p - 1) := by
    exact_mod_cast mul_narayana (r := m) (k := p) (by omega) (by omega)
  apply mul_left_cancel₀ hm
  calc (m : ℤ) * ((p : ℤ) * q * narayana m p)
      = p * q * ((m : ℤ) * narayana m p) := by ring
    _ = ((m.choose p : ℤ) * p) * ((m.choose (p - 1) : ℤ) * q) := by rw [hN]; ring
    _ = (m * ((m - 1).choose (p - 1) : ℤ)) * (m * ((m - 1).choose (p - 1) : ℤ)) := by
      rw [binomial_right hp hq h, binomial_left hp hq h]
    _ = m * (m * ((m - 1).choose (p - 1) : ℤ) ^ 2) := by ring

/-- The Narayana form of the family coefficient (1.6):
`coefficientValue m p = N(m, p)·(2 - (p-2)(q-2))` for `p + q = m + 1`. -/
theorem coefficientValue_eq_narayana {m p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (h : p + q = m + 1) :
    coefficientValue m p = narayana m p * (2 - ((p : ℤ) - 2) * ((q : ℤ) - 2)) := by
  have hpq : (p : ℤ) * q ≠ 0 := by positivity
  apply mul_left_cancel₀ hpq
  rw [coefficientValue_scaled hp hq h, ← narayana_family hp hq h]
  ring

end Schubert.RS.Family
