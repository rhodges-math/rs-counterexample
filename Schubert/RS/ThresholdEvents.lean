import Schubert.RS.ThresholdPaths
import Mathlib.Order.Interval.Finset.Fin

/-! Each threshold is one east step, and all other steps are north steps. -/

namespace Schubert.RS
noncomputable section
variable {k y : ℕ} (s : ℕ) (r : Fin k → Fin (y+1))
variable (hr : Monotone (fun q => (r q).val))

include hr in
theorem thresholdHorizontal_at_east (q : Fin k) :
    thresholdHorizontal s r (eastTime s r q) = (s+q.val+1 : ℕ) := by
  have he : thresholdSet (eastTime s r) (eastTime s r q) = Finset.Iic q := by
    apply Finset.ext
    intro p
    change (p ∈ Finset.univ.filter (fun p => eastTime s r p ≤ eastTime s r q)) ↔ p ∈ Finset.Iic q
    rw [Finset.mem_filter]
    simp only [Finset.mem_univ, true_and, Finset.mem_Iic]
    exact (eastTime_strictMono s r hr).le_iff_le
  simp only [thresholdHorizontal, he, Fin.card_Iic]
  omega

include hr in
theorem thresholdHorizontal_before_east (q : Fin k) :
    thresholdHorizontal s r (eastTime s r q-1) = (s+q.val : ℕ) := by
  have he : thresholdSet (eastTime s r) (eastTime s r q-1) = Finset.Iio q := by
    apply Finset.ext
    intro p
    change (p ∈ Finset.univ.filter (fun p => eastTime s r p ≤ eastTime s r q-1)) ↔ p ∈ Finset.Iio q
    rw [Finset.mem_filter]
    simp only [Finset.mem_univ, true_and, Finset.mem_Iio]
    have hp := (eastTime_strictMono s r hr).lt_iff_lt (a := p) (b := q)
    have hpos : 0 < eastTime s r q := by unfold eastTime; omega
    omega
  simp only [thresholdHorizontal, he, Fin.card_Iio]
  omega

theorem thresholdHorizontal_no_east (t : ℕ) (ht : 0 < t)
    (hn : ∀ q, eastTime s r q ≠ t) :
    thresholdHorizontal s r (t-1) = thresholdHorizontal s r t := by
  have he : thresholdSet (eastTime s r) (t-1) = thresholdSet (eastTime s r) t := by
    apply Finset.ext
    intro q
    change (q ∈ Finset.univ.filter (fun q => eastTime s r q ≤ t-1)) ↔
      q ∈ Finset.univ.filter (fun q => eastTime s r q ≤ t)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hq := hn q
    omega
  simp only [thresholdHorizontal, he]

end
end Schubert.RS
