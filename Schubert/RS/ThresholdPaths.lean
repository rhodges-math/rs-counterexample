import Schubert.RS.LatticePathOrder
import Mathlib.Data.Finset.Card
import Mathlib.Order.Fin.Basic

/-! Weakly increasing east-step heights give genuine north/east paths. -/

namespace Schubert.RS
noncomputable section

def eastTime {k y : ℕ} (s : ℕ) (r : Fin k → Fin (y+1)) (q : Fin k) : ℕ :=
  s+q.val+(r q).val+1

theorem eastTime_strictMono {k y : ℕ} (s : ℕ) (r : Fin k → Fin (y+1))
    (hr : Monotone (fun q => (r q).val)) : StrictMono (eastTime s r) := by
  intro q p h
  have hv : q.val < p.val := h
  have hh := hr h.le
  change (r q).val ≤ (r p).val at hh
  unfold eastTime
  omega

def thresholdSet {k : ℕ} (e : Fin k → ℕ) (t : ℕ) : Finset (Fin k) :=
  Finset.univ.filter (fun q => e q ≤ t)

theorem thresholdSet_mono {k : ℕ} (e : Fin k → ℕ) {t u : ℕ} (h : t ≤ u) :
    thresholdSet e t ⊆ thresholdSet e u := by
  intro q hq
  simp only [thresholdSet, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
  omega

theorem thresholdSet_card_succ {k : ℕ} (e : Fin k → ℕ) (he : Function.Injective e) (t : ℕ) :
    (thresholdSet e (t+1)).card ≤ (thresholdSet e t).card+1 := by
  have hu : thresholdSet e (t+1) = thresholdSet e t ∪
      Finset.univ.filter (fun q => e q = t+1) := by
    apply Finset.ext
    intro q
    simp only [thresholdSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    omega
  have hd : Disjoint (thresholdSet e t) (Finset.univ.filter (fun q => e q = t+1)) := by
    apply Finset.disjoint_left.mpr
    intro q hq hp
    simp only [thresholdSet, Finset.mem_filter, Finset.mem_univ, true_and] at hq hp
    omega
  have hc : (Finset.univ.filter (fun q => e q = t+1)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro q hq p hp
    apply he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq hp
    omega
  rw [hu, Finset.card_union_of_disjoint hd]
  omega

def thresholdHorizontal {k y : ℕ} (s : ℕ) (r : Fin k → Fin (y+1)) (t : ℕ) : ℤ :=
  s+(thresholdSet (eastTime s r) t).card

theorem thresholdHorizontal_source {k y : ℕ} (s : ℕ) (r : Fin k → Fin (y+1)) :
    thresholdHorizontal s r s = s := by
  have he : thresholdSet (eastTime s r) s = ∅ := by
    apply Finset.ext
    intro q
    change (q ∈ Finset.univ.filter (fun q => eastTime s r q ≤ s)) ↔ q ∈ (∅ : Finset (Fin k))
    rw [Finset.mem_filter]
    simp only [Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
    change ¬s+q.val+(r q).val+1 ≤ s
    omega
  simp [thresholdHorizontal, he]

theorem thresholdHorizontal_target {k y : ℕ} (s : ℕ) (r : Fin k → Fin (y+1)) :
    thresholdHorizontal s r (s+k+y) = (s+k : ℕ) := by
  have he : thresholdSet (eastTime s r) (s+k+y) = Finset.univ := by
    apply Finset.ext
    intro q
    change (q ∈ Finset.univ.filter (fun q => eastTime s r q ≤ s+k+y)) ↔ q ∈ (Finset.univ : Finset (Fin k))
    rw [Finset.mem_filter]
    simp only [Finset.mem_univ, true_and, iff_true]
    change s+q.val+(r q).val+1 ≤ s+k+y
    have hq := q.isLt
    have hr := (r q).isLt
    omega
  simp [thresholdHorizontal, he]

def thresholdPath {k y : ℕ} (s : ℕ) (r : Fin k → Fin (y+1))
    (hr : Monotone (fun q => (r q).val)) : DiagonalLatticePath s (s+k) y where
  horizontal := thresholdHorizontal s r
  nonempty := by omega
  source := thresholdHorizontal_source s r
  target := thresholdHorizontal_target s r
  step t _ _ := by
    have hlo := Finset.card_le_card (thresholdSet_mono (eastTime s r) (Nat.le_succ t))
    have hhi := thresholdSet_card_succ (eastTime s r) (eastTime_strictMono s r hr).injective t
    change (thresholdSet (eastTime s r) t).card ≤ (thresholdSet (eastTime s r) (t+1)).card at hlo
    simp only [thresholdHorizontal]
    omega

end
end Schubert.RS
