import Mathlib.Data.Int.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Lean.Elab.Tactic.Omega

/-! The planar order argument in the Hall determinant proof.
Diagonal time is x+y, so a north/east step changes x by zero or one. -/

namespace Schubert.RS

theorem northEast_interval_bounds (x : ℕ → ℤ) (s e : ℕ)
    (hx : ∀ t, s ≤ t → t < e → x t ≤ x (t+1) ∧ x (t+1) ≤ x t + 1)
    (a b : ℕ) (hsa : s ≤ a) (hab : a ≤ b) (hbe : b ≤ e) :
    x a ≤ x b ∧ x b ≤ x a + ((b-a : ℕ) : ℤ) := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    have hi := ih (by omega)
    have hs := hx b (by omega) (by omega)
    have hdiff : b + 1 - a = (b-a) + 1 := by omega
    rw [hdiff, Int.natCast_add, Int.natCast_one]
    omega

theorem northEast_strict_order (x y : ℕ → ℤ) (a b : ℕ) (hab : a ≤ b)
    (hx : ∀ t, a ≤ t → t < b → x t ≤ x (t+1) ∧ x (t+1) ≤ x t + 1)
    (hy : ∀ t, a ≤ t → t < b → y t ≤ y (t+1) ∧ y (t+1) ≤ y t + 1)
    (hne : ∀ t, a ≤ t → t ≤ b → x t ≠ y t) (hstart : x a < y a) :
    x b < y b := by
  induction b, hab using Nat.le_induction with
  | base => exact hstart
  | succ b hab ih =>
    have hi := ih (fun t hat htb => hx t hat (by omega))
      (fun t hat htb => hy t hat (by omega))
      (fun t hat htb => hne t hat (by omega))
    have hxs := hx b hab (by omega)
    have hys := hy b hab (by omega)
    have hn := hne (b+1) (by omega) le_rfl
    omega

/-- A north/east path from (s,0) to (x,y), represented on its actual diagonal
time interval. Values outside that interval are immaterial. -/
structure DiagonalLatticePath (s x y : ℕ) where
  horizontal : ℕ → ℤ
  nonempty : s ≤ x+y
  source : horizontal s = s
  target : horizontal (x+y) = x
  step : ∀ t, s ≤ t → t < x+y →
    horizontal t ≤ horizontal (t+1) ∧ horizontal (t+1) ≤ horizontal t + 1

namespace DiagonalLatticePath
variable {s x y : ℕ} (P : DiagonalLatticePath s x y)

include P in
theorem source_le_target : s ≤ x := by
  have h := (northEast_interval_bounds P.horizontal s (x+y) P.step s (x+y)
    le_rfl P.nonempty le_rfl).1
  rw [P.source, P.target] at h
  omega

theorem horizontal_le_time (t : ℕ) (hst : s ≤ t) (hte : t ≤ x+y) :
    P.horizontal t ≤ t := by
  have h := (northEast_interval_bounds P.horizontal s (x+y) P.step s t le_rfl hst hte).2
  rw [P.source] at h
  have he : (s : ℤ) + ((t-s : ℕ) : ℤ) = t := by omega
  omega

theorem horizontal_le_target (t : ℕ) (hst : s ≤ t) (hte : t ≤ x+y) :
    P.horizontal t ≤ x := by
  have h := (northEast_interval_bounds P.horizontal s (x+y) P.step t (x+y) hst hte le_rfl).1
  simpa only [P.target] using h

theorem time_sub_height_le (t : ℕ) (hst : s ≤ t) (hte : t ≤ x+y) :
    (t : ℤ) - y ≤ P.horizontal t := by
  have h := (northEast_interval_bounds P.horizontal s (x+y) P.step t (x+y) hst hte le_rfl).2
  rw [P.target] at h
  have he : (((x+y)-t : ℕ) : ℤ) = (x : ℤ) + y - t := by omega
  rw [he] at h
  omega

end DiagonalLatticePath

/-- Inverted endpoints force a common vertex: the path starting further
right cannot finish further left and at least as high without meeting the
other path. This is the manuscript's planar matching argument. -/
theorem inverted_lattice_paths_intersect {s₁ s₂ x₁ x₂ y₁ y₂ : ℕ}
    (P : DiagonalLatticePath s₁ x₁ y₁) (Q : DiagonalLatticePath s₂ x₂ y₂)
    (hs : s₂ < s₁) (hx : x₁ < x₂) (hy : y₂ ≤ y₁) :
    ∃ t, s₁ ≤ t ∧ s₂ ≤ t ∧ t ≤ x₁+y₁ ∧ t ≤ x₂+y₂ ∧
      P.horizontal t = Q.horizontal t := by
  by_contra hn
  have hne (t : ℕ) (h₁ : s₁ ≤ t) (h₂ : s₂ ≤ t)
      (he₁ : t ≤ x₁+y₁) (he₂ : t ≤ x₂+y₂) : P.horizontal t ≠ Q.horizontal t := by
    intro h
    exact hn ⟨t, h₁, h₂, he₁, he₂, h⟩
  have hsx := P.source_le_target
  have he₂ : s₁ ≤ x₂+y₂ := by omega
  have hstart : Q.horizontal s₁ < P.horizontal s₁ := by
    have hle := Q.horizontal_le_time s₁ (by omega) he₂
    have he := hne s₁ le_rfl (by omega) P.nonempty he₂
    rw [P.source] at he ⊢
    omega
  let t := min (x₁+y₁) (x₂+y₂)
  have hst : s₁ ≤ t := le_min P.nonempty he₂
  have ht₁ : t ≤ x₁+y₁ := min_le_left _ _
  have ht₂ : t ≤ x₂+y₂ := min_le_right _ _
  have ho : Q.horizontal t < P.horizontal t :=
    northEast_strict_order Q.horizontal P.horizontal s₁ t hst
      (fun k hsk hkt => Q.step k (by omega) (by omega))
      (fun k hsk hkt => P.step k hsk (by omega))
      (fun k hsk hkt => (hne k hsk (by omega) (by omega) (by omega)).symm) hstart
  by_cases he : x₁+y₁ ≤ x₂+y₂
  · have ht : t = x₁+y₁ := min_eq_left he
    have hq := Q.time_sub_height_le t (by omega) ht₂
    rw [ht, P.target] at ho
    rw [ht] at hq
    omega
  · have ht : t = x₂+y₂ := min_eq_right (by omega)
    have hp := P.horizontal_le_target t hst ht₁
    rw [ht, Q.target] at ho
    rw [ht] at hp
    omega

/-- With the Hall source and endpoint orders, every nonintersecting family
has identity matching. This includes arbitrary repeated endpoint heights. -/
theorem ordered_lattice_matching {d : ℕ} (s x y : Fin d → ℕ)
    (hs : StrictAnti s) (hx : StrictAnti x) (hy : Monotone y)
    (σ : Equiv.Perm (Fin d))
    (P : ∀ i, DiagonalLatticePath (s i) (x (σ i)) (y (σ i)))
    (hdisjoint : ∀ i j, i ≠ j → ∀ t, s i ≤ t → s j ≤ t →
      t ≤ x (σ i) + y (σ i) → t ≤ x (σ j) + y (σ j) →
      (P i).horizontal t ≠ (P j).horizontal t) : σ = 1 := by
  apply (Equiv.Perm.monotone_iff σ).mp
  intro i j hij
  by_cases he : i = j
  · subst j; exact le_rfl
  have hij' : i < j := lt_of_le_of_ne hij he
  by_contra hn
  have hinv : σ j < σ i := lt_of_not_ge hn
  obtain ⟨t, hi, hj, hti, htj, ht⟩ :=
    inverted_lattice_paths_intersect (P i) (P j) (hs hij') (hx hinv) (hy hinv.le)
  exact hdisjoint i j he t hi hj hti htj ht

end Schubert.RS
