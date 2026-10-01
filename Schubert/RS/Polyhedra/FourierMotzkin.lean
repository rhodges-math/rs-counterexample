import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Fourier–Motzkin elimination

A finite system of linear inequalities `∑ i, a i * x i ≤ β` with integer data has a solution over
one linearly ordered field if and only if it has one over every linearly ordered field. The proof is
Fourier–Motzkin elimination: eliminating the last variable (`Schubert.RS.LinRows.elim`) keeps the
data integral and preserves solvability over every linearly ordered field, in both directions; after
all variables are eliminated, solvability is the sign condition `0 ≤ β` on the remaining rows.

## Main definitions

* `Schubert.RS.LinRows`: a list of rows `(a, β)` in the variables `Fin m`.
* `Schubert.RS.LinRows.Feasible`: the system has a solution over a given field.
* `Schubert.RS.LinRows.elim`: the system after eliminating the last variable.

## Main results

* `Schubert.RS.LinRows.feasible_elim_iff`: elimination preserves solvability.
* `Schubert.RS.LinRows.feasible_iff_elimAll`: solvability is a condition on the integer data.
* `Schubert.RS.LinRows.feasible_congr`: solvability does not depend on the field.
-/

namespace Schubert.RS

/-- A finite system of linear inequalities `∑ i, a i * x i ≤ β` with integer data in the variables
`Fin m`, given by its rows `(a, β)`. -/
abbrev LinRows (m : ℕ) : Type := List ((Fin m → ℤ) × ℤ)

namespace LinRows

variable {m : ℕ} {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The value `∑ i, a i * x i` of a coefficient vector at a point. -/
def value (a : Fin m → ℤ) (x : Fin m → K) : K := ∑ i, (a i : K) * x i

/-- The point `x` satisfies every inequality of the system. -/
def Holds (S : LinRows m) (x : Fin m → K) : Prop := ∀ r ∈ S, value r.1 x ≤ r.2

variable (K) in
/-- The system has a solution over `K`. -/
def Feasible (S : LinRows m) : Prop := ∃ x : Fin m → K, S.Holds x

/-! ### Eliminating the last variable -/

/-- A row without its last coefficient. -/
def initRow (r : (Fin (m + 1) → ℤ) × ℤ) : (Fin m → ℤ) × ℤ := (fun i => r.1 i.castSucc, r.2)

/-- The combination `(−a_q) · p + a_p · q` of a row `p` with positive last coefficient `a_p` and a
row `q` with negative last coefficient `a_q`, in which the last variable cancels. -/
def combine (p q : (Fin (m + 1) → ℤ) × ℤ) : (Fin m → ℤ) × ℤ :=
  (fun i => -q.1 (Fin.last m) * p.1 i.castSucc + p.1 (Fin.last m) * q.1 i.castSucc,
    -q.1 (Fin.last m) * p.2 + p.1 (Fin.last m) * q.2)

/-- **Fourier–Motzkin elimination** of the last variable: the rows not involving it, and the
combinations of every row with positive last coefficient with every row with negative last
coefficient. -/
def elim (S : LinRows (m + 1)) : LinRows m :=
  (S.filter fun r => r.1 (Fin.last m) = 0).map initRow ++
    (S.filter fun r => 0 < r.1 (Fin.last m)).flatMap fun p =>
      (S.filter fun r => r.1 (Fin.last m) < 0).map (combine p)

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem value_eq (a : Fin (m + 1) → ℤ) (x : Fin (m + 1) → K) :
    value a x = value (fun i => a i.castSucc) (Fin.init x) + a (Fin.last m) * x (Fin.last m) := by
  rw [value, Fin.sum_univ_castSucc]
  rfl

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem value_snoc (a : Fin (m + 1) → ℤ) (y : Fin m → K) (t : K) :
    value a (Fin.snoc y t : Fin (m + 1) → K) =
      value (fun i => a i.castSucc) y + a (Fin.last m) * t := by
  rw [value_eq, Fin.init_snoc, Fin.snoc_last]

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem value_combine (p q : (Fin (m + 1) → ℤ) × ℤ) (y : Fin m → K) :
    value (combine p q).1 y =
      -(q.1 (Fin.last m) : K) * value (initRow p).1 y +
        (p.1 (Fin.last m) : K) * value (initRow q).1 y := by
  simp only [value, combine, initRow, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast
  ring

/-- Elimination is necessary: a solution of the system gives one of the eliminated system. -/
theorem holds_elim {S : LinRows (m + 1)} {x : Fin (m + 1) → K} (hx : S.Holds x) :
    (elim S).Holds (Fin.init x) := by
  intro r hr
  simp only [elim, List.mem_append, List.mem_map, List.mem_filter, List.mem_flatMap,
    decide_eq_true_eq] at hr
  rcases hr with ⟨r', ⟨hr', h0⟩, rfl⟩ | ⟨p, ⟨hp, hpos⟩, q, ⟨hq, hneg⟩, rfl⟩
  · have h := hx r' hr'
    rw [value_eq, h0, Int.cast_zero, zero_mul, add_zero] at h
    exact h
  · have h1 := hx p hp
    have h2 := hx q hq
    rw [value_eq] at h1 h2
    rw [value_combine]
    have hp' : (0 : K) < p.1 (Fin.last m) := by exact_mod_cast hpos
    have hq' : (q.1 (Fin.last m) : K) < 0 := by exact_mod_cast hneg
    simp only [combine, initRow] at h1 h2 ⊢
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left h1 (le_of_lt (neg_pos.mpr hq')),
      mul_le_mul_of_nonneg_left h2 (le_of_lt hp')]

omit [IsStrictOrderedRing K] in
/-- Between a finite list of lower bounds and a finite list of upper bounds, each lower bound below
each upper bound, lies a point. -/
theorem exists_between_lists (L U : List K) (h : ∀ l ∈ L, ∀ u ∈ U, l ≤ u) :
    ∃ t : K, (∀ l ∈ L, l ≤ t) ∧ ∀ u ∈ U, t ≤ u := by
  induction L with
  | nil =>
    clear h
    induction U with
    | nil => exact ⟨0, by simp, by simp⟩
    | cons u U ih =>
      obtain ⟨t, -, ht⟩ := ih
      refine ⟨min t u, by simp, ?_⟩
      simp only [List.mem_cons, forall_eq_or_imp]
      exact ⟨min_le_right _ _, fun v hv => (min_le_left _ _).trans (ht v hv)⟩
  | cons l L ih =>
    obtain ⟨t, htL, htU⟩ := ih fun l' hl' => h l' (List.mem_cons_of_mem _ hl')
    refine ⟨max t l, ?_, fun u hu => max_le (htU u hu) (h l List.mem_cons_self u hu)⟩
    simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨le_max_right _ _, fun l' hl' => (htL l' hl').trans (le_max_left _ _)⟩

/-- Elimination is sufficient: a solution of the eliminated system extends to one of the system. -/
theorem exists_holds_snoc {S : LinRows (m + 1)} {y : Fin m → K} (hy : (elim S).Holds y) :
    ∃ t : K, S.Holds (Fin.snoc y t : Fin (m + 1) → K) := by
  set P := S.filter fun r => 0 < r.1 (Fin.last m)
  set N := S.filter fun r => r.1 (Fin.last m) < 0
  -- lower bounds from the rows with negative, upper bounds from those with positive last
  -- coefficient
  let lo : (Fin (m + 1) → ℤ) × ℤ → K := fun q =>
    (value (initRow q).1 y - q.2) / (-(q.1 (Fin.last m) : K))
  let up : (Fin (m + 1) → ℤ) × ℤ → K := fun p =>
    ((p.2 : K) - value (initRow p).1 y) / (p.1 (Fin.last m) : K)
  have hmemP : ∀ p, p ∈ P ↔ p ∈ S ∧ 0 < p.1 (Fin.last m) := fun p => by
    simp [P, List.mem_filter]
  have hmemN : ∀ q, q ∈ N ↔ q ∈ S ∧ q.1 (Fin.last m) < 0 := fun q => by
    simp [N, List.mem_filter]
  obtain ⟨t, hlo, hup⟩ := exists_between_lists (N.map lo) (P.map up) (by
    simp only [List.mem_map]
    rintro _ ⟨q, hq, rfl⟩ _ ⟨p, hp, rfl⟩
    have hq' := (hmemN q).1 hq
    have hp' := (hmemP p).1 hp
    have hc : combine p q ∈ elim S := by
      simp only [elim, List.mem_append, List.mem_flatMap, List.mem_map]
      exact Or.inr ⟨p, hp, q, hq, rfl⟩
    have h := hy _ hc
    rw [value_combine] at h
    have hpk : (0 : K) < p.1 (Fin.last m) := by exact_mod_cast hp'.2
    have hqk : (0 : K) < -(q.1 (Fin.last m) : K) := neg_pos.mpr (by exact_mod_cast hq'.2)
    simp only [lo, up]
    rw [div_le_div_iff₀ hqk hpk]
    simp only [combine] at h
    push_cast at h
    linarith)
  refine ⟨t, fun r hr => ?_⟩
  rw [value_snoc]
  rcases lt_trichotomy (r.1 (Fin.last m)) 0 with hneg | h0 | hpos
  · have hl := hlo (lo r) (List.mem_map_of_mem ((hmemN r).2 ⟨hr, hneg⟩))
    have hqk : (0 : K) < -(r.1 (Fin.last m) : K) := neg_pos.mpr (by exact_mod_cast hneg)
    simp only [lo] at hl
    rw [div_le_iff₀ hqk] at hl
    simp only [initRow] at hl
    linarith
  · have hm : initRow r ∈ elim S := by
      simp only [elim, List.mem_append, List.mem_map, List.mem_filter, decide_eq_true_eq]
      exact Or.inl ⟨r, ⟨hr, h0⟩, rfl⟩
    have h := hy _ hm
    rw [h0, Int.cast_zero, zero_mul, add_zero]
    exact h
  · have hu := hup (up r) (List.mem_map_of_mem ((hmemP r).2 ⟨hr, hpos⟩))
    have hpk : (0 : K) < r.1 (Fin.last m) := by exact_mod_cast hpos
    simp only [up] at hu
    rw [le_div_iff₀ hpk] at hu
    simp only [initRow] at hu
    linarith

/-- **Fourier–Motzkin**: eliminating the last variable preserves solvability over `K`. -/
theorem feasible_elim_iff (S : LinRows (m + 1)) : Feasible K (elim S) ↔ Feasible K S := by
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨t, ht⟩ := exists_holds_snoc hy
    exact ⟨_, ht⟩
  · rintro ⟨x, hx⟩
    exact ⟨_, holds_elim hx⟩

/-! ### Eliminating all variables -/

/-- The system after eliminating all variables. -/
def elimAll : (m : ℕ) → LinRows m → LinRows 0
  | 0, S => S
  | m + 1, S => elimAll m (elim S)

/-- A system without variables is solvable iff all its right-hand sides are nonnegative. -/
theorem feasible_zero_iff (S : LinRows 0) : Feasible K S ↔ ∀ r ∈ S, 0 ≤ r.2 := by
  constructor
  · rintro ⟨x, hx⟩ r hr
    have h := hx r hr
    simp only [value, Finset.univ_eq_empty, Finset.sum_empty] at h
    exact_mod_cast h
  · intro h
    refine ⟨Fin.elim0, fun r hr => ?_⟩
    simp only [value, Finset.univ_eq_empty, Finset.sum_empty]
    exact_mod_cast h r hr

theorem feasible_elimAll_iff : ∀ (m : ℕ) (S : LinRows m),
    Feasible K (elimAll m S) ↔ Feasible K S
  | 0, _ => Iff.rfl
  | m + 1, S => (feasible_elimAll_iff m (elim S)).trans (feasible_elim_iff S)

/-- **Solvability is a condition on the integer data**: the right-hand sides after eliminating all
variables are nonnegative. -/
theorem feasible_iff_elimAll (S : LinRows m) :
    Feasible K S ↔ ∀ r ∈ elimAll m S, 0 ≤ r.2 :=
  (feasible_elimAll_iff m S).symm.trans (feasible_zero_iff _)

/-- **Solvability does not depend on the field**: a system with integer data has a solution over
one linearly ordered field iff it has one over another (for instance over `ℝ` iff over `ℚ`). -/
theorem feasible_congr (L : Type*) [Field L] [LinearOrder L] [IsStrictOrderedRing L]
    (S : LinRows m) : Feasible K S ↔ Feasible L S :=
  (feasible_iff_elimAll S).trans (feasible_iff_elimAll S).symm

end LinRows

end Schubert.RS
