import RSCounterexample.Paper.Quiver.Polytope.Flat
import RSCounterexample.Paper.Polyhedra.Points
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Tactic.Linarith

/-!
# Reading the rows of the positional polytope

The rows of `Schubert.RS.Quiver.Flat.PositionalQuiver.polytope` are dense coefficient lists. Here
they are read back in the coordinates of the positional layout: the partition variables
`sh i j k r` and the row-count variables `ce i j k r l` of a point. Each family of inequalities
becomes the condition it was built to express
(`Schubert.RS.Quiver.Flat.PositionalQuiver.holds_iff`).

## Main definitions

* `Schubert.RS.Quiver.Flat.PositionalQuiver.Holds`: a point (over an ordered ring) satisfies the
  system.
* `Schubert.RS.Quiver.Flat.PositionalQuiver.sh`, `ce`: the coordinates of a point;
  `ofCoords`: the point with given coordinates.
* `Schubert.RS.Quiver.Flat.PositionalQuiver.ShapeCond`, …, `FinalCond`, `Conditions`: the six
  families.
* `Schubert.RS.Quiver.Flat.PositionalQuiver.WellFormed`: the conditions on the positional data used
  to read the rows.
* `Schubert.RS.Quiver.Flat.PositionalQuiver.withWeight`: the same quiver with another weight.

## Main results

* `Schubert.RS.Quiver.Flat.PositionalQuiver.lhs_mkRow`: the value of a row at a point, as sums over
  the index ranges.
* `Schubert.RS.Quiver.Flat.PositionalQuiver.holds_iff`, `mem_intPoints_iff`, `mem_points_iff`: a
  point satisfies the system iff its coordinates satisfy the six families of conditions.
* `Schubert.RS.Quiver.Flat.PositionalQuiver.ofCoords_sh_ce`, `eq_of_coords`: a point is determined
  by its coordinates.
* `Schubert.RS.Quiver.Flat.PositionalQuiver.polytope_withWeight_nsmul`: homogeneity in the weight.
* `Schubert.RS.Quiver.Flat.wellFormed_positionalOf`: the positional quiver of a triple is well
  formed.
-/

namespace Schubert.RS.Quiver.Flat

open Finset

/-- `∑_{c < a b} F c = ∑_{q < a} ∑_{t < b} F (q b + t)`. -/
theorem sum_range_mul {M : Type*} [AddCommMonoid M] (a b : ℕ) (F : ℕ → M) :
    ∑ c ∈ range (a * b), F c = ∑ q ∈ range a, ∑ t ∈ range b, F (q * b + t) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Nat.succ_mul, sum_range_add, ih, sum_range_succ]

theorem div_mod_of_lt {q t b : ℕ} (ht : t < b) : (q * b + t) / b = q ∧ (q * b + t) % b = t := by
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega : 0 < b), Nat.div_eq_of_lt ht, zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht]

namespace PositionalQuiver

variable (Q : PositionalQuiver)

/-- The coordinates of a column index, combined by `f` (a partition column `(i, j, k, r)`) or by
`g` (a row-count column `(i, j, k, r, l)`); `colFun` is the case of integer coefficients. -/
def decode {α : Type*} (f : ℕ → ℕ → ℕ → ℕ → α) (g : ℕ → ℕ → ℕ → ℕ → ℕ → α) (col : ℕ) : α :=
  if col < 2 * Q.n ^ 3 then
    f (col / (2 * Q.n ^ 2)) (col / (2 * Q.n) % Q.n) (col / Q.n % 2) (col % Q.n)
  else
    g ((col - 2 * Q.n ^ 3) / (2 * Q.n ^ 3)) ((col - 2 * Q.n ^ 3) / (2 * Q.n ^ 2) % Q.n)
      ((col - 2 * Q.n ^ 3) / Q.n ^ 2 % 2) ((col - 2 * Q.n ^ 3) / Q.n % Q.n)
      ((col - 2 * Q.n ^ 3) % Q.n)

theorem colFun_eq_decode (f : ℕ → ℕ → ℕ → ℕ → ℤ) (g : ℕ → ℕ → ℕ → ℕ → ℕ → ℤ) :
    Q.colFun f g = Q.decode f g :=
  rfl

theorem shapeCol_lt_cube {i j k r : ℕ} (hi : i < Q.n) (hj : j < Q.n) (hk : k < 2)
    (hr : r < Q.n) : Q.shapeCol i j k r < 2 * Q.n ^ 3 := by
  unfold shapeCol
  have : (i * Q.n + j) * 2 + k < Q.n * Q.n * 2 := by nlinarith
  nlinarith

theorem shapeCol_lt {i j k r : ℕ} (hi : i < Q.n) (hj : j < Q.n) (hk : k < 2) (hr : r < Q.n) :
    Q.shapeCol i j k r < Q.dim := by
  have := Q.shapeCol_lt_cube hi hj hk hr
  unfold dim
  omega

theorem cellCol_eq (i j k r l : ℕ) :
    Q.cellCol i j k r l = 2 * Q.n ^ 3 + ((((i * Q.n + j) * 2 + k) * Q.n + r) * Q.n + l) := by
  unfold cellCol
  omega

theorem cellCol_lt {i j k r l : ℕ} (hi : i < Q.n) (hj : j < Q.n) (hk : k < 2) (hr : r < Q.n)
    (hl : l < Q.n) : Q.cellCol i j k r l < Q.dim := by
  rw [cellCol_eq]
  unfold dim
  have h1 : (i * Q.n + j) * 2 + k < Q.n * Q.n * 2 := by nlinarith
  have h2 : ((i * Q.n + j) * 2 + k) * Q.n + r < Q.n * Q.n * 2 * Q.n := by nlinarith
  have h3 : (((i * Q.n + j) * 2 + k) * Q.n + r) * Q.n + l < Q.n * Q.n * 2 * Q.n * Q.n := by
    nlinarith
  have e : 2 * Q.n ^ 4 = Q.n * Q.n * 2 * Q.n * Q.n := by ring
  omega

theorem decode_shapeCol {α : Type*} (f : ℕ → ℕ → ℕ → ℕ → α) (g : ℕ → ℕ → ℕ → ℕ → ℕ → α)
    {i j k r : ℕ} (hi : i < Q.n) (hj : j < Q.n) (hk : k < 2) (hr : r < Q.n) :
    Q.decode f g (Q.shapeCol i j k r) = f i j k r := by
  have h1 := div_mod_of_lt (q := (i * Q.n + j) * 2 + k) hr
  have h2 := div_mod_of_lt (q := i * Q.n + j) hk
  have h3 := div_mod_of_lt (q := i) hj
  have e1 : 2 * Q.n ^ 2 = Q.n * 2 * Q.n := by ring
  have e2 : 2 * Q.n = Q.n * 2 := by ring
  unfold decode
  rw [ite_eq_left (Q.shapeCol_lt_cube hi hj hk hr), e1, e2]
  simp only [← Nat.div_div_eq_div_mul]
  unfold shapeCol
  rw [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem decode_cellCol {α : Type*} (f : ℕ → ℕ → ℕ → ℕ → α) (g : ℕ → ℕ → ℕ → ℕ → ℕ → α)
    {i j k r l : ℕ} (hj : j < Q.n) (hk : k < 2) (hr : r < Q.n) (hl : l < Q.n) :
    Q.decode f g (Q.cellCol i j k r l) = g i j k r l := by
  have h0 := div_mod_of_lt (q := ((i * Q.n + j) * 2 + k) * Q.n + r) hl
  have h1 := div_mod_of_lt (q := (i * Q.n + j) * 2 + k) hr
  have h2 := div_mod_of_lt (q := i * Q.n + j) hk
  have h3 := div_mod_of_lt (q := i) hj
  have hsub : Q.cellCol i j k r l - 2 * Q.n ^ 3 =
      (((i * Q.n + j) * 2 + k) * Q.n + r) * Q.n + l := by
    rw [cellCol_eq]
    omega
  have hge : ¬ Q.cellCol i j k r l < 2 * Q.n ^ 3 := by
    rw [cellCol_eq]
    omega
  have e1 : 2 * Q.n ^ 3 = Q.n * Q.n * 2 * Q.n := by ring
  have e2 : 2 * Q.n ^ 2 = Q.n * Q.n * 2 := by ring
  have e3 : Q.n ^ 2 = Q.n * Q.n := by ring
  unfold decode
  rw [ite_eq_right hge, hsub, e1, e2, e3]
  simp only [← Nat.div_div_eq_div_mul]
  rw [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem colFun_shapeCol (f : ℕ → ℕ → ℕ → ℕ → ℤ) (g : ℕ → ℕ → ℕ → ℕ → ℕ → ℤ) {i j k r : ℕ}
    (hi : i < Q.n) (hj : j < Q.n) (hk : k < 2) (hr : r < Q.n) :
    Q.colFun f g (Q.shapeCol i j k r) = f i j k r :=
  Q.decode_shapeCol f g hi hj hk hr

theorem colFun_cellCol (f : ℕ → ℕ → ℕ → ℕ → ℤ) (g : ℕ → ℕ → ℕ → ℕ → ℕ → ℤ) {i j k r l : ℕ}
    (hj : j < Q.n) (hk : k < 2) (hr : r < Q.n) (hl : l < Q.n) :
    Q.colFun f g (Q.cellCol i j k r l) = g i j k r l :=
  Q.decode_cellCol f g hj hk hr hl

/-- Every partition column is the column of its coordinates. -/
theorem shapeCol_decode (c : ℕ) :
    Q.shapeCol (c / (2 * Q.n ^ 2)) (c / (2 * Q.n) % Q.n) (c / Q.n % 2) (c % Q.n) = c := by
  have e1 : 2 * Q.n ^ 2 = Q.n * 2 * Q.n := by ring
  have e2 : 2 * Q.n = Q.n * 2 := by ring
  rw [e1, e2]
  simp only [← Nat.div_div_eq_div_mul]
  unfold shapeCol
  rw [Nat.div_add_mod', Nat.div_add_mod', Nat.div_add_mod']

/-- Every row-count column is the column of its coordinates. -/
theorem cellCol_decode {c : ℕ} (hc : 2 * Q.n ^ 3 ≤ c) :
    Q.cellCol ((c - 2 * Q.n ^ 3) / (2 * Q.n ^ 3)) ((c - 2 * Q.n ^ 3) / (2 * Q.n ^ 2) % Q.n)
      ((c - 2 * Q.n ^ 3) / Q.n ^ 2 % 2) ((c - 2 * Q.n ^ 3) / Q.n % Q.n)
      ((c - 2 * Q.n ^ 3) % Q.n) = c := by
  rw [cellCol_eq]
  generalize hd : c - 2 * Q.n ^ 3 = d
  have e1 : 2 * Q.n ^ 3 = Q.n * Q.n * 2 * Q.n := by ring
  have e2 : 2 * Q.n ^ 2 = Q.n * Q.n * 2 := by ring
  have e3 : Q.n ^ 2 = Q.n * Q.n := by ring
  have key : (((d / (2 * Q.n ^ 3) * Q.n + d / (2 * Q.n ^ 2) % Q.n) * 2 + d / Q.n ^ 2 % 2) * Q.n +
      d / Q.n % Q.n) * Q.n + d % Q.n = d := by
    rw [e1, e2, e3]
    simp only [← Nat.div_div_eq_div_mul]
    rw [Nat.div_add_mod', Nat.div_add_mod', Nat.div_add_mod', Nat.div_add_mod']
  rw [key]
  omega

variable {R : Type*} [CommRing R]

/-- The value `a · x` of a coefficient list at a point. -/
def lhs (a : List ℤ) (x : Fin Q.dim → R) : R := ∑ c : Fin Q.dim, (a.getD c 0 : R) * x c

/-- A point, extended by `0` to all column indices. -/
def ext (x : Fin Q.dim → R) (c : ℕ) : R := if h : c < Q.dim then x ⟨c, h⟩ else 0

/-- The partition variable `(i, j, k, r)` of a point. -/
def sh (x : Fin Q.dim → R) (i j k r : ℕ) : R := Q.ext x (Q.shapeCol i j k r)

/-- The row-count variable `(i, j, k, r, l)` of a point. -/
def ce (x : Fin Q.dim → R) (i j k r l : ℕ) : R := Q.ext x (Q.cellCol i j k r l)

/-! ### Points from coordinates -/

/-- The point with partition coordinates `f` and row-count coordinates `g`. -/
def ofCoords (f : ℕ → ℕ → ℕ → ℕ → R) (g : ℕ → ℕ → ℕ → ℕ → ℕ → R) : Fin Q.dim → R :=
  fun c => Q.decode f g c

theorem sh_ofCoords (f : ℕ → ℕ → ℕ → ℕ → R) (g : ℕ → ℕ → ℕ → ℕ → ℕ → R) {i j k r : ℕ}
    (hi : i < Q.n) (hj : j < Q.n) (hk : k < 2) (hr : r < Q.n) :
    Q.sh (Q.ofCoords f g) i j k r = f i j k r := by
  rw [PositionalQuiver.sh, ext, dite_eq_left (Q.shapeCol_lt hi hj hk hr), ofCoords,
    Q.decode_shapeCol f g hi hj hk hr]

theorem ce_ofCoords (f : ℕ → ℕ → ℕ → ℕ → R) (g : ℕ → ℕ → ℕ → ℕ → ℕ → R) {i j k r l : ℕ}
    (hi : i < Q.n) (hj : j < Q.n) (hk : k < 2) (hr : r < Q.n)
    (hl : l < Q.n) : Q.ce (Q.ofCoords f g) i j k r l = g i j k r l := by
  rw [PositionalQuiver.ce, ext, dite_eq_left (Q.cellCol_lt hi hj hk hr hl), ofCoords,
    Q.decode_cellCol f g hj hk hr hl]

/-- A point is the point of its coordinates. -/
theorem ofCoords_sh_ce (x : Fin Q.dim → R) : Q.ofCoords (Q.sh x) (Q.ce x) = x := by
  funext c
  unfold ofCoords decode
  split_ifs with h
  · rw [PositionalQuiver.sh, Q.shapeCol_decode, ext, dite_eq_left c.isLt]
  · rw [PositionalQuiver.ce, Q.cellCol_decode (by omega), ext, dite_eq_left c.isLt]

/-- A point is determined by its coordinates in the index ranges. -/
theorem eq_of_coords {x y : Fin Q.dim → R}
    (hsh : ∀ i < Q.n, ∀ j < Q.n, ∀ k < 2, ∀ r < Q.n, Q.sh x i j k r = Q.sh y i j k r)
    (hce : ∀ i < Q.n, ∀ j < Q.n, ∀ k < 2, ∀ r < Q.n, ∀ l < Q.n,
      Q.ce x i j k r l = Q.ce y i j k r l) : x = y := by
  rw [← Q.ofCoords_sh_ce x, ← Q.ofCoords_sh_ce y]
  funext c
  have hn : 0 < Q.n := by
    rcases Nat.eq_zero_or_pos Q.n with h | h
    · exact absurd c.isLt (by simp [dim, h])
    · exact h
  have hc := c.isLt
  unfold ofCoords decode
  split_ifs with h
  · refine hsh _ ?_ _ (Nat.mod_lt _ hn) _ (Nat.mod_lt _ (by norm_num)) _ (Nat.mod_lt _ hn)
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    calc (c : ℕ) < 2 * Q.n ^ 3 := h
      _ = Q.n * (2 * Q.n ^ 2) := by ring
  · refine hce _ ?_ _ (Nat.mod_lt _ hn) _ (Nat.mod_lt _ (by norm_num)) _ (Nat.mod_lt _ hn) _
      (Nat.mod_lt _ hn)
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    have : (c : ℕ) < 2 * Q.n ^ 3 + 2 * Q.n ^ 4 := hc
    calc (c : ℕ) - 2 * Q.n ^ 3 < 2 * Q.n ^ 4 := by omega
      _ = Q.n * (2 * Q.n ^ 3) := by ring


/-- **Reading a row**: the value of `mkRow f g` at a point, as sums over the index ranges. -/
theorem lhs_mkRow (f : ℕ → ℕ → ℕ → ℕ → ℤ) (g : ℕ → ℕ → ℕ → ℕ → ℕ → ℤ) (rhs : ℤ)
    (x : Fin Q.dim → R) :
    Q.lhs (Q.mkRow f g rhs).1 x =
      (∑ i ∈ range Q.n, ∑ j ∈ range Q.n, ∑ k ∈ range 2, ∑ r ∈ range Q.n,
        (f i j k r : R) * Q.sh x i j k r) +
      ∑ i ∈ range Q.n, ∑ j ∈ range Q.n, ∑ k ∈ range 2, ∑ r ∈ range Q.n, ∑ l ∈ range Q.n,
        (g i j k r l : R) * Q.ce x i j k r l := by
  have h1 : Q.lhs (Q.mkRow f g rhs).1 x =
      ∑ c ∈ range Q.dim, (Q.colFun f g c : R) * Q.ext x c := by
    rw [lhs, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [mkRow, ext, c.isLt, dite_true]
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_range]
  rw [h1, dim, sum_range_add]
  congr 1
  · rw [show 2 * Q.n ^ 3 = Q.n * Q.n * 2 * Q.n by ring, sum_range_mul, sum_range_mul,
      sum_range_mul]
    refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj =>
      Finset.sum_congr rfl fun k hk => Finset.sum_congr rfl fun r hr => ?_
    rw [mem_range] at hi hj hk hr
    rw [← Q.colFun_shapeCol f g hi hj hk hr]
    rfl
  · rw [show 2 * Q.n ^ 4 = Q.n * Q.n * 2 * Q.n * Q.n by ring, sum_range_mul, sum_range_mul,
      sum_range_mul, sum_range_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj =>
      Finset.sum_congr rfl fun k hk => Finset.sum_congr rfl fun r hr =>
        Finset.sum_congr rfl fun l hl => ?_
    rw [mem_range] at hj hk hr hl
    have hc : Q.cellCol i j k r l =
        2 * Q.n ^ 3 + ((((i * Q.n + j) * 2 + k) * Q.n + r) * Q.n + l) := by
      unfold cellCol
      ring
    rw [← Q.colFun_cellCol (i := i) f g hj hk hr hl, ce, hc]

/-! ### Collapsing sums of indicators -/

omit [CommRing R] in
theorem sum_range_ite_eq {M : Type*} [AddCommMonoid M] {n a : ℕ} (ha : a < n) (F : ℕ → M) :
    ∑ i ∈ range n, (if i = a then F i else 0) = F a := by
  rw [Finset.sum_ite_eq', ite_eq_left (mem_range.mpr ha)]

omit [CommRing R] in
theorem sum_range_ite_le {M : Type*} [AddCommMonoid M] {n a : ℕ} (ha : a < n) (F : ℕ → M) :
    ∑ i ∈ range n, (if i ≤ a then F i else 0) = ∑ i ∈ range (a + 1), F i := by
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp only [mem_filter, mem_range]
  omega

omit [CommRing R] in
theorem sum_range_ite_lt {M : Type*} [AddCommMonoid M] {n a : ℕ} (ha : a ≤ n) (F : ℕ → M) :
    ∑ i ∈ range n, (if i < a then F i else 0) = ∑ i ∈ range a, F i := by
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp only [mem_filter, mem_range]
  omega

theorem sum4_shapeAt (F : ℕ → ℕ → ℕ → ℕ → R) {i0 j0 k0 r0 : ℕ} (hi : i0 < Q.n)
    (hj : j0 < Q.n) (hk : k0 < 2) (hr : r0 < Q.n) :
    ∑ i ∈ range Q.n, ∑ j ∈ range Q.n, ∑ k ∈ range 2, ∑ r ∈ range Q.n,
      ((shapeAt i0 j0 k0 r0 i j k r : ℤ) : R) * F i j k r = F i0 j0 k0 r0 := by
  simp only [shapeAt, Int.cast_ite, Int.cast_one, Int.cast_zero, ite_mul, one_mul, zero_mul,
    ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero, sum_range_ite_eq hi, sum_range_ite_eq hj,
    sum_range_ite_eq hk, sum_range_ite_eq hr]

theorem sum5_cellAt (F : ℕ → ℕ → ℕ → ℕ → ℕ → R) {i0 j0 k0 r0 l0 : ℕ} (hi : i0 < Q.n)
    (hj : j0 < Q.n) (hk : k0 < 2) (hr : r0 < Q.n) (hl : l0 < Q.n) :
    ∑ i ∈ range Q.n, ∑ j ∈ range Q.n, ∑ k ∈ range 2, ∑ r ∈ range Q.n, ∑ l ∈ range Q.n,
      ((cellAt i0 j0 k0 r0 l0 i j k r l : ℤ) : R) * F i j k r l = F i0 j0 k0 r0 l0 := by
  simp only [cellAt, Int.cast_ite, Int.cast_one, Int.cast_zero, ite_mul, one_mul, zero_mul,
    ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero, sum_range_ite_eq hi, sum_range_ite_eq hj,
    sum_range_ite_eq hk, sum_range_ite_eq hr, sum_range_ite_eq hl]

/-! ### The value of each row -/

theorem lhs_mkRow_shape (f : ℕ → ℕ → ℕ → ℕ → ℤ) (rhs : ℤ) (x : Fin Q.dim → R) :
    Q.lhs (Q.mkRow f (fun _ _ _ _ _ => 0) rhs).1 x =
      ∑ i ∈ range Q.n, ∑ j ∈ range Q.n, ∑ k ∈ range 2, ∑ r ∈ range Q.n,
        (f i j k r : R) * Q.sh x i j k r := by
  rw [lhs_mkRow]
  simp

theorem lhs_mkRow_cell (g : ℕ → ℕ → ℕ → ℕ → ℕ → ℤ) (rhs : ℤ) (x : Fin Q.dim → R) :
    Q.lhs (Q.mkRow (fun _ _ _ _ => 0) g rhs).1 x =
      ∑ i ∈ range Q.n, ∑ j ∈ range Q.n, ∑ k ∈ range 2, ∑ r ∈ range Q.n, ∑ l ∈ range Q.n,
        (g i j k r l : R) * Q.ce x i j k r l := by
  rw [lhs_mkRow]
  simp

theorem lhs_trivialRow (x : Fin Q.dim → R) : Q.lhs Q.trivialRow.1 x = 0 := by
  rw [trivialRow, lhs_mkRow_shape]
  simp

theorem lhs_shapeAt {i j k r : ℕ} (hi : i < Q.n) (hj : j < Q.n) (hk : k < 2) (hr : r < Q.n)
    (rhs : ℤ) (x : Fin Q.dim → R) :
    Q.lhs (Q.mkRow (shapeAt i j k r) (fun _ _ _ _ _ => 0) rhs).1 x = Q.sh x i j k r := by
  rw [lhs_mkRow_shape, Q.sum4_shapeAt _ hi hj hk hr]

theorem lhs_neg_shapeAt {i j k r : ℕ} (hi : i < Q.n) (hj : j < Q.n) (hk : k < 2) (hr : r < Q.n)
    (rhs : ℤ) (x : Fin Q.dim → R) :
    Q.lhs (Q.mkRow (fun i' j' k' r' => -shapeAt i j k r i' j' k' r') (fun _ _ _ _ _ => 0)
      rhs).1 x = -Q.sh x i j k r := by
  rw [lhs_mkRow_shape, ← Q.sum4_shapeAt (Q.sh x) hi hj hk hr]
  simp only [Int.cast_neg, neg_mul, Finset.sum_neg_distrib]

theorem lhs_shapeAt_sub {i j k r : ℕ} (hi : i < Q.n) (hj : j < Q.n) (hk : k < 2)
    (hr : r + 1 < Q.n) (rhs : ℤ) (x : Fin Q.dim → R) :
    Q.lhs (Q.mkRow (fun i' j' k' r' => shapeAt i j k (r + 1) i' j' k' r' -
      shapeAt i j k r i' j' k' r') (fun _ _ _ _ _ => 0) rhs).1 x =
      Q.sh x i j k (r + 1) - Q.sh x i j k r := by
  rw [lhs_mkRow_shape, ← Q.sum4_shapeAt (Q.sh x) hi hj hk hr,
    ← Q.sum4_shapeAt (Q.sh x) hi hj hk (by omega)]
  simp only [Int.cast_sub, sub_mul, Finset.sum_sub_distrib]

theorem lhs_cellAt {i j k r l : ℕ} (hi : i < Q.n) (hj : j < Q.n) (hk : k < 2) (hr : r < Q.n)
    (hl : l < Q.n) (rhs : ℤ) (x : Fin Q.dim → R) :
    Q.lhs (Q.mkRow (fun _ _ _ _ => 0) (cellAt i j k r l) rhs).1 x = Q.ce x i j k r l := by
  rw [lhs_mkRow_cell, Q.sum5_cellAt _ hi hj hk hr hl]

theorem lhs_neg_cellAt {i j k r l : ℕ} (hi : i < Q.n) (hj : j < Q.n) (hk : k < 2)
    (hr : r < Q.n) (hl : l < Q.n) (rhs : ℤ) (x : Fin Q.dim → R) :
    Q.lhs (Q.mkRow (fun _ _ _ _ => 0) (fun i' j' k' r' l' => -cellAt i j k r l i' j' k' r' l')
      rhs).1 x = -Q.ce x i j k r l := by
  rw [lhs_mkRow_cell, ← Q.sum5_cellAt (Q.ce x) hi hj hk hr hl]
  simp only [Int.cast_neg, neg_mul, Finset.sum_neg_distrib]

theorem lhs_mkRow_neg (f : ℕ → ℕ → ℕ → ℕ → ℤ) (g : ℕ → ℕ → ℕ → ℕ → ℕ → ℤ) (rhs rhs' : ℤ)
    (x : Fin Q.dim → R) :
    Q.lhs (Q.mkRow (fun i j k r => -f i j k r) (fun i j k r l => -g i j k r l) rhs).1 x =
      -Q.lhs (Q.mkRow f g rhs').1 x := by
  rw [lhs_mkRow, lhs_mkRow]
  simp only [Int.cast_neg, neg_mul, Finset.sum_neg_distrib]
  ring

/-- The length of row `r` of the shape of the factor `(j, k)` at the vertex `i`: `μ_r` for an
outgoing arrow, `μ₀ − μ_{d−1−r}` for an incoming one. -/
def rowLength (sh : ℕ → ℕ → ℕ → ℕ → R) (i j k r : ℕ) : R :=
  if Q.outSlot i j k then sh i j k r else sh j i k 0 - sh j i k (Q.blockDim i - 1 - r)

theorem lhs_rowSum {i j k r : ℕ} (hi : i < Q.n) (hj : j < Q.n) (hk : k < 2) (hr : r < Q.n)
    (hd : Q.blockDim i ≤ Q.n) (rhs : ℤ) (x : Fin Q.dim → R) :
    Q.lhs (Q.mkRow (Q.rowSumShape i j k r) (rowSumCell i j k r) rhs).1 x =
      -Q.rowLength (Q.sh x) i j k r + ∑ l ∈ range Q.n, Q.ce x i j k r l := by
  rw [lhs_mkRow]
  congr 1
  · unfold rowSumShape rowLength
    by_cases ho : Q.outSlot i j k = true
    · simp only [ho, ↓reduceIte, Int.cast_neg, neg_mul, Finset.sum_neg_distrib]
      rw [Q.sum4_shapeAt (Q.sh x) hi hj hk hr]
    · simp only [ho, Bool.false_eq_true, ↓reduceIte, Int.cast_add, Int.cast_neg, add_mul,
        neg_mul, Finset.sum_add_distrib, Finset.sum_neg_distrib]
      rw [Q.sum4_shapeAt (Q.sh x) hj hi hk (by omega),
        Q.sum4_shapeAt (Q.sh x) hj hi hk (by omega)]
      ring
  · have h : ∀ i' j' k' r' l', (rowSumCell i j k r i' j' k' r' l' : R) * Q.ce x i' j' k' r' l' =
        (shapeAt i j k r i' j' k' r' : R) * Q.ce x i' j' k' r' l' := fun _ _ _ _ _ => rfl
    simp only [h, ← Finset.mul_sum]
    rw [Q.sum4_shapeAt (fun i' j' k' r' => ∑ l ∈ range Q.n, Q.ce x i' j' k' r' l) hi hj hk hr]

theorem lhs_columnRow {i j k r l : ℕ} (h : Q.cellOK i j k (r + 1) l = true) (hi : i < Q.n)
    (hj : j < Q.n) (hk : k < 2) (hr : r + 1 < Q.n) (hl : l < Q.n) (x : Fin Q.dim → R) :
    Q.lhs (Q.columnRow i j k r l).1 x =
      ∑ l' ∈ range (l + 1), Q.ce x i j k (r + 1) l' - ∑ l' ∈ range l, Q.ce x i j k r l' := by
  unfold columnRow
  rw [ite_eq_left h, lhs_mkRow_cell]
  simp only [Int.cast_ite, Int.cast_sub, Int.cast_one, Int.cast_zero, ite_mul, zero_mul, sub_mul,
    one_mul, ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_sub_distrib,
    sum_range_ite_eq hi, sum_range_ite_eq hj, sum_range_ite_eq hk, sum_range_ite_eq hr,
    sum_range_ite_eq (by omega : r < Q.n), sum_range_ite_le hl, sum_range_ite_lt hl.le]

/-- The total number of entries `l` in the tableaux of the factors before `(j, k)` at the vertex
`i`. -/
def before (ce : ℕ → ℕ → ℕ → ℕ → ℕ → R) (i j k l : ℕ) : R :=
  ∑ j' ∈ range Q.n, ∑ k' ∈ range 2,
    if Q.slotBefore i j' k' j k then ∑ r' ∈ range Q.n, ce i j' k' r' l else 0

theorem slotBefore_self (i j k : ℕ) : Q.slotBefore i j k j k = false := by
  simp [slotBefore]

theorem lhs_latticeRow {i j k r l : ℕ} (h : Q.cellOK i j k r (l + 1) = true) (hi : i < Q.n)
    (hj : j < Q.n) (hk : k < 2) (hr : r < Q.n) (hl : l + 1 < Q.n) (x : Fin Q.dim → R) :
    Q.lhs (Q.latticeRow i j k r l).1 x =
      (∑ r' ∈ range (r + 1), Q.ce x i j k r' (l + 1) - ∑ r' ∈ range r, Q.ce x i j k r' l) +
        (Q.before (Q.ce x) i j k (l + 1) - Q.before (Q.ce x) i j k l) := by
  unfold latticeRow
  rw [ite_eq_left h, lhs_mkRow_cell]
  have hpt : ∀ i' j' k' r' l',
      (((if i' = i then
          if j' = j ∧ k' = k then
            ((if l' = l + 1 ∧ r' ≤ r then 1 else 0) - (if l' = l ∧ r' < r then 1 else 0) : ℤ)
          else if Q.slotBefore i j' k' j k then
            ((if l' = l + 1 then 1 else 0) - (if l' = l then 1 else 0) : ℤ)
          else 0
        else 0 : ℤ) : R) * Q.ce x i' j' k' r' l') =
      (if i' = i ∧ j' = j ∧ k' = k then
        (((if l' = l + 1 ∧ r' ≤ r then 1 else 0) - (if l' = l ∧ r' < r then 1 else 0) : ℤ) : R) *
          Q.ce x i j k r' l' else 0) +
      (if i' = i ∧ Q.slotBefore i j' k' j k = true then
        (((if l' = l + 1 then 1 else 0) - (if l' = l then 1 else 0) : ℤ) : R) *
          Q.ce x i j' k' r' l' else 0) := by
    intro i' j' k' r' l'
    by_cases h1 : i' = i
    · subst h1
      by_cases h2 : j' = j ∧ k' = k
      · obtain ⟨rfl, rfl⟩ := h2
        simp [Q.slotBefore_self]
      · simp only [h2, true_and, ↓reduceIte]
        split_ifs <;> simp
    · simp [h1]
  simp only [hpt, Finset.sum_add_distrib]
  congr 1
  · simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero, sum_range_ite_eq hi,
      sum_range_ite_eq hj, sum_range_ite_eq hk]
    simp only [Int.cast_sub, Int.cast_ite, Int.cast_one, Int.cast_zero, sub_mul, ite_mul, one_mul,
      zero_mul, Finset.sum_sub_distrib, sum_range_ite_eq hl,
      sum_range_ite_eq (by omega : l < Q.n), sum_range_ite_le hr, sum_range_ite_lt hr.le]
  · simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero, sum_range_ite_eq hi]
    simp only [Int.cast_sub, Int.cast_ite, Int.cast_one, Int.cast_zero, sub_mul, ite_mul, one_mul,
      zero_mul, Finset.sum_sub_distrib, sum_range_ite_eq hl, sum_range_ite_eq (by omega : l < Q.n)]
    unfold before
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j' _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k' _ => ?_
    split_ifs <;> simp

/-- The total shift `∑ μ₀` over the arrows into the vertex `i`. -/
def inShift (sh : ℕ → ℕ → ℕ → ℕ → R) (i : ℕ) : R :=
  ∑ i' ∈ range Q.n, ∑ k' ∈ range 2, if k' < Q.arrowCount i' i then sh i' i k' 0 else 0

/-- The total number of entries `l` over all tableaux at the vertex `i`. -/
def total (ce : ℕ → ℕ → ℕ → ℕ → ℕ → R) (i l : ℕ) : R :=
  ∑ j' ∈ range Q.n, ∑ k' ∈ range 2, ∑ r' ∈ range Q.n, ce i j' k' r' l

theorem lhs_final {i l : ℕ} (hi : i < Q.n) (hl : l < Q.n) (rhs : ℤ) (x : Fin Q.dim → R) :
    Q.lhs (Q.mkRow (Q.finalShape i) (finalCell i l) rhs).1 x =
      -Q.inShift (Q.sh x) i + Q.total (Q.ce x) i l := by
  have hn : 0 < Q.n := by omega
  rw [lhs_mkRow]
  congr 1
  · unfold finalShape inShift
    simp only [Int.cast_ite, Int.cast_neg, Int.cast_one, Int.cast_zero, ite_mul, neg_mul, one_mul,
      zero_mul, ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero, sum_range_ite_eq hi,
      sum_range_ite_eq hn]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i' _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k' _ => ?_
    split_ifs <;> simp
  · unfold finalCell total
    simp only [Int.cast_ite, Int.cast_one, Int.cast_zero, ite_mul, one_mul, zero_mul, ite_and,
      Finset.sum_ite_irrel, Finset.sum_const_zero, sum_range_ite_eq hi, sum_range_ite_eq hl]

omit [CommRing R] in
@[simp]
theorem mkRow_snd (f : ℕ → ℕ → ℕ → ℕ → ℤ) (g : ℕ → ℕ → ℕ → ℕ → ℕ → ℤ) (rhs : ℤ) :
    (Q.mkRow f g rhs).2 = rhs :=
  rfl

omit [CommRing R] in
@[simp]
theorem trivialRow_snd : Q.trivialRow.2 = 0 :=
  rfl

/-! ### The six families -/

/-- The conditions on the positional data under which the rows are read: vertices have positive
dimension and their intervals end by position `n`; there are at most two parallel arrows; arrows
join vertices, in increasing order. -/
structure WellFormed : Prop where
  dim_pos : ∀ i < Q.n, Q.isStart i = true → 0 < Q.blockDim i
  dim_le : ∀ i < Q.n, Q.isStart i = true → i + Q.blockDim i ≤ Q.n
  arrow_le : ∀ i < Q.n, ∀ j < Q.n, Q.arrowCount i j ≤ 2
  arrow_pos : ∀ i < Q.n, ∀ j < Q.n, 0 < Q.arrowCount i j →
    i < j ∧ Q.isStart i = true ∧ Q.isStart j = true

variable [LinearOrder R] [IsStrictOrderedRing R]

/-- The point `x` satisfies every inequality of the system. -/
def Holds (x : Fin Q.dim → R) : Prop := ∀ row ∈ Q.polytope.rows, Q.lhs row.1 x ≤ row.2

variable (sh : ℕ → ℕ → ℕ → ℕ → R) (ce : ℕ → ℕ → ℕ → ℕ → ℕ → R)

/-- Family 1: the partitions are nonnegative and weakly decreasing; unused partition variables
vanish. -/
def ShapeCond (i j k r : ℕ) : Prop :=
  if Q.shapeOK i j k r then
    0 ≤ sh i j k r ∧ (Q.shapeOK i j k (r + 1) = true → sh i j k (r + 1) ≤ sh i j k r)
  else sh i j k r = 0

/-- Family 2: the row counts are nonnegative; unused row-count variables vanish. -/
def CellCond (i j k r l : ℕ) : Prop :=
  if Q.cellOK i j k r l then 0 ≤ ce i j k r l else ce i j k r l = 0

/-- Family 3: row `r` of the tableau of each factor has the length of row `r` of its shape. -/
def RowSumCond (i j k r : ℕ) : Prop :=
  (Q.isStart i && (Q.outSlot i j k || Q.inSlot i j k) && decide (r < Q.blockDim i)) = true →
    ∑ l ∈ range Q.n, ce i j k r l = Q.rowLength sh i j k r

/-- Family 4: the columns of each tableau are strict. -/
def ColumnCond (i j k r l : ℕ) : Prop :=
  Q.cellOK i j k (r + 1) l = true →
    ∑ l' ∈ range (l + 1), ce i j k (r + 1) l' ≤ ∑ l' ∈ range l, ce i j k r l'

/-- Family 5: each tableau is lattice from the weight accumulated before it. -/
def LatticeCond (i j k r l : ℕ) : Prop :=
  Q.cellOK i j k r (l + 1) = true →
    Q.before ce i j k (l + 1) + ∑ r' ∈ range (r + 1), ce i j k r' (l + 1) ≤
      Q.before ce i j k l + ∑ r' ∈ range r, ce i j k r' l

/-- Family 6: the accumulated weight at each vertex, with the shifts of the incoming arrows, is the
weight of the vertex. -/
def FinalCond (i l : ℕ) : Prop :=
  (Q.isStart i && decide (l < Q.blockDim i)) = true →
    -Q.inShift sh i + Q.total ce i l = Q.weight i l

/-- **The six families** of conditions on the coordinates `sh`, `ce`. -/
def Conditions : Prop :=
  (∀ i < Q.n, ∀ j < Q.n, ∀ k < 2, ∀ r < Q.n, Q.ShapeCond sh i j k r) ∧
  (∀ i < Q.n, ∀ j < Q.n, ∀ k < 2, ∀ r < Q.n, ∀ l < Q.n, Q.CellCond ce i j k r l) ∧
  (∀ i < Q.n, ∀ j < Q.n, ∀ k < 2, ∀ r < Q.n, Q.RowSumCond sh ce i j k r) ∧
  (∀ i < Q.n, ∀ j < Q.n, ∀ k < 2, ∀ r < Q.n, ∀ l < Q.n, Q.ColumnCond ce i j k r l) ∧
  (∀ i < Q.n, ∀ j < Q.n, ∀ k < 2, ∀ r < Q.n, ∀ l < Q.n, Q.LatticeCond ce i j k r l) ∧
  ∀ i < Q.n, ∀ l < Q.n, Q.FinalCond sh ce i l

/-! ### Reading the families -/

variable {Q}

theorem WellFormed.lt_of_shapeOK (hQ : Q.WellFormed) {i j k r : ℕ} (hi : i < Q.n)
    (hj : j < Q.n) (h : Q.shapeOK i j k r = true) : r < Q.n := by
  simp only [shapeOK, Bool.and_eq_true, decide_eq_true_eq] at h
  have := hQ.arrow_pos i hi j hj (by omega)
  have := hQ.dim_le i hi this.2.1
  omega

theorem WellFormed.dim_le_n (hQ : Q.WellFormed) {i : ℕ} (hi : i < Q.n)
    (hs : Q.isStart i = true) : Q.blockDim i ≤ Q.n := by
  have := hQ.dim_le i hi hs
  omega

omit [LinearOrder R] [IsStrictOrderedRing R] in
theorem forall_mem_loop4 {α : Type} {f : ℕ → ℕ → ℕ → ℕ → List α} {P : α → Prop} :
    (∀ x ∈ Q.loop4 f, P x) ↔ ∀ i < Q.n, ∀ j < Q.n, ∀ k < 2, ∀ r < Q.n, ∀ x ∈ f i j k r, P x := by
  simp only [mem_loop4]
  constructor
  · intro h i hi j hj k hk r hr x hx
    exact h x ⟨i, hi, j, hj, k, hk, r, hr, hx⟩
  · rintro h x ⟨i, hi, j, hj, k, hk, r, hr, hx⟩
    exact h i hi j hj k hk r hr x hx

omit [LinearOrder R] [IsStrictOrderedRing R] in
theorem forall_mem_loop5 {α : Type} {f : ℕ → ℕ → ℕ → ℕ → ℕ → List α} {P : α → Prop} :
    (∀ x ∈ Q.loop5 f, P x) ↔
      ∀ i < Q.n, ∀ j < Q.n, ∀ k < 2, ∀ r < Q.n, ∀ l < Q.n, ∀ x ∈ f i j k r l, P x := by
  simp only [mem_loop5]
  constructor
  · intro h i hi j hj k hk r hr l hl x hx
    exact h x ⟨i, hi, j, hj, k, hk, r, hr, l, hl, hx⟩
  · rintro h x ⟨i, hi, j, hj, k, hk, r, hr, l, hl, hx⟩
    exact h i hi j hj k hk r hr l hl x hx

theorem shapeRows_iff (hQ : Q.WellFormed) (x : Fin Q.dim → R) {i j k r : ℕ} (hi : i < Q.n)
    (hj : j < Q.n) (hk : k < 2) (hr : r < Q.n) :
    (∀ row ∈ Q.shapeRows i j k r, Q.lhs row.1 x ≤ row.2) ↔ Q.ShapeCond (Q.sh x) i j k r := by
  unfold shapeRows ShapeCond
  split_ifs with h1 h2
  · have hr1 := hQ.lt_of_shapeOK hi hj h2
    simp only [mkRow_snd, List.forall_mem_cons, List.not_mem_nil,
      IsEmpty.forall_iff, implies_true, and_true,
      Q.lhs_neg_shapeAt hi hj hk hr, Q.lhs_shapeAt_sub hi hj hk hr1, Int.cast_zero, neg_nonpos,
      sub_nonpos, h2, forall_const]
  · simp only [mkRow_snd, trivialRow_snd, List.forall_mem_cons, List.not_mem_nil,
      IsEmpty.forall_iff, implies_true, and_true,
      Q.lhs_neg_shapeAt hi hj hk hr, Q.lhs_trivialRow, Int.cast_zero, neg_nonpos, le_refl, h2,
      Bool.false_eq_true, IsEmpty.forall_iff]
  · simp only [mkRow_snd, List.forall_mem_cons, List.not_mem_nil,
      IsEmpty.forall_iff, implies_true, and_true,
      Q.lhs_shapeAt hi hj hk hr, Q.lhs_neg_shapeAt hi hj hk hr, Int.cast_zero, neg_nonpos]
    exact ⟨fun h => le_antisymm h.1 h.2, fun h => ⟨h.le, h.ge⟩⟩

theorem cellRows_iff (x : Fin Q.dim → R) {i j k r l : ℕ} (hi : i < Q.n) (hj : j < Q.n)
    (hk : k < 2) (hr : r < Q.n) (hl : l < Q.n) :
    (∀ row ∈ Q.cellRows i j k r l, Q.lhs row.1 x ≤ row.2) ↔ Q.CellCond (Q.ce x) i j k r l := by
  unfold cellRows CellCond
  split_ifs with h1
  · simp only [mkRow_snd, trivialRow_snd, List.forall_mem_cons, List.not_mem_nil,
      IsEmpty.forall_iff, implies_true, and_true,
      Q.lhs_neg_cellAt hi hj hk hr hl, Q.lhs_trivialRow, Int.cast_zero, neg_nonpos, le_refl]
  · simp only [mkRow_snd, List.forall_mem_cons, List.not_mem_nil,
      IsEmpty.forall_iff, implies_true, and_true,
      Q.lhs_cellAt hi hj hk hr hl, Q.lhs_neg_cellAt hi hj hk hr hl, Int.cast_zero, neg_nonpos]
    exact ⟨fun h => le_antisymm h.1 h.2, fun h => ⟨h.le, h.ge⟩⟩

theorem rowSumRows_iff (hQ : Q.WellFormed) (x : Fin Q.dim → R) {i j k r : ℕ} (hi : i < Q.n)
    (hj : j < Q.n) (hk : k < 2) (hr : r < Q.n) :
    (∀ row ∈ Q.rowSumRows i j k r, Q.lhs row.1 x ≤ row.2) ↔
      Q.RowSumCond (Q.sh x) (Q.ce x) i j k r := by
  unfold rowSumRows RowSumCond
  split_ifs with h1
  · have hs : Q.isStart i = true := by
      simp only [Bool.and_eq_true] at h1
      exact h1.1.1
    have hd := hQ.dim_le_n hi hs
    simp only [mkRow_snd, List.forall_mem_cons, List.not_mem_nil,
      IsEmpty.forall_iff, implies_true, and_true,
      Q.lhs_mkRow_neg _ _ 0 0, Q.lhs_rowSum hi hj hk hr hd, Int.cast_zero]
    refine ⟨fun h _ => le_antisymm (by linarith [h.1, h.2]) (by linarith [h.1, h.2]),
      fun h => ?_⟩
    rw [h h1]
    constructor <;> simp
  · simp only [trivialRow_snd, List.forall_mem_cons, List.not_mem_nil,
      IsEmpty.forall_iff, implies_true, and_true,
      Q.lhs_trivialRow, Int.cast_zero, le_refl, h1, Bool.false_eq_true, IsEmpty.forall_iff]

theorem columnRow_iff (x : Fin Q.dim → R) {i j k r l : ℕ} (hi : i < Q.n) (hj : j < Q.n)
    (hk : k < 2) (hr : r < Q.n) (hl : l < Q.n) (hQ : Q.WellFormed) :
    Q.lhs (Q.columnRow i j k r l).1 x ≤ (Q.columnRow i j k r l).2 ↔
      Q.ColumnCond (Q.ce x) i j k r l := by
  unfold ColumnCond
  by_cases h : Q.cellOK i j k (r + 1) l = true
  · have hs : Q.isStart i = true ∧ r + 1 < Q.blockDim i := by
      simp only [cellOK, Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨h.1.1.1, h.1.2⟩
    have hd := hQ.dim_le_n hi hs.1
    rw [Q.lhs_columnRow h hi hj hk (by omega) hl]
    have h2 : (Q.columnRow i j k r l).2 = 0 := by
      unfold columnRow
      rw [ite_eq_left h]
      rfl
    rw [h2, Int.cast_zero, sub_nonpos]
    exact ⟨fun h' _ => h', fun h' => h' h⟩
  · have h2 : Q.columnRow i j k r l = Q.trivialRow := by
      unfold columnRow
      rw [ite_eq_right h]
    rw [h2, Q.lhs_trivialRow, trivialRow_snd, Int.cast_zero]
    exact ⟨fun _ h' => absurd h' h, fun _ => le_refl _⟩

theorem latticeRow_iff (x : Fin Q.dim → R) {i j k r l : ℕ} (hi : i < Q.n) (hj : j < Q.n)
    (hk : k < 2) (hr : r < Q.n) (hQ : Q.WellFormed) :
    Q.lhs (Q.latticeRow i j k r l).1 x ≤ (Q.latticeRow i j k r l).2 ↔
      Q.LatticeCond (Q.ce x) i j k r l := by
  unfold LatticeCond
  by_cases h : Q.cellOK i j k r (l + 1) = true
  · have hs : Q.isStart i = true ∧ l + 1 < Q.blockDim i := by
      simp only [cellOK, Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨h.1.1.1, h.2⟩
    have hd := hQ.dim_le_n hi hs.1
    rw [Q.lhs_latticeRow h hi hj hk hr (by omega)]
    have h2 : (Q.latticeRow i j k r l).2 = 0 := by
      unfold latticeRow
      rw [ite_eq_left h]
      rfl
    rw [h2, Int.cast_zero]
    constructor
    · intro h' _
      linarith
    · intro h'
      linarith [h' h]
  · have h2 : Q.latticeRow i j k r l = Q.trivialRow := by
      unfold latticeRow
      rw [ite_eq_right h]
    rw [h2, Q.lhs_trivialRow, trivialRow_snd, Int.cast_zero]
    exact ⟨fun _ h' => absurd h' h, fun _ => le_refl _⟩

theorem finalRows_iff (x : Fin Q.dim → R) {i l : ℕ} (hi : i < Q.n) (hl : l < Q.n) :
    (∀ row ∈ Q.finalRows i l, Q.lhs row.1 x ≤ row.2) ↔ Q.FinalCond (Q.sh x) (Q.ce x) i l := by
  unfold finalRows FinalCond
  split_ifs with h1
  · simp only [mkRow_snd, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, Q.lhs_mkRow_neg _ _ _ (Q.weight i l), Q.lhs_final hi hl,
      Int.cast_neg, neg_le_neg_iff]
    exact ⟨fun h _ => le_antisymm h.1 h.2, fun h => ⟨(h h1).le, (h h1).ge⟩⟩
  · simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
      and_true, Q.lhs_trivialRow, trivialRow_snd, Int.cast_zero, le_refl, true_iff]
    exact fun h' => absurd h' h1

/-- **Reading the system**: a point satisfies the system iff its coordinates satisfy the six
families of conditions. -/
theorem holds_iff (hQ : Q.WellFormed) (x : Fin Q.dim → R) :
    Q.Holds x ↔ Q.Conditions (Q.sh x) (Q.ce x) := by
  unfold Holds Conditions polytope
  simp only [List.forall_mem_append, forall_mem_loop4, forall_mem_loop5, List.forall_mem_flatMap,
    List.mem_range, List.forall_mem_singleton, and_assoc]
  refine and_congr ?_ (and_congr ?_ (and_congr ?_ (and_congr ?_ (and_congr ?_ ?_))))
  · exact forall₂_congr fun i hi => forall₂_congr fun j hj => forall₂_congr fun k hk =>
      forall₂_congr fun r hr => shapeRows_iff hQ x hi hj hk hr
  · exact forall₂_congr fun i hi => forall₂_congr fun j hj => forall₂_congr fun k hk =>
      forall₂_congr fun r hr => forall₂_congr fun l hl => cellRows_iff x hi hj hk hr hl
  · exact forall₂_congr fun i hi => forall₂_congr fun j hj => forall₂_congr fun k hk =>
      forall₂_congr fun r hr => rowSumRows_iff hQ x hi hj hk hr
  · exact forall₂_congr fun i hi => forall₂_congr fun j hj => forall₂_congr fun k hk =>
      forall₂_congr fun r hr => forall₂_congr fun l hl => columnRow_iff x hi hj hk hr hl hQ
  · exact forall₂_congr fun i hi => forall₂_congr fun j hj => forall₂_congr fun k hk =>
      forall₂_congr fun r hr => forall₂_congr fun l _ => latticeRow_iff x hi hj hk hr hQ
  · exact forall₂_congr fun i hi => forall₂_congr fun l hl => finalRows_iff x hi hl

/-! ### Integer and real points -/

/-- The real (or rational) points of the polytope are the points satisfying the system. -/
theorem mem_points_iff_holds {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (x : Fin Q.polytope.dim → K) : x ∈ Q.polytope.points K ↔ Q.Holds (R := K) x :=
  Iff.rfl

/-- The integer points of the polytope are the integer points satisfying the system. -/
theorem mem_intPoints_iff_holds (z : Fin Q.polytope.dim → ℤ) :
    z ∈ Q.polytope.intPoints ↔ Q.Holds (R := ℤ) z := by
  simp only [IntPolyhedron.intPoints, Set.mem_ofPred_eq, Holds, lhs, Int.cast_id]
  rfl

/-- **The integer points**, read in coordinates. -/
theorem mem_intPoints_iff (hQ : Q.WellFormed) (z : Fin Q.polytope.dim → ℤ) :
    z ∈ Q.polytope.intPoints ↔ Q.Conditions (Q.sh z) (Q.ce z) :=
  (mem_intPoints_iff_holds z).trans (holds_iff hQ z)

/-- **The real points**, read in coordinates. -/
theorem mem_points_iff {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (hQ : Q.WellFormed) (x : Fin Q.polytope.dim → K) :
    x ∈ Q.polytope.points K ↔ Q.Conditions (Q.sh x) (Q.ce x) :=
  (mem_points_iff_holds x).trans (holds_iff hQ x)

end PositionalQuiver

/-! ### Changing the weight -/

namespace PositionalQuiver

variable (Q : PositionalQuiver)

/-- The same positional quiver with the weight `w`. -/
def withWeight (w : ℕ → ℕ → ℤ) : PositionalQuiver :=
  { Q with weight := w }

theorem withWeight_weight : Q.withWeight Q.weight = Q :=
  rfl

theorem WellFormed.withWeight {Q : PositionalQuiver} (hQ : Q.WellFormed) (w : ℕ → ℕ → ℤ) :
    (Q.withWeight w).WellFormed :=
  ⟨hQ.1, hQ.2, hQ.3, hQ.4⟩

theorem finalRows_withWeight (w : ℕ → ℕ → ℤ) (i l : ℕ) :
    (Q.withWeight w).finalRows i l =
      if Q.isStart i && decide (l < Q.blockDim i) then
        [Q.mkRow (Q.finalShape i) (finalCell i l) (w i l),
          Q.mkRow (fun i' j' k' r' => -Q.finalShape i i' j' k' r')
            (fun i' j' k' r' l' => -finalCell i l i' j' k' r' l') (-w i l)]
      else [Q.trivialRow, Q.trivialRow] :=
  rfl

theorem rhs_eq_zero_of_mem_shapeRows {i j k r : ℕ} {row : List ℤ × ℤ}
    (h : row ∈ Q.shapeRows i j k r) : row.2 = 0 := by
  unfold shapeRows at h
  split_ifs at h <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at h <;>
    rcases h with rfl | rfl <;> rfl

theorem rhs_eq_zero_of_mem_cellRows {i j k r l : ℕ} {row : List ℤ × ℤ}
    (h : row ∈ Q.cellRows i j k r l) : row.2 = 0 := by
  unfold cellRows at h
  split_ifs at h <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at h <;>
    rcases h with rfl | rfl <;> rfl

theorem rhs_eq_zero_of_mem_rowSumRows {i j k r : ℕ} {row : List ℤ × ℤ}
    (h : row ∈ Q.rowSumRows i j k r) : row.2 = 0 := by
  unfold rowSumRows at h
  split_ifs at h <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at h <;>
    rcases h with rfl | rfl <;> rfl

theorem columnRow_snd (i j k r l : ℕ) : (Q.columnRow i j k r l).2 = 0 := by
  unfold columnRow
  split_ifs <;> rfl

theorem latticeRow_snd (i j k r l : ℕ) : (Q.latticeRow i j k r l).2 = 0 := by
  unfold latticeRow
  split_ifs <;> rfl

/-- The rows of `P` with right-hand sides multiplied by `N`. -/
theorem map_scale_eq_self {l : List (List ℤ × ℤ)} (N : ℕ) (h : ∀ row ∈ l, row.2 = 0) :
    l.map (fun row => (row.1, (N : ℤ) * row.2)) = l := by
  conv_rhs => rw [← List.map_id l]
  refine List.map_congr_left fun row hrow => ?_
  obtain ⟨u, v⟩ := row
  have hv : v = 0 := h _ hrow
  simp [hv]

/-- **Homogeneity**: scaling the weight by `N` scales the right-hand sides by `N`. -/
theorem polytope_withWeight_nsmul (N : ℕ) :
    (Q.withWeight fun i l => N * Q.weight i l).polytope = Q.polytope.scaleRhs N := by
  simp only [IntPolyhedron.scaleRhs, polytope, List.map_append]
  have h1 := map_scale_eq_self (l := Q.loop4 Q.shapeRows) N fun row h => by
    obtain ⟨_, _, _, _, _, _, _, _, h⟩ := Q.mem_loop4.1 h
    exact Q.rhs_eq_zero_of_mem_shapeRows h
  have h2 := map_scale_eq_self (l := Q.loop5 Q.cellRows) N fun row h => by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, h⟩ := Q.mem_loop5.1 h
    exact Q.rhs_eq_zero_of_mem_cellRows h
  have h3 := map_scale_eq_self (l := Q.loop4 Q.rowSumRows) N fun row h => by
    obtain ⟨_, _, _, _, _, _, _, _, h⟩ := Q.mem_loop4.1 h
    exact Q.rhs_eq_zero_of_mem_rowSumRows h
  have h4 := map_scale_eq_self (l := Q.loop5 fun i j k r l => [Q.columnRow i j k r l]) N
    fun row h => by
      obtain ⟨_, _, _, _, _, _, _, _, _, _, h⟩ := Q.mem_loop5.1 h
      rw [List.mem_singleton] at h
      rw [h, columnRow_snd]
  have h5 := map_scale_eq_self (l := Q.loop5 fun i j k r l => [Q.latticeRow i j k r l]) N
    fun row h => by
      obtain ⟨_, _, _, _, _, _, _, _, _, _, h⟩ := Q.mem_loop5.1 h
      rw [List.mem_singleton] at h
      rw [h, latticeRow_snd]
  rw [h1, h2, h3, h4, h5]
  congr 1
  refine congrArg₂ (fun u v : List (List ℤ × ℤ) => u ++ v) rfl ?_
  simp only [List.map_flatMap]
  refine List.flatMap_congr fun i _ => List.flatMap_congr fun l _ => ?_
  rw [finalRows_withWeight]
  unfold finalRows
  split_ifs <;> simp [mkRow, trivialRow]

/-- The polytope only depends on the weight at the vertices, on the entries below their
dimension. -/
theorem polytope_withWeight_congr {w w' : ℕ → ℕ → ℤ}
    (h : ∀ i < Q.n, Q.isStart i = true → ∀ l < Q.blockDim i, w i l = w' i l) :
    (Q.withWeight w).polytope = (Q.withWeight w').polytope := by
  simp only [polytope]
  congr 1
  refine congrArg₂ (fun u v : List (List ℤ × ℤ) => u ++ v) rfl ?_
  refine List.flatMap_congr fun i hi => List.flatMap_congr fun l hl => ?_
  rw [List.mem_range] at hi hl
  rw [finalRows_withWeight, finalRows_withWeight]
  split_ifs with h1
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
    rw [h i hi h1.1 l h1.2]
  · rfl

end PositionalQuiver

/-! ### The canonical quiver of a triple -/

variable (a b c : List ℕ)

theorem blockDim_pos (i : ℕ) : 0 < blockDim a b c i := by
  unfold blockDim
  omega

theorem add_blockDim_le {i : ℕ} (hi : i < c.length) : i + blockDim a b c i ≤ c.length := by
  unfold blockDim
  have := List.length_filter_le (fun t => (List.range (t + 1)).all fun s =>
    !isStart a b c (i + 1 + s)) (List.range (c.length - (i + 1)))
  rw [List.length_range] at this
  omega

theorem arrowCount_le_two (i j : ℕ) : arrowCount a b c i j ≤ 2 := by
  unfold arrowCount
  have : cmpAt a b c i j ≤ 2 := by
    unfold cmpAt
    split_ifs <;> norm_num
  split_ifs <;> omega

theorem lt_of_arrowCount_pos {i j : ℕ} (h : 0 < arrowCount a b c i j) :
    i < j ∧ isStart a b c i = true ∧ isStart a b c j = true := by
  unfold arrowCount at h
  split_ifs at h with h1
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
    exact ⟨h1.2, h1.1.1, h1.1.2⟩
  · omega

/-- **The positional quiver of any triple is well formed**, for every weight. -/
theorem wellFormed_positionalOf (w : ℕ → ℕ → ℤ) :
    ((positionalOf a b c).withWeight w).WellFormed where
  dim_pos _ _ _ := blockDim_pos a b c _
  dim_le _ hi _ := add_blockDim_le a b c hi
  arrow_le i _ j _ := arrowCount_le_two a b c i j
  arrow_pos _ _ _ _ h := lt_of_arrowCount_pos a b c h

/-- The polytope `P(a, b, c)` is the polytope of its positional quiver. -/
theorem quiverPolytope_eq_withWeight :
    quiverPolytope a b c = ((positionalOf a b c).withWeight (positionalOf a b c).weight).polytope :=
  rfl

end Schubert.RS.Quiver.Flat
