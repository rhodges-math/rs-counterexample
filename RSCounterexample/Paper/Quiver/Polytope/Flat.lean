import RSCounterexample.Paper.Polyhedra.IntPolyhedron
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Data.List.GetD
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The polytope `P(a, b, c)` of Theorem 1.4

The explicit polytope of Theorem 1.4 of the paper, as a finite system of integer linear inequalities
computed from the lists `a, b, c` by loops over index ranges. Its construction follows
Vergne–Walter (M. Vergne, M. Walter, *Moment cone membership for quivers in strongly polynomial
time*, arXiv:2303.14821, Theorem 1): one partition per arrow of the quiver, and at each vertex a
chain of Littlewood–Richardson tableaux, one per incident arrow. The tableaux are recorded by their
row counts.

**Positional layout.** All indices are positions `0, …, n − 1` of the input (`n = c.length`). The
vertices of the quiver are the starting positions `i` of the intervals of the canonical partition
(`isStart`), of dimension `blockDim i`; between starts `i < j` there are `arrowCount i j ≤ 2` arrows
`i → j`, numbered `k = 0, 1`.

**Variables** (`dim = 2n³ + 2n⁴`):
* `shapeCol i j k r`: row `r` of the partition `μ` of the arrow `(i → j, k)`;
* `cellCol i j k r l`: at the vertex `i`, for the factor of the arrow between `i` and `j` numbered
  `k` (outgoing if `i < j`, incoming if `j < i`), the number of entries `l` in row `r` of its
  tableau.
Variables that do not belong to an arrow, a row, a vertex or a letter are fixed to `0`.

**Constraints** (coefficients in `{−1, 0, 1}`):
1. the partitions are weakly decreasing and nonnegative, with at most `min(d_i, d_j)` rows;
2. the row counts are nonnegative;
3. row `r` of the factor's tableau has `μ_r` cells (outgoing arrow) or `μ₀ − μ_{d−1−r}` cells
   (incoming arrow: the shape of `s_μ(x⁻¹) = det^{−μ₀} s_{μ^c}(x)`);
4. the columns of each tableau are strict;
5. each tableau is lattice from the weight accumulated by the factors before it (outgoing arrows
   first, then incoming ones, each by position and number);
6. at every vertex the accumulated weight, with the shifts `−μ₀` of the incoming factors, is the
   weight `λ` of the vertex.

Only the rows of family 6 have a nonzero right-hand side, the entries `ν_x = c_x − a_x − b_x`.

## Main definitions

* `Schubert.RS.Quiver.Flat.PositionalQuiver`: the positional data of a quiver with weights.
* `Schubert.RS.Quiver.Flat.PositionalQuiver.polytope`: its polytope.
* `Schubert.RS.Quiver.Flat.positionalOf`: the data of the canonical quiver of `(a, b, c)`.
* `Schubert.RS.Quiver.Flat.quiverPolytope`: the polytope `P(a, b, c)`.
-/

namespace Schubert.RS.Quiver.Flat

/-- Positional data of a quiver with dimension vector and weight, with vertices among the positions
`0, …, n − 1` and at most two parallel arrows. -/
structure PositionalQuiver where
  /-- The number of positions. -/
  n : ℕ
  /-- The vertices. -/
  isStart : ℕ → Bool
  /-- The dimension of the vertex at a position. -/
  blockDim : ℕ → ℕ
  /-- The number of arrows `i → j` (at most two). -/
  arrowCount : ℕ → ℕ → ℕ
  /-- Entry `l` of the weight of the vertex at `i`. -/
  weight : ℕ → ℕ → ℤ

namespace PositionalQuiver

variable (Q : PositionalQuiver)

/-- The number of variables, `2n³ + 2n⁴`. -/
def dim : ℕ := 2 * Q.n ^ 3 + 2 * Q.n ^ 4

/-- The variable of row `r` of the partition of the arrow `(i → j, k)`. -/
def shapeCol (i j k r : ℕ) : ℕ := ((i * Q.n + j) * 2 + k) * Q.n + r

/-- The variable counting the entries `l` in row `r` of the tableau of the factor `(j, k)` at the
vertex `i`. -/
def cellCol (i j k r l : ℕ) : ℕ := 2 * Q.n ^ 3 + (((i * Q.n + j) * 2 + k) * Q.n + r) * Q.n + l

/-- The partition variable `(i, j, k, r)` belongs to an arrow and a row. -/
def shapeOK (i j k r : ℕ) : Bool :=
  decide (k < Q.arrowCount i j) && decide (r < min (Q.blockDim i) (Q.blockDim j))

/-- The factor `(j, k)` at the vertex `i` is an outgoing arrow `i → j`. -/
def outSlot (i j k : ℕ) : Bool := decide (k < Q.arrowCount i j)

/-- The factor `(j, k)` at the vertex `i` is an incoming arrow `j → i`. -/
def inSlot (i j k : ℕ) : Bool := decide (k < Q.arrowCount j i)

/-- The row-count variable `(i, j, k, r, l)` belongs to a vertex, a factor, a row and a letter. -/
def cellOK (i j k r l : ℕ) : Bool :=
  Q.isStart i && (Q.outSlot i j k || Q.inSlot i j k) && decide (r < Q.blockDim i) &&
    decide (l < Q.blockDim i)

/-- The rank of the position `j` in the order of the factors at the vertex `i`: the positions after
`i` first, then the positions before `i`. -/
def slotRank (i j : ℕ) : ℕ := (j + Q.n - i - 1) % Q.n

/-- The factor `(j', k')` comes before the factor `(j, k)` at the vertex `i`. -/
def slotBefore (i j' k' j k : ℕ) : Bool :=
  decide (Q.slotRank i j' < Q.slotRank i j) || (decide (j' = j) && decide (k' < k))

/-- The coefficient of the variable `col` in a row given by its coefficients `f` on the partition
variables and `g` on the row-count variables. -/
def colFun (f : ℕ → ℕ → ℕ → ℕ → ℤ) (g : ℕ → ℕ → ℕ → ℕ → ℕ → ℤ) (col : ℕ) : ℤ :=
  if col < 2 * Q.n ^ 3 then
    f (col / (2 * Q.n ^ 2)) (col / (2 * Q.n) % Q.n) (col / Q.n % 2) (col % Q.n)
  else
    g ((col - 2 * Q.n ^ 3) / (2 * Q.n ^ 3)) ((col - 2 * Q.n ^ 3) / (2 * Q.n ^ 2) % Q.n)
      ((col - 2 * Q.n ^ 3) / Q.n ^ 2 % 2) ((col - 2 * Q.n ^ 3) / Q.n % Q.n)
      ((col - 2 * Q.n ^ 3) % Q.n)

/-- The row `∑ coefficients · x ≤ rhs`. -/
def mkRow (f : ℕ → ℕ → ℕ → ℕ → ℤ) (g : ℕ → ℕ → ℕ → ℕ → ℕ → ℤ) (rhs : ℤ) : List ℤ × ℤ :=
  ((List.range Q.dim).map (Q.colFun f g), rhs)

/-- The trivial row `0 ≤ 0`. -/
def trivialRow : List ℤ × ℤ := Q.mkRow (fun _ _ _ _ => 0) (fun _ _ _ _ _ => 0) 0

/-- `1` at one partition variable. -/
def shapeAt (i j k r : ℕ) : ℕ → ℕ → ℕ → ℕ → ℤ := fun i' j' k' r' =>
  if i' = i ∧ j' = j ∧ k' = k ∧ r' = r then 1 else 0

/-- `1` at one row-count variable. -/
def cellAt (i j k r l : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ → ℤ := fun i' j' k' r' l' =>
  if i' = i ∧ j' = j ∧ k' = k ∧ r' = r ∧ l' = l then 1 else 0

/-- Family 1: nonnegativity and monotonicity of the partitions, and the unused partition variables
fixed to `0`. -/
def shapeRows (i j k r : ℕ) : List (List ℤ × ℤ) :=
  if Q.shapeOK i j k r then
    [Q.mkRow (fun i' j' k' r' => -shapeAt i j k r i' j' k' r') (fun _ _ _ _ _ => 0) 0,
      if Q.shapeOK i j k (r + 1) then
        Q.mkRow (fun i' j' k' r' => shapeAt i j k (r + 1) i' j' k' r' -
          shapeAt i j k r i' j' k' r') (fun _ _ _ _ _ => 0) 0
      else Q.trivialRow]
  else
    [Q.mkRow (shapeAt i j k r) (fun _ _ _ _ _ => 0) 0,
      Q.mkRow (fun i' j' k' r' => -shapeAt i j k r i' j' k' r') (fun _ _ _ _ _ => 0) 0]

/-- Family 2: nonnegativity of the row counts, and the unused row-count variables fixed to `0`. -/
def cellRows (i j k r l : ℕ) : List (List ℤ × ℤ) :=
  if Q.cellOK i j k r l then
    [Q.mkRow (fun _ _ _ _ => 0) (fun i' j' k' r' l' => -cellAt i j k r l i' j' k' r' l') 0,
      Q.trivialRow]
  else
    [Q.mkRow (fun _ _ _ _ => 0) (cellAt i j k r l) 0,
      Q.mkRow (fun _ _ _ _ => 0) (fun i' j' k' r' l' => -cellAt i j k r l i' j' k' r' l') 0]

/-- The coefficients of `(row length of the tableau) − (row length of the factor's shape)` for row
`r` of the factor `(j, k)` at the vertex `i`. -/
def rowSumShape (i j k r : ℕ) : ℕ → ℕ → ℕ → ℕ → ℤ := fun i' j' k' r' =>
  if Q.outSlot i j k then -shapeAt i j k r i' j' k' r'
  else -shapeAt j i k 0 i' j' k' r' + shapeAt j i k (Q.blockDim i - 1 - r) i' j' k' r'

/-- The coefficients of the row length of the tableau of the factor `(j, k)` at `i`, row `r`. -/
def rowSumCell (i j k r : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ → ℤ := fun i' j' k' r' _ =>
  if i' = i ∧ j' = j ∧ k' = k ∧ r' = r then 1 else 0

/-- Family 3: row `r` of the tableau of each factor has the length of row `r` of its shape. -/
def rowSumRows (i j k r : ℕ) : List (List ℤ × ℤ) :=
  if Q.isStart i && (Q.outSlot i j k || Q.inSlot i j k) && decide (r < Q.blockDim i) then
    [Q.mkRow (Q.rowSumShape i j k r) (rowSumCell i j k r) 0,
      Q.mkRow (fun i' j' k' r' => -Q.rowSumShape i j k r i' j' k' r')
        (fun i' j' k' r' l' => -rowSumCell i j k r i' j' k' r' l') 0]
  else [Q.trivialRow, Q.trivialRow]

/-- Family 4: strict columns. The entries `≤ l` of row `r + 1` are at most as many as the entries
`< l` of row `r`. -/
def columnRow (i j k r l : ℕ) : List ℤ × ℤ :=
  if Q.cellOK i j k (r + 1) l then
    Q.mkRow (fun _ _ _ _ => 0) (fun i' j' k' r' l' =>
      if i' = i ∧ j' = j ∧ k' = k then
        (if r' = r + 1 ∧ l' ≤ l then 1 else 0) - (if r' = r ∧ l' < l then 1 else 0)
      else 0) 0
  else Q.trivialRow

/-- Family 5: the lattice condition. With `κ` the weight accumulated before the factor `(j, k)`,
`κ_{l+1} + #{entries l + 1 in rows ≤ r} ≤ κ_l + #{entries l in rows < r}`. -/
def latticeRow (i j k r l : ℕ) : List ℤ × ℤ :=
  if Q.cellOK i j k r (l + 1) then
    Q.mkRow (fun _ _ _ _ => 0) (fun i' j' k' r' l' =>
      if i' = i then
        if j' = j ∧ k' = k then
          (if l' = l + 1 ∧ r' ≤ r then 1 else 0) - (if l' = l ∧ r' < r then 1 else 0)
        else if Q.slotBefore i j' k' j k then
          (if l' = l + 1 then 1 else 0) - (if l' = l then 1 else 0)
        else 0
      else 0) 0
  else Q.trivialRow

/-- The coefficients of the weight accumulated over all factors at the vertex `i`, entry `l`,
including the shifts `−μ₀` of the incoming arrows. -/
def finalShape (i : ℕ) : ℕ → ℕ → ℕ → ℕ → ℤ := fun i' j' k' r' =>
  if j' = i ∧ r' = 0 ∧ k' < Q.arrowCount i' i then -1 else 0

/-- See `finalShape`. -/
def finalCell (i l : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ → ℤ := fun i' _ _ _ l' =>
  if i' = i ∧ l' = l then 1 else 0

/-- Family 6: the accumulated weight at every vertex is its weight. -/
def finalRows (i l : ℕ) : List (List ℤ × ℤ) :=
  if Q.isStart i && decide (l < Q.blockDim i) then
    [Q.mkRow (Q.finalShape i) (finalCell i l) (Q.weight i l),
      Q.mkRow (fun i' j' k' r' => -Q.finalShape i i' j' k' r')
        (fun i' j' k' r' l' => -finalCell i l i' j' k' r' l') (-Q.weight i l)]
  else [Q.trivialRow, Q.trivialRow]

/-- `∑_{i, j < n, k < 2, r < n} f i j k r`, as a list. -/
def loop4 {α : Type} (f : ℕ → ℕ → ℕ → ℕ → List α) : List α :=
  (List.range Q.n).flatMap fun i => (List.range Q.n).flatMap fun j =>
    (List.range 2).flatMap fun k => (List.range Q.n).flatMap fun r => f i j k r

/-- `∑_{i, j < n, k < 2, r, l < n} f i j k r l`, as a list. -/
def loop5 {α : Type} (f : ℕ → ℕ → ℕ → ℕ → ℕ → List α) : List α :=
  Q.loop4 fun i j k r => (List.range Q.n).flatMap fun l => f i j k r l

/-- **The polytope of the positional quiver**, families 1–6. -/
def polytope : IntPolyhedron where
  dim := Q.dim
  rows := Q.loop4 Q.shapeRows ++ Q.loop5 Q.cellRows ++ Q.loop4 Q.rowSumRows ++
    Q.loop5 (fun i j k r l => [Q.columnRow i j k r l]) ++
    Q.loop5 (fun i j k r l => [Q.latticeRow i j k r l]) ++
    (List.range Q.n).flatMap fun i => (List.range Q.n).flatMap fun l => Q.finalRows i l

end PositionalQuiver

/-! ## The canonical quiver of a triple -/

/-- Entry `i` of a list, `0` beyond its length. -/
def entry (x : List ℕ) (i : ℕ) : ℕ := x.getD i 0

variable (a b c : List ℕ)

/-- The residual `ν_i = c_i − a_i − b_i`. -/
def nu (i : ℕ) : ℤ := (entry c i : ℤ) - entry a i - entry b i

/-- The canonical partition cuts before `i`: from `i − 1` to `i`, `a` or `b` strictly increases or
`c` strictly decreases. -/
def riseAt (i : ℕ) : Bool :=
  decide (0 < i) && (decide (entry a (i - 1) < entry a i) || decide (entry b (i - 1) < entry b i) ||
    decide (entry c i < entry c (i - 1)))

/-- The position `i` starts an interval of the canonical partition. -/
def isStart (i : ℕ) : Bool := decide (i = 0) || riseAt a b c i

/-- The length of the interval starting at `i`: one plus the number of consecutive positions after
`i` that start no interval. -/
def blockDim (i : ℕ) : ℕ :=
  ((List.range (c.length - (i + 1))).filter fun t =>
    (List.range (t + 1)).all fun s => !isStart a b c (i + 1 + s)).length + 1

/-- The comparison weight `cmp((a_i, b_i, c̄_i), (a_j, b_j, c̄_j))` of two positions, with
`c̄ = N − c`. -/
def cmpAt (i j : ℕ) : ℤ :=
  (if entry a i < entry a j then 1 else 0) + (if entry b i < entry b j then 1 else 0) +
    (if entry c j < entry c i then 1 else 0) - 1

/-- The number of arrows between the intervals starting at `i < j`. -/
def arrowCount (i j : ℕ) : ℕ :=
  if isStart a b c i && isStart a b c j && decide (i < j) then (cmpAt a b c i j).toNat else 0

/-- The positional data of the canonical quiver of `(a, b, c)`, with the weight
`λ^{(i)}_l = ν_{i + d_i − 1 − l}` on the interval starting at `i`. -/
def positionalOf : PositionalQuiver where
  n := c.length
  isStart := isStart a b c
  blockDim := blockDim a b c
  arrowCount := arrowCount a b c
  weight i l := nu a b c (i + blockDim a b c i - 1 - l)

/-- **The polytope `P(a, b, c)` of Theorem 1.4.** -/
def quiverPolytope : IntPolyhedron := (positionalOf a b c).polytope

/-! ## Size -/

namespace PositionalQuiver

variable (Q : PositionalQuiver)

theorem length_loop4 {α : Type} (f : ℕ → ℕ → ℕ → ℕ → List α) (s : ℕ)
    (hf : ∀ i j k r, (f i j k r).length = s) : (Q.loop4 f).length = 2 * Q.n ^ 3 * s := by
  simp only [loop4, List.length_flatMap, hf, List.map_const', List.sum_replicate,
    List.length_range, smul_eq_mul]
  ring

theorem length_loop5 {α : Type} (f : ℕ → ℕ → ℕ → ℕ → ℕ → List α) (s : ℕ)
    (hf : ∀ i j k r l, (f i j k r l).length = s) : (Q.loop5 f).length = 2 * Q.n ^ 4 * s := by
  rw [loop5, Q.length_loop4 _ (Q.n * s)]
  · ring
  · intro i j k r
    rw [List.length_flatMap]
    simp only [hf, List.map_const', List.sum_replicate, List.length_range, smul_eq_mul]

theorem length_shapeRows (i j k r : ℕ) : (Q.shapeRows i j k r).length = 2 := by
  unfold shapeRows
  split_ifs <;> rfl

theorem length_cellRows (i j k r l : ℕ) : (Q.cellRows i j k r l).length = 2 := by
  unfold cellRows
  split_ifs <;> rfl

theorem length_rowSumRows (i j k r : ℕ) : (Q.rowSumRows i j k r).length = 2 := by
  unfold rowSumRows
  split_ifs <;> rfl

theorem length_finalRows (i l : ℕ) : (Q.finalRows i l).length = 2 := by
  unfold finalRows
  split_ifs <;> rfl

/-- The number of inequalities, `8n⁴ + 8n³ + 2n²`. -/
theorem length_rows : Q.polytope.rows.length = 8 * Q.n ^ 4 + 8 * Q.n ^ 3 + 2 * Q.n ^ 2 := by
  simp only [polytope, List.length_append]
  rw [Q.length_loop4 _ 2 Q.length_shapeRows, Q.length_loop5 _ 2 Q.length_cellRows,
    Q.length_loop4 _ 2 Q.length_rowSumRows, Q.length_loop5 _ 1 (fun _ _ _ _ _ => rfl),
    Q.length_loop5 _ 1 (fun _ _ _ _ _ => rfl)]
  simp only [List.length_flatMap, Q.length_finalRows, List.map_const', List.sum_replicate,
    List.length_range, smul_eq_mul]
  ring

theorem length_mkRow (f : ℕ → ℕ → ℕ → ℕ → ℤ) (g : ℕ → ℕ → ℕ → ℕ → ℕ → ℤ) (rhs : ℤ) :
    (Q.mkRow f g rhs).1.length = Q.dim := by
  simp [mkRow]

/-- Membership in `loop4`. -/
theorem mem_loop4 {α : Type} {f : ℕ → ℕ → ℕ → ℕ → List α} {x : α} :
    x ∈ Q.loop4 f ↔ ∃ i < Q.n, ∃ j < Q.n, ∃ k < 2, ∃ r < Q.n, x ∈ f i j k r := by
  simp [loop4, List.mem_flatMap, List.mem_range]

/-- Membership in `loop5`. -/
theorem mem_loop5 {α : Type} {f : ℕ → ℕ → ℕ → ℕ → ℕ → List α} {x : α} :
    x ∈ Q.loop5 f ↔ ∃ i < Q.n, ∃ j < Q.n, ∃ k < 2, ∃ r < Q.n, ∃ l < Q.n, x ∈ f i j k r l := by
  simp [loop5, mem_loop4, List.mem_flatMap, List.mem_range]

/-- A row with `dim` coefficients, all in `[-1, 1]`, and right-hand side in a set `S`. -/
def GoodRow (S : Set ℤ) (row : List ℤ × ℤ) : Prop :=
  row.1.length = Q.dim ∧ (∀ z ∈ row.1, |z| ≤ 1) ∧ row.2 ∈ S

theorem goodRow_mkRow {S : Set ℤ} {f : ℕ → ℕ → ℕ → ℕ → ℤ} {g : ℕ → ℕ → ℕ → ℕ → ℕ → ℤ} {rhs : ℤ}
    (hf : ∀ i j k r, |f i j k r| ≤ 1) (hg : ∀ i j k r l, |g i j k r l| ≤ 1) (hrhs : rhs ∈ S) :
    Q.GoodRow S (Q.mkRow f g rhs) := by
  refine ⟨Q.length_mkRow f g rhs, fun z hz => ?_, hrhs⟩
  simp only [mkRow, List.mem_map, List.mem_range] at hz
  obtain ⟨col, -, rfl⟩ := hz
  unfold colFun
  split_ifs
  exacts [hf _ _ _ _, hg _ _ _ _ _]

theorem abs_ind_sub_ind_le (p q : Prop) [Decidable p] [Decidable q] :
    |(if p then (1 : ℤ) else 0) - if q then 1 else 0| ≤ 1 := by
  split_ifs <;> norm_num

theorem abs_ind_le (p : Prop) [Decidable p] : |(if p then (1 : ℤ) else 0)| ≤ 1 := by
  split_ifs <;> norm_num

theorem abs_neg_ind_le (p : Prop) [Decidable p] : |-(if p then (1 : ℤ) else 0)| ≤ 1 := by
  split_ifs <;> norm_num

theorem goodRow_trivialRow {S : Set ℤ} (h0 : (0 : ℤ) ∈ S) : Q.GoodRow S Q.trivialRow :=
  Q.goodRow_mkRow (fun _ _ _ _ => by norm_num) (fun _ _ _ _ _ => by norm_num) h0

/-- **The rows of the polytope**: each has `dim` coefficients, all in `[-1, 1]`, and right-hand
side `0` or `±weight i l`. -/
theorem goodRow_of_mem_rows {row : List ℤ × ℤ} (h : row ∈ Q.polytope.rows) :
    Q.GoodRow {z | z = 0 ∨ ∃ i l, z = Q.weight i l ∨ z = -Q.weight i l} row := by
  have h0 : (0 : ℤ) ∈ {z : ℤ | z = 0 ∨ ∃ i l, z = Q.weight i l ∨ z = -Q.weight i l} :=
    Or.inl rfl
  simp only [polytope, List.mem_append, mem_loop4, mem_loop5, List.mem_flatMap, List.mem_range,
    List.mem_singleton] at h
  rcases h with ((((h | h) | h) | h) | h) | h
  · obtain ⟨i, -, j, -, k, -, r, -, h⟩ := h
    unfold shapeRows at h
    split_ifs at h <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at h <;>
      rcases h with rfl | rfl <;> (try unfold trivialRow) <;>
      refine Q.goodRow_mkRow (fun _ _ _ _ => ?_) (fun _ _ _ _ _ => ?_) h0 <;>
      (try unfold shapeAt) <;> (try split_ifs) <;> norm_num
  · obtain ⟨i, -, j, -, k, -, r, -, l, -, h⟩ := h
    unfold cellRows at h
    split_ifs at h <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at h <;>
      rcases h with rfl | rfl <;> (try unfold trivialRow) <;>
      refine Q.goodRow_mkRow (fun _ _ _ _ => ?_) (fun _ _ _ _ _ => ?_) h0 <;>
      (try unfold cellAt) <;> (try split_ifs) <;> norm_num
  · obtain ⟨i, -, j, -, k, -, r, -, h⟩ := h
    unfold rowSumRows at h
    split_ifs at h <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at h <;>
      rcases h with rfl | rfl <;> (try unfold trivialRow) <;>
      refine Q.goodRow_mkRow (fun _ _ _ _ => ?_) (fun _ _ _ _ _ => ?_) h0 <;>
      (try unfold rowSumShape) <;> (try unfold rowSumCell) <;> (try unfold shapeAt) <;>
      (try split_ifs) <;> norm_num
  · obtain ⟨i, -, j, -, k, -, r, -, l, -, rfl⟩ := h
    unfold columnRow
    split_ifs <;> (try unfold trivialRow) <;>
      refine Q.goodRow_mkRow (fun _ _ _ _ => ?_) (fun _ _ _ _ _ => ?_) h0 <;>
      (try split_ifs) <;> norm_num
  · obtain ⟨i, -, j, -, k, -, r, -, l, -, rfl⟩ := h
    unfold latticeRow
    split_ifs <;> (try unfold trivialRow) <;>
      refine Q.goodRow_mkRow (fun _ _ _ _ => ?_) (fun _ _ _ _ _ => ?_) h0 <;>
      (try split_ifs) <;> norm_num
  · obtain ⟨i, -, l, -, h⟩ := h
    unfold finalRows at h
    split_ifs at h <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at h <;>
      rcases h with rfl | rfl
    · refine Q.goodRow_mkRow (fun _ _ _ _ => ?_) (fun _ _ _ _ _ => ?_) (Or.inr ⟨i, l, Or.inl rfl⟩)
        <;> (try unfold finalShape) <;> (try unfold finalCell) <;> split_ifs <;> norm_num
    · refine Q.goodRow_mkRow (fun _ _ _ _ => ?_) (fun _ _ _ _ _ => ?_) (Or.inr ⟨i, l, Or.inr rfl⟩)
        <;> (try unfold finalShape) <;> (try unfold finalCell) <;> split_ifs <;> norm_num
    all_goals exact Q.goodRow_trivialRow h0

end PositionalQuiver

theorem quiverPolytope_dim : (quiverPolytope a b c).dim = 2 * c.length ^ 3 + 2 * c.length ^ 4 :=
  rfl

theorem quiverPolytope_rows_length :
    (quiverPolytope a b c).rows.length =
      8 * c.length ^ 4 + 8 * c.length ^ 3 + 2 * c.length ^ 2 :=
  (positionalOf a b c).length_rows

/-- Every row of `P(a, b, c)` has `dim` coefficients. -/
theorem quiverPolytope_length_row {row : List ℤ × ℤ} (h : row ∈ (quiverPolytope a b c).rows) :
    row.1.length = (quiverPolytope a b c).dim :=
  ((positionalOf a b c).goodRow_of_mem_rows h).1

/-- **Coefficients**: every coefficient of `P(a, b, c)` is `-1`, `0` or `1`. -/
theorem quiverPolytope_coeff_mem {row : List ℤ × ℤ} (h : row ∈ (quiverPolytope a b c).rows)
    {z : ℤ} (hz : z ∈ row.1) : z ∈ ({-1, 0, 1} : Set ℤ) := by
  have := ((positionalOf a b c).goodRow_of_mem_rows h).2.1 z hz
  rw [abs_le] at this
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  omega

/-- **Right-hand sides**: every right-hand side of `P(a, b, c)` is `0` or `±ν_x` for a position
`x`, with `ν_x = c_x − a_x − b_x`. -/
theorem quiverPolytope_rhs_mem {row : List ℤ × ℤ} (h : row ∈ (quiverPolytope a b c).rows) :
    row.2 = 0 ∨ ∃ x, row.2 = nu a b c x ∨ row.2 = -nu a b c x := by
  rcases ((positionalOf a b c).goodRow_of_mem_rows h).2.2 with h0 | ⟨i, l, h1 | h1⟩
  · exact Or.inl h0
  · exact Or.inr ⟨_, Or.inl h1⟩
  · exact Or.inr ⟨_, Or.inr h1⟩

theorem entry_le_sum (x : List ℕ) (i : ℕ) : entry x i ≤ x.sum := by
  unfold entry
  rcases lt_or_ge i x.length with hi | hi
  · rw [List.getD_eq_getElem _ _ hi]
    exact List.le_sum_of_mem (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ hi]
    exact Nat.zero_le _

theorem abs_nu_le (x : ℕ) : |nu a b c x| ≤ (a.sum + b.sum + c.sum : ℕ) := by
  have ha := entry_le_sum a x
  have hb := entry_le_sum b x
  have hc := entry_le_sum c x
  unfold nu
  rw [abs_le, Nat.cast_add, Nat.cast_add]
  constructor <;> omega

/-- **Size of the right-hand sides**: `|β| ≤ ∑ a + ∑ b + ∑ c` for every row `(α, β)`. -/
theorem quiverPolytope_abs_rhs_le {row : List ℤ × ℤ} (h : row ∈ (quiverPolytope a b c).rows) :
    |row.2| ≤ (a.sum + b.sum + c.sum : ℕ) := by
  rcases quiverPolytope_rhs_mem a b c h with h0 | ⟨x, h1 | h1⟩
  · rw [h0, abs_zero]
    exact Nat.cast_nonneg _
  · rw [h1]
    exact abs_nu_le a b c x
  · rw [h1, abs_neg]
    exact abs_nu_le a b c x

end Schubert.RS.Quiver.Flat
