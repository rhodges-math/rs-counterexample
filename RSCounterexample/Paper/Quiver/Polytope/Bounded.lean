import RSCounterexample.Paper.Quiver.Polytope.Decode
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The polytope is bounded

The positional polytope of a well-formed positional quiver is bounded. At each vertex, summing the
final-weight conditions over the entries gives the balance
`∑_l λ_l = ∑_{out} |μ_e| − ∑_{in} |μ_e|`
(`Schubert.RS.Quiver.Flat.PositionalQuiver.vertexWeight_eq`):
an outgoing factor contributes its `|μ_e|` cells, an incoming factor `d μ_{e,0} − |μ_e|` cells and
the shift `−d μ_{e,0}`. Since the arrows go forward, induction over the vertices bounds every
`|μ_e|`, hence every partition entry and every row count.

## Main results

* `Schubert.RS.Quiver.Flat.PositionalQuiver.exists_abs_le`: every point of the polytope of a
  well-formed positional quiver is bounded by a constant.
* `Schubert.RS.Quiver.Flat.quiverPolytope_bounded`: the polytope `P(a, b, c)` is bounded.
-/

namespace Schubert.RS.Quiver.Flat

open Finset

namespace PositionalQuiver

variable {Q : PositionalQuiver} {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
  {sh : ℕ → ℕ → ℕ → ℕ → R} {ce : ℕ → ℕ → ℕ → ℕ → ℕ → R}

variable (Q) in
/-- The number of cells `|μ|` of the partition of the arrow `(i → j, k)`. -/
def size (sh : ℕ → ℕ → ℕ → ℕ → R) (i j k : ℕ) : R := ∑ r ∈ range Q.n, sh i j k r

variable (Q) in
/-- The total size of the partitions of the arrows out of `i`. -/
def outSize (sh : ℕ → ℕ → ℕ → ℕ → R) (i : ℕ) : R :=
  ∑ j ∈ range Q.n, ∑ k ∈ range 2, if k < Q.arrowCount i j then Q.size sh i j k else 0

variable (Q) in
/-- The total size of the partitions of the arrows into `i`. -/
def inSize (sh : ℕ → ℕ → ℕ → ℕ → R) (i : ℕ) : R :=
  ∑ j ∈ range Q.n, ∑ k ∈ range 2, if k < Q.arrowCount j i then Q.size sh j i k else 0

variable (Q) in
/-- The sum of the entries of the weight of the vertex `i`. -/
def vertexWeight (i : ℕ) : R := ∑ l ∈ range (Q.blockDim i), (Q.weight i l : R)

/-! ### Consequences of the first three families -/

omit [IsStrictOrderedRing R] in
theorem sh_nonneg (hC : Q.Conditions sh ce) {i j k r : ℕ} (hi : i < Q.n) (hj : j < Q.n)
    (hk : k < 2) (hr : r < Q.n) : 0 ≤ sh i j k r := by
  have h := hC.1 i hi j hj k hk r hr
  unfold ShapeCond at h
  split_ifs at h
  exacts [h.1, h.ge]

omit [IsStrictOrderedRing R] in
theorem sh_eq_zero (hC : Q.Conditions sh ce) {i j k r : ℕ} (hi : i < Q.n) (hj : j < Q.n)
    (hk : k < 2) (hr : r < Q.n) (h : Q.shapeOK i j k r = false) : sh i j k r = 0 := by
  have h' := hC.1 i hi j hj k hk r hr
  unfold ShapeCond at h'
  rw [h] at h'
  exact h'

omit [IsStrictOrderedRing R] in
theorem ce_nonneg (hC : Q.Conditions sh ce) {i j k r l : ℕ} (hi : i < Q.n) (hj : j < Q.n)
    (hk : k < 2) (hr : r < Q.n) (hl : l < Q.n) : 0 ≤ ce i j k r l := by
  have h := hC.2.1 i hi j hj k hk r hr l hl
  unfold CellCond at h
  split_ifs at h
  exacts [h, h.ge]

omit [IsStrictOrderedRing R] in
theorem ce_eq_zero (hC : Q.Conditions sh ce) {i j k r l : ℕ} (hi : i < Q.n) (hj : j < Q.n)
    (hk : k < 2) (hr : r < Q.n) (hl : l < Q.n) (h : Q.cellOK i j k r l = false) :
    ce i j k r l = 0 := by
  have h' := hC.2.1 i hi j hj k hk r hr l hl
  unfold CellCond at h'
  rw [h] at h'
  exact h'

omit [IsStrictOrderedRing R] in
/-- Outside the arrows' rows, the partition variables vanish. -/
theorem sh_eq_zero_of_le (hC : Q.Conditions sh ce) {i j k r : ℕ} (hi : i < Q.n) (hj : j < Q.n)
    (hk : k < 2) (hr : r < Q.n) (h : Q.blockDim i ≤ r ∨ Q.blockDim j ≤ r) : sh i j k r = 0 := by
  refine sh_eq_zero hC hi hj hk hr ?_
  simp only [shapeOK, Bool.and_eq_false_iff, decide_eq_false_iff_not, not_lt]
  right
  omega

omit [IsStrictOrderedRing R] in
theorem size_eq_sum_blockDim_left (hQ : Q.WellFormed) (hC : Q.Conditions sh ce) {i j k : ℕ}
    (hi : i < Q.n) (hj : j < Q.n) (hk : k < 2) (hs : Q.isStart i = true) :
    Q.size sh i j k = ∑ r ∈ range (Q.blockDim i), sh i j k r := by
  have hd := hQ.dim_le_n hi hs
  unfold size
  refine (Finset.sum_subset (range_subset_range.mpr hd) fun r hr hr' => ?_).symm
  rw [mem_range] at hr hr'
  exact sh_eq_zero_of_le hC hi hj hk hr (Or.inl (not_lt.mp hr'))

omit [IsStrictOrderedRing R] in
theorem size_eq_sum_blockDim_right (hQ : Q.WellFormed) (hC : Q.Conditions sh ce) {i j k : ℕ}
    (hi : i < Q.n) (hj : j < Q.n) (hk : k < 2) (hs : Q.isStart j = true) :
    Q.size sh i j k = ∑ r ∈ range (Q.blockDim j), sh i j k r := by
  have hd := hQ.dim_le_n hj hs
  unfold size
  refine (Finset.sum_subset (range_subset_range.mpr hd) fun r hr hr' => ?_).symm
  rw [mem_range] at hr hr'
  exact sh_eq_zero_of_le hC hi hj hk hr (Or.inr (not_lt.mp hr'))

omit [IsStrictOrderedRing R] in
/-- The row sums of the row counts. -/
theorem sum_ce_eq (hC : Q.Conditions sh ce) {i j k r : ℕ} (hi : i < Q.n) (hj : j < Q.n)
    (hk : k < 2) (hr : r < Q.n) :
    ∑ l ∈ range Q.n, ce i j k r l =
      if (Q.isStart i && (Q.outSlot i j k || Q.inSlot i j k) && decide (r < Q.blockDim i)) = true
      then Q.rowLength sh i j k r else 0 := by
  split_ifs with h
  · exact hC.2.2.1 i hi j hj k hk r hr h
  · refine Finset.sum_eq_zero fun l hl => ce_eq_zero hC hi hj hk hr (mem_range.mp hl) ?_
    simp only [Bool.not_eq_true] at h
    simp only [cellOK, h, Bool.false_and]

/-! ### The balance at a vertex -/

theorem not_out_and_in (hQ : Q.WellFormed) {i j k : ℕ} (hi : i < Q.n) (hj : j < Q.n)
    (h1 : k < Q.arrowCount i j) (h2 : k < Q.arrowCount j i) : False := by
  have := (hQ.arrow_pos i hi j hj (by omega)).1
  have := (hQ.arrow_pos j hj i hi (by omega)).1
  omega

omit [IsStrictOrderedRing R] in
/-- The cells of the tableau of the factor `(j, k)` at the vertex `i`: `|μ_e|` for an outgoing
arrow, `d μ_{e,0} − |μ_e|` for an incoming one. -/
theorem sum_sum_ce (hQ : Q.WellFormed) (hC : Q.Conditions sh ce) {i j k : ℕ} (hi : i < Q.n)
    (hj : j < Q.n) (hk : k < 2) (hs : Q.isStart i = true) :
    ∑ r ∈ range Q.n, ∑ l ∈ range Q.n, ce i j k r l =
      (if k < Q.arrowCount i j then Q.size sh i j k else 0) +
        (if k < Q.arrowCount j i then (Q.blockDim i : R) * sh j i k 0 - Q.size sh j i k
          else 0) := by
  have hd := hQ.dim_le_n hi hs
  rw [Finset.sum_congr rfl fun r hr => sum_ce_eq hC hi hj hk (mem_range.mp hr)]
  simp only [hs, Bool.true_and, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, outSlot,
    inSlot]
  by_cases h1 : k < Q.arrowCount i j
  · have h2 : ¬ k < Q.arrowCount j i := fun h2 => not_out_and_in hQ hi hj h1 h2
    simp only [h1, true_or, true_and, ↓reduceIte, h2, add_zero]
    rw [size_eq_sum_blockDim_left hQ hC hi hj hk hs, ← Finset.sum_filter]
    congr 1
    · ext r
      simp only [mem_filter, mem_range]
      omega
    · funext r
      simp [rowLength, outSlot, h1]
  · simp only [h1, false_or, ↓reduceIte, zero_add]
    by_cases h2 : k < Q.arrowCount j i
    · simp only [h2, true_and, ↓reduceIte]
      have hst := (hQ.arrow_pos j hj i hi (by omega)).2.2
      rw [size_eq_sum_blockDim_right hQ hC hj hi hk hst, ← Finset.sum_filter]
      have hf : (range Q.n).filter (fun r => r < Q.blockDim i) = range (Q.blockDim i) := by
        ext r
        simp only [mem_filter, mem_range]
        omega
      rw [hf]
      simp only [rowLength, outSlot, decide_eq_true_eq, h1, ↓reduceIte,
        Finset.sum_sub_distrib, Finset.sum_const, card_range, nsmul_eq_mul]
      rw [Finset.sum_range_reflect (fun r => sh j i k r) (Q.blockDim i)]
    · simp only [h2, false_and, ↓reduceIte, Finset.sum_const_zero]

omit [IsStrictOrderedRing R] in
/-- **The balance at a vertex**: the entries of the weight sum to the sizes of the outgoing
partitions minus the sizes of the incoming ones. -/
theorem vertexWeight_eq (hQ : Q.WellFormed) (hC : Q.Conditions sh ce) {i : ℕ} (hi : i < Q.n)
    (hs : Q.isStart i = true) : Q.vertexWeight i = Q.outSize sh i - Q.inSize sh i := by
  have hd := hQ.dim_le_n hi hs
  -- the final conditions, summed over the entries
  have h1 : Q.vertexWeight i =
      ∑ l ∈ range (Q.blockDim i), (-Q.inShift sh i + Q.total ce i l) := by
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [mem_range] at hl
    exact (hC.2.2.2.2.2 i hi l (by omega) (by simp [hs, hl])).symm
  -- the total number of entries `l`, for `l` beyond the dimension, is zero
  have h2 : ∑ l ∈ range (Q.blockDim i), Q.total ce i l = ∑ l ∈ range Q.n, Q.total ce i l := by
    refine Finset.sum_subset (range_subset_range.mpr hd) fun l hl hl' => ?_
    rw [mem_range] at hl hl'
    refine Finset.sum_eq_zero fun j hj => Finset.sum_eq_zero fun k hk =>
      Finset.sum_eq_zero fun r hr => ce_eq_zero hC hi (mem_range.mp hj) (mem_range.mp hk)
        (mem_range.mp hr) hl ?_
    simp only [cellOK, Bool.and_eq_false_iff, decide_eq_false_iff_not, not_lt]
    right
    omega
  have h3 : ∑ l ∈ range Q.n, Q.total ce i l =
      ∑ j ∈ range Q.n, ∑ k ∈ range 2, ∑ r ∈ range Q.n, ∑ l ∈ range Q.n, ce i j k r l := by
    unfold total
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_comm]
  rw [h1, Finset.sum_add_distrib, h2, h3]
  rw [Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun k hk =>
    sum_sum_ce hQ hC hi (mem_range.mp hj) (mem_range.mp hk) hs]
  simp only [Finset.sum_add_distrib, Finset.sum_const, card_range, nsmul_eq_mul, outSize,
    inSize, inShift]
  have h4 : ∀ j k, (if k < Q.arrowCount j i then (Q.blockDim i : R) * sh j i k 0 -
      Q.size sh j i k else 0) = (Q.blockDim i : R) * (if k < Q.arrowCount j i then sh j i k 0
        else 0) - (if k < Q.arrowCount j i then Q.size sh j i k else 0) := by
    intro j k
    split_ifs <;> ring
  simp only [h4, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/-! ### The induction over the vertices -/

theorem size_nonneg (hC : Q.Conditions sh ce) {i j k : ℕ} (hi : i < Q.n) (hj : j < Q.n)
    (hk : k < 2) : 0 ≤ Q.size sh i j k :=
  Finset.sum_nonneg fun _ hr => sh_nonneg hC hi hj hk (mem_range.mp hr)

theorem size_le_outSize (hC : Q.Conditions sh ce) {i j k : ℕ} (hi : i < Q.n) (hj : j < Q.n)
    (hk : k < 2) (h : k < Q.arrowCount i j) : Q.size sh i j k ≤ Q.outSize sh i := by
  have hnn : ∀ j' ∈ range Q.n, 0 ≤ ∑ k' ∈ range 2,
      (if k' < Q.arrowCount i j' then Q.size sh i j' k' else 0) := fun j' hj' =>
    Finset.sum_nonneg fun k' hk' => by
      split_ifs
      exacts [size_nonneg hC hi (mem_range.mp hj') (mem_range.mp hk'), le_refl _]
  calc Q.size sh i j k
      = if k < Q.arrowCount i j then Q.size sh i j k else 0 := by rw [ite_eq_left h]
    _ ≤ ∑ k' ∈ range 2, (if k' < Q.arrowCount i j then Q.size sh i j k' else 0) := by
        refine Finset.single_le_sum (f := fun k' => if k' < Q.arrowCount i j then
          Q.size sh i j k' else 0) (fun k' hk' => ?_) (mem_range.mpr hk)
        split_ifs
        exacts [size_nonneg hC hi hj (mem_range.mp hk'), le_refl _]
    _ ≤ Q.outSize sh i := Finset.single_le_sum hnn (mem_range.mpr hj)

theorem outSize_nonneg (hC : Q.Conditions sh ce) {i : ℕ} (hi : i < Q.n) :
    0 ≤ Q.outSize sh i :=
  Finset.sum_nonneg fun j hj => Finset.sum_nonneg fun k hk => by
    split_ifs
    exacts [size_nonneg hC hi (mem_range.mp hj) (mem_range.mp hk), le_refl _]

theorem inSize_le (hQ : Q.WellFormed) (hC : Q.Conditions sh ce) {i : ℕ} (hi : i < Q.n) :
    Q.inSize sh i ≤ ∑ j ∈ range i, Q.outSize sh j := by
  unfold inSize
  rw [← Finset.sum_range_add_sum_Ico _ hi.le]
  have hzero : ∑ j ∈ Finset.Ico i Q.n, ∑ k ∈ range 2,
      (if k < Q.arrowCount j i then Q.size sh j i k else 0) = 0 := by
    refine Finset.sum_eq_zero fun j hj => Finset.sum_eq_zero fun k _ => ?_
    rw [Finset.mem_Ico] at hj
    rw [ite_eq_right fun h => ?_]
    have := (hQ.arrow_pos j hj.2 i hi (by omega)).1
    omega
  rw [hzero, add_zero]
  refine Finset.sum_le_sum fun j hj => ?_
  have hj' : j < Q.n := by
    rw [mem_range] at hj
    omega
  calc ∑ k ∈ range 2, (if k < Q.arrowCount j i then Q.size sh j i k else 0)
      ≤ ∑ j' ∈ range Q.n, ∑ k ∈ range 2,
          (if k < Q.arrowCount j j' then Q.size sh j j' k else 0) := by
        refine Finset.single_le_sum (f := fun j' => ∑ k ∈ range 2,
          (if k < Q.arrowCount j j' then Q.size sh j j' k else 0)) (fun j' hj'' => ?_)
          (mem_range.mpr hi)
        exact Finset.sum_nonneg fun k hk => by
          split_ifs
          exacts [size_nonneg hC hj' (mem_range.mp hj'') (mem_range.mp hk), le_refl _]
    _ = Q.outSize sh j := rfl

omit [LinearOrder R] [IsStrictOrderedRing R] in
theorem outSize_eq_zero (hQ : Q.WellFormed) {i : ℕ} (hi : i < Q.n) (hs : Q.isStart i = false) :
    Q.outSize sh i = 0 := by
  refine Finset.sum_eq_zero fun j hj => Finset.sum_eq_zero fun k _ => ?_
  rw [ite_eq_right fun h => ?_]
  have := (hQ.arrow_pos i hi j (mem_range.mp hj) (by omega)).2.1
  rw [hs] at this
  exact Bool.false_ne_true this

omit [LinearOrder R] [IsStrictOrderedRing R] in
theorem sum_pow_two_add_one (i : ℕ) : ∑ j ∈ range i, (2 : R) ^ j + 1 = 2 ^ i := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Finset.sum_range_succ, add_right_comm, ih, pow_succ]
    ring

variable (Q) in
/-- The constant `∑_i |∑_l λ^{(i)}_l|` of the bound. -/
def weightBound : R := ∑ i ∈ range Q.n, |Q.vertexWeight i|

theorem weightBound_nonneg : (0 : R) ≤ Q.weightBound :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- **The sizes of the outgoing partitions are bounded**, by induction over the vertices. -/
theorem outSize_le (hQ : Q.WellFormed) (hC : Q.Conditions sh ce) {i : ℕ} (hi : i < Q.n) :
    Q.outSize sh i ≤ 2 ^ i * Q.weightBound := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    cases hs : Q.isStart i
    · rw [outSize_eq_zero hQ hi hs]
      exact mul_nonneg (pow_nonneg (by norm_num) _) weightBound_nonneg
    · have hW : (Q.vertexWeight i : R) ≤ Q.weightBound := by
        calc (Q.vertexWeight i : R) ≤ |(Q.vertexWeight i : R)| := le_abs_self _
          _ ≤ Q.weightBound :=
            Finset.single_le_sum (f := fun i => |(Q.vertexWeight i : R)|)
              (fun _ _ => abs_nonneg _) (mem_range.mpr hi)
      have hin : Q.inSize sh i ≤ ∑ j ∈ range i, 2 ^ j * Q.weightBound :=
        (inSize_le hQ hC hi).trans (Finset.sum_le_sum fun j hj =>
          ih j (mem_range.mp hj) (by have := mem_range.mp hj; omega))
      have hbal := vertexWeight_eq hQ hC hi hs
      rw [← Finset.sum_mul] at hin
      have hgeom := sum_pow_two_add_one (R := R) i
      have hB : (0 : R) ≤ Q.weightBound := weightBound_nonneg
      nlinarith

/-- **Every coordinate of a point of the polytope is bounded.** -/
theorem abs_sh_ce_le (hQ : Q.WellFormed) (hC : Q.Conditions sh ce) :
    (∀ i < Q.n, ∀ j < Q.n, ∀ k < 2, ∀ r < Q.n, |sh i j k r| ≤ 2 ^ Q.n * Q.weightBound) ∧
      ∀ i < Q.n, ∀ j < Q.n, ∀ k < 2, ∀ r < Q.n, ∀ l < Q.n,
        |ce i j k r l| ≤ 2 ^ Q.n * Q.weightBound := by
  have hpow : ∀ i < Q.n, (2 : R) ^ i * Q.weightBound ≤ 2 ^ Q.n * Q.weightBound := fun i hi =>
    mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hi.le) weightBound_nonneg
  -- every partition entry is at most the size of its partition
  have hsh : ∀ i < Q.n, ∀ j < Q.n, ∀ k < 2, ∀ r < Q.n, sh i j k r ≤ 2 ^ Q.n * Q.weightBound := by
    intro i hi j hj k hk r hr
    cases hok : Q.shapeOK i j k r
    · rw [sh_eq_zero hC hi hj hk hr hok]
      exact mul_nonneg (pow_nonneg (by norm_num) _) weightBound_nonneg
    · have hac : k < Q.arrowCount i j := by
        simp only [shapeOK, Bool.and_eq_true, decide_eq_true_eq] at hok
        exact hok.1
      calc sh i j k r ≤ Q.size sh i j k :=
            Finset.single_le_sum (f := fun r => sh i j k r)
              (fun r' hr' => sh_nonneg hC hi hj hk (mem_range.mp hr')) (mem_range.mpr hr)
        _ ≤ Q.outSize sh i := size_le_outSize hC hi hj hk hac
        _ ≤ 2 ^ i * Q.weightBound := outSize_le hQ hC hi
        _ ≤ 2 ^ Q.n * Q.weightBound := hpow i hi
  refine ⟨fun i hi j hj k hk r hr => ?_, fun i hi j hj k hk r hr l hl => ?_⟩
  · rw [abs_of_nonneg (sh_nonneg hC hi hj hk hr)]
    exact hsh i hi j hj k hk r hr
  · rw [abs_of_nonneg (ce_nonneg hC hi hj hk hr hl)]
    cases hok : Q.cellOK i j k r l
    · rw [ce_eq_zero hC hi hj hk hr hl hok]
      exact mul_nonneg (pow_nonneg (by norm_num) _) weightBound_nonneg
    · have hcond : (Q.isStart i && (Q.outSlot i j k || Q.inSlot i j k) &&
          decide (r < Q.blockDim i)) = true := by
        simp only [cellOK, Bool.and_eq_true] at hok
        simp only [hok, Bool.and_self]
      have hs : Q.isStart i = true := by
        simp only [Bool.and_eq_true] at hcond
        exact hcond.1.1
      have hd := hQ.dim_le_n hi hs
      have hrow := sum_ce_eq hC hi hj hk hr (sh := sh)
      rw [ite_eq_left hcond] at hrow
      calc ce i j k r l ≤ ∑ l' ∈ range Q.n, ce i j k r l' :=
            Finset.single_le_sum (f := fun l' => ce i j k r l')
              (fun l' hl' => ce_nonneg hC hi hj hk hr (mem_range.mp hl')) (mem_range.mpr hl)
        _ = Q.rowLength sh i j k r := hrow
        _ ≤ 2 ^ Q.n * Q.weightBound := by
          unfold rowLength
          split_ifs
          · exact hsh i hi j hj k hk r hr
          · have h0 := sh_nonneg hC hj hi hk (r := Q.blockDim i - 1 - r) (by omega)
            have h1 := hsh j hj i hi k hk 0 (by omega)
            linarith

/-- **Boundedness**: every point of the polytope of a well-formed positional quiver has all its
coordinates bounded by `2^n ∑_i |∑_l λ^{(i)}_l|`. -/
theorem abs_le_of_holds (hQ : Q.WellFormed) {x : Fin Q.dim → R} (hx : Q.Holds x)
    (c : Fin Q.dim) : |x c| ≤ 2 ^ Q.n * Q.weightBound := by
  have hC := (holds_iff hQ x).1 hx
  obtain ⟨hsh, hce⟩ := abs_sh_ce_le hQ hC
  have hn : 0 < Q.n := by
    rcases Nat.eq_zero_or_pos Q.n with h | h
    · exact absurd c.isLt (by simp [dim, h])
    · exact h
  have hc := c.isLt
  rw [← Q.ofCoords_sh_ce x]
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

/-- **The polytope of a well-formed positional quiver is bounded.** -/
theorem exists_abs_le {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (hQ : Q.WellFormed) : ∃ B : K, ∀ x ∈ Q.polytope.points K, ∀ c, |x c| ≤ B :=
  ⟨_, fun x hx c => abs_le_of_holds hQ ((mem_points_iff_holds x).1 hx) c⟩

end PositionalQuiver

/-- **The polytope `P(a, b, c)` is bounded**, for every triple of lists. -/
theorem quiverPolytope_bounded (a b c : List ℕ) :
    ∃ B : ℝ, ∀ x ∈ (quiverPolytope a b c).points ℝ, ∀ i, |x i| ≤ B :=
  PositionalQuiver.exists_abs_le (wellFormed_positionalOf a b c (positionalOf a b c).weight)

end Schubert.RS.Quiver.Flat
