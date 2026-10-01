import Schubert.LinearProgramming.Input.Parse
import Schubert.LinearProgramming.Polyhedra.Perturbation
import Mathlib.Data.List.GetD

/-!
# Systems of linear inequalities and their encoding

A system is a number `dim` of variables and a list of rows `(a, β)`, read as `a · x ≤ β` with the
dense coefficient list `a` (missing coefficients are `0`, coefficients beyond `dim` are ignored).
It is encoded as the serialized `Data` tree `[dim, [[a, β], …]]`, integers as their sign and the
binary digits of their absolute value (`LinearProgramming.encodeSystem`).

Only the first `n = min dim (longest row)` variables matter: variables beyond the longest row
have no coefficient (`LinearProgramming.systemFeasible_iff`). So a system is the `m × n` integer
system `A x ≤ b` with `A i j = a_i.getD j 0` and `b i = β_i`.

The data are read from the encoding in polynomial time (`LinearProgramming.mOf`,
`LinearProgramming.nOf`, `LinearProgramming.aWordStr`, `LinearProgramming.bWordStr`), and they
are small: `m, n ≤ |z|` and all entries are below `2 ^ |z|` (`LinearProgramming.encodeSystem_size`).

## Main definitions

* `LinearProgramming.encodeSystem dim rows`, `LinearProgramming.SystemFeasible dim rows`.
* `LinearProgramming.sysA`, `LinearProgramming.sysB`, `LinearProgramming.effDim`.

## Main results

* `LinearProgramming.systemFeasible_iff`: reduction to `A x ≤ b` in `n` variables.
* `LinearProgramming.mOf_encodeSystem`, `LinearProgramming.nOf_encodeSystem`,
  `LinearProgramming.aWordStr_encodeSystem`, `LinearProgramming.bWordStr_encodeSystem`: the data
  read from an encoding.
-/

namespace LinearProgramming

open Complexity

noncomputable section

/-! ### Systems -/

/-- A row `(a, β)` of a system as `Data`. -/
def rowData (r : List ℤ × ℤ) : Data := Data.l [Data.l (r.1.map intData), intData r.2]

/-- The encoding of the system with `dim` variables and the rows `rows`. -/
def encodeSystem (dim : ℕ) (rows : List (List ℤ × ℤ)) : List Bool :=
  (Data.l [DataEncode.encode dim, Data.l (rows.map rowData)]).toBits

/-- The system with `dim` variables and the rows `rows` has a rational solution. -/
def SystemFeasible (dim : ℕ) (rows : List (List ℤ × ℤ)) : Prop :=
  ∃ x : Fin dim → ℚ, ∀ r ∈ rows, ∑ i : Fin dim, ((r.1.getD i 0 : ℤ) : ℚ) * x i ≤ r.2

/-- The coefficient `j` of row `i`, `0` past the end. -/
def sysA (rows : List (List ℤ × ℤ)) (i j : ℕ) : ℤ := ((rows.getD i ([], 0)).1).getD j 0

/-- The right-hand side of row `i`. -/
def sysB (rows : List (List ℤ × ℤ)) (i : ℕ) : ℤ := (rows.getD i ([], 0)).2

/-- The length of the longest row. -/
def maxLen (rows : List (List ℤ × ℤ)) : ℕ :=
  (Finset.range rows.length).sup fun i => (rows.getD i ([], 0)).1.length

/-- The number of variables that matter: `min dim (longest row)`. -/
def effDim (dim : ℕ) (rows : List (List ℤ × ℤ)) : ℕ := min dim (maxLen rows)

theorem getD_rows {rows : List (List ℤ × ℤ)} {i : ℕ} (hi : i < rows.length) :
    rows.getD i ([], 0) = rows[i] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

theorem sysA_of_lt {rows : List (List ℤ × ℤ)} {i : ℕ} (hi : i < rows.length) (j : ℕ) :
    sysA rows i j = rows[i].1.getD j 0 := by
  rw [sysA, getD_rows hi]

theorem sysB_of_lt {rows : List (List ℤ × ℤ)} {i : ℕ} (hi : i < rows.length) :
    sysB rows i = rows[i].2 := by
  rw [sysB, getD_rows hi]

theorem length_le_maxLen {rows : List (List ℤ × ℤ)} {i : ℕ} (hi : i < rows.length) :
    rows[i].1.length ≤ maxLen rows := by
  have := Finset.le_sup (f := fun i => (rows.getD i ([], 0)).1.length) (Finset.mem_range.mpr hi)
  rwa [getD_rows hi] at this

/-- The sum over the `dim` variables is the sum over the first `effDim dim rows` of them. -/
theorem sum_effDim {dim : ℕ} {rows : List (List ℤ × ℤ)} {i : ℕ} (hi : i < rows.length)
    (x : ℕ → ℚ) :
    ∑ j : Fin dim, ((sysA rows i j : ℤ) : ℚ) * x j =
      ∑ j : Fin (effDim dim rows), ((sysA rows i j : ℤ) : ℚ) * x j := by
  rw [Fin.sum_univ_eq_sum_range (fun j => ((sysA rows i j : ℤ) : ℚ) * x j),
    Fin.sum_univ_eq_sum_range (fun j => ((sysA rows i j : ℤ) : ℚ) * x j)]
  symm
  refine Finset.sum_subset (Finset.range_subset_range.mpr (min_le_left _ _)) fun j hj hj' => ?_
  rw [Finset.mem_range] at hj hj'
  have hlen : rows[i].1.length ≤ j := by
    have := length_le_maxLen hi
    simp only [effDim] at hj'
    omega
  rw [sysA_of_lt hi, List.getD_eq_default _ _ hlen, Int.cast_zero, zero_mul]

/-- **Only the first `effDim dim rows` variables matter.** -/
theorem systemFeasible_iff (dim : ℕ) (rows : List (List ℤ × ℤ)) :
    SystemFeasible dim rows ↔
      Feasible rows.length (effDim dim rows) (sysA rows) (sysB rows) := by
  have hle : effDim dim rows ≤ dim := min_le_left _ _
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨fun j => x ⟨j, lt_of_lt_of_le j.2 hle⟩, fun i => ?_⟩
    have := hx rows[i] (List.getElem_mem _)
    set y : ℕ → ℚ := fun j => if h : j < dim then x ⟨j, h⟩ else 0
    calc ∑ j : Fin (effDim dim rows), ((sysA rows i j : ℤ) : ℚ) * x ⟨j, lt_of_lt_of_le j.2 hle⟩
        = ∑ j : Fin (effDim dim rows), ((sysA rows i j : ℤ) : ℚ) * y j :=
          Finset.sum_congr rfl fun j _ => by simp [y, lt_of_lt_of_le j.2 hle]
      _ = ∑ j : Fin dim, ((sysA rows i j : ℤ) : ℚ) * y j := (sum_effDim i.2 y).symm
      _ = ∑ j : Fin dim, ((rows[i].1.getD j 0 : ℤ) : ℚ) * x j :=
          Finset.sum_congr rfl fun j _ => by simp [y, sysA_of_lt i.2, j.2]
      _ ≤ rows[i].2 := this
      _ = sysB rows i := by rw [sysB_of_lt i.2]; rfl
  · rintro ⟨x, hx⟩
    refine ⟨fun j => if h : (j : ℕ) < effDim dim rows then x ⟨j, h⟩ else 0, fun r hr => ?_⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
    set y : ℕ → ℚ := fun j => if h : j < effDim dim rows then x ⟨j, h⟩ else 0
    calc ∑ j : Fin dim, ((rows[i].1.getD j 0 : ℤ) : ℚ) *
          (if h : (j : ℕ) < effDim dim rows then x ⟨j, h⟩ else 0)
        = ∑ j : Fin dim, ((sysA rows i j : ℤ) : ℚ) * y j :=
          Finset.sum_congr rfl fun j _ => by simp [y, sysA_of_lt hi]
      _ = ∑ j : Fin (effDim dim rows), ((sysA rows i j : ℤ) : ℚ) * y j := sum_effDim hi y
      _ = ∑ j : Fin (effDim dim rows), ((sysA rows i j : ℤ) : ℚ) * x j :=
          Finset.sum_congr rfl fun j _ => by simp [y, j.2]
      _ ≤ sysB rows i := hx ⟨i, hi⟩
      _ = rows[i].2 := by rw [sysB_of_lt hi]

/-! ### Sizes -/

theorem length_toBits_le_of_mem {d : Data} {xs : List Data} (h : d ∈ xs) :
    d.toBits.length ≤ (Data.l xs).toBits.length := by
  rw [Data.toBits_l]
  simp only [List.length_cons, List.length_append, List.length_flatten, List.map_map]
  have := List.le_sum_of_mem (List.mem_map_of_mem (f := fun d => d.toBits.length) h)
  simp only [Function.comp_def] at this ⊢
  omega

theorem lt_two_pow_length_encode (x : ℕ) : x < 2 ^ (DataEncode.encode x).toBits.length := by
  have h1 : x < 2 ^ x.bits.length := by
    rw [Nat.size_eq_bits_len]
    exact Nat.lt_size_self x
  refine lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) ?_)
  rw [show DataEncode.encode x = Data.l (x.bits.map DataEncode.encode) from rfl, Data.toBits_l]
  simp only [List.length_cons, List.length_append, List.length_flatten, List.map_map]
  have : ∀ b : Bool, 1 ≤ (DataEncode.encode b).toBits.length := fun b => by
    cases b <;> simp [DataEncode.encode, Data.toBits_l]
  have h2 : x.bits.length ≤ (x.bits.map fun b => (DataEncode.encode b).toBits.length).sum := by
    rw [← List.length_map (f := fun b => (DataEncode.encode b).toBits.length)]
    exact List.length_le_sum_of_one_le _ fun n hn => by
      obtain ⟨b, _, rfl⟩ := List.mem_map.mp hn
      exact this b
  simp only [Function.comp_def] at h2 ⊢
  omega

theorem natAbs_lt_of_intData (v : ℤ) : v.natAbs < 2 ^ (intData v).toBits.length :=
  lt_of_lt_of_le (lt_two_pow_length_encode v.natAbs) (Nat.pow_le_pow_right (by norm_num)
    (length_toBits_le_of_mem (by simp)))

/-- **The data of an encoded system are small**: at most `|z|` rows, all rows at most `|z|` long,
`dim < 2 ^ |z|`, and all entries below `2 ^ |z|` in absolute value. -/
theorem encodeSystem_size (dim : ℕ) (rows : List (List ℤ × ℤ)) :
    rows.length ≤ (encodeSystem dim rows).length ∧
      maxLen rows ≤ (encodeSystem dim rows).length ∧
      dim < 2 ^ (encodeSystem dim rows).length ∧
      (∀ i j, (sysA rows i j).natAbs < 2 ^ (encodeSystem dim rows).length) ∧
      ∀ i, (sysB rows i).natAbs < 2 ^ (encodeSystem dim rows).length := by
  set z := encodeSystem dim rows
  have hrowsD : (Data.l (rows.map rowData)).toBits.length ≤ z.length :=
    length_toBits_le_of_mem (by simp)
  have hrow : ∀ i (hi : i < rows.length), (rowData rows[i]).toBits.length ≤ z.length :=
    fun i hi => (length_toBits_le_of_mem (List.mem_map_of_mem (List.getElem_mem hi))).trans
      hrowsD
  have hcoeffs : ∀ i (hi : i < rows.length),
      (Data.l (rows[i].1.map intData)).toBits.length ≤ z.length :=
    fun i hi => (length_toBits_le_of_mem (by simp)).trans (hrow i hi)
  have hpow : ∀ {a b : ℕ}, a ≤ b → 2 ^ a ≤ 2 ^ b := fun h => Nat.pow_le_pow_right (by norm_num) h
  refine ⟨?_, ?_, ?_, fun i j => ?_, fun i => ?_⟩
  · have := List.length_le_sum_of_one_le (rows.map fun r => (rowData r).toBits.length)
      fun n hn => by
        obtain ⟨r, _, rfl⟩ := List.mem_map.mp hn
        rw [Data.length_toBits]
        exact Data.size_pos
    rw [Data.toBits_l] at hrowsD
    simp only [List.length_cons, List.length_append, List.length_flatten, List.map_map,
      List.length_map] at hrowsD this
    simp only [Function.comp_def] at hrowsD
    omega
  · refine Finset.sup_le fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    have h1 := hcoeffs i hi'
    rw [Data.toBits_l] at h1
    have := List.length_le_sum_of_one_le (rows[i].1.map fun v => (intData v).toBits.length)
      fun n hn => by
        obtain ⟨v, _, rfl⟩ := List.mem_map.mp hn
        rw [Data.length_toBits]
        exact Data.size_pos
    simp only [List.length_cons, List.length_append, List.length_flatten, List.map_map,
      List.length_map] at h1 this
    simp only [Function.comp_def] at h1
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some]
    omega
  · exact lt_of_lt_of_le (lt_two_pow_length_encode dim)
      (hpow (length_toBits_le_of_mem (by simp)))
  · unfold sysA
    by_cases hi : i < rows.length
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
      by_cases hj : j < rows[i].1.length
      · simp only [List.getElem?_eq_getElem hj, Option.getD_some]
        exact lt_of_lt_of_le (natAbs_lt_of_intData _) (hpow ((length_toBits_le_of_mem
          (List.mem_map_of_mem (List.getElem_mem hj))).trans (hcoeffs i hi)))
      · simp [List.getElem?_eq_none (not_lt.mp hj)]
    · simp [List.getElem?_eq_none (not_lt.mp hi)]
  · unfold sysB
    by_cases hi : i < rows.length
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
      exact lt_of_lt_of_le (natAbs_lt_of_intData _) (hpow ((length_toBits_le_of_mem
        (by simp)).trans (hrow i hi)))
    · simp [List.getElem?_eq_none (not_lt.mp hi)]

/-! ### Reading the data -/

/-- The encoded list of rows. -/
def rowsStr (z : List Bool) : List Bool := childStr 1 z

/-- The number of rows. -/
def mOf (z : List Bool) : ℕ := childNum (rowsStr z)

/-- The encoded coefficients of row `i`. -/
def coeffsStr (z : List Bool) (i : ℕ) : List Bool := childStr 0 (childStr i (rowsStr z))

/-- The encoded right-hand side of row `i`. -/
def rhsStr (z : List Bool) (i : ℕ) : List Bool := childStr 1 (childStr i (rowsStr z))

/-- The length of the longest row. -/
def maxLenOf (z : List Bool) : ℕ :=
  (Finset.range (mOf z)).sup fun i => childNum (coeffsStr z i)

/-- The number of variables that matter, `min dim (longest row)`. -/
def nOf (z : List Bool) : ℕ :=
  min (Nat.fromBitsLE (numBits z.length (childStr 0 z))) (maxLenOf z)

/-- The word of the coefficient `j` of row `i`. -/
def aWordStr (W : ℕ) (z : List Bool) (i j : ℕ) : List Bool :=
  intWordStr W (childStr j (coeffsStr z i))

/-- The word of the right-hand side of row `i`. -/
def bWordStr (W : ℕ) (z : List Bool) (i : ℕ) : List Bool := intWordStr W (rhsStr z i)

theorem rowsStr_encodeSystem (dim : ℕ) (rows : List (List ℤ × ℤ)) :
    rowsStr (encodeSystem dim rows) = (Data.l (rows.map rowData)).toBits := by
  simp [rowsStr, encodeSystem, childStr_toBits]

theorem mOf_encodeSystem (dim : ℕ) (rows : List (List ℤ × ℤ)) :
    mOf (encodeSystem dim rows) = rows.length := by
  rw [mOf, rowsStr_encodeSystem, childNum_toBits, List.length_map]

theorem childStr_rowsStr {dim : ℕ} {rows : List (List ℤ × ℤ)} {i : ℕ} (hi : i < rows.length) :
    childStr i (rowsStr (encodeSystem dim rows)) = (rowData rows[i]).toBits := by
  rw [rowsStr_encodeSystem, childStr_toBits]
  simp [hi]

theorem coeffsStr_encodeSystem {dim : ℕ} {rows : List (List ℤ × ℤ)} {i : ℕ}
    (hi : i < rows.length) :
    coeffsStr (encodeSystem dim rows) i = (Data.l (rows[i].1.map intData)).toBits := by
  rw [coeffsStr, childStr_rowsStr hi, rowData, childStr_toBits]
  rfl

theorem maxLenOf_encodeSystem (dim : ℕ) (rows : List (List ℤ × ℤ)) :
    maxLenOf (encodeSystem dim rows) = maxLen rows := by
  rw [maxLenOf, mOf_encodeSystem, maxLen]
  refine Finset.sup_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  rw [coeffsStr_encodeSystem hi', childNum_toBits, List.length_map]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']

theorem nOf_encodeSystem (dim : ℕ) (rows : List (List ℤ × ℤ)) :
    nOf (encodeSystem dim rows) = effDim dim rows := by
  have hdim := (encodeSystem_size dim rows).2.2.1
  rw [nOf, maxLenOf_encodeSystem, effDim]
  congr 1
  have h0 : childStr 0 (encodeSystem dim rows) = (DataEncode.encode dim).toBits := by
    simp [encodeSystem, childStr_toBits]
  rw [h0, numBits_toBits hdim, Nat.fromBitsLE_toBitsLE hdim]

/-- **Reading a coefficient** of an encoded system. -/
theorem aWordStr_encodeSystem {W dim : ℕ} {rows : List (List ℤ × ℤ)} {i j : ℕ}
    (hi : i < rows.length) (hW : (encodeSystem dim rows).length ≤ W) :
    aWordStr W (encodeSystem dim rows) i j = word W (sysA rows i j) := by
  rw [aWordStr, coeffsStr_encodeSystem hi, childStr_toBits]
  by_cases hj : j < rows[i].1.length
  · simp only [List.getElem?_map, List.getElem?_eq_getElem hj, Option.map_some,
      Option.getD_some]
    have hval : sysA rows i j = rows[i].1[j] := by
      rw [sysA_of_lt hi, List.getD_eq_getElem _ _ hj]
    have hlt := (encodeSystem_size dim rows).2.2.2.1 i j
    rw [hval] at hlt
    rw [intWordStr_intData (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num) hW)), hval]
  · simp only [List.getElem?_map, List.getElem?_eq_none (not_lt.mp hj), Option.map_none,
      Option.getD_none, intWordStr_nil]
    rw [sysA_of_lt hi, List.getD_eq_default _ _ (not_lt.mp hj)]

/-- **Reading a right-hand side** of an encoded system. -/
theorem bWordStr_encodeSystem {W dim : ℕ} {rows : List (List ℤ × ℤ)} {i : ℕ}
    (hi : i < rows.length) (hW : (encodeSystem dim rows).length ≤ W) :
    bWordStr W (encodeSystem dim rows) i = word W (sysB rows i) := by
  rw [bWordStr, rhsStr, childStr_rowsStr hi, rowData, childStr_toBits]
  simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.map_some, Option.getD_some]
  have hlt := (encodeSystem_size dim rows).2.2.2.2 i
  rw [sysB_of_lt hi] at hlt
  rw [intWordStr_intData (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num) hW)),
    sysB_of_lt hi]

/-! ### Polynomial time -/

theorem rowsStr_mem_FP : rowsStr ∈ FP := childStr_mem_FP (UnaryFn.const 1) id_mem_FP

theorem mOf_unary : UnaryFn mOf := childNum_unary rowsStr_mem_FP

theorem coeffsStr_mem_FP {Z : List Bool → List Bool} {I : List Bool → ℕ} (hZ : Z ∈ FP)
    (hI : UnaryFn I) : (fun y => coeffsStr (Z y) (I y)) ∈ FP :=
  childStr_mem_FP (UnaryFn.const 0) (childStr_mem_FP hI (mem_FP_comp hZ rowsStr_mem_FP))

theorem rhsStr_mem_FP {Z : List Bool → List Bool} {I : List Bool → ℕ} (hZ : Z ∈ FP)
    (hI : UnaryFn I) : (fun y => rhsStr (Z y) (I y)) ∈ FP :=
  childStr_mem_FP (UnaryFn.const 1) (childStr_mem_FP hI (mem_FP_comp hZ rowsStr_mem_FP))

theorem maxLenOf_unary : UnaryFn maxLenOf :=
  (UnaryFn.bmax mOf_unary (childNum_unary (coeffsStr_mem_FP pairFst_mem_FP
    UnaryFn.index))).of_eq fun z => by simp [maxLenOf]

theorem nOf_unary : UnaryFn nOf :=
  UnaryFn.fromBitsLE_min (numBits_mem_FP (UnaryFn.length id_mem_FP)
    (childStr_mem_FP (UnaryFn.const 0) id_mem_FP)) maxLenOf_unary

theorem aWordStr_mem_FP {W I J : List Bool → ℕ} {Z : List Bool → List Bool} (hW : UnaryFn W)
    (hZ : Z ∈ FP) (hI : UnaryFn I) (hJ : UnaryFn J) :
    (fun y => aWordStr (W y) (Z y) (I y) (J y)) ∈ FP :=
  intWordStr_mem_FP hW (childStr_mem_FP hJ (coeffsStr_mem_FP hZ hI))

theorem bWordStr_mem_FP {W I : List Bool → ℕ} {Z : List Bool → List Bool} (hW : UnaryFn W)
    (hZ : Z ∈ FP) (hI : UnaryFn I) : (fun y => bWordStr (W y) (Z y) (I y)) ∈ FP :=
  intWordStr_mem_FP hW (rhsStr_mem_FP hZ hI)

end

end LinearProgramming
