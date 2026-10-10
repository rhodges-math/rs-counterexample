import RSCounterexample.LinearProgramming.Vectors.Search

/-!
# Matrices of words

An `r × c` matrix is stored as the vector of its entries in row-major order: entry `(i, j)` is
block `i * c + j` (`LinearProgramming.matStr`). Writing a matrix entry by entry and reading an
entry are polynomial-time (`LinearProgramming.matStr_mem_FP`, `LinearProgramming.WordFn.readMat`).

## Main definitions

* `LinearProgramming.matStr W M r c`: the words of the entries of `M` in row-major order.

## Main results

* `LinearProgramming.blockOf_matStr`: reading back an entry.
* `LinearProgramming.matStr_mem_FP`, `LinearProgramming.WordFn.readMat`.
-/

namespace LinearProgramming

open Complexity

/-- The `r × c` matrix `M`: the words of width `W` of its entries in row-major order. -/
def matStr (W : ℕ) (M : ℕ → ℕ → ℤ) (r c : ℕ) : List Bool :=
  vecStr W (fun t => M (t / c) (t % c)) (r * c)

@[simp] theorem length_matStr (W : ℕ) (M : ℕ → ℕ → ℤ) (r c : ℕ) :
    (matStr W M r c).length = r * c * W := by
  simp [matStr]

theorem mul_add_lt {r c i j : ℕ} (hi : i < r) (hj : j < c) : i * c + j < r * c := by
  calc i * c + j < i * c + c := by omega
    _ = (i + 1) * c := by ring
    _ ≤ r * c := Nat.mul_le_mul_right _ hi

/-- **Reading an entry** of a matrix. -/
theorem blockOf_matStr {W : ℕ} {M : ℕ → ℕ → ℤ} {r c i j : ℕ} (hi : i < r) (hj : j < c) :
    blockOf W (matStr W M r c) (i * c + j) = word W (M i j) := by
  rw [matStr, blockOf_vecStr (mul_add_lt hi hj)]
  have hc : 0 < c := by omega
  rw [Nat.mul_comm i c, Nat.mul_add_div hc, Nat.div_eq_of_lt hj, Nat.add_zero,
    Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hj]

theorem matStr_congr {W r c : ℕ} {M N : ℕ → ℕ → ℤ} (h : ∀ i < r, ∀ j < c, M i j = N i j) :
    matStr W M r c = matStr W N r c :=
  vecStr_congr fun t ht => by
    have hc : 0 < c := by
      rcases Nat.eq_zero_or_pos c with h0 | h0
      · simp [h0] at ht
      · exact h0
    exact h _ ((Nat.div_lt_iff_lt_mul hc).mpr ht) _ (Nat.mod_lt _ hc)

/-- **Writing a matrix entry by entry is polynomial-time.** The entry rule reads the input and
the row-major position `t` from `pair z (1^t)`. -/
theorem matStr_mem_FP {W r c : List Bool → ℕ} {M : List Bool → ℕ → ℕ → ℤ} (hr : UnaryFn r)
    (hc : UnaryFn c)
    (hM : WordFn (fun y => W (pairFst y)) fun y =>
      M (pairFst y) ((pairSnd y).length / c (pairFst y)) ((pairSnd y).length % c (pairFst y))) :
    (fun z => matStr (W z) (M z) (r z) (c z)) ∈ FP :=
  vecStr_mem_FP (f := fun z t => M z (t / c z) (t % c z)) (hr.mul hc) hM

/-- **Reading an entry of a polynomial-time matrix** at polynomial-time indices. -/
theorem WordFn.readMat {X : List Bool → List Bool} {W r c I J : List Bool → ℕ}
    {M : List Bool → ℕ → ℕ → ℤ} (hX : X ∈ FP) (hW : UnaryFn W) (hc : UnaryFn c) (hI : UnaryFn I)
    (hJ : UnaryFn J) (hrep : ∀ z, X z = matStr (W z) (M z) (r z) (c z)) (hIr : ∀ z, I z < r z)
    (hJc : ∀ z, J z < c z) : WordFn W fun z => M z (I z) (J z) :=
  mem_FP_of_eq (blockOf_mem_FP hW hX ((hI.mul hc).add hJ)) fun z => by
    rw [hrep z, blockOf_matStr (hIr z) (hJc z)]

end LinearProgramming
