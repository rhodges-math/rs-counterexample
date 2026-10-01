import Schubert.RS.Complexity.Parse

/-!
# Recognizing quiver triples in polynomial time

Theorem 1.4 (recognition): whether `(a, b, c)` is a quiver triple can be decided in time
polynomial in the binary length of the input (`quiverTriple_recognition`).

The algorithm is the paper's recognition argument (lines 1879–1893), in the arithmetic form of
`ListConditions`: it checks Definition 5.1 on the canonical partition. All loops are bounded by
the length `n` of the input lists, and all arithmetic compares sums of input entries in binary.

The test is the string predicate `RecogP`. It is built from complexitylib's polynomial-time tests
(`FPPred`) by conjunction, negation and quantifiers bounded by unary lengths
(`fpred_recogP`). On a valid encoding it holds exactly for quiver triples
(`recogP_encodeTriple_iff`).
-/

namespace Schubert.RS.Algorithms

open Complexity

noncomputable section

/-! ### Terms in a context of bounded quantifiers -/

/-- The length of `c`, read from the input at quantifier depth `d`. -/
def lenC (d : ℕ) (w : List Bool) : ℕ := childNum (childStr 2 (inp d w))

/-- Entry `x_{v + o}` of list `ℓ`, for the bound variable `v` of index `e`, in binary. -/
def ent (ℓ d e o : ℕ) (w : List Bool) : List Bool := valStr ℓ (var e w + o) (inp d w)

/-- The prefix sum `x_0 + ⋯ + x_{v + o − 1}` of list `ℓ`, for the bound variable `v` of index
`e`, in binary. -/
def pre (ℓ d e o : ℕ) (w : List Bool) : List Bool := psumStr ℓ (var e w + o) (inp d w)

/-- The full sum of list `ℓ` (prefix of length `n`), at depth `0`. -/
def preN (ℓ : ℕ) (z : List Bool) : List Bool := psumStr ℓ (lenC 0 z) z

theorem lenC_unary (d : ℕ) : UnaryFn (lenC d) :=
  childNum_unary (childStr_mem_FP (UnaryFn.const 2) (inp_mem_FP d))

theorem ent_mem_FP (ℓ d e o : ℕ) : ent ℓ d e o ∈ FP :=
  valStr_mem_FP (inp_mem_FP d) (UnaryFn.add (var_unary e) (UnaryFn.const o)) ℓ

theorem pre_mem_FP (ℓ d e o : ℕ) : pre ℓ d e o ∈ FP :=
  psumStr_mem_FP (inp_mem_FP d) (inp_length_le d) (UnaryFn.add (var_unary e) (UnaryFn.const o)) ℓ

theorem preN_mem_FP (ℓ : ℕ) : preN ℓ ∈ FP :=
  psumStr_mem_FP id_mem_FP (fun _ => le_rfl) (lenC_unary 0) ℓ

@[simp] theorem length_ent (ℓ d e o : ℕ) (w : List Bool) :
    (ent ℓ d e o w).length = width (inp d w) := length_valStr _ _ _

@[simp] theorem length_pre (ℓ d e o : ℕ) (w : List Bool) :
    (pre ℓ d e o w).length = width (inp d w) := length_psumStr _ _ _

@[simp] theorem length_preN (ℓ : ℕ) (z : List Bool) : (preN ℓ z).length = width z :=
  length_psumStr _ _ _

theorem length_addBits_of_eq {u v : List Bool} {W : ℕ} (hu : u.length = W) (hv : v.length = W) :
    (addBits u v).length = W := by
  rw [addBits_length u v (by rw [hu, hv]), hu]

/-! ### The test -/

/-- `a` and `b` have the length of `c`. -/
def LenP (z : List Bool) : Prop :=
  childNum (childStr 0 z) = lenC 0 z ∧ childNum (childStr 1 z) = lenC 0 z

/-- The degree equality `|a| + |b| = |c|`. -/
def BalP (z : List Bool) : Prop :=
  ¬ binValLE (addBits (preN 0 z) (preN 1 z)) < binValLE (preN 2 z) ∧
    ¬ binValLE (preN 2 z) < binValLE (addBits (preN 0 z) (preN 1 z))

/-- Depth `1` (`k` = variable `0`): the prefix height `h_k` is nonnegative. -/
def HeightP1 (w : List Bool) : Prop :=
  ¬ binValLE (pre 2 1 0 0 w) < binValLE (addBits (pre 0 1 0 0 w) (pre 1 1 0 0 w))

/-- All prefix heights are nonnegative. -/
def HeightP (z : List Bool) : Prop :=
  ∀ k < lenC 0 z + 1, HeightP1 (pair z (List.replicate k true))

/-- Depth `3` (`i, j, k` = variables `2, 1, 0`): `i ≤ k < j` and
`C_{k+1} + u_p ≤ A_{k+1} + B_{k+1} + u_q` for the positions `p`, `q` of index `p + 1`, `q + 1`. -/
def WinP3 (ℓ p q : ℕ) (w : List Bool) : Prop :=
  var 2 w ≤ var 0 w ∧ var 0 w < var 1 w ∧
    ¬ binValLE (addBits (addBits (pre 0 3 0 1 w) (pre 1 3 0 1 w)) (ent ℓ 3 (q + 1) 0 w)) <
      binValLE (addBits (pre 2 3 0 1 w) (ent ℓ 3 (p + 1) 0 w))

/-- Depth `2` (`i, j` = variables `1, 0`): the window inequality at `(i, j)`. -/
def WinP2 (ℓ p q : ℕ) (w : List Bool) : Prop :=
  ¬ var 1 w < var 0 w ∨ ¬ binValLE (ent ℓ 2 p 0 w) < binValLE (ent ℓ 2 q 0 w) ∨
    ∃ k < lenC 2 w, WinP3 ℓ p q (pair w (List.replicate k true))

/-- Depth `1`. -/
def WinP1 (ℓ p q : ℕ) (w : List Bool) : Prop :=
  ∀ j < lenC 1 w, WinP2 ℓ p q (pair w (List.replicate j true))

/-- The window inequalities (2.12) for list `ℓ`; `(p, q) = (1, 0)` for `a` and `b`, and
`(p, q) = (0, 1)` for `c̄`, whose comparisons are those of `c` reversed. -/
def WinP (ℓ p q : ℕ) (z : List Bool) : Prop :=
  ∀ i < lenC 0 z, WinP1 ℓ p q (pair z (List.replicate i true))

/-- The triple rises at the bound variable of index `e`. -/
def RiseP (d e : ℕ) (w : List Bool) : Prop :=
  binValLE (ent 0 d e 0 w) < binValLE (ent 0 d e 1 w) ∨
    binValLE (ent 1 d e 0 w) < binValLE (ent 1 d e 1 w) ∨
      binValLE (ent 2 d e 1 w) < binValLE (ent 2 d e 0 w)

/-- Depth `d + 1` (`m` = variable `0`): no rise at `m` between the variables `x`, `y`. -/
def SBP1 (d x y : ℕ) (w : List Bool) : Prop :=
  ¬ min (var (x + 1) w) (var (y + 1) w) ≤ var 0 w ∨
    ¬ var 0 w < max (var (x + 1) w) (var (y + 1) w) ∨ ¬ RiseP (d + 1) 0 w

/-- The variables `x`, `y` lie in the same interval of the canonical partition. -/
def SBP (d x y : ℕ) (w : List Bool) : Prop :=
  ∀ m < lenC d w, SBP1 d x y (pair w (List.replicate m true))

/-- `cmp + 1` for the variables `x`, `y`. -/
def cnt (d x y : ℕ) (w : List Bool) : ℕ :=
  (if binValLE (ent 0 d x 0 w) < binValLE (ent 0 d y 0 w) then 1 else 0) +
    (if binValLE (ent 1 d x 0 w) < binValLE (ent 1 d y 0 w) then 1 else 0) +
      (if binValLE (ent 2 d y 0 w) < binValLE (ent 2 d x 0 w) then 1 else 0)

/-- Depth `4` (`i, j, i', j'` = variables `3, 2, 1, 0`): condition (ii) of Definition 5.1. -/
def CmpP4 (w : List Bool) : Prop :=
  ¬ var 3 w < var 2 w ∨ SBP 4 3 2 w ∨ ¬ SBP 4 3 1 w ∨ ¬ SBP 4 2 0 w ∨
    (cnt 4 3 2 w = cnt 4 1 0 w ∧ 1 ≤ cnt 4 3 2 w)

/-- Depth `3`. -/
def CmpP3 (w : List Bool) : Prop := ∀ j < lenC 3 w, CmpP4 (pair w (List.replicate j true))

/-- Depth `2`. -/
def CmpP2 (w : List Bool) : Prop := ∀ i < lenC 2 w, CmpP3 (pair w (List.replicate i true))

/-- Depth `1`. -/
def CmpP1 (w : List Bool) : Prop := ∀ j < lenC 1 w, CmpP2 (pair w (List.replicate j true))

/-- Condition (ii) of Definition 5.1 on the canonical partition. -/
def CmpP (z : List Bool) : Prop := ∀ i < lenC 0 z, CmpP1 (pair z (List.replicate i true))

/-- **The recognition test** on an encoded triple. -/
def RecogP (z : List Bool) : Prop :=
  LenP z ∧ BalP z ∧ HeightP z ∧ WinP 0 1 0 z ∧ WinP 1 1 0 z ∧ WinP 2 0 1 z ∧ CmpP z

/-! ### The test is polynomial-time -/

theorem fpred_lenP : FPPred LenP :=
  (FPPred.eq (childNum_unary (childStr_mem_FP (UnaryFn.const 0) id_mem_FP)) (lenC_unary 0)).and
    (FPPred.eq (childNum_unary (childStr_mem_FP (UnaryFn.const 1) id_mem_FP)) (lenC_unary 0))

theorem fpred_balP : FPPred BalP := by
  have hs := addBitsFn_mem_FP (preN_mem_FP 0) (preN_mem_FP 1)
  have hlen : ∀ z, (addBits (preN 0 z) (preN 1 z)).length = width z := fun z =>
    length_addBits_of_eq (length_preN 0 z) (length_preN 1 z)
  exact (fpred_binValLE_lt hs (preN_mem_FP 2) fun z => by rw [hlen, length_preN]).not.and
    (fpred_binValLE_lt (preN_mem_FP 2) hs fun z => by rw [hlen, length_preN]).not

theorem fpred_heightP : FPPred HeightP := by
  have hs := addBitsFn_mem_FP (pre_mem_FP 0 1 0 0) (pre_mem_FP 1 1 0 0)
  have h1 : FPPred HeightP1 :=
    (fpred_binValLE_lt (pre_mem_FP 2 1 0 0) hs fun w => by
      rw [length_addBits_of_eq (length_pre _ _ _ _ w) (length_pre _ _ _ _ w), length_pre]).not
  exact FPPred.forall_lt (UnaryFn.add (lenC_unary 0) (UnaryFn.const 1)) h1

theorem fpred_winP (ℓ p q : ℕ) : FPPred (WinP ℓ p q) := by
  have hX := addBitsFn_mem_FP (addBitsFn_mem_FP (pre_mem_FP 0 3 0 1) (pre_mem_FP 1 3 0 1))
    (ent_mem_FP ℓ 3 (q + 1) 0)
  have hY := addBitsFn_mem_FP (pre_mem_FP 2 3 0 1) (ent_mem_FP ℓ 3 (p + 1) 0)
  have h3 : FPPred (WinP3 ℓ p q) :=
    (FPPred.le (var_unary 2) (var_unary 0)).and ((FPPred.lt (var_unary 0) (var_unary 1)).and
      (fpred_binValLE_lt hX hY fun w => by
        rw [length_addBits_of_eq (length_pre _ _ _ _ w) (length_ent _ _ _ _ w),
          length_addBits_of_eq (length_addBits_of_eq (length_pre _ _ _ _ w)
            (length_pre _ _ _ _ w)) (length_ent _ _ _ _ w)]).not)
  have h2 : FPPred (WinP2 ℓ p q) :=
    (FPPred.lt (var_unary 1) (var_unary 0)).not.or
      ((fpred_binValLE_lt (ent_mem_FP ℓ 2 p 0) (ent_mem_FP ℓ 2 q 0) fun w => by
        rw [length_ent, length_ent]).not.or (FPPred.exists_lt (lenC_unary 2) h3))
  exact FPPred.forall_lt (lenC_unary 0) (FPPred.forall_lt (lenC_unary 1) h2)

theorem fpred_entLt (ℓ ℓ' d e o e' o' : ℕ) :
    FPPred fun w => binValLE (ent ℓ d e o w) < binValLE (ent ℓ' d e' o' w) :=
  fpred_binValLE_lt (ent_mem_FP ℓ d e o) (ent_mem_FP ℓ' d e' o') fun w => by
    rw [length_ent, length_ent]

theorem fpred_riseP (d e : ℕ) : FPPred (RiseP d e) :=
  (fpred_entLt 0 0 d e 0 e 1).or ((fpred_entLt 1 1 d e 0 e 1).or (fpred_entLt 2 2 d e 1 e 0))

theorem fpred_SBP (d x y : ℕ) : FPPred (SBP d x y) := by
  have h1 : FPPred (SBP1 d x y) :=
    (FPPred.le (UnaryFn.min (var_unary (x + 1)) (var_unary (y + 1))) (var_unary 0)).not.or
      ((FPPred.lt (var_unary 0) (UnaryFn.max (var_unary (x + 1)) (var_unary (y + 1)))).not.or
        (fpred_riseP (d + 1) 0).not)
  exact FPPred.forall_lt (lenC_unary d) h1

theorem cnt_unary (d x y : ℕ) : UnaryFn (cnt d x y) := by
  classical
  exact UnaryFn.add (UnaryFn.add
    (UnaryFn.ite (fpred_entLt 0 0 d x 0 y 0) (UnaryFn.const 1) (UnaryFn.const 0))
    (UnaryFn.ite (fpred_entLt 1 1 d x 0 y 0) (UnaryFn.const 1) (UnaryFn.const 0)))
    (UnaryFn.ite (fpred_entLt 2 2 d y 0 x 0) (UnaryFn.const 1) (UnaryFn.const 0))

theorem fpred_cmpP : FPPred CmpP := by
  have h4 : FPPred CmpP4 :=
    (FPPred.lt (var_unary 3) (var_unary 2)).not.or ((fpred_SBP 4 3 2).or
      ((fpred_SBP 4 3 1).not.or ((fpred_SBP 4 2 0).not.or
        ((FPPred.eq (cnt_unary 4 3 2) (cnt_unary 4 1 0)).and
          (FPPred.le (UnaryFn.const 1) (cnt_unary 4 3 2))))))
  exact FPPred.forall_lt (lenC_unary 0) (FPPred.forall_lt (lenC_unary 1)
    (FPPred.forall_lt (lenC_unary 2) (FPPred.forall_lt (lenC_unary 3) h4)))

/-- **The recognition test is polynomial-time.** -/
theorem fpred_recogP : FPPred RecogP :=
  fpred_lenP.and (fpred_balP.and (fpred_heightP.and ((fpred_winP 0 1 0).and
    ((fpred_winP 1 1 0).and ((fpred_winP 2 0 1).and fpred_cmpP)))))

/-! ### Values on valid inputs -/

section Values

variable (a b c : List ℕ)

@[simp] theorem binValLE_valStr_zero (i : ℕ) :
    binValLE (valStr 0 i (encodeTriple a b c)) = a.getD i 0 :=
  binValLE_valStr a b c (by norm_num) i

@[simp] theorem binValLE_valStr_one (i : ℕ) :
    binValLE (valStr 1 i (encodeTriple a b c)) = b.getD i 0 :=
  binValLE_valStr a b c (by norm_num) i

@[simp] theorem binValLE_valStr_two (i : ℕ) :
    binValLE (valStr 2 i (encodeTriple a b c)) = c.getD i 0 :=
  binValLE_valStr a b c (by norm_num) i

@[simp] theorem binValLE_psumStr_zero (k : ℕ) :
    binValLE (psumStr 0 k (encodeTriple a b c)) = psum a k :=
  binValLE_psumStr a b c (by norm_num) k

@[simp] theorem binValLE_psumStr_one (k : ℕ) :
    binValLE (psumStr 1 k (encodeTriple a b c)) = psum b k :=
  binValLE_psumStr a b c (by norm_num) k

@[simp] theorem binValLE_psumStr_two (k : ℕ) :
    binValLE (psumStr 2 k (encodeTriple a b c)) = psum c k :=
  binValLE_psumStr a b c (by norm_num) k

@[simp] theorem lenC_encodeTriple : childNum (childStr 2 (encodeTriple a b c)) = c.length :=
  childNum_encodeTriple a b c (by norm_num)

@[simp] theorem childNum_zero_encodeTriple :
    childNum (childStr 0 (encodeTriple a b c)) = a.length :=
  childNum_encodeTriple a b c (by norm_num)

@[simp] theorem childNum_one_encodeTriple :
    childNum (childStr 1 (encodeTriple a b c)) = b.length :=
  childNum_encodeTriple a b c (by norm_num)

theorem total_eq : total a b c = a.sum + b.sum + c.sum := by
  simp only [total, List.sum_append]

theorem le_total_of_mem {ℓ : ℕ} (hℓ : ℓ < 3) (i : ℕ) :
    binValLE (valStr ℓ i (encodeTriple a b c)) ≤ total a b c := by
  rw [binValLE_valStr a b c hℓ]
  exact (getD_le_sum _ _).trans (sum_listOf_le a b c ℓ)

@[simp] theorem binValLE_addBits_ab (k : ℕ) :
    binValLE (addBits (psumStr 0 k (encodeTriple a b c)) (psumStr 1 k (encodeTriple a b c))) =
      psum a k + psum b k := by
  rw [binValLE_addBits_of_le a b c _ _ (length_psumStr _ _ _) (length_psumStr _ _ _)]
  · simp
  · simp only [binValLE_psumStr_zero, binValLE_psumStr_one]
    have := psum_le_sum a k
    have := psum_le_sum b k
    rw [total_eq]
    omega

theorem binValLE_addBits_abx {ℓ : ℕ} (hℓ : ℓ < 3) (k j : ℕ) :
    binValLE (addBits (addBits (psumStr 0 k (encodeTriple a b c))
        (psumStr 1 k (encodeTriple a b c))) (valStr ℓ j (encodeTriple a b c))) =
      psum a k + psum b k + (listOf a b c ℓ).getD j 0 := by
  have hlen := length_addBits_of_eq (length_psumStr 0 k (encodeTriple a b c))
    (length_psumStr 1 k (encodeTriple a b c))
  rw [binValLE_addBits_of_le a b c _ _ hlen (length_valStr _ _ _)]
  · rw [binValLE_addBits_ab, binValLE_valStr a b c hℓ]
  · rw [binValLE_addBits_ab]
    have := le_total_of_mem a b c hℓ j
    have := psum_le_sum a k
    have := psum_le_sum b k
    have := total_eq a b c
    omega

theorem binValLE_addBits_cx {ℓ : ℕ} (hℓ : ℓ < 3) (k i : ℕ) :
    binValLE (addBits (psumStr 2 k (encodeTriple a b c)) (valStr ℓ i (encodeTriple a b c))) =
      psum c k + (listOf a b c ℓ).getD i 0 := by
  rw [binValLE_addBits_of_le a b c _ _ (length_psumStr _ _ _) (length_valStr _ _ _)]
  · rw [binValLE_psumStr_two, binValLE_valStr a b c hℓ]
  · rw [binValLE_psumStr_two]
    have := le_total_of_mem a b c hℓ i
    have := psum_le_sum c k
    have := total_eq a b c
    omega

end Values

/-! ### Correctness on valid inputs -/

section Correctness

variable (a b c : List ℕ)

theorem lenP_iff : LenP (encodeTriple a b c) ↔ a.length = c.length ∧ b.length = c.length := by
  simp [LenP, lenC]

theorem balP_iff :
    BalP (encodeTriple a b c) ↔ psum a c.length + psum b c.length = psum c c.length := by
  simp only [BalP, preN, lenC, inp_zero, lenC_encodeTriple, binValLE_addBits_ab,
    binValLE_psumStr_two]
  omega

theorem heightP_iff :
    HeightP (encodeTriple a b c) ↔ ∀ k < c.length + 1, psum a k + psum b k ≤ psum c k := by
  simp only [HeightP, HeightP1, pre, lenC, inp_zero, inp_succ_pair, var_zero_pair, Nat.add_zero,
    lenC_encodeTriple, binValLE_addBits_ab, binValLE_psumStr_two, not_lt]

theorem winP_iff {ℓ : ℕ} (hℓ : ℓ < 2) :
    WinP ℓ 1 0 (encodeTriple a b c) ↔ WindowOK a b c (listOf a b c ℓ) := by
  have hℓ3 : ℓ < 3 := by omega
  simp only [WinP, WinP1, WinP2, WinP3, pre, ent, lenC, inp_zero, inp_succ_pair, var_zero_pair,
    var_succ_pair, Nat.add_zero, lenC_encodeTriple, binValLE_addBits_abx a b c hℓ3,
    binValLE_addBits_cx a b c hℓ3, binValLE_valStr a b c hℓ3, WindowOK]
  constructor
  · intro h i hi j hj hij hu
    rcases h i hi j hj with h1 | h1 | ⟨k, hk, hk1, hk2, hk3⟩
    · exact absurd hij h1
    · exact absurd hu h1
    · exact ⟨k, hk, hk1, hk2, by omega⟩
  · intro h i hi j hj
    by_cases hij : i < j
    · by_cases hu : (listOf a b c ℓ).getD i 0 < (listOf a b c ℓ).getD j 0
      · obtain ⟨k, hk, hk1, hk2, hk3⟩ := h i hi j hj hij hu
        exact Or.inr (Or.inr ⟨k, hk, hk1, hk2, by omega⟩)
      · exact Or.inr (Or.inl hu)
    · exact Or.inl hij

theorem winP_c_iff : WinP 2 0 1 (encodeTriple a b c) ↔ WindowOKc a b c := by
  simp only [WinP, WinP1, WinP2, WinP3, pre, ent, lenC, inp_zero, inp_succ_pair, var_zero_pair,
    var_succ_pair, Nat.add_zero, lenC_encodeTriple, binValLE_addBits_abx a b c (ℓ := 2)
      (by norm_num), binValLE_addBits_cx a b c (ℓ := 2) (by norm_num), binValLE_valStr_two,
    listOf_two, WindowOKc]
  constructor
  · intro h i hi j hj hij hu
    rcases h i hi j hj with h1 | h1 | ⟨k, hk, hk1, hk2, hk3⟩
    · exact absurd hij h1
    · exact absurd hu h1
    · exact ⟨k, hk, hk1, hk2, by omega⟩
  · intro h i hi j hj
    by_cases hij : i < j
    · by_cases hu : c.getD j 0 < c.getD i 0
      · obtain ⟨k, hk, hk1, hk2, hk3⟩ := h i hi j hj hij hu
        exact Or.inr (Or.inr ⟨k, hk, hk1, hk2, by omega⟩)
      · exact Or.inr (Or.inl hu)
    · exact Or.inl hij

theorem riseP_iff {d e : ℕ} {w : List Bool} (hw : inp d w = encodeTriple a b c) :
    RiseP d e w ↔ RisesAt a b c (var e w) := by
  simp only [RiseP, ent, hw, binValLE_valStr_zero, binValLE_valStr_one, binValLE_valStr_two,
    Nat.add_zero, RisesAt]

theorem SBP_iff {d x y : ℕ} {w : List Bool} (hw : inp d w = encodeTriple a b c) :
    SBP d x y w ↔ SameBlock a b c (var x w) (var y w) := by
  simp only [SBP, SBP1, lenC, hw, lenC_encodeTriple, var_succ_pair, var_zero_pair, SameBlock]
  refine forall₂_congr fun m _ => ?_
  rw [riseP_iff a b c (by rw [inp_succ_pair, hw])]
  simp only [var_zero_pair]
  tauto

theorem cnt_eq {d x y : ℕ} {w : List Bool} (hw : inp d w = encodeTriple a b c) :
    cnt d x y w = cmpCount a b c (var x w) (var y w) := by
  simp only [cnt, ent, hw, binValLE_valStr_zero, binValLE_valStr_one, binValLE_valStr_two,
    Nat.add_zero, cmpCount]

theorem cmpP4_iff (i j i' j' : ℕ) :
    CmpP4 (pair (pair (pair (pair (encodeTriple a b c) (List.replicate i true))
      (List.replicate j true)) (List.replicate i' true)) (List.replicate j' true)) ↔
      (¬ i < j ∨ SameBlock a b c i j ∨ ¬ SameBlock a b c i i' ∨ ¬ SameBlock a b c j j' ∨
        (cmpCount a b c i j = cmpCount a b c i' j' ∧ 1 ≤ cmpCount a b c i j)) := by
  have hw : inp 4 (pair (pair (pair (pair (encodeTriple a b c) (List.replicate i true))
      (List.replicate j true)) (List.replicate i' true)) (List.replicate j' true)) =
      encodeTriple a b c := by simp
  rw [CmpP4, SBP_iff a b c hw, SBP_iff a b c hw, SBP_iff a b c hw, cnt_eq a b c hw,
    cnt_eq a b c hw]
  simp only [var_zero_pair, var_succ_pair]

theorem cmpP_iff :
    CmpP (encodeTriple a b c) ↔
      ∀ i < c.length, ∀ j < c.length, ∀ i' < c.length, ∀ j' < c.length, i < j →
        ¬ SameBlock a b c i j → SameBlock a b c i i' → SameBlock a b c j j' →
          cmpCount a b c i j = cmpCount a b c i' j' ∧ 1 ≤ cmpCount a b c i j := by
  constructor
  · intro h i hi j hj i' hi' j' hj' hij hn hii hjj
    have h4 := h i (by simpa [lenC] using hi) j (by simpa [lenC] using hj)
      i' (by simpa [lenC] using hi') j' (by simpa [lenC] using hj')
    rcases (cmpP4_iff a b c i j i' j').1 h4 with h5 | h5 | h5 | h5 | h5
    · exact absurd hij h5
    · exact absurd h5 hn
    · exact absurd hii h5
    · exact absurd hjj h5
    · exact h5
  · intro h i hi j hj i' hi' j' hj'
    simp only [lenC, inp_zero, inp_succ_pair, lenC_encodeTriple] at hi hj hi' hj'
    rw [cmpP4_iff]
    by_cases hij : i < j
    · by_cases hn : SameBlock a b c i j
      · exact Or.inr (Or.inl hn)
      · by_cases hii : SameBlock a b c i i'
        · by_cases hjj : SameBlock a b c j j'
          · exact Or.inr (Or.inr (Or.inr (Or.inr (h i hi j hj i' hi' j' hj' hij hn hii hjj))))
          · exact Or.inr (Or.inr (Or.inr (Or.inl hjj)))
        · exact Or.inr (Or.inr (Or.inl hii))
    · exact Or.inl hij

/-- **Correctness of the test**: on the encoding of `(a, b, c)` it holds exactly for quiver
triples. -/
theorem recogP_encodeTriple_iff :
    RecogP (encodeTriple a b c) ↔ IsQuiverTripleList a b c := by
  rw [isQuiverTripleList_iff_listConditions, RecogP, lenP_iff, balP_iff, heightP_iff,
    winP_iff a b c (ℓ := 0) (by norm_num), winP_iff a b c (ℓ := 1) (by norm_num), winP_c_iff,
    cmpP_iff, listOf_zero, listOf_one]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4, h5, h6, h7, h8⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
    exact ⟨⟨h1, h2⟩, h3, h4, h5, h6, h7, h8⟩

end Correctness

/-- **Theorem 1.4, recognition.** Whether three lists of natural numbers, given in binary, form a
quiver triple (Definition 5.1) is decidable in polynomial time: some polynomial-time function
on bitstrings outputs the answer bit on every encoded input. -/
theorem quiverTriple_recognition :
    ∃ f ∈ FP, ∀ a b c : List ℕ, f (encodeTriple a b c) = [isQuiverTripleListBool a b c] := by
  classical
  refine ⟨fun z => [decide (RecogP z)], FPPred.flag_mem_FP fpred_recogP, fun a b c => ?_⟩
  simp only [isQuiverTripleListBool, List.cons.injEq, and_true]
  exact decide_eq_decide.mpr (recogP_encodeTriple_iff a b c)

end

end Schubert.RS.Algorithms
