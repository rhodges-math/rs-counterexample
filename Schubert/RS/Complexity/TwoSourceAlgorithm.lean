import Schubert.RS.Complexity.UnaryEncoding
import Schubert.RS.Complexity.TwoSourceCoefficient
import Schubert.RS.Complexity.PolytopeEncode

/-!
# Computing the two-source coefficient in polynomial time

Proposition 5.8 (last sentence): the coefficient (5.10) can be computed by a deterministic
algorithm whose running time is polynomial in `n + |a| + |b| + |c|`
(`twoSource_coefficient_computable`). The input is the unary encoding `encodeTripleUnary` of
`(a, b, c)`, whose length is linear in `n + |a| + |b| + |c|` (`length_encodeTripleUnary_ofFn`), and
the output is the encoding of the integer `[𝒜_c](κ_a κ_b)`.

The algorithm reads `m = n − 2`, `ν₁ = c₁ − a₁ − b₁` and `r_j = a_{j+2} + b_{j+2} − c_{j+2}` (in
unary), and runs the dynamic program `twoSourceCount` over the `r_j` (last to first), keeping the
values at `0, …, ν₁` in binary blocks of width `|z| + 1`. By `twoSource_eq_count`, the coefficient
is the difference of the values at `ν₁` and `ν₁ − 1`.
-/

namespace Schubert.RS.Algorithms

open Complexity Quiver

noncomputable section

/-! ### The data read from the input -/

/-- The working width `|z| + 1` of the binary values. -/
def widthU (z : List Bool) : ℕ := z.length + 1

/-- `m = n − 2`. -/
def mU (z : List Bool) : ℕ := ulen 2 z - 2

/-- `ν₁ = c₁ − a₁ − b₁`, capped at `|z|`. -/
def nuU (z : List Bool) : ℕ := min (uent 2 0 z - uent 0 0 z - uent 1 0 z) z.length

/-- `r_j = a_{j+2} + b_{j+2} − c_{j+2}`. -/
def rU (z : List Bool) (j : ℕ) : ℕ := uent 0 (j + 2) z + uent 1 (j + 2) z - uent 2 (j + 2) z

/-- The bound `r_{m−1−i}` of the step `i` of the dynamic program. -/
def tU (z : List Bool) (i : ℕ) : ℕ := rU z (mU z - 1 - i)

/-! ### The dynamic program on strings -/

/-- Block `q` of width `W` of a string (padded with `false`). -/
def blockOf (W : ℕ) (x : List Bool) (q : ℕ) : List Bool :=
  (x.drop (q * W) ++ List.replicate W false).take W

/-- `∑_{k < K} (block p − k of x)`, one addition per symbol of the counter. -/
def innerAux (z x : List Bool) (p : ℕ) : List Bool → List Bool
  | [] => List.replicate (widthU z) false
  | _ :: t => addBits (innerAux z x p t) (blockOf (widthU z) x (p - t.length))

/-- `∑_{k ≤ min(r, p)} (block p − k of x)`, with `r` the bound of step `i`. -/
def innerSum (z x : List Bool) (i p : ℕ) : List Bool :=
  innerAux z x p (List.replicate (min (tU z i) p + 1) true)

/-- One step of the dynamic program: the blocks `0, …, ν₁` of the new values. -/
def stepState (z x : List Bool) (i : ℕ) : List Bool :=
  (List.range (nuU z + 1)).flatMap fun p => innerSum z x i p

/-- The initial values: `1` at `0`, `0` elsewhere. -/
def initState (z : List Bool) : List Bool :=
  (List.range (nuU z + 1)).flatMap fun p => pow2Str (widthU z) (if p = 0 then 0 else widthU z)

/-- The dynamic program after as many steps as the counter has symbols. -/
def dpAux (z : List Bool) : List Bool → List Bool
  | [] => initState z
  | _ :: t => stepState z (dpAux z t) t.length

/-- The dynamic program after its `m` steps. -/
def dpFinal (z : List Bool) : List Bool := dpAux z (List.replicate (mU z) true)

/-- The value at `ν₁`. -/
def upperU (z : List Bool) : List Bool := blockOf (widthU z) (dpFinal z) (nuU z)

/-- The value at `ν₁ − 1` (zero if `ν₁ = 0`). -/
def lowerU (z : List Bool) : List Bool :=
  if 1 ≤ nuU z then blockOf (widthU z) (dpFinal z) (nuU z - 1)
  else List.replicate (widthU z) false

/-- The algorithm: the encoding of the difference of the two values. -/
def twoSourceAlgorithm (z : List Bool) : List Bool :=
  DataEncode.bitstringEncode ((binValLE (upperU z) : ℤ) - binValLE (lowerU z))

/-! ### Lengths -/

@[simp] theorem length_blockOf (W : ℕ) (x : List Bool) (q : ℕ) : (blockOf W x q).length = W := by
  simp only [blockOf, List.length_take, List.length_append, List.length_replicate]
  omega

theorem length_innerAux (z x : List Bool) (p : ℕ) :
    ∀ t, (innerAux z x p t).length = widthU z
  | [] => by simp [innerAux]
  | _ :: t => by
    rw [innerAux, addBits_length _ _ (by rw [length_blockOf, length_innerAux z x p t]),
      length_innerAux z x p t]

theorem length_flatMap_range_const (N W : ℕ) (f : ℕ → List Bool)
    (hf : ∀ p, (f p).length = W) : ((List.range N).flatMap f).length = N * W := by
  rw [List.length_flatMap]
  simp only [hf, List.map_const', List.sum_replicate, List.length_range, smul_eq_mul]

theorem length_stepState (z x : List Bool) (i : ℕ) :
    (stepState z x i).length = (nuU z + 1) * widthU z :=
  length_flatMap_range_const _ _ _ fun p => length_innerAux z x p _

theorem length_initState (z : List Bool) : (initState z).length = (nuU z + 1) * widthU z :=
  length_flatMap_range_const _ _ _ fun _ => length_pow2Str _ _

theorem length_dpAux (z : List Bool) : ∀ t, (dpAux z t).length = (nuU z + 1) * widthU z
  | [] => length_initState z
  | _ :: _ => length_stepState z _ _

/-! ### Polynomial time -/

section Polytime

theorem widthU_unary {Z : List Bool → List Bool} (hZ : Z ∈ FP) :
    UnaryFn fun v => widthU (Z v) :=
  (UnaryFn.length hZ).add (UnaryFn.const 1)

theorem mU_unary {Z : List Bool → List Bool} (hZ : Z ∈ FP) : UnaryFn fun v => mU (Z v) :=
  (ulen_unary hZ 2).sub (UnaryFn.const 2)

theorem nuU_unary {Z : List Bool → List Bool} (hZ : Z ∈ FP) : UnaryFn fun v => nuU (Z v) :=
  ((((uent_unary hZ (UnaryFn.const 0) 2).sub (uent_unary hZ (UnaryFn.const 0) 0)).sub
    (uent_unary hZ (UnaryFn.const 0) 1)).min (UnaryFn.length hZ)).of_eq fun _ => rfl

theorem rU_unary {Z : List Bool → List Bool} {J : List Bool → ℕ} (hZ : Z ∈ FP)
    (hJ : UnaryFn J) : UnaryFn fun v => rU (Z v) (J v) := by
  have hJ2 : UnaryFn fun v => J v + 2 := hJ.add (UnaryFn.const 2)
  exact (((uent_unary hZ hJ2 0).add (uent_unary hZ hJ2 1)).sub
    (uent_unary hZ hJ2 2)).of_eq fun _ => rfl

theorem tU_unary {Z : List Bool → List Bool} {I : List Bool → ℕ} (hZ : Z ∈ FP)
    (hI : UnaryFn I) : UnaryFn fun v => tU (Z v) (I v) :=
  rU_unary hZ (((mU_unary hZ).sub (UnaryFn.const 1)).sub hI)

theorem blockOf_mem_FP {W Q : List Bool → ℕ} {X : List Bool → List Bool} (hW : UnaryFn W)
    (hX : X ∈ FP) (hQ : UnaryFn Q) : (fun v => blockOf (W v) (X v) (Q v)) ∈ FP :=
  take_mem_FP (Cobham.appendFn_mem_FP (drop_mem_FP hX (hQ.mul hW)) (hW.replicate_mem_FP false))
    hW

theorem pairFst_pairFst_mem_FP : (fun y => pairFst (pairFst y)) ∈ FP :=
  mem_FP_comp pairFst_mem_FP pairFst_mem_FP

theorem innerAux_mem_FP {Z X : List Bool → List Bool} {P K : List Bool → ℕ} (hZ : Z ∈ FP)
    (hZlen : ∀ v, (Z v).length ≤ v.length) (hX : X ∈ FP) (hP : UnaryFn P) (hK : UnaryFn K) :
    (fun v => innerAux (Z v) (X v) (P v) (List.replicate (K v) true)) ∈ FP := by
  have hZ' : (fun y => Z (pairFst (pairFst y))) ∈ FP := mem_FP_comp pairFst_pairFst_mem_FP hZ
  have hX' : (fun y => X (pairFst (pairFst y))) ∈ FP := mem_FP_comp pairFst_pairFst_mem_FP hX
  have hstep : (fun y => addBits (pairSnd (pairFst y))
      (blockOf (widthU (Z (pairFst (pairFst y)))) (X (pairFst (pairFst y)))
        (P (pairFst (pairFst y)) - (pairSnd y).length))) ∈ FP :=
    addBitsFn_mem_FP (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)
      (blockOf_mem_FP (widthU_unary hZ') hX' ((hP.comp pairFst_pairFst_mem_FP).sub
        UnaryFn.index))
  have hbound : PolyBound fun n => n + 1 :=
    ⟨Polynomial.X + Polynomial.C 1, fun n => by simp⟩
  exact recFold_mem_FP_of_bound (g := fun v t => innerAux (Z v) (X v) (P v) t) hstep hstep
    ((widthU_unary hZ).replicate_mem_FP false) id_mem_FP (UnaryFn.mem_FP hK) (fun _ => rfl)
    (fun _ _ => by simp [innerAux]) (fun _ _ => by simp [innerAux]) hbound fun v t _ => by
      rw [length_innerAux, widthU]
      have := hZlen v
      omega

theorem stepFn_mem_FP :
    (fun q => stepState (pairFst (pairFst q)) (pairSnd (pairFst q)) (pairSnd q).length) ∈ FP := by
  have hZ : (fun v => pairFst (pairFst (pairFst v))) ∈ FP :=
    mem_FP_comp pairFst_pairFst_mem_FP pairFst_mem_FP
  have hX : (fun v => pairSnd (pairFst (pairFst v))) ∈ FP :=
    mem_FP_comp pairFst_pairFst_mem_FP pairSnd_mem_FP
  have hI : UnaryFn fun v => (pairSnd (pairFst v)).length :=
    UnaryFn.length (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)
  have hF := innerAux_mem_FP hZ
    (fun v => (pairFst_length_le _).trans ((pairFst_length_le _).trans (pairFst_length_le _)))
    hX UnaryFn.index (((tU_unary hZ hI).min UnaryFn.index).add (UnaryFn.const 1))
  exact loop_mem_FP ((nuU_unary pairFst_pairFst_mem_FP).add (UnaryFn.const 1))
    (F := fun q p => innerSum (pairFst (pairFst q)) (pairSnd (pairFst q)) (pairSnd q).length p) hF

theorem initState_mem_FP : initState ∈ FP :=
  loop_mem_FP ((nuU_unary id_mem_FP).add (UnaryFn.const 1))
    (F := fun z p => pow2Str (widthU z) (if p = 0 then 0 else widthU z))
    (pow2Str_mem_FP (widthU_unary pairFst_mem_FP)
      (UnaryFn.ite (FPPred.eq UnaryFn.index (UnaryFn.const 0)) (UnaryFn.const 0)
        (widthU_unary pairFst_mem_FP)))

theorem dpFinal_mem_FP : dpFinal ∈ FP := by
  have hbound : PolyBound fun n => (n + 1) * (n + 1) :=
    ⟨(Polynomial.X + Polynomial.C 1) * (Polynomial.X + Polynomial.C 1), fun n => by simp⟩
  exact recFold_mem_FP_of_bound (g := fun z t => dpAux z t) stepFn_mem_FP stepFn_mem_FP
    initState_mem_FP id_mem_FP (UnaryFn.mem_FP (mU_unary id_mem_FP)) (fun _ => rfl)
    (fun _ _ => by simp [dpAux]) (fun _ _ => by simp [dpAux]) hbound fun z t _ => by
      rw [length_dpAux, widthU]
      have : nuU z ≤ z.length := min_le_right _ _
      exact Nat.mul_le_mul (by omega) le_rfl

theorem upperU_mem_FP : upperU ∈ FP :=
  blockOf_mem_FP (widthU_unary id_mem_FP) dpFinal_mem_FP (nuU_unary id_mem_FP)

theorem lowerU_mem_FP : lowerU ∈ FP :=
  FPPred.ite_mem_FP (FPPred.le (UnaryFn.const 1) (nuU_unary id_mem_FP))
    (blockOf_mem_FP (widthU_unary id_mem_FP) dpFinal_mem_FP
      ((nuU_unary id_mem_FP).sub (UnaryFn.const 1)))
    ((widthU_unary id_mem_FP).replicate_mem_FP false)

theorem twoSourceAlgorithm_mem_FP : twoSourceAlgorithm ∈ FP :=
  diffEncode_mem_FP upperU_mem_FP lowerU_mem_FP fun z => by
    simp only [lowerU, upperU]
    split_ifs <;> simp

end Polytime

/-! ### Correctness -/

section Correctness

theorem blockOf_flatMap {W : ℕ} {f : ℕ → List Bool} (hf : ∀ p, (f p).length = W) :
    ∀ N q, q < N → blockOf W ((List.range N).flatMap f) q = f q
  | 0, q, h => absurd h (Nat.not_lt_zero q)
  | N + 1, q, h => by
    have hL : ((List.range N).flatMap f).length = N * W := length_flatMap_range_const N W f hf
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
    rcases Nat.lt_or_ge q N with hq | hq
    · rw [← blockOf_flatMap hf N q hq]
      unfold blockOf
      have hqW : (q + 1) * W ≤ N * W := Nat.mul_le_mul_right _ hq
      rw [Nat.succ_mul] at hqW
      have hle : q * W ≤ ((List.range N).flatMap f).length := by rw [hL]; omega
      have hW : W ≤ (List.drop (q * W) ((List.range N).flatMap f)).length := by
        rw [List.length_drop, hL]
        omega
      rw [List.drop_append_of_le_length hle, List.append_assoc,
        List.take_append_of_le_length hW, List.take_append_of_le_length hW]
    · have hqN : q = N := by omega
      subst hqN
      unfold blockOf
      rw [List.drop_left' (by rw [hL]), List.take_append_of_le_length (by rw [hf]),
        List.take_of_length_le (by rw [hf])]

/-- The blocks `0, …, S` of `x` have the values `v`. -/
def Rep (W S : ℕ) (x : List Bool) (v : ℕ → ℕ) : Prop :=
  ∀ p ≤ S, binValLE (blockOf W x p) = v p

theorem binValLE_innerAux {z x : List Bool} {v : ℕ → ℕ} (hx : Rep (widthU z) (nuU z) x v)
    {p : ℕ} (hp : p ≤ nuU z) : ∀ K, K ≤ p + 1 →
      ∑ k ∈ Finset.range K, v (p - k) < 2 ^ widthU z →
      binValLE (innerAux z x p (List.replicate K true)) = ∑ k ∈ Finset.range K, v (p - k)
  | 0, _, _ => by simp [innerAux, binValLE_replicate_false]
  | K + 1, hK, hsum => by
    have hsum' : ∑ k ∈ Finset.range K, v (p - k) < 2 ^ widthU z :=
      lt_of_le_of_lt (Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr (by omega)))
        hsum
    have ih := binValLE_innerAux hx hp K (by omega) hsum'
    rw [Finset.sum_range_succ] at hsum
    rw [List.replicate_succ, innerAux, List.length_replicate,
      binValLE_addBits _ _ (by rw [length_blockOf, length_innerAux])
        (by rw [ih, hx (p - K) (by omega), length_innerAux]; exact hsum),
      ih, hx (p - K) (by omega), Finset.sum_range_succ]

theorem rep_stepState {z x : List Bool} {v : ℕ → ℕ} (hx : Rep (widthU z) (nuU z) x v) (i : ℕ)
    (hb : ∀ p ≤ nuU z, ∑ k ∈ Finset.range (min (tU z i) p + 1), v (p - k) < 2 ^ widthU z) :
    Rep (widthU z) (nuU z) (stepState z x i)
      fun p => ∑ k ∈ Finset.range (min (tU z i) p + 1), v (p - k) := by
  intro p hp
  rw [stepState, blockOf_flatMap (f := fun p => innerSum z x i p)
    (fun q => length_innerAux z x q _) _ p (by omega), innerSum]
  exact binValLE_innerAux hx hp _ (by omega) (hb p hp)

theorem binValLE_pow2Str_of_le {W j : ℕ} (h : W ≤ j) : binValLE (pow2Str W j) = 0 := by
  have : pow2Str W j = List.replicate W false := by
    rw [pow2Str, List.map_congr_left (g := fun _ => false) fun t ht => by
      rw [List.mem_range] at ht
      simp only [decide_eq_false_iff_not]
      omega, List.map_const', List.length_range]
  rw [this, binValLE_replicate_false]

theorem rep_initState (z : List Bool) :
    Rep (widthU z) (nuU z) (initState z) (twoSourceCount []) := by
  intro p hp
  rw [initState, blockOf_flatMap (fun q => length_pow2Str _ _) _ p (by omega), twoSourceCount]
  split_ifs with h
  · rw [binValLE_pow2Str (by simp [widthU]), pow_zero]
  · exact binValLE_pow2Str_of_le le_rfl

variable {m : ℕ} {a b c : Composition (m + 2)} {N ν₁ ν₂ : ℕ} {r : Fin m → ℕ}

theorem uent_ofFn (a b c : Fin (m + 2) → ℕ) {i : ℕ} (hi : i < m + 2) :
    uent 0 i (encodeTripleUnary (List.ofFn a) (List.ofFn b) (List.ofFn c)) = a ⟨i, hi⟩ ∧
      uent 1 i (encodeTripleUnary (List.ofFn a) (List.ofFn b) (List.ofFn c)) = b ⟨i, hi⟩ ∧
      uent 2 i (encodeTripleUnary (List.ofFn a) (List.ofFn b) (List.ofFn c)) = c ⟨i, hi⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · rw [uent_encodeTripleUnary _ _ _ (by norm_num)
      (by rw [listOf_zero, List.length_ofFn]; exact hi)]
    simp only [listOf_zero, List.getElem_ofFn]
  · rw [uent_encodeTripleUnary _ _ _ (by norm_num)
      (by rw [listOf_one, List.length_ofFn]; exact hi)]
    simp only [listOf_one, List.getElem_ofFn]
  · rw [uent_encodeTripleUnary _ _ _ (by norm_num)
      (by rw [listOf_two, List.length_ofFn]; exact hi)]
    simp only [listOf_two, List.getElem_ofFn]

theorem mU_ofFn (a b c : Fin (m + 2) → ℕ) :
    mU (encodeTripleUnary (List.ofFn a) (List.ofFn b) (List.ofFn c)) = m := by
  rw [mU, ulen_encodeTripleUnary _ _ _ (by norm_num)]
  simp

theorem nuU_ofFn (hν₁ : Window.residual a b c 0 = ν₁) :
    nuU (encodeTripleUnary (List.ofFn a) (List.ofFn b) (List.ofFn c)) = ν₁ := by
  obtain ⟨h0, h1, h2⟩ := uent_ofFn a b c (i := 0) (by omega)
  have hlen := length_encodeTripleUnary_ofFn a b c
  have hc : c 0 ≤ ∑ i, c i := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0)
  simp only [Window.residual] at hν₁
  rw [nuU, h0, h1, h2, hlen]
  have e : (⟨0, by omega⟩ : Fin (m + 2)) = 0 := rfl
  rw [e]
  omega

theorem rU_ofFn (hr : ∀ j, Window.residual a b c (singletonPos j) = -(r j : ℤ)) {j : ℕ}
    (hj : j < m) :
    rU (encodeTripleUnary (List.ofFn a) (List.ofFn b) (List.ofFn c)) j = r ⟨j, hj⟩ := by
  obtain ⟨h0, h1, h2⟩ := uent_ofFn a b c (i := j + 2) (by omega)
  have h := hr ⟨j, hj⟩
  simp only [Window.residual, singletonPos] at h
  rw [rU, h0, h1, h2]
  omega

theorem tU_ofFn (hr : ∀ j, Window.residual a b c (singletonPos j) = -(r j : ℤ)) {i : ℕ}
    (hi : i < m) :
    tU (encodeTripleUnary (List.ofFn a) (List.ofFn b) (List.ofFn c)) i =
      r ⟨m - (i + 1), by omega⟩ := by
  rw [tU, mU_ofFn, rU_ofFn hr (by omega)]
  congr 2
  omega

theorem sum_r_lt_widthU (hW : Window.Hypotheses a b c N)
    (hν₁ : Window.residual a b c 0 = ν₁) (hν₂ : Window.residual a b c 1 = ν₂)
    (hr : ∀ j, Window.residual a b c (singletonPos j) = -(r j : ℤ)) :
    (List.ofFn r).sum < widthU (encodeTripleUnary (List.ofFn a) (List.ofFn b) (List.ofFn c)) := by
  rw [List.sum_ofFn, sum_eq_of_twoSource hW hν₁ hν₂ hr, widthU,
    length_encodeTripleUnary_ofFn]
  have hc : c 0 + c 1 ≤ ∑ i, c i := by
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    have : (Fin.succ 0 : Fin (m + 2)) = 1 := rfl
    rw [this]
    omega
  simp only [Window.residual] at hν₁ hν₂
  omega

theorem rep_dpAux (hW : Window.Hypotheses a b c N)
    (hν₁ : Window.residual a b c 0 = ν₁) (hν₂ : Window.residual a b c 1 = ν₂)
    (hr : ∀ j, Window.residual a b c (singletonPos j) = -(r j : ℤ)) :
    ∀ i ≤ m, Rep (widthU (encodeTripleUnary (List.ofFn a) (List.ofFn b) (List.ofFn c)))
      (nuU (encodeTripleUnary (List.ofFn a) (List.ofFn b) (List.ofFn c)))
      (dpAux (encodeTripleUnary (List.ofFn a) (List.ofFn b) (List.ofFn c))
        (List.replicate i true))
      (twoSourceCount ((List.ofFn r).drop (m - i)))
  | 0, _ => by
    rw [Nat.sub_zero, List.drop_of_length_le (by simp)]
    exact rep_initState _
  | i + 1, hi => by
    set z := encodeTripleUnary (List.ofFn a) (List.ofFn b) (List.ofFn c)
    have ih := rep_dpAux hW hν₁ hν₂ hr i (by omega)
    have hdrop : (List.ofFn r).drop (m - (i + 1)) =
        r ⟨m - (i + 1), by omega⟩ :: (List.ofFn r).drop (m - i) := by
      rw [List.drop_eq_getElem_cons (by simp; omega), List.getElem_ofFn]
      congr 2
      omega
    have hsum := sum_r_lt_widthU hW hν₁ hν₂ hr
    have hstep := rep_stepState ih i fun p _ => by
      have h1 : ∑ k ∈ Finset.range (min (tU z i) p + 1),
          twoSourceCount ((List.ofFn r).drop (m - i)) (p - k) =
          twoSourceCount ((List.ofFn r).drop (m - (i + 1))) p := by
        rw [hdrop, twoSourceCount, tU_ofFn hr (by omega)]
      rw [h1]
      refine lt_of_le_of_lt (twoSourceCount_le _ _) (Nat.pow_lt_pow_right (by norm_num) ?_)
      exact lt_of_le_of_lt ((List.drop_sublist _ _).sum_le_sum fun _ _ => Nat.zero_le _) hsum
    rw [List.replicate_succ, dpAux, List.length_replicate]
    intro p hp
    rw [hstep p hp, hdrop, twoSourceCount, tU_ofFn hr (by omega)]

/-- **The algorithm computes the two-source coefficient.** -/
theorem twoSourceAlgorithm_correct (hW : Window.Hypotheses a b c N)
    (hstar : ∀ i j : Fin (m + 2), i < j →
      Window.cmp (Window.triple a b (Window.complement N c) i)
        (Window.triple a b (Window.complement N c) j) = starPattern i j)
    (hν₁ : Window.residual a b c 0 = ν₁) (hν₂ : Window.residual a b c 1 = ν₂)
    (hr : ∀ j, Window.residual a b c (singletonPos j) = -(r j : ℤ)) :
    twoSourceAlgorithm (encodeTripleUnary (List.ofFn a) (List.ofFn b) (List.ofFn c)) =
      DataEncode.bitstringEncode (atomCoefficient (key a * key b) c) := by
  have hrep := rep_dpAux hW hν₁ hν₂ hr m le_rfl
  rw [Nat.sub_self, List.drop_zero] at hrep
  set z := encodeTripleUnary (List.ofFn a) (List.ofFn b) (List.ofFn c)
  have hfin : dpFinal z = dpAux z (List.replicate m true) := by rw [dpFinal, mU_ofFn]
  have hnu : nuU z = ν₁ := nuU_ofFn hν₁
  have hup : binValLE (upperU z) = twoSourceCount (List.ofFn r) ν₁ := by
    rw [upperU, hfin, hrep _ le_rfl, hnu]
  have hlow : binValLE (lowerU z) = twoSourceCountZ (List.ofFn r) ((ν₁ : ℤ) - 1) := by
    rw [lowerU, twoSourceCountZ]
    by_cases h1 : 1 ≤ nuU z
    · have e : nuU z - 1 = ((ν₁ : ℤ) - 1).toNat := by omega
      rw [ite_eq_left h1, hfin, hrep _ (by omega), ite_eq_left (by omega), e]
    · rw [ite_eq_right h1, binValLE_replicate_false, ite_eq_right (by omega)]
  rw [twoSourceAlgorithm, hup, hlow, twoSource_eq_count hW hstar hν₁ hν₂ hr]

end Correctness

/-- **Proposition 5.8 (last sentence): the coefficient (5.10) can be computed in time polynomial
in `n + |a| + |b| + |c|`.** Some polynomial-time function maps the unary encoding of every triple
`(a, b, c)` satisfying the hypotheses of Proposition 5.8 (`n = m + 2`, the hypotheses of
Proposition 2.13, the star pattern (5.9), and `ν = c − a − b = (ν₁, ν₂, −r₁, …, −r_m)` with
`0 ≤ ν₁ ≤ ν₂`) to the encoding of the integer `[𝒜_c](κ_a κ_b)`. The length of the unary encoding
is `4 (|a| + |b| + |c|) + 6 n + 8` (`length_encodeTripleUnary_ofFn`). -/
theorem twoSource_coefficient_computable :
    ∃ f ∈ FP, ∀ (m : ℕ) (a b c : Composition (m + 2)) (N ν₁ ν₂ : ℕ) (r : Fin m → ℕ),
      ν₁ ≤ ν₂ → Window.Hypotheses a b c N →
      (∀ i j : Fin (m + 2), i < j →
        Window.cmp (Window.triple a b (Window.complement N c) i)
          (Window.triple a b (Window.complement N c) j) = starPattern i j) →
      Window.residual a b c 0 = ν₁ → Window.residual a b c 1 = ν₂ →
      (∀ j, Window.residual a b c (singletonPos j) = -(r j : ℤ)) →
      f (encodeTripleUnary (List.ofFn a) (List.ofFn b) (List.ofFn c)) =
        DataEncode.bitstringEncode (atomCoefficient (key a * key b) c) :=
  ⟨twoSourceAlgorithm, twoSourceAlgorithm_mem_FP,
    fun _ _ _ _ _ _ _ _ _ hW hstar hν₁ hν₂ hr => twoSourceAlgorithm_correct hW hstar hν₁ hν₂ hr⟩

end

end Schubert.RS.Algorithms
