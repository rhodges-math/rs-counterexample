import RSCounterexample.Paper.Complexity.IntEncode
import RSCounterexample.Paper.Quiver.Polytope.Flat

/-!
# Writing the polytope of a positional quiver in polynomial time

Let `Q z` be a positional quiver computed from an input `z` (`Quiver.Flat.PositionalQuiver`). If
its number of positions, its vertices, their dimensions and the numbers of arrows are
polynomial-time (in unary, `PolytopeData`), and the encodings of its weights `±λ` are
polynomial-time, then so is writing its polytope `(Q z).polytope` (`polytope_encode_mem_FP`).

The polytope is written as the loops of its definition: its rows are four- and five-fold loops
over index ranges (`loop_mem_FP`), each row is a loop over its `2n³ + 2n⁴` columns, and every
coefficient is an integer of polynomial size (`IntFn`) computed from the column's indices
(`colFun_intFn`).
-/

namespace Schubert.RS.Algorithms

open Complexity Schubert.RS.Quiver.Flat

noncomputable section

/-! ### Loops and lists -/

/-- **A loop over a polynomial-time range is polynomial-time**, when its body reads the loop's
input and index from `pair z (1^i)`. -/
theorem loop_mem_FP {N : List Bool → ℕ} (hN : UnaryFn N) {F : List Bool → ℕ → List Bool}
    (hF : (fun w => F (pairFst w) (pairSnd w).length) ∈ FP) :
    (fun z => (List.range (N z)).flatMap (F z)) ∈ FP := by
  refine mem_FP_of_eq (flatMap_range_mem_FP hF (UnaryFn.mem_FP hN)) fun z => ?_
  simp only [List.length_replicate, pairFst_pair, pairSnd_pair]

/-- `z ↦ 0 x 1`. -/
theorem bracket1_mem_FP {x : List Bool → List Bool} (hx : x ∈ FP) :
    (fun z => false :: (x z ++ [true])) ∈ FP :=
  mem_FP_comp (Cobham.appendFn_mem_FP hx (constFn_mem_FP [true])) (Cobham.cons_mem_FP false)

theorem bitstringEncode_list_eq {α : Type} [DataEncode α] (l : List α) :
    DataEncode.bitstringEncode l = false :: (l.flatMap DataEncode.bitstringEncode ++ [true]) := by
  rw [DataEncode.bitstringEncode_list, List.flatMap]

theorem append_mem_FP {x y : List Bool → List Bool} (hx : x ∈ FP) (hy : y ∈ FP) :
    (fun z => x z ++ y z) ∈ FP :=
  Cobham.appendFn_mem_FP hx hy

/-! ### Contexts -/

/-- `pair x (1^i)`, with `x` and `i` polynomial-time. -/
theorem pairIdx_mem_FP {X : List Bool → List Bool} {I : List Bool → ℕ} (hX : X ∈ FP)
    (hI : UnaryFn I) : (fun u => pair (X u) (List.replicate (I u) true)) ∈ FP :=
  mem_FP_pair hX (UnaryFn.mem_FP hI)

/-- The data of a family of positional quivers that the polytope's construction reads, as
polynomial-time numbers and tests. -/
structure PolytopeData (Q : List Bool → PositionalQuiver) : Prop where
  n : UnaryFn fun z => (Q z).n
  isStart : FPPred fun w => (Q (pairFst w)).isStart (pairSnd w).length = true
  blockDim : UnaryFn fun w => (Q (pairFst w)).blockDim (pairSnd w).length
  arrowCount : UnaryFn fun w =>
    (Q (pairFst (pairFst w))).arrowCount (pairSnd (pairFst w)).length (pairSnd w).length
  weight : (fun w => DataEncode.bitstringEncode
    ((Q (pairFst (pairFst w))).weight (pairSnd (pairFst w)).length (pairSnd w).length)) ∈ FP
  weightNeg : (fun w => DataEncode.bitstringEncode
    (-(Q (pairFst (pairFst w))).weight (pairSnd (pairFst w)).length (pairSnd w).length)) ∈ FP

namespace PolytopeData

variable {Q : List Bool → PositionalQuiver} (hQ : PolytopeData Q) {X : List Bool → List Bool}
  (hX : X ∈ FP) {I J : List Bool → ℕ} (hI : UnaryFn I) (hJ : UnaryFn J)

include hQ hX

theorem n_at : UnaryFn fun u => (Q (X u)).n := hQ.n.comp hX

include hI

theorem isStart_at : FPPred fun u => (Q (X u)).isStart (I u) = true :=
  (hQ.isStart.comp (pairIdx_mem_FP hX hI)).of_iff fun u => by
    simp only [pairFst_pair, pairSnd_pair, List.length_replicate]

theorem blockDim_at : UnaryFn fun u => (Q (X u)).blockDim (I u) :=
  (hQ.blockDim.comp (pairIdx_mem_FP hX hI)).of_eq fun u => by
    simp only [pairFst_pair, pairSnd_pair, List.length_replicate]

include hJ

theorem arrowCount_at : UnaryFn fun u => (Q (X u)).arrowCount (I u) (J u) :=
  (hQ.arrowCount.comp (pairIdx_mem_FP (pairIdx_mem_FP hX hI) hJ)).of_eq fun u => by
    simp only [pairFst_pair, pairSnd_pair, List.length_replicate]

theorem weight_at :
    (fun u => DataEncode.bitstringEncode ((Q (X u)).weight (I u) (J u))) ∈ FP :=
  mem_FP_of_eq (mem_FP_comp (pairIdx_mem_FP (pairIdx_mem_FP hX hI) hJ) hQ.weight) fun u => by
    simp only [Function.comp_apply, pairFst_pair, pairSnd_pair, List.length_replicate]

theorem weightNeg_at :
    (fun u => DataEncode.bitstringEncode (-(Q (X u)).weight (I u) (J u))) ∈ FP :=
  mem_FP_of_eq (mem_FP_comp (pairIdx_mem_FP (pairIdx_mem_FP hX hI) hJ) hQ.weightNeg) fun u => by
    simp only [Function.comp_apply, pairFst_pair, pairSnd_pair, List.length_replicate]

/-! ### Tests on the quiver -/

include hJ in
theorem outSlot_at {K : List Bool → ℕ} (hK : UnaryFn K) :
    FPPred fun u => (Q (X u)).outSlot (I u) (J u) (K u) = true :=
  (FPPred.lt hK (hQ.arrowCount_at hX hI hJ)).of_iff fun u => by
    simp [PositionalQuiver.outSlot]

include hJ in
theorem shapeOK_at {K R : List Bool → ℕ} (hK : UnaryFn K) (hR : UnaryFn R) :
    FPPred fun u => (Q (X u)).shapeOK (I u) (J u) (K u) (R u) = true :=
  ((FPPred.lt hK (hQ.arrowCount_at hX hI hJ)).and
    (FPPred.lt hR ((hQ.blockDim_at hX hI).min (hQ.blockDim_at hX hJ)))).of_iff fun u => by
    simp [PositionalQuiver.shapeOK]

include hJ in
theorem slot_at {K R : List Bool → ℕ} (hK : UnaryFn K) (hR : UnaryFn R) :
    FPPred fun u => ((Q (X u)).isStart (I u) && ((Q (X u)).outSlot (I u) (J u) (K u) ||
      (Q (X u)).inSlot (I u) (J u) (K u)) && decide (R u < (Q (X u)).blockDim (I u))) = true :=
  (((hQ.isStart_at hX hI).and ((FPPred.lt hK (hQ.arrowCount_at hX hI hJ)).or
    (FPPred.lt hK (hQ.arrowCount_at hX hJ hI)))).and
    (FPPred.lt hR (hQ.blockDim_at hX hI))).of_iff fun u => by
    simp [PositionalQuiver.outSlot, PositionalQuiver.inSlot]

include hJ in
theorem cellOK_at {K R L : List Bool → ℕ} (hK : UnaryFn K) (hR : UnaryFn R) (hL : UnaryFn L) :
    FPPred fun u => (Q (X u)).cellOK (I u) (J u) (K u) (R u) (L u) = true :=
  ((hQ.slot_at hX hI hJ hK hR).and (FPPred.lt hL (hQ.blockDim_at hX hI))).of_iff fun u => by
    simp only [PositionalQuiver.cellOK, Bool.and_eq_true, decide_eq_true_eq]

include hJ in
theorem slotBefore_at {J' K' K : List Bool → ℕ} (hJ' : UnaryFn J') (hK' : UnaryFn K')
    (hK : UnaryFn K) :
    FPPred fun u => (Q (X u)).slotBefore (I u) (J' u) (K' u) (J u) (K u) = true := by
  have hn := hQ.n_at hX
  have hrank : ∀ {Y : List Bool → ℕ}, UnaryFn Y →
      UnaryFn fun u => (Q (X u)).slotRank (I u) (Y u) := fun hY =>
    ((((hY.add hn).sub hI).sub (UnaryFn.const 1)).mod hn).of_eq fun u => rfl
  exact ((FPPred.lt (hrank hJ') (hrank hJ)).or ((FPPred.eq hJ' hJ).and
    (FPPred.lt hK' hK))).of_iff fun u => by
      simp [PositionalQuiver.slotBefore]

end PolytopeData

/-! ### Coefficients -/

/-- Index `e` of a row's context, read from a column's context. -/
theorem varL (e : ℕ) : UnaryFn fun u => var e (pairFst u) := (var_unary e).lift

section Coefficients

variable {I J K R L A B D E G : List Bool → ℕ}

theorem shapeAt_intFn (hI : UnaryFn I) (hJ : UnaryFn J) (hK : UnaryFn K) (hR : UnaryFn R)
    (hA : UnaryFn A) (hB : UnaryFn B) (hD : UnaryFn D) (hE : UnaryFn E) :
    IntFn fun u => PositionalQuiver.shapeAt (I u) (J u) (K u) (R u) (A u) (B u) (D u) (E u) :=
  (IntFn.ind ((FPPred.eq hA hI).and ((FPPred.eq hB hJ).and ((FPPred.eq hD hK).and
    (FPPred.eq hE hR))))).of_eq fun _ => rfl

theorem cellAt_intFn (hI : UnaryFn I) (hJ : UnaryFn J) (hK : UnaryFn K) (hR : UnaryFn R)
    (hL : UnaryFn L) (hA : UnaryFn A) (hB : UnaryFn B) (hD : UnaryFn D) (hE : UnaryFn E)
    (hG : UnaryFn G) :
    IntFn fun u =>
      PositionalQuiver.cellAt (I u) (J u) (K u) (R u) (L u) (A u) (B u) (D u) (E u) (G u) :=
  (IntFn.ind ((FPPred.eq hA hI).and ((FPPred.eq hB hJ).and ((FPPred.eq hD hK).and
    ((FPPred.eq hE hR).and (FPPred.eq hG hL)))))).of_eq fun _ => rfl

theorem rowSumCell_intFn (hI : UnaryFn I) (hJ : UnaryFn J) (hK : UnaryFn K) (hR : UnaryFn R)
    (hA : UnaryFn A) (hB : UnaryFn B) (hD : UnaryFn D) (hE : UnaryFn E) :
    IntFn fun u => PositionalQuiver.rowSumCell (I u) (J u) (K u) (R u) (A u) (B u) (D u) (E u)
      (G u) :=
  (IntFn.ind ((FPPred.eq hA hI).and ((FPPred.eq hB hJ).and ((FPPred.eq hD hK).and
    (FPPred.eq hE hR))))).of_eq fun _ => rfl

theorem finalCell_intFn (hI : UnaryFn I) (hL : UnaryFn L) (hA : UnaryFn A) (hG : UnaryFn G) :
    IntFn fun u => PositionalQuiver.finalCell (I u) (L u) (A u) (B u) (D u) (E u) (G u) :=
  (IntFn.ind ((FPPred.eq hA hI).and (FPPred.eq hG hL))).of_eq fun _ => rfl

end Coefficients

namespace PolytopeData

variable {Q : List Bool → PositionalQuiver} (hQ : PolytopeData Q) {X : List Bool → List Bool}
  (hX : X ∈ FP)

include hQ hX

theorem dim_at : UnaryFn fun u => (Q (X u)).dim :=
  (((UnaryFn.const 2).mul ((hQ.n_at hX).pow_const 3)).add
    ((UnaryFn.const 2).mul ((hQ.n_at hX).pow_const 4))).of_eq fun _ => rfl

/-- **The coefficient of a column** is an integer of polynomial size, when the row's coefficient
functions are, at every polynomial-time index. -/
theorem colFun_intFn {C : List Bool → ℕ} (hC : UnaryFn C)
    {f : List Bool → ℕ → ℕ → ℕ → ℕ → ℤ} {g : List Bool → ℕ → ℕ → ℕ → ℕ → ℕ → ℤ}
    (hf : ∀ {A B D E : List Bool → ℕ}, UnaryFn A → UnaryFn B → UnaryFn D → UnaryFn E →
      IntFn fun u => f u (A u) (B u) (D u) (E u))
    (hg : ∀ {A B D E G : List Bool → ℕ}, UnaryFn A → UnaryFn B → UnaryFn D → UnaryFn E →
      UnaryFn G → IntFn fun u => g u (A u) (B u) (D u) (E u) (G u)) :
    IntFn fun u => (Q (X u)).colFun (f u) (g u) (C u) := by
  have hn := hQ.n_at hX
  have h2 : ∀ k, UnaryFn fun u => 2 * (Q (X u)).n ^ k := fun k =>
    (UnaryFn.const 2).mul (hn.pow_const k)
  have hC' : UnaryFn fun u => C u - 2 * (Q (X u)).n ^ 3 := hC.sub (h2 3)
  unfold PositionalQuiver.colFun
  exact IntFn.ite (FPPred.lt hC (h2 3))
    (hf (hC.div (h2 2)) ((hC.div ((UnaryFn.const 2).mul hn)).mod hn)
      ((hC.div hn).mod (UnaryFn.const 2)) (hC.mod hn))
    (hg (hC'.div (h2 3)) ((hC'.div (h2 2)).mod hn) ((hC'.div (hn.pow_const 2)).mod
      (UnaryFn.const 2)) ((hC'.div hn).mod hn) (hC'.mod hn))

/-- **Writing a row is polynomial-time.** -/
theorem mkRow_mem_FP
    {f : List Bool → ℕ → ℕ → ℕ → ℕ → ℤ} {g : List Bool → ℕ → ℕ → ℕ → ℕ → ℕ → ℤ}
    {rhs : List Bool → ℤ}
    (hf : ∀ {A B D E : List Bool → ℕ}, UnaryFn A → UnaryFn B → UnaryFn D → UnaryFn E →
      IntFn fun u => f (pairFst u) (A u) (B u) (D u) (E u))
    (hg : ∀ {A B D E G : List Bool → ℕ}, UnaryFn A → UnaryFn B → UnaryFn D → UnaryFn E →
      UnaryFn G → IntFn fun u => g (pairFst u) (A u) (B u) (D u) (E u) (G u))
    (hrhs : (fun v => DataEncode.bitstringEncode (rhs v)) ∈ FP) :
    (fun v => DataEncode.bitstringEncode ((Q (X v)).mkRow (f v) (g v) (rhs v))) ∈ FP := by
  have hXc : (fun u => X (pairFst u)) ∈ FP := mem_FP_comp pairFst_mem_FP hX
  have hcol := hQ.colFun_intFn hXc UnaryFn.index (f := fun u => f (pairFst u))
    (g := fun u => g (pairFst u)) hf hg
  have hcols : (fun v => (List.range (Q (X v)).dim).flatMap fun col =>
      DataEncode.bitstringEncode ((Q (X v)).colFun (f v) (g v) col)) ∈ FP :=
    loop_mem_FP (hQ.dim_at hX) (IntFn.encode_mem_FP hcol)
  refine mem_FP_of_eq (bracket_mem_FP (bracket1_mem_FP hcols) hrhs) fun v => ?_
  simp only [PositionalQuiver.mkRow, bitstringEncode_prod, bitstringEncode_list_eq,
    List.flatMap_map]

theorem trivialRow_mem_FP :
    (fun v => DataEncode.bitstringEncode (Q (X v)).trivialRow) ∈ FP :=
  hQ.mkRow_mem_FP hX (f := fun _ _ _ _ _ => 0) (g := fun _ _ _ _ _ _ => 0) (rhs := fun _ => 0)
    (fun _ _ _ _ => IntFn.const 0) (fun _ _ _ _ _ => IntFn.const 0)
    (IntFn.encode_mem_FP (IntFn.const 0))

theorem rowSumShape_intFn {I J K R A B D E : List Bool → ℕ} (hI : UnaryFn I) (hJ : UnaryFn J)
    (hK : UnaryFn K) (hR : UnaryFn R) (hA : UnaryFn A) (hB : UnaryFn B) (hD : UnaryFn D)
    (hE : UnaryFn E) :
    IntFn fun u => (Q (X u)).rowSumShape (I u) (J u) (K u) (R u) (A u) (B u) (D u) (E u) := by
  unfold PositionalQuiver.rowSumShape
  exact IntFn.ite (hQ.outSlot_at hX hI hJ hK) (shapeAt_intFn hI hJ hK hR hA hB hD hE).neg
    ((shapeAt_intFn hJ hI hK (UnaryFn.const 0) hA hB hD hE).neg.add
      (shapeAt_intFn hJ hI hK (((hQ.blockDim_at hX hI).sub (UnaryFn.const 1)).sub hR)
        hA hB hD hE))

theorem finalShape_intFn {I A B D E : List Bool → ℕ} (hI : UnaryFn I) (hA : UnaryFn A)
    (hB : UnaryFn B) (hD : UnaryFn D) (hE : UnaryFn E) :
    IntFn fun u => (Q (X u)).finalShape (I u) (A u) (B u) (D u) (E u) := by
  unfold PositionalQuiver.finalShape
  exact IntFn.ite ((FPPred.eq hB hI).and ((FPPred.eq hE (UnaryFn.const 0)).and
    (FPPred.lt hD (hQ.arrowCount_at hX hA hI)))) (IntFn.const (-1)) (IntFn.const 0)

omit hX

/-! ### The six families of rows -/

omit hQ in
/-- The rows' coefficient functions that vanish. -/
theorem zero4 {A B D E : List Bool → ℕ} (_ : UnaryFn A) (_ : UnaryFn B) (_ : UnaryFn D)
    (_ : UnaryFn E) : IntFn fun u =>
      (fun (_ : List Bool) (_ _ _ _ : ℕ) => (0 : ℤ)) (pairFst u) (A u) (B u) (D u) (E u) :=
  IntFn.const 0

omit hQ in
theorem zero5 {A B D E G : List Bool → ℕ} (_ : UnaryFn A) (_ : UnaryFn B) (_ : UnaryFn D)
    (_ : UnaryFn E) (_ : UnaryFn G) : IntFn fun u =>
      (fun (_ : List Bool) (_ _ _ _ _ : ℕ) => (0 : ℤ)) (pairFst u) (A u) (B u) (D u) (E u) (G u) :=
  IntFn.const 0

omit hQ in
theorem enc0 : (fun (_ : List Bool) => DataEncode.bitstringEncode (0 : ℤ)) ∈ FP :=
  IntFn.encode_mem_FP (IntFn.const 0)

/-- Family 1. -/
theorem shapeRows_mem_FP :
    (fun v => ((Q (inp 4 v)).shapeRows (var 3 v) (var 2 v) (var 1 v) (var 0 v)).flatMap
      DataEncode.bitstringEncode) ∈ FP := by
  have hX := inp_mem_FP 4
  have hS : ∀ {R : List Bool → ℕ}, UnaryFn R → ∀ {A B D E : List Bool → ℕ}, UnaryFn A →
      UnaryFn B → UnaryFn D → UnaryFn E → IntFn fun u =>
        PositionalQuiver.shapeAt (var 3 (pairFst u)) (var 2 (pairFst u)) (var 1 (pairFst u))
          (R u) (A u) (B u) (D u) (E u) :=
    fun hR _ _ _ _ hA hB hD hE => shapeAt_intFn (varL 3) (varL 2) (varL 1) hR hA hB hD hE
  have hr1 := hQ.mkRow_mem_FP hX
    (f := fun v i' j' k' r' =>
      -PositionalQuiver.shapeAt (var 3 v) (var 2 v) (var 1 v) (var 0 v) i' j' k' r')
    (g := fun _ _ _ _ _ _ => 0) (rhs := fun _ => 0)
    (fun hA hB hD hE => (hS (varL 0) hA hB hD hE).neg) zero5 enc0
  have hr2 := hQ.mkRow_mem_FP hX
    (f := fun v i' j' k' r' =>
      PositionalQuiver.shapeAt (var 3 v) (var 2 v) (var 1 v) (var 0 v + 1) i' j' k' r' -
        PositionalQuiver.shapeAt (var 3 v) (var 2 v) (var 1 v) (var 0 v) i' j' k' r')
    (g := fun _ _ _ _ _ _ => 0) (rhs := fun _ => 0)
    (fun hA hB hD hE => (hS ((varL 0).add (UnaryFn.const 1)) hA hB hD hE).sub
      (hS (varL 0) hA hB hD hE)) zero5 enc0
  have hr3 := hQ.mkRow_mem_FP hX
    (f := fun v => PositionalQuiver.shapeAt (var 3 v) (var 2 v) (var 1 v) (var 0 v))
    (g := fun _ _ _ _ _ _ => 0) (rhs := fun _ => 0)
    (fun hA hB hD hE => hS (varL 0) hA hB hD hE) zero5 enc0
  have hok := hQ.shapeOK_at hX (var_unary 3) (var_unary 2) (var_unary 1) (var_unary 0)
  have hok' := hQ.shapeOK_at hX (var_unary 3) (var_unary 2) (var_unary 1)
    ((var_unary 0).add (UnaryFn.const 1))
  refine mem_FP_of_eq (FPPred.ite_mem_FP hok (append_mem_FP hr1
    (FPPred.ite_mem_FP hok' hr2 (hQ.trivialRow_mem_FP hX))) (append_mem_FP hr3 hr1)) fun v => ?_
  simp only [PositionalQuiver.shapeRows]
  split_ifs <;> simp

/-- Family 2. -/
theorem cellRows_mem_FP :
    (fun v => ((Q (inp 5 v)).cellRows (var 4 v) (var 3 v) (var 2 v) (var 1 v) (var 0 v)).flatMap
      DataEncode.bitstringEncode) ∈ FP := by
  have hX := inp_mem_FP 5
  have hC : ∀ {A B D E G : List Bool → ℕ}, UnaryFn A → UnaryFn B → UnaryFn D → UnaryFn E →
      UnaryFn G → IntFn fun u =>
        PositionalQuiver.cellAt (var 4 (pairFst u)) (var 3 (pairFst u)) (var 2 (pairFst u))
          (var 1 (pairFst u)) (var 0 (pairFst u)) (A u) (B u) (D u) (E u) (G u) :=
    fun hA hB hD hE hG =>
      cellAt_intFn (varL 4) (varL 3) (varL 2) (varL 1) (varL 0) hA hB hD hE hG
  have hr1 := hQ.mkRow_mem_FP hX (f := fun _ _ _ _ _ => 0)
    (g := fun v i' j' k' r' l' =>
      -PositionalQuiver.cellAt (var 4 v) (var 3 v) (var 2 v) (var 1 v) (var 0 v) i' j' k' r' l')
    (rhs := fun _ => 0) zero4 (fun hA hB hD hE hG => (hC hA hB hD hE hG).neg) enc0
  have hr2 := hQ.mkRow_mem_FP hX (f := fun _ _ _ _ _ => 0)
    (g := fun v => PositionalQuiver.cellAt (var 4 v) (var 3 v) (var 2 v) (var 1 v) (var 0 v))
    (rhs := fun _ => 0) zero4 (fun hA hB hD hE hG => hC hA hB hD hE hG) enc0
  have hok := hQ.cellOK_at hX (var_unary 4) (var_unary 3) (var_unary 2) (var_unary 1)
    (var_unary 0)
  refine mem_FP_of_eq (FPPred.ite_mem_FP hok (append_mem_FP hr1 (hQ.trivialRow_mem_FP hX))
    (append_mem_FP hr2 hr1)) fun v => ?_
  simp only [PositionalQuiver.cellRows]
  split_ifs <;> simp

/-- Family 3. -/
theorem rowSumRows_mem_FP :
    (fun v => ((Q (inp 4 v)).rowSumRows (var 3 v) (var 2 v) (var 1 v) (var 0 v)).flatMap
      DataEncode.bitstringEncode) ∈ FP := by
  have hX := inp_mem_FP 4
  have hXc : (fun u => inp 4 (pairFst u)) ∈ FP := mem_FP_comp pairFst_mem_FP hX
  have hS : ∀ {A B D E : List Bool → ℕ}, UnaryFn A → UnaryFn B → UnaryFn D → UnaryFn E →
      IntFn fun u => (Q (inp 4 (pairFst u))).rowSumShape (var 3 (pairFst u)) (var 2 (pairFst u))
        (var 1 (pairFst u)) (var 0 (pairFst u)) (A u) (B u) (D u) (E u) :=
    fun hA hB hD hE =>
      hQ.rowSumShape_intFn hXc (varL 3) (varL 2) (varL 1) (varL 0) hA hB hD hE
  have hC : ∀ {A B D E G : List Bool → ℕ}, UnaryFn A → UnaryFn B → UnaryFn D → UnaryFn E →
      UnaryFn G → IntFn fun u =>
        PositionalQuiver.rowSumCell (var 3 (pairFst u)) (var 2 (pairFst u)) (var 1 (pairFst u))
          (var 0 (pairFst u)) (A u) (B u) (D u) (E u) (G u) :=
    fun hA hB hD hE _ => rowSumCell_intFn (varL 3) (varL 2) (varL 1) (varL 0) hA hB hD hE
  have hr1 := hQ.mkRow_mem_FP hX
    (f := fun v => (Q (inp 4 v)).rowSumShape (var 3 v) (var 2 v) (var 1 v) (var 0 v))
    (g := fun v => PositionalQuiver.rowSumCell (var 3 v) (var 2 v) (var 1 v) (var 0 v))
    (rhs := fun _ => 0) (fun hA hB hD hE => hS hA hB hD hE)
    (fun hA hB hD hE hG => hC hA hB hD hE hG) enc0
  have hr2 := hQ.mkRow_mem_FP hX
    (f := fun v i' j' k' r' =>
      -(Q (inp 4 v)).rowSumShape (var 3 v) (var 2 v) (var 1 v) (var 0 v) i' j' k' r')
    (g := fun v i' j' k' r' l' =>
      -PositionalQuiver.rowSumCell (var 3 v) (var 2 v) (var 1 v) (var 0 v) i' j' k' r' l')
    (rhs := fun _ => 0) (fun hA hB hD hE => (hS hA hB hD hE).neg)
    (fun hA hB hD hE hG => (hC hA hB hD hE hG).neg) enc0
  have hok := hQ.slot_at hX (var_unary 3) (var_unary 2) (var_unary 1) (var_unary 0)
  refine mem_FP_of_eq (FPPred.ite_mem_FP hok (append_mem_FP hr1 hr2)
    (append_mem_FP (hQ.trivialRow_mem_FP hX) (hQ.trivialRow_mem_FP hX))) fun v => ?_
  simp only [PositionalQuiver.rowSumRows]
  split_ifs <;> simp

/-- Family 4. -/
theorem columnRow_mem_FP :
    (fun v => DataEncode.bitstringEncode
      ((Q (inp 5 v)).columnRow (var 4 v) (var 3 v) (var 2 v) (var 1 v) (var 0 v))) ∈ FP := by
  have hX := inp_mem_FP 5
  have hr := hQ.mkRow_mem_FP hX (f := fun _ _ _ _ _ => 0)
    (g := fun v i' j' k' r' l' =>
      if i' = var 4 v ∧ j' = var 3 v ∧ k' = var 2 v then
        (if r' = var 1 v + 1 ∧ l' ≤ var 0 v then 1 else 0) -
          (if r' = var 1 v ∧ l' < var 0 v then 1 else 0)
      else 0)
    (rhs := fun _ => 0) zero4
    (fun hA hB hD hE hG => IntFn.ite ((FPPred.eq hA (varL 4)).and ((FPPred.eq hB (varL 3)).and
      (FPPred.eq hD (varL 2))))
      ((IntFn.ind ((FPPred.eq hE ((varL 1).add (UnaryFn.const 1))).and
        (FPPred.le hG (varL 0)))).sub
        (IntFn.ind ((FPPred.eq hE (varL 1)).and (FPPred.lt hG (varL 0)))))
      (IntFn.const 0)) enc0
  have hok := hQ.cellOK_at hX (var_unary 4) (var_unary 3) (var_unary 2)
    ((var_unary 1).add (UnaryFn.const 1)) (var_unary 0)
  refine mem_FP_of_eq (FPPred.ite_mem_FP hok hr (hQ.trivialRow_mem_FP hX)) fun v => ?_
  simp only [PositionalQuiver.columnRow]
  split_ifs <;> rfl

/-- Family 5. -/
theorem latticeRow_mem_FP :
    (fun v => DataEncode.bitstringEncode
      ((Q (inp 5 v)).latticeRow (var 4 v) (var 3 v) (var 2 v) (var 1 v) (var 0 v))) ∈ FP := by
  have hX := inp_mem_FP 5
  have hXc : (fun u => inp 5 (pairFst u)) ∈ FP := mem_FP_comp pairFst_mem_FP hX
  have hr := hQ.mkRow_mem_FP hX (f := fun _ _ _ _ _ => 0)
    (g := fun v i' j' k' r' l' =>
      if i' = var 4 v then
        if j' = var 3 v ∧ k' = var 2 v then
          (if l' = var 0 v + 1 ∧ r' ≤ var 1 v then 1 else 0) -
            (if l' = var 0 v ∧ r' < var 1 v then 1 else 0)
        else if (Q (inp 5 v)).slotBefore (var 4 v) j' k' (var 3 v) (var 2 v) then
          (if l' = var 0 v + 1 then 1 else 0) - (if l' = var 0 v then 1 else 0)
        else 0
      else 0)
    (rhs := fun _ => 0) zero4
    (fun hA hB hD hE hG => IntFn.ite (FPPred.eq hA (varL 4))
      (IntFn.ite ((FPPred.eq hB (varL 3)).and (FPPred.eq hD (varL 2)))
        ((IntFn.ind ((FPPred.eq hG ((varL 0).add (UnaryFn.const 1))).and
          (FPPred.le hE (varL 1)))).sub
          (IntFn.ind ((FPPred.eq hG (varL 0)).and (FPPred.lt hE (varL 1)))))
        (IntFn.ite (hQ.slotBefore_at hXc (varL 4) (varL 3) hB hD (varL 2))
          ((IntFn.ind (FPPred.eq hG ((varL 0).add (UnaryFn.const 1)))).sub
            (IntFn.ind (FPPred.eq hG (varL 0))))
          (IntFn.const 0)))
      (IntFn.const 0)) enc0
  have hok := hQ.cellOK_at hX (var_unary 4) (var_unary 3) (var_unary 2) (var_unary 1)
    ((var_unary 0).add (UnaryFn.const 1))
  refine mem_FP_of_eq (FPPred.ite_mem_FP hok hr (hQ.trivialRow_mem_FP hX)) fun v => ?_
  simp only [PositionalQuiver.latticeRow]
  split_ifs <;> rfl

/-- Family 6. -/
theorem finalRows_mem_FP :
    (fun v => ((Q (inp 2 v)).finalRows (var 1 v) (var 0 v)).flatMap
      DataEncode.bitstringEncode) ∈ FP := by
  have hX := inp_mem_FP 2
  have hXc : (fun u => inp 2 (pairFst u)) ∈ FP := mem_FP_comp pairFst_mem_FP hX
  have hS : ∀ {A B D E : List Bool → ℕ}, UnaryFn A → UnaryFn B → UnaryFn D → UnaryFn E →
      IntFn fun u => (Q (inp 2 (pairFst u))).finalShape (var 1 (pairFst u)) (A u) (B u) (D u)
        (E u) :=
    fun hA hB hD hE => hQ.finalShape_intFn hXc (varL 1) hA hB hD hE
  have hC : ∀ {A B D E G : List Bool → ℕ}, UnaryFn A → UnaryFn B → UnaryFn D → UnaryFn E →
      UnaryFn G → IntFn fun u =>
        PositionalQuiver.finalCell (var 1 (pairFst u)) (var 0 (pairFst u)) (A u) (B u) (D u)
          (E u) (G u) :=
    fun hA _ _ _ hG => finalCell_intFn (varL 1) (varL 0) hA hG
  have hr1 := hQ.mkRow_mem_FP hX (f := fun v => (Q (inp 2 v)).finalShape (var 1 v))
    (g := fun v => PositionalQuiver.finalCell (var 1 v) (var 0 v))
    (rhs := fun v => (Q (inp 2 v)).weight (var 1 v) (var 0 v))
    (fun hA hB hD hE => hS hA hB hD hE) (fun hA hB hD hE hG => hC hA hB hD hE hG)
    (hQ.weight_at hX (var_unary 1) (var_unary 0))
  have hr2 := hQ.mkRow_mem_FP hX
    (f := fun v i' j' k' r' => -(Q (inp 2 v)).finalShape (var 1 v) i' j' k' r')
    (g := fun v i' j' k' r' l' => -PositionalQuiver.finalCell (var 1 v) (var 0 v) i' j' k' r' l')
    (rhs := fun v => -(Q (inp 2 v)).weight (var 1 v) (var 0 v))
    (fun hA hB hD hE => (hS hA hB hD hE).neg) (fun hA hB hD hE hG => (hC hA hB hD hE hG).neg)
    (hQ.weightNeg_at hX (var_unary 1) (var_unary 0))
  have hok : FPPred fun v => ((Q (inp 2 v)).isStart (var 1 v) &&
      decide (var 0 v < (Q (inp 2 v)).blockDim (var 1 v))) = true :=
    ((hQ.isStart_at hX (var_unary 1)).and (FPPred.lt (var_unary 0)
      (hQ.blockDim_at hX (var_unary 1)))).of_iff fun v => by simp
  refine mem_FP_of_eq (FPPred.ite_mem_FP hok (append_mem_FP hr1 hr2)
    (append_mem_FP (hQ.trivialRow_mem_FP hX) (hQ.trivialRow_mem_FP hX))) fun v => ?_
  simp only [PositionalQuiver.finalRows]
  split_ifs <;> simp

/-! ### The loops -/

theorem loop4_mem_FP {F : List Bool → ℕ → ℕ → ℕ → ℕ → List Bool}
    (hF : (fun v => F (inp 4 v) (var 3 v) (var 2 v) (var 1 v) (var 0 v)) ∈ FP) :
    (fun z => (Q z).loop4 (F z)) ∈ FP := by
  have h3 : (fun w => (List.range (Q (inp 3 w)).n).flatMap
      (F (inp 3 w) (var 2 w) (var 1 w) (var 0 w))) ∈ FP :=
    loop_mem_FP (hQ.n_at (inp_mem_FP 3)) (F := fun w => F (inp 3 w) (var 2 w) (var 1 w) (var 0 w))
      (mem_FP_of_eq hF fun _ => rfl)
  have h2 : (fun w => (List.range 2).flatMap fun k => (List.range (Q (inp 2 w)).n).flatMap
      (F (inp 2 w) (var 1 w) (var 0 w) k)) ∈ FP :=
    loop_mem_FP (UnaryFn.const 2) (F := fun w k => (List.range (Q (inp 2 w)).n).flatMap
      (F (inp 2 w) (var 1 w) (var 0 w) k)) (mem_FP_of_eq h3 fun _ => rfl)
  have h1 : (fun w => (List.range (Q (inp 1 w)).n).flatMap fun j => (List.range 2).flatMap
      fun k => (List.range (Q (inp 1 w)).n).flatMap (F (inp 1 w) (var 0 w) j k)) ∈ FP :=
    loop_mem_FP (hQ.n_at (inp_mem_FP 1)) (F := fun w j => (List.range 2).flatMap fun k =>
      (List.range (Q (inp 1 w)).n).flatMap (F (inp 1 w) (var 0 w) j k))
      (mem_FP_of_eq h2 fun _ => rfl)
  exact mem_FP_of_eq (loop_mem_FP hQ.n (F := fun z i => (List.range (Q z).n).flatMap fun j =>
      (List.range 2).flatMap fun k => (List.range (Q z).n).flatMap (F z i j k))
    (mem_FP_of_eq h1 fun _ => rfl)) fun _ => rfl

theorem loop5_mem_FP {F : List Bool → ℕ → ℕ → ℕ → ℕ → ℕ → List Bool}
    (hF : (fun v => F (inp 5 v) (var 4 v) (var 3 v) (var 2 v) (var 1 v) (var 0 v)) ∈ FP) :
    (fun z => (Q z).loop5 (F z)) ∈ FP := by
  have h4 : (fun v => (List.range (Q (inp 4 v)).n).flatMap
      (F (inp 4 v) (var 3 v) (var 2 v) (var 1 v) (var 0 v))) ∈ FP :=
    loop_mem_FP (hQ.n_at (inp_mem_FP 4))
      (F := fun v => F (inp 4 v) (var 3 v) (var 2 v) (var 1 v) (var 0 v))
      (mem_FP_of_eq hF fun _ => rfl)
  exact hQ.loop4_mem_FP (F := fun z i j k r => (List.range (Q z).n).flatMap (F z i j k r)) h4

omit hQ in
theorem loop4_flatMap {α : Type} (P : PositionalQuiver) (f : ℕ → ℕ → ℕ → ℕ → List α)
    (h : α → List Bool) :
    (P.loop4 f).flatMap h = P.loop4 fun i j k r => (f i j k r).flatMap h := by
  simp only [PositionalQuiver.loop4, List.flatMap_assoc]

omit hQ in
theorem loop5_flatMap {α : Type} (P : PositionalQuiver) (f : ℕ → ℕ → ℕ → ℕ → ℕ → List α)
    (h : α → List Bool) :
    (P.loop5 f).flatMap h = P.loop5 fun i j k r l => (f i j k r l).flatMap h := by
  simp only [PositionalQuiver.loop5, loop4_flatMap, List.flatMap_assoc]

/-- **Writing the rows of the polytope is polynomial-time.** -/
theorem rows_mem_FP :
    (fun z => (Q z).polytope.rows.flatMap DataEncode.bitstringEncode) ∈ FP := by
  have h1 := hQ.loop4_mem_FP (F := fun z i j k r => ((Q z).shapeRows i j k r).flatMap
    DataEncode.bitstringEncode) hQ.shapeRows_mem_FP
  have h2 := hQ.loop5_mem_FP (F := fun z i j k r l => ((Q z).cellRows i j k r l).flatMap
    DataEncode.bitstringEncode) hQ.cellRows_mem_FP
  have h3 := hQ.loop4_mem_FP (F := fun z i j k r => ((Q z).rowSumRows i j k r).flatMap
    DataEncode.bitstringEncode) hQ.rowSumRows_mem_FP
  have h4 := hQ.loop5_mem_FP (F := fun z i j k r l => DataEncode.bitstringEncode
    ((Q z).columnRow i j k r l)) hQ.columnRow_mem_FP
  have h5 := hQ.loop5_mem_FP (F := fun z i j k r l => DataEncode.bitstringEncode
    ((Q z).latticeRow i j k r l)) hQ.latticeRow_mem_FP
  have h6' : (fun w => (List.range (Q (inp 1 w)).n).flatMap fun l =>
      ((Q (inp 1 w)).finalRows (var 0 w) l).flatMap DataEncode.bitstringEncode) ∈ FP :=
    loop_mem_FP (hQ.n_at (inp_mem_FP 1)) (F := fun w l =>
      ((Q (inp 1 w)).finalRows (var 0 w) l).flatMap DataEncode.bitstringEncode)
      (mem_FP_of_eq hQ.finalRows_mem_FP fun _ => rfl)
  have h6 : (fun z => (List.range (Q z).n).flatMap fun i => (List.range (Q z).n).flatMap
      fun l => ((Q z).finalRows i l).flatMap DataEncode.bitstringEncode) ∈ FP :=
    loop_mem_FP hQ.n (F := fun z i => (List.range (Q z).n).flatMap fun l =>
      ((Q z).finalRows i l).flatMap DataEncode.bitstringEncode) (mem_FP_of_eq h6' fun _ => rfl)
  refine mem_FP_of_eq (append_mem_FP (append_mem_FP (append_mem_FP (append_mem_FP
    (append_mem_FP h1 h2) h3) h4) h5) h6) fun z => ?_
  simp only [PositionalQuiver.polytope, List.flatMap_append, loop4_flatMap, loop5_flatMap,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.flatMap_assoc]

/-- **Writing the polytope of a positional quiver is polynomial-time**, when its data are. -/
theorem polytope_encode_mem_FP :
    (fun z => DataEncode.bitstringEncode (Q z).polytope) ∈ FP := by
  have hdim : UnaryFn fun z => (Q z).polytope.dim := hQ.dim_at id_mem_FP
  refine mem_FP_of_eq (bracket_mem_FP (natEncode_mem_FP hdim) (bracket1_mem_FP hQ.rows_mem_FP))
    fun z => ?_
  rw [show DataEncode.bitstringEncode (Q z).polytope =
    DataEncode.bitstringEncode ((Q z).polytope.dim, (Q z).polytope.rows) from rfl,
    bitstringEncode_prod, bitstringEncode_list_eq]

end PolytopeData

end

end Schubert.RS.Algorithms
