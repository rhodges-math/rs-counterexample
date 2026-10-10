import RSCounterexample.LinearProgramming.Words.Mul

/-!
# Division of words

Unsigned words are divided by schoolbook long division. The digits of the dividend are read from
the most significant one down. The remainder, one digit wider than the divisor, takes the next
digit, and the divisor is subtracted whenever it fits; this records a quotient digit `1`. The loop
is a fold over the digits of the dividend with states of fixed length, so it is polynomial-time
(`LinearProgramming.udiv_mem_FP`, `LinearProgramming.umod_mem_FP`).

Signed division divides the absolute values and fixes the sign. It is truncated division
`Int.tdiv`, and it needs the integers to fit their words (`LinearProgramming.wtdiv_word`). For an
exact division it is the usual quotient (`LinearProgramming.wtdiv_word_of_dvd`).

## Main definitions

* `LinearProgramming.udiv`, `LinearProgramming.umod`: quotient and remainder of unsigned words.
* `LinearProgramming.wabs`: the absolute value of a word.
* `LinearProgramming.wtdiv`: truncated division of words.

## Main results

* `LinearProgramming.udiv_toBitsLE`, `LinearProgramming.umod_toBitsLE`: long division computes the
  quotient and the remainder.
* `LinearProgramming.wtdiv_word`, `LinearProgramming.wtdiv_word_of_dvd`,
  `LinearProgramming.wtdiv_mem_FP`, `LinearProgramming.WordFn.tdiv`,
  `LinearProgramming.WordFn.div_of_dvd`.
-/

namespace LinearProgramming

open Complexity

theorem selectHead_single (b : Bool) (x y : List Bool) :
    Cobham.selectHead [b] x y = if b = true then x else y := by
  cases b <;> rfl

theorem toBitsLE_zero (W : ℕ) : Nat.toBitsLE W 0 = List.replicate W false :=
  ((eq_toBitsLE_iff (by positivity)).mpr ⟨by simp, binValLE_replicate_false W⟩).symm

theorem binValLE_append_false : ∀ x : List Bool, binValLE (x ++ [false]) = binValLE x
  | [] => rfl
  | b :: x => by rw [List.cons_append, binValLE_cons, binValLE_cons, binValLE_append_false x]

/-- The comparison flag of two binary expansions of the same length. -/
theorem ltFlag_toBitsLE {W a b : ℕ} (ha : a < 2 ^ W) (hb : b < 2 ^ W) :
    ltFlag (Nat.toBitsLE W a) (Nat.toBitsLE W b) = [decide (a < b)] := by
  have h := ltFlag_eq_true_iff (Nat.toBitsLE W a) (Nat.toBitsLE W b) (by simp)
  rw [binValLE_toBitsLE, binValLE_toBitsLE, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h
  rw [ltFlag_eq _ _ (by simp)] at h ⊢
  by_cases hab : a < b
  · simp only [hab, decide_true]
    exact h.mpr hab
  · simp only [hab, decide_false, List.cons.injEq, and_true]
    by_contra hne
    simp only [Bool.not_eq_false] at hne
    exact hab (h.mp (by rw [hne]))

/-! ### Unsigned long division -/

/-- One step of long division by `y`. The state is a pair: the quotient so far, of the width of
`y`, and the remainder, one digit wider. The digit `b` is brought down into the remainder, and `y`
is subtracted if it fits; the quotient digit records whether it did. -/
def divStep (y : List Bool) (b : Bool) (s : List Bool) : List Bool :=
  Cobham.selectHead (ltFlag ((b :: pairSnd s).take (y.length + 1)) (y ++ [false]))
    (pair ((false :: pairFst s).take y.length) ((b :: pairSnd s).take (y.length + 1)))
    (pair ((true :: pairFst s).take y.length)
      (wsub ((b :: pairSnd s).take (y.length + 1)) (y ++ [false])))

/-- Long division of the dividend `t` by `y`, over the digits of `t` from the most significant one
down. -/
def divAux (y : List Bool) : List Bool → List Bool
  | [] => pair (List.replicate y.length false) (List.replicate (y.length + 1) false)
  | b :: t => divStep y b (divAux y t)

/-- The quotient of unsigned words. -/
def udiv (x y : List Bool) : List Bool := pairFst (divAux y x)

/-- The remainder of unsigned words. -/
def umod (x y : List Bool) : List Bool := (pairSnd (divAux y x)).take y.length

theorem length_divStep (y : List Bool) (b : Bool) (q r : List Bool) (hq : q.length = y.length)
    (hr : r.length = y.length + 1) :
    (divStep y b (pair q r)).length = 3 * y.length + 3 := by
  have hlen : ((b :: r).take (y.length + 1)).length = (y ++ [false]).length := by simp [hr]
  rw [divStep, pairFst_pair, pairSnd_pair, ltFlag_eq _ _ hlen.symm, selectHead_single]
  split
  · simp [hq, hr]
    omega
  · rw [pair_length, wsub, length_wadd _ _ (by rw [length_wneg, hlen])]
    simp [hq, hr]
    omega

theorem divAux_eq_pair (y : List Bool) :
    ∀ t, ∃ q r, divAux y t = pair q r ∧ q.length = y.length ∧ r.length = y.length + 1
  | [] => ⟨_, _, rfl, by simp, by simp⟩
  | b :: t => by
    obtain ⟨q, r, h, hq, hr⟩ := divAux_eq_pair y t
    have hlen : ((b :: r).take (y.length + 1)).length = (y ++ [false]).length := by simp [hr]
    rw [divAux, h, divStep, pairFst_pair, pairSnd_pair, ltFlag_eq _ _ hlen.symm,
      selectHead_single]
    split
    · exact ⟨_, _, rfl, by simp [hq], by simp [hr]⟩
    · refine ⟨_, _, rfl, by simp [hq], ?_⟩
      rw [wsub, length_wadd _ _ (by rw [length_wneg, hlen])]
      simp [hr]

theorem length_divAux (y t : List Bool) : (divAux y t).length = 3 * y.length + 3 := by
  obtain ⟨q, r, h, hq, hr⟩ := divAux_eq_pair y t
  rw [h, pair_length, hq, hr]
  omega

/-- **Long division computes the quotient and the remainder** of every dividend with at most as
many digits as the divisor. -/
theorem divAux_eq (y : List Bool) (hy : 0 < binValLE y) :
    ∀ t : List Bool, t.length ≤ y.length →
      divAux y t = pair (Nat.toBitsLE y.length (binValLE t / binValLE y))
        (Nat.toBitsLE (y.length + 1) (binValLE t % binValLE y))
  | [], _ => by simp [divAux, binValLE, toBitsLE_zero]
  | b :: t, ht => by
    have htW : t.length + 1 ≤ y.length := by simpa using ht
    rw [divAux, divAux_eq y hy t (by omega), divStep, pairFst_pair, pairSnd_pair, binValLE_cons]
    set W := y.length with hW
    set d := binValLE y with hd
    set v := binValLE t with hv
    have hdW : d < 2 ^ W := binValLE_lt y
    have hvt : v < 2 ^ t.length := binValLE_lt t
    have hv2 : 2 * v < 2 ^ W := by
      calc 2 * v < 2 * 2 ^ t.length := by omega
        _ = 2 ^ (t.length + 1) := by ring
        _ ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) htW
    have hmod : v % d < d := Nat.mod_lt _ hy
    have hdiv : v / d ≤ v := Nat.div_le_self v d
    have hb : b.toNat < 2 := by cases b <;> simp
    have hW1 : (2 : ℕ) ^ (W + 1) = 2 * 2 ^ W := by ring
    have hr : (b :: Nat.toBitsLE (W + 1) (v % d)).take (W + 1) =
        Nat.toBitsLE (W + 1) (b.toNat + 2 * (v % d)) := by
      have h1 : v % d < 2 ^ (W + 1) := by omega
      have h2 : b.toNat + 2 * (v % d) < 2 ^ (W + 1) := by omega
      rw [eq_toBitsLE_iff h2]
      refine ⟨by simp, ?_⟩
      rw [binValLE_take, binValLE_cons, binValLE_toBitsLE, Nat.mod_eq_of_lt h1,
        Nat.mod_eq_of_lt h2]
    have hy' : y ++ [false] = Nat.toBitsLE (W + 1) d := by
      rw [eq_toBitsLE_iff (by omega)]
      exact ⟨by simp [hW], binValLE_append_false y⟩
    have hq : ∀ c : Bool, (c :: Nat.toBitsLE W (v / d)).take W =
        Nat.toBitsLE W (c.toNat + 2 * (v / d)) := by
      intro c
      have hc : c.toNat < 2 := by cases c <;> simp
      have hlt : c.toNat + 2 * (v / d) < 2 ^ W := by
        have : 2 * (v / d) + 2 ≤ 2 ^ W := by
          have h2 : 2 ^ (t.length + 1) ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) htW
          rw [pow_succ] at h2
          omega
        omega
      have h3 : v / d < 2 ^ W := by omega
      rw [eq_toBitsLE_iff hlt]
      refine ⟨by simp, ?_⟩
      rw [binValLE_take, binValLE_cons, binValLE_toBitsLE, Nat.mod_eq_of_lt h3,
        Nat.mod_eq_of_lt hlt]
    rw [hr, hy', ltFlag_toBitsLE (by omega) (by omega), selectHead_single]
    by_cases hc : b.toNat + 2 * (v % d) < d
    · rw [ite_eq_left (by simpa using hc), hq false]
      obtain ⟨h1, h2⟩ := (Nat.div_mod_unique hy).mpr
        (show b.toNat + 2 * (v % d) + d * (2 * (v / d)) = b.toNat + 2 * v ∧
          b.toNat + 2 * (v % d) < d from ⟨by
            have := Nat.div_add_mod v d
            nlinarith, hc⟩)
      rw [h1, h2]
      simp
    · rw [ite_eq_right (by simpa using hc), hq true]
      have hsub : wsub (Nat.toBitsLE (W + 1) (b.toNat + 2 * (v % d))) (Nat.toBitsLE (W + 1) d)
          = Nat.toBitsLE (W + 1) (b.toNat + 2 * (v % d) - d) := by
        rw [← word_natCast, ← word_natCast, wsub_word, ← word_natCast]
        congr 1
        push_cast [show d ≤ b.toNat + 2 * (v % d) by omega]
        ring
      rw [hsub]
      obtain ⟨h1, h2⟩ := (Nat.div_mod_unique hy).mpr
        (show b.toNat + 2 * (v % d) - d + d * (1 + 2 * (v / d)) = b.toNat + 2 * v ∧
          b.toNat + 2 * (v % d) - d < d from ⟨by
            have := Nat.div_add_mod v d
            have hle : d ≤ b.toNat + 2 * (v % d) := by omega
            zify [hle]
            have hc' : (d : ℤ) * (v / d : ℕ) + (v % d : ℕ) = v := by exact_mod_cast this
            nlinarith, by omega⟩)
      rw [h1, h2]
      simp [Bool.toNat_true]

/-- **Quotient of unsigned words.** -/
theorem udiv_toBitsLE {W a d : ℕ} (ha : a < 2 ^ W) (hd : 0 < d) (hdW : d < 2 ^ W) :
    udiv (Nat.toBitsLE W a) (Nat.toBitsLE W d) = Nat.toBitsLE W (a / d) := by
  have hy : binValLE (Nat.toBitsLE W d) = d := by
    rw [binValLE_toBitsLE, Nat.mod_eq_of_lt hdW]
  have hx : binValLE (Nat.toBitsLE W a) = a := by
    rw [binValLE_toBitsLE, Nat.mod_eq_of_lt ha]
  rw [udiv, divAux_eq _ (by rw [hy]; exact hd) _ (by simp), pairFst_pair, hx, hy,
    Nat.length_toBitsLE]

/-- **Remainder of unsigned words.** -/
theorem umod_toBitsLE {W a d : ℕ} (ha : a < 2 ^ W) (hd : 0 < d) (hdW : d < 2 ^ W) :
    umod (Nat.toBitsLE W a) (Nat.toBitsLE W d) = Nat.toBitsLE W (a % d) := by
  have hy : binValLE (Nat.toBitsLE W d) = d := by
    rw [binValLE_toBitsLE, Nat.mod_eq_of_lt hdW]
  have hx : binValLE (Nat.toBitsLE W a) = a := by
    rw [binValLE_toBitsLE, Nat.mod_eq_of_lt ha]
  rw [umod, divAux_eq _ (by rw [hy]; exact hd) _ (by simp), pairSnd_pair, hx, hy,
    Nat.length_toBitsLE]
  have hm : a % d < 2 ^ W := lt_trans (Nat.mod_lt a hd) hdW
  have hm' : a % d < 2 ^ (W + 1) :=
    lt_of_lt_of_le hm (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ W))
  rw [eq_toBitsLE_iff hm]
  refine ⟨by simp, ?_⟩
  rw [binValLE_take, binValLE_toBitsLE, Nat.mod_eq_of_lt hm', Nat.mod_eq_of_lt hm]

theorem divStep_mem_FP {Y S : List Bool → List Bool} (hY : Y ∈ FP) (hS : S ∈ FP) (b : Bool) :
    (fun z => divStep (Y z) b (S z)) ∈ FP := by
  have hW1 : UnaryFn fun z => (Y z).length + 1 := (UnaryFn.length hY).add (UnaryFn.const 1)
  have hr : (fun z => (b :: pairSnd (S z)).take ((Y z).length + 1)) ∈ FP :=
    take_mem_FP (mem_FP_comp (mem_FP_comp hS pairSnd_mem_FP) (Cobham.cons_mem_FP b)) hW1
  have hy : (fun z => Y z ++ [false]) ∈ FP := Cobham.appendFn_mem_FP hY (constFn_mem_FP _)
  have hq : ∀ c : Bool, (fun z => (c :: pairFst (S z)).take (Y z).length) ∈ FP := fun c =>
    take_mem_FP (mem_FP_comp (mem_FP_comp hS pairFst_mem_FP) (Cobham.cons_mem_FP c))
      (UnaryFn.length hY)
  exact Cobham.selectHeadFn_mem_FP (ltFlagFn_mem_FP hr hy) (mem_FP_pair (hq false) hr)
    (mem_FP_pair (hq true) (wsub_mem_FP hr hy))

theorem divAux_mem_FP {X Y : List Bool → List Bool} (hX : X ∈ FP) (hY : Y ∈ FP) :
    (fun z => divAux (Y z) (X z)) ∈ FP := by
  have hw : (fun q => pairFst (pairFst q)) ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have hs : (fun q => pairSnd (pairFst q)) ∈ FP := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
  have hE : (fun z => pair (List.replicate (Y z).length false)
      (List.replicate ((Y z).length + 1) false)) ∈ FP :=
    mem_FP_pair ((UnaryFn.length hY).replicate_mem_FP false)
      (((UnaryFn.length hY).add (UnaryFn.const 1)).replicate_mem_FP false)
  obtain ⟨p, hp⟩ := Cobham.output_length_poly_of_mem_FP hY
  exact recFold_mem_FP_of_bound (g := fun z t => divAux (Y z) t)
    (divStep_mem_FP hw hs false) (divStep_mem_FP hw hs true) hE hY hX (fun _ => rfl)
    (fun _ _ => by simp [divAux]) (fun _ _ => by simp [divAux])
    ((PolyBound.const 3).mul (PolyBound.eval p) |>.add (PolyBound.const 3)) fun z t _ => by
      rw [length_divAux]
      have := hp z
      omega

theorem udiv_mem_FP {X Y : List Bool → List Bool} (hX : X ∈ FP) (hY : Y ∈ FP) :
    (fun z => udiv (X z) (Y z)) ∈ FP :=
  mem_FP_comp (divAux_mem_FP hX hY) pairFst_mem_FP

theorem umod_mem_FP {X Y : List Bool → List Bool} (hX : X ∈ FP) (hY : Y ∈ FP) :
    (fun z => umod (X z) (Y z)) ∈ FP :=
  take_mem_FP (mem_FP_comp (divAux_mem_FP hX hY) pairSnd_mem_FP) (UnaryFn.length hY)

/-! ### Signed division -/

/-- The absolute value of a word. -/
def wabs (x : List Bool) : List Bool := Cobham.selectHead [msb x] (wneg x) x

theorem wabs_word {W : ℕ} {a : ℤ} (h : Fits W a) : wabs (word W a) = Nat.toBitsLE W a.natAbs := by
  rw [wabs, msb_word h, selectHead_single, ← word_natCast]
  by_cases ha : a < 0
  · rw [ite_eq_left (by simpa using ha), wneg_word]
    congr 1
    omega
  · rw [ite_eq_right (by simpa using ha)]
    congr 1
    omega

theorem wabs_mem_FP {X : List Bool → List Bool} (hX : X ∈ FP) : (fun z => wabs (X z)) ∈ FP :=
  Cobham.selectHeadFn_mem_FP (msb_mem_FP hX) (wneg_mem_FP hX) hX

/-- Truncated division of words: the quotient of the absolute values, with the sign of the
product. -/
def wtdiv (x y : List Bool) : List Bool :=
  Cobham.selectHead [msb x == msb y] (udiv (wabs x) (wabs y)) (wneg (udiv (wabs x) (wabs y)))

/-- **Truncated division of words** of integers that fit. -/
theorem wtdiv_word {W : ℕ} {a b : ℤ} (ha : Fits W a) (hb : Fits W b) (hb0 : b ≠ 0) :
    wtdiv (word W a) (word W b) = word W (a.tdiv b) := by
  have hpow : (2 : ℤ) ^ (W - 1) ≤ 2 ^ W := pow_le_pow_right₀ (by norm_num) (by omega)
  have hlt : ∀ c : ℤ, Fits W c → c.natAbs < 2 ^ W := fun c hc => by
    have h1 : ((c.natAbs : ℕ) : ℤ) < 2 ^ W := by
      rw [Int.natCast_natAbs]
      exact lt_of_lt_of_le hc hpow
    exact_mod_cast h1
  have hq : udiv (wabs (word W a)) (wabs (word W b)) = word W (a.natAbs / b.natAbs : ℕ) := by
    rw [wabs_word ha, wabs_word hb, udiv_toBitsLE (hlt a ha) (Int.natAbs_pos.mpr hb0) (hlt b hb),
      word_natCast]
  rw [wtdiv, hq, msb_word ha, msb_word hb, selectHead_single, wneg_word]
  have key : a.tdiv b = (if a < 0 ↔ b < 0 then 1 else -1) * ((a.natAbs / b.natAbs : ℕ) : ℤ) := by
    rw [Int.ofNat_tdiv]
    rcases Int.natAbs_eq a with h1 | h1 <;> rcases Int.natAbs_eq b with h2 | h2
    · rw [ite_eq_left (by omega)]
      conv_lhs => rw [h1, h2]
      ring
    · rw [ite_eq_right (by omega)]
      conv_lhs => rw [h1, h2, Int.tdiv_neg]
      ring
    · by_cases ha0 : a = 0
      · subst ha0
        simp
      rw [ite_eq_right (by omega)]
      conv_lhs => rw [h1, h2, Int.neg_tdiv]
      ring
    · by_cases ha0 : a = 0
      · subst ha0
        simp
      rw [ite_eq_left (by omega)]
      conv_lhs => rw [h1, h2, Int.neg_tdiv, Int.tdiv_neg, neg_neg]
      ring
  rw [key]
  by_cases hs : (a < 0 ↔ b < 0)
  · rw [ite_eq_left (by simpa [beq_iff_eq] using hs), ite_eq_left hs, one_mul]
  · rw [ite_eq_right (by simpa [beq_iff_eq] using hs), ite_eq_right hs, neg_one_mul]

/-- **Exact division of words.** -/
theorem wtdiv_word_of_dvd {W : ℕ} {a b : ℤ} (ha : Fits W a) (hb : Fits W b) (hb0 : b ≠ 0)
    (hdvd : b ∣ a) : wtdiv (word W a) (word W b) = word W (a / b) := by
  rw [wtdiv_word ha hb hb0, Int.tdiv_eq_ediv_of_dvd hdvd]

theorem wtdiv_mem_FP {X Y : List Bool → List Bool} (hX : X ∈ FP) (hY : Y ∈ FP) :
    (fun z => wtdiv (X z) (Y z)) ∈ FP := by
  have hflag : (fun z => [msb (X z) == msb (Y z)]) ∈ FP := by
    refine mem_FP_of_eq (Cobham.selectHeadFn_mem_FP (msb_mem_FP hX) (msb_mem_FP hY)
      (notBitFn_mem_FP (msb_mem_FP hY))) fun z => ?_
    rw [selectHead_single]
    cases msb (X z) <;> cases msb (Y z) <;> rfl
  have hq := udiv_mem_FP (wabs_mem_FP hX) (wabs_mem_FP hY)
  exact Cobham.selectHeadFn_mem_FP hflag hq (wneg_mem_FP hq)

variable {W : List Bool → ℕ} {v w : List Bool → ℤ}

theorem WordFn.tdiv (hv : WordFn W v) (hw : WordFn W w) (hvf : ∀ z, Fits (W z) (v z))
    (hwf : ∀ z, Fits (W z) (w z)) (hw0 : ∀ z, w z ≠ 0) : WordFn W fun z => (v z).tdiv (w z) :=
  mem_FP_of_eq (wtdiv_mem_FP hv hw) fun z => wtdiv_word (hvf z) (hwf z) (hw0 z)

theorem WordFn.div_of_dvd (hv : WordFn W v) (hw : WordFn W w) (hvf : ∀ z, Fits (W z) (v z))
    (hwf : ∀ z, Fits (W z) (w z)) (hw0 : ∀ z, w z ≠ 0) (hdvd : ∀ z, w z ∣ v z) :
    WordFn W fun z => v z / w z :=
  (hv.tdiv hw hvf hwf hw0).of_eq fun z => Int.tdiv_eq_ediv_of_dvd (hdvd z)

end LinearProgramming
