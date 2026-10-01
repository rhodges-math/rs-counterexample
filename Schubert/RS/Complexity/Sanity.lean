import Complexitylib.Classes.Hierarchy
import Complexitylib.Models.TuringMachine.Internal
import Complexitylib.Models.TuringMachine.Combinators.Internal.Generic

/-!
# Sanity checks: the complexity classes are non-trivial

The complexity statements of Theorem 1.4 use complexitylib's polynomial-time classes
`Complexity.FP` (functions) and `Complexity.P` (languages). These are sanity checks that the
classes are non-trivial: neither contains everything, and time is genuinely counted.

* **Cardinality.** `Complexity.FP` and `Complexity.P` are countable (`FP_countable`,
  `P_countable`). A Turing machine has a finite type of states; relabelling the states by `Fin m`
  (`relabel`) does not change what the machine computes, and a machine with states `Fin m` and
  `k` work tapes is determined by finite data (`MachineCode`). A machine computes at most one
  function and decides at most one language (`computesInTime_unique`, `decidesInTime_unique`).
  Hence some function on bitstrings is not in `Complexity.FP` (`exists_not_mem_FP`), and some
  language is not in `Complexity.P` (`exists_not_mem_P`).
* **The time hierarchy.** By complexitylib's deterministic time hierarchy theorem
  (`Complexity.DTIME_pow_ssubset`), for every `a ≥ 1` some language in `Complexity.P` is not
  decidable in time `O(n^a)` (`exists_mem_P_not_mem_DTIME`). So the step count of the machine
  model is not too generous: `Complexity.P` is not contained in any fixed polynomial time class.
-/

namespace Schubert.RS.Algorithms

open Complexity

noncomputable section

/-! ### Machines with states `Fin m` -/

/-- The data of a machine with `k` work tapes and states `Fin m`: start state, halt state and
transition function. -/
abbrev MachineCode (k m : ℕ) : Type :=
  Fin m × Fin m × (Fin m → Γ → (Fin k → Γ) → Γ →
    Fin m × (Fin k → Γw) × Γw × Dir3 × (Fin k → Dir3) × Dir3)

/-- The left-end condition of `Complexity.TM` for a machine code. -/
def CodeRight {k m : ℕ} (c : MachineCode k m) : Prop :=
  ∀ (q : Fin m) (iHead : Γ) (wHeads : Fin k → Γ) (oHead : Γ),
    let (_, _, _, inDir, workDirs, outDir) := c.2.2 q iHead wHeads oHead
    (iHead = Γ.start → inDir = Dir3.right) ∧
    (∀ i, wHeads i = Γ.start → workDirs i = Dir3.right) ∧
    (oHead = Γ.start → outDir = Dir3.right)

/-- The machine with a given code. -/
def ofCode {k m : ℕ} (c : MachineCode k m) (hc : CodeRight c) : TM k where
  Q := Fin m
  qstart := c.1
  qhalt := c.2.1
  δ := c.2.2
  δ_right_of_start := hc

/-- The code of a machine after relabelling its states along `e`. -/
def codeOf {k m : ℕ} (tm : TM k) (e : tm.Q ≃ Fin m) : MachineCode k m :=
  (e tm.qstart, e tm.qhalt, fun q i w o => Prod.map e id (tm.δ (e.symm q) i w o))

theorem codeRight_codeOf {k m : ℕ} (tm : TM k) (e : tm.Q ≃ Fin m) :
    CodeRight (codeOf tm e) := by
  intro q i w o
  have h := tm.δ_right_of_start (e.symm q) i w o
  simp only [codeOf]
  rcases hδ : tm.δ (e.symm q) i w o with ⟨q', ww, ow, d1, d2, d3⟩
  rw [hδ] at h
  exact h

/-- The machine `tm` with its states relabelled along `e : tm.Q ≃ Fin m`. -/
def relabel {k m : ℕ} (tm : TM k) (e : tm.Q ≃ Fin m) : TM k :=
  ofCode (codeOf tm e) (codeRight_codeOf tm e)

/-- A configuration of `tm`, with its state relabelled along `e`. -/
def relabelCfg {k m : ℕ} (tm : TM k) (e : tm.Q ≃ Fin m) (c : Cfg k tm.Q) :
    Cfg k (relabel tm e).Q :=
  { state := e c.state, input := c.input, work := c.work, output := c.output }

theorem relabel_step {k m : ℕ} (tm : TM k) (e : tm.Q ≃ Fin m) (c c' : Cfg k tm.Q)
    (h : tm.step c = some c') :
    (relabel tm e).step (relabelCfg tm e c) = some (relabelCfg tm e c') := by
  have hc : c.state ≠ tm.qhalt := TM.state_ne_qhalt_of_step h
  rcases hδ : tm.δ c.state c.input.read (fun i => (c.work i).read) c.output.read with
    ⟨q', ww, ow, d1, d2, d3⟩
  simp only [TM.step, hc, hδ, ite_false, Option.some.injEq] at h
  subst h
  have hne : ¬ e c.state = e tm.qhalt := fun h' => hc (e.injective h')
  simp only [TM.step, relabel, ofCode, codeOf, relabelCfg, hne, ite_false, Equiv.symm_apply_apply,
    hδ, Prod.map, id]

theorem relabel_reachesIn {k m : ℕ} (tm : TM k) (e : tm.Q ≃ Fin m) {t : ℕ}
    {c c' : Cfg k tm.Q} (h : tm.reachesIn t c c') :
    (relabel tm e).reachesIn t (relabelCfg tm e c) (relabelCfg tm e c') :=
  TM.reachesIn_map (relabelCfg tm e) (relabel_step tm e) h

theorem relabelCfg_initCfg {k m : ℕ} (tm : TM k) (e : tm.Q ≃ Fin m) (x : List Bool) :
    relabelCfg tm e (tm.initCfg x) = (relabel tm e).initCfg x := rfl

/-- Relabelling the states does not change the computed function. -/
theorem relabel_computesInTime {k m : ℕ} {tm : TM k} (e : tm.Q ≃ Fin m)
    {f : List Bool → List Bool} {T : ℕ → ℕ} (h : tm.ComputesInTime f T) :
    (relabel tm e).ComputesInTime f T := by
  intro x
  obtain ⟨c', t, ht, hr, hh, ho⟩ := h x
  refine ⟨relabelCfg tm e c', t, ht, ?_, ?_, ho⟩
  · rw [← relabelCfg_initCfg]
    exact relabel_reachesIn tm e hr
  · change e c'.state = e tm.qhalt
    rw [hh]

/-- Relabelling the states does not change the decided language. -/
theorem relabel_decidesInTime {k m : ℕ} {tm : TM k} (e : tm.Q ≃ Fin m) {L : Language}
    {T : ℕ → ℕ} (h : tm.DecidesInTime L T) : (relabel tm e).DecidesInTime L T := by
  intro x
  obtain ⟨c', t, ht, hr, hh, h1, h2⟩ := h x
  refine ⟨relabelCfg tm e c', t, ht, ?_, ?_, h1, h2⟩
  · rw [← relabelCfg_initCfg]
    exact relabel_reachesIn tm e hr
  · change e c'.state = e tm.qhalt
    rw [hh]

/-! ### Determinism -/

theorem hasOutput_unique {t : Tape} {y y' : List Bool} (h : t.HasOutput y)
    (h' : t.HasOutput y') : y = y' := by
  have hlen : y.length = y'.length := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have e1 := h'.1 y.length hlt
      rw [h.2] at e1
      exact Γ.ofBool_ne_blank _ e1.symm
    · have e1 := h.1 y'.length hlt
      rw [h'.2] at e1
      exact Γ.ofBool_ne_blank _ e1.symm
  refine List.ext_getElem hlen fun i hi hi' => ?_
  have e1 := h.1 i hi
  have e2 := h'.1 i hi'
  rw [e1] at e2
  revert e2
  cases y[i] <;> cases y'[i] <;> simp [Γ.ofBool]

/-- The halting configuration of a deterministic run is unique. -/
theorem halted_unique {k : ℕ} {tm : TM k} {c c₁ c₂ : Cfg k tm.Q} {t₁ t₂ : ℕ}
    (h₁ : tm.reachesIn t₁ c c₁) (hh₁ : tm.halted c₁) (h₂ : tm.reachesIn t₂ c c₂)
    (hh₂ : tm.halted c₂) : c₁ = c₂ := by
  have ht : t₁ = t₂ :=
    le_antisymm (TM.reachesIn_le_halt tm h₁ h₂ hh₂) (TM.reachesIn_le_halt tm h₂ h₁ hh₁)
  subst ht
  exact TM.reachesIn_right_unique h₁ h₂

/-- A machine computes at most one function. -/
theorem computesInTime_unique {k : ℕ} {tm : TM k} {f g : List Bool → List Bool}
    {T T' : ℕ → ℕ} (hf : tm.ComputesInTime f T) (hg : tm.ComputesInTime g T') : f = g := by
  funext x
  obtain ⟨c₁, t₁, -, h₁, hh₁, ho₁⟩ := hf x
  obtain ⟨c₂, t₂, -, h₂, hh₂, ho₂⟩ := hg x
  obtain rfl := halted_unique h₁ hh₁ h₂ hh₂
  exact hasOutput_unique ho₁ ho₂

/-- A machine decides at most one language. -/
theorem decidesInTime_unique {k : ℕ} {tm : TM k} {L L' : Language} {T T' : ℕ → ℕ}
    (hL : tm.DecidesInTime L T) (hL' : tm.DecidesInTime L' T') : L = L' := by
  ext x
  obtain ⟨c₁, t₁, -, h₁, hh₁, hin₁, hout₁⟩ := hL x
  obtain ⟨c₂, t₂, -, h₂, hh₂, hin₂, hout₂⟩ := hL' x
  obtain rfl := halted_unique h₁ hh₁ h₂ hh₂
  constructor
  · intro hx
    by_contra hx'
    have e1 := hin₁ hx
    rw [hout₂ hx'] at e1
    exact absurd e1 (by decide)
  · intro hx
    by_contra hx'
    have e1 := hin₂ hx
    rw [hout₁ hx'] at e1
    exact absurd e1 (by decide)

/-! ### Countability -/

/-- **`Complexity.FP` is countable.** -/
theorem FP_countable : Complexity.FP.Countable := by
  have key : Complexity.FP ⊆ ⋃ (k : ℕ) (m : ℕ) (c : MachineCode k m),
      {f | ∃ (hc : CodeRight c) (T : ℕ → ℕ), (ofCode c hc).ComputesInTime f T} := by
    intro f hf
    obtain ⟨-, k, tm, T, hT, -⟩ := hf
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    exact ⟨k, Fintype.card tm.Q, codeOf tm (Fintype.equivFin tm.Q),
      codeRight_codeOf tm _, T, relabel_computesInTime _ hT⟩
  refine Set.Countable.mono key (Set.countable_iUnion fun k => Set.countable_iUnion fun m =>
    Set.countable_iUnion fun c => Set.Subsingleton.countable ?_)
  rintro f ⟨hc, T, hf⟩ g ⟨_hc, T', hg⟩
  exact computesInTime_unique hf hg

/-- **`Complexity.P` is countable.** -/
theorem P_countable : Complexity.P.Countable := by
  have key : Complexity.P ⊆ ⋃ (k : ℕ) (m : ℕ) (c : MachineCode k m),
      {L | ∃ (hc : CodeRight c) (T : ℕ → ℕ), (ofCode c hc).DecidesInTime L T} := by
    intro L hL
    rw [Complexity.P, Set.mem_iUnion] at hL
    obtain ⟨-, k, tm, T, hT, -⟩ := hL
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    exact ⟨k, Fintype.card tm.Q, codeOf tm (Fintype.equivFin tm.Q),
      codeRight_codeOf tm _, T, relabel_decidesInTime _ hT⟩
  refine Set.Countable.mono key (Set.countable_iUnion fun k => Set.countable_iUnion fun m =>
    Set.countable_iUnion fun c => Set.Subsingleton.countable ?_)
  rintro L ⟨hc, T, hL⟩ L' ⟨_hc, T', hL'⟩
  exact decidesInTime_unique hL hL'

theorem not_countable_nat_bool : ¬ Countable (ℕ → Bool) := by
  intro h
  obtain ⟨s, hs⟩ := exists_surjective_nat (ℕ → Bool)
  obtain ⟨n, hn⟩ := hs fun n => !(s n n)
  have h' := congrFun hn n
  cases hsn : s n n <;> simp [hsn] at h'

/-- **Not every function on bitstrings is polynomial-time computable.** -/
theorem exists_not_mem_FP : ∃ f : List Bool → List Bool, f ∉ Complexity.FP := by
  by_contra h
  simp only [not_exists, not_not] at h
  have huniv : (Set.univ : Set (List Bool → List Bool)).Countable :=
    FP_countable.mono fun f _ => h f
  rw [Set.countable_univ_iff] at huniv
  have hinj : Function.Injective fun (g : ℕ → Bool) (l : List Bool) => [g l.length] := by
    intro g g' hg
    funext n
    have := congrFun hg (List.replicate n false)
    simpa using this
  exact not_countable_nat_bool hinj.countable

/-- **Not every language is decidable in polynomial time.** -/
theorem exists_not_mem_P : ∃ L : Language, L ∉ Complexity.P := by
  by_contra h
  simp only [not_exists, not_not] at h
  have huniv : (Set.univ : Set Language).Countable := P_countable.mono fun L _ => h L
  rw [Set.countable_univ_iff] at huniv
  have hinj : Function.Injective fun (g : ℕ → Bool) => {l : List Bool | g l.length = true} := by
    intro g g' hg
    funext n
    have := congrArg (List.replicate n false ∈ ·) hg
    simp only [Set.mem_ofPred_eq, List.length_replicate, eq_iff_iff] at this
    cases hgn : g n <;> cases hgn' : g' n <;> simp_all
  exact not_countable_nat_bool hinj.countable

/-! ### The time hierarchy -/

theorem bigO_succ_pow (b : ℕ) : (fun n : ℕ => (n + 1) ^ b) =O (fun n => n ^ b) := by
  show (fun n : ℕ => (((n + 1) ^ b : ℕ) : ℝ)) =O[Filter.atTop] (fun n : ℕ => ((n ^ b : ℕ) : ℝ))
  apply Asymptotics.IsBigO.of_bound ((2 : ℝ) ^ b)
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have h : (n + 1) ^ b ≤ 2 ^ b * n ^ b :=
    calc (n + 1) ^ b ≤ (2 * n) ^ b := Nat.pow_le_pow_left (by omega) b
      _ = 2 ^ b * n ^ b := mul_pow 2 n b
  simp only [Real.norm_natCast]
  exact_mod_cast h

theorem DTIME_succ_pow_subset_P (b : ℕ) : DTIME (fun n => (n + 1) ^ b) ⊆ Complexity.P :=
  fun _ hL => Set.mem_iUnion.mpr ⟨b, DTIME_mono (bigO_succ_pow b) hL⟩

/-- **The time hierarchy inside `P`.** For every `a ≥ 1`, some language decidable in polynomial
time is not decidable in time `O(n^a)`. -/
theorem exists_mem_P_not_mem_DTIME (a : ℕ) (ha : 1 ≤ a) :
    ∃ L ∈ Complexity.P, L ∉ DTIME (· ^ a) := by
  obtain ⟨L, hL, hLn⟩ := Set.exists_of_ssubset (DTIME_pow_ssubset a ha)
  refine ⟨L, DTIME_succ_pow_subset_P _ hL, fun h => hLn ?_⟩
  exact DTIME_mono (BigO.of_le fun n => Nat.pow_le_pow_left (Nat.le_succ n) a) h

end

end Schubert.RS.Algorithms
