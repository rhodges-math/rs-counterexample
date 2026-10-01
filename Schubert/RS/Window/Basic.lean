import Schubert.RS.Compositions
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Ring.Int

/-!
# The hypotheses of the rational extraction formula

Definitions for Proposition 2.13 (`prop:window`) of the paper. For weak compositions `a b c` of
length `n` and an integer `N ≥ max c`:

* the complement `c̄ = N·1 − c`;
* the residual weight `c − a − b` (2.8) and its prefix heights `h_k` (2.9);
* the comparison weight `cmp` (2.10) of two triples;
* the window inequalities (2.12).

The rational extraction formula (2.14) itself is `Schubert.RS.Window.window_rational_extraction`
in `Schubert.RS.Window.General`.

## Main definitions

* `Schubert.RS.Window.complement`, `residual`, `prefixHeight`, `cmp`, `triple`.
* `Schubert.RS.Window.WindowInequality`: the window inequality (2.12) for one composition.
* `Schubert.RS.Window.Hypotheses`: all hypotheses of Proposition 2.13.

## Main results

* `Schubert.RS.Window.cmp_complement_eq` and `Schubert.RS.Window.hypotheses_iff_of_le`: the
  comparison weights and the hypotheses do not depend on the choice of `N ≥ max c` (the remark
  after (2.12)).

## Conventions

Positions are `0`-based. The paper's `h_k = ∑_{i ≤ k} (c_i − a_i − b_i)` (1-based) is
`prefixHeight a b c k`, the sum over the `0`-based positions `i < k`. A cut between the `0`-based
positions `k` and `k + 1` therefore has height `prefixHeight a b c (k + 1)`.
-/

namespace Schubert.RS.Window

variable {n : ℕ}

/-- The complement `c̄ = N·1 − c` of a weak composition. -/
def complement (N : ℕ) (c : Composition n) : Composition n := fun i => N - c i

/-- The residual weight `c − a − b`, (2.8) of the paper. -/
def residual (a b c : Composition n) : Fin n → ℤ := fun i => (c i : ℤ) - a i - b i

/-- The prefix heights (2.9): `prefixHeight a b c k = ∑_{i < k} (c_i − a_i − b_i)`, the paper's
`h_k`. -/
def prefixHeight (a b c : Composition n) (k : ℕ) : ℤ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k), residual a b c i

/-- The comparison weight (2.10): `cmp(P, Q) = #{ℓ ∈ {1,2,3} : P_ℓ < Q_ℓ} − 1`. -/
def cmp (P Q : ℕ × ℕ × ℕ) : ℤ :=
  (if P.1 < Q.1 then 1 else 0) + (if P.2.1 < Q.2.1 then 1 else 0) +
    (if P.2.2 < Q.2.2 then 1 else 0) - 1

/-- The triple `(a_i, b_i, g_i)` at position `i`. -/
def triple (a b g : Composition n) (i : Fin n) : ℕ × ℕ × ℕ := (a i, b i, g i)

/-- The window inequality (2.12) for one composition `u` and prefix heights `h`:
`u_j − u_i + 1 > min_{i ≤ k < j} h_k` whenever `i < j` and `u_i < u_j`. The minimum is below the
bound exactly when one of the cut heights is, so the condition is written with an existential over
the `0`-based cut index `k`, whose height is `h (k + 1)`. -/
def WindowInequality (u : Composition n) (h : ℕ → ℤ) : Prop :=
  ∀ i j : Fin n, i < j → u i < u j →
    ∃ k : ℕ, i.val ≤ k ∧ k < j.val ∧ h (k + 1) < (u j : ℤ) - u i + 1

/-- The hypotheses of Proposition 2.13 (`prop:window`): the degree equality `|a| + |b| = |c|`, the
bound `N ≥ max c`, nonnegative prefix heights, and the window inequalities (2.12) for `a`, `b` and
`c̄ = N·1 − c`. -/
structure Hypotheses (a b c : Composition n) (N : ℕ) : Prop where
  balance : ∑ i, a i + ∑ i, b i = ∑ i, c i
  le_N : ∀ i, c i ≤ N
  height_nonneg : ∀ k, 0 ≤ prefixHeight a b c k
  window_a : WindowInequality a (prefixHeight a b c)
  window_b : WindowInequality b (prefixHeight a b c)
  window_c : WindowInequality (complement N c) (prefixHeight a b c)

/-! ## Independence of `N` -/

section Independence

variable {c : Composition n} {N N' : ℕ}

theorem complement_cast (hN : ∀ i, c i ≤ N) (i : Fin n) :
    (complement N c i : ℤ) = N - c i := by
  simp only [complement]
  have := hN i
  omega

theorem complement_lt_complement_iff (hN : ∀ i, c i ≤ N) (i j : Fin n) :
    complement N c i < complement N c j ↔ c j < c i := by
  have hi := hN i
  have hj := hN j
  simp only [complement]
  omega

/-- The comparison weights of the triples `(a_i, b_i, c̄_i)` do not depend on `N ≥ max c`. -/
theorem cmp_complement_eq (a b : Composition n) (hN : ∀ i, c i ≤ N) (hN' : ∀ i, c i ≤ N')
    (i j : Fin n) :
    cmp (triple a b (complement N c) i) (triple a b (complement N c) j) =
      cmp (triple a b (complement N' c) i) (triple a b (complement N' c) j) := by
  simp only [cmp, triple, complement_lt_complement_iff hN, complement_lt_complement_iff hN']
  split_ifs <;> rfl

theorem windowInequality_complement_iff (hN : ∀ i, c i ≤ N) (hN' : ∀ i, c i ≤ N')
    (h : ℕ → ℤ) :
    WindowInequality (complement N c) h ↔ WindowInequality (complement N' c) h := by
  have key : ∀ i j : Fin n,
      ((complement N c j : ℤ) - complement N c i) =
        (complement N' c j : ℤ) - complement N' c i := by
    intro i j
    rw [complement_cast hN, complement_cast hN, complement_cast hN', complement_cast hN']
    ring
  unfold WindowInequality
  simp only [complement_lt_complement_iff hN, complement_lt_complement_iff hN']
  constructor
  · intro hw i j hij hlt
    obtain ⟨k, hk1, hk2, hk3⟩ := hw i j hij hlt
    exact ⟨k, hk1, hk2, by linarith [key i j]⟩
  · intro hw i j hij hlt
    obtain ⟨k, hk1, hk2, hk3⟩ := hw i j hij hlt
    exact ⟨k, hk1, hk2, by linarith [key i j]⟩

/-- The hypotheses of Proposition 2.13 do not depend on the choice of `N ≥ max c` (the remark
after (2.12)). -/
theorem hypotheses_iff_of_le {a b : Composition n} (hN : ∀ i, c i ≤ N) (hN' : ∀ i, c i ≤ N') :
    Hypotheses a b c N ↔ Hypotheses a b c N' := by
  constructor
  · intro h
    exact ⟨h.balance, hN', h.height_nonneg, h.window_a, h.window_b,
      (windowInequality_complement_iff hN hN' _).1 h.window_c⟩
  · intro h
    exact ⟨h.balance, hN, h.height_nonneg, h.window_a, h.window_b,
      (windowInequality_complement_iff hN hN' _).2 h.window_c⟩

end Independence

end Schubert.RS.Window
