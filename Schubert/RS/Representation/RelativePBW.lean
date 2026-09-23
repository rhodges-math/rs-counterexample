import Schubert.RS.Representation.Torus
import Schubert.RS.Representation.Dominant

namespace Schubert.RS.Representation
noncomputable section

abbrev KillingRoot {n : ℕ} (u : Fin n → ℕ) :=
  {r : PositiveRoot n // u r.val.2 ≤ u r.val.1}

def isAscentRoot {n : ℕ} (u : Fin n → ℕ) (r : PositiveRoot n) : Bool :=
  decide (u r.val.1 < u r.val.2)

/-- The PBW order used by the paper: ascent roots first, killing roots last. -/
def adaptedRootOrdering {n : ℕ} (u : Fin n → ℕ) : RootOrdering n where
  roots := (defaultRootOrdering n).roots.filter (isAscentRoot u) ++
    (defaultRootOrdering n).roots.filter (fun r => !(isAscentRoot u r))
  nodup := (List.filter_append_perm _ _).nodup_iff.mpr (defaultRootOrdering n).nodup
  complete r := (List.filter_append_perm _ _).mem_iff.mpr ((defaultRootOrdering n).complete r)

/-- A complex span, with an arbitrary UEA coefficient to the LEFT of a killing root. -/
def trailingKillingSpan {n : ℕ} (u : Fin n → ℕ) : Submodule ℂ (Enveloping n) :=
  Submodule.span ℂ {z | ∃ a : Enveloping n, ∃ r : KillingRoot u,
    z = a * rootOperator r.val}

private theorem mul_mem_trailingKillingSpan {n : ℕ} (u : Fin n → ℕ)
    (a : Enveloping n) {b : Enveloping n} (hb : b ∈ trailingKillingSpan u) :
    a * b ∈ trailingKillingSpan u := by
  induction hb using Submodule.span_induction with
  | mem b hb =>
    obtain ⟨c, r, rfl⟩ := hb
    exact Submodule.subset_span ⟨a * c, r, (mul_assoc a c _).symm⟩
  | zero => simp
  | add b c hb hc ib ic => simpa only [mul_add] using (trailingKillingSpan u).add_mem ib ic
  | smul c b hb ib =>
    rw [mul_smul_comm]
    exact (trailingKillingSpan u).smul_mem c ib

/-- Left-ideal generation and complex spanning by left multiples agree.
No right-ideal closure is used. -/
theorem linearLeftIdeal_eq_trailingSpan {n : ℕ} (u : Fin n → ℕ) :
    (linearLeftIdeal u).restrictScalars ℂ = trailingKillingSpan u := by
  apply le_antisymm
  · intro a ha
    change a ∈ linearLeftIdeal u at ha
    induction ha using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨r, hr, rfl⟩ := ha
      exact Submodule.subset_span ⟨1, ⟨r, hr⟩, (one_mul _).symm⟩
    | zero => exact (trailingKillingSpan u).zero_mem
    | add a b ha hb ia ib => exact (trailingKillingSpan u).add_mem ia ib
    | smul a b hb ib => exact mul_mem_trailingKillingSpan u a ib
  · apply Submodule.span_le.mpr
    rintro z ⟨a, r, rfl⟩
    exact (linearLeftIdeal u).smul_mem a (Submodule.subset_span ⟨r.val, r.property, rfl⟩)

/-- Expand only the arbitrary left coefficient in PBW; a trailing killing
root is retained explicitly and is NOT silently sorted. -/
def pbwTrailingKillingSpan {n : ℕ} (u : Fin n → ℕ) (order : RootOrdering n) :
    Submodule ℂ (Enveloping n) :=
  Submodule.span ℂ {z | ∃ powers : PositiveRoot n → ℕ, ∃ r : KillingRoot u,
    z = orderedRootMonomial order powers * rootOperator r.val}

theorem trailingSpan_eq_pbwTrailing {n : ℕ} (u : Fin n → ℕ)
    (order : RootOrdering n) (hpbw : HasOrderedPBWBasis n) :
    trailingKillingSpan u = pbwTrailingKillingSpan u order := by
  obtain ⟨b, hb⟩ := hpbw order
  have hm (a : Enveloping n) (r : KillingRoot u) :
      a * rootOperator r.val ∈ pbwTrailingKillingSpan u order := by
    have ha : a ∈ Submodule.span ℂ (Set.range b) := by rw [b.span_eq]; trivial
    induction ha using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨powers, rfl⟩ := ha
      rw [hb]
      exact Submodule.subset_span ⟨powers, r, rfl⟩
    | zero => simp
    | add a c ha hc ia ic =>
      simpa only [add_mul] using (pbwTrailingKillingSpan u order).add_mem ia ic
    | smul c a ha ia =>
      rw [smul_mul_assoc]
      exact (pbwTrailingKillingSpan u order).smul_mem c ia
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro z ⟨a, r, rfl⟩
    exact hm a r
  · apply Submodule.span_le.mpr
    rintro z ⟨powers, r, rfl⟩
    exact Submodule.subset_span ⟨orderedRootMonomial order powers, r, rfl⟩

theorem linearLeftIdeal_eq_pbwTrailing {n : ℕ} (u : Fin n → ℕ)
    (order : RootOrdering n) (hpbw : HasOrderedPBWBasis n) :
    (linearLeftIdeal u).restrictScalars ℂ = pbwTrailingKillingSpan u order := by
  rw [linearLeftIdeal_eq_trailingSpan, trailingSpan_eq_pbwTrailing u order hpbw]

end
end Schubert.RS.Representation
