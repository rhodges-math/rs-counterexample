import Schubert.RS.Representation.KillingStraightening

namespace Schubert.RS.Representation
noncomputable section

def ascentRootList {n : ℕ} (u : Fin n → ℕ) : List (PositiveRoot n) :=
  (defaultRootOrdering n).roots.filter (isAscentRoot u)
def killingRootList {n : ℕ} (u : Fin n → ℕ) : List (PositiveRoot n) :=
  (defaultRootOrdering n).roots.filter (fun r => !(isAscentRoot u r))

theorem mem_ascentRootList {n : ℕ} (u : Fin n → ℕ) (r : PositiveRoot n) :
    r ∈ ascentRootList u ↔ u r.val.1 < u r.val.2 := by
  simp [ascentRootList, isAscentRoot, (defaultRootOrdering n).complete r]

theorem mem_killingRootList {n : ℕ} (u : Fin n → ℕ) (r : PositiveRoot n) :
    r ∈ killingRootList u ↔ u r.val.2 ≤ u r.val.1 := by
  simp [killingRootList, isAscentRoot, (defaultRootOrdering n).complete r, Nat.not_lt]

def blockProduct {n : ℕ} (roots : List (PositiveRoot n)) (powers : PositiveRoot n → ℕ) :
    Enveloping n := (roots.map fun r => rootOperator r ^ powers r).prod

theorem adapted_monomial_split {n : ℕ} (u : Fin n → ℕ) (powers : PositiveRoot n → ℕ) :
    orderedRootMonomial (adaptedRootOrdering u) powers =
      blockProduct (ascentRootList u) powers * blockProduct (killingRootList u) powers := by
  simp [orderedRootMonomial_eq, adaptedRootOrdering, blockProduct, ascentRootList, killingRootList]

def expandedWord {n : ℕ} (roots : List (PositiveRoot n)) (powers : PositiveRoot n → ℕ) :
    List (PositiveRoot n) := roots.flatMap fun r => List.replicate (powers r) r

theorem rootWord_expanded {n : ℕ} (roots : List (PositiveRoot n)) (powers : PositiveRoot n → ℕ) :
    rootWord (expandedWord roots powers) = blockProduct roots powers := by
  unfold expandedWord rootWord blockProduct
  induction roots with
  | nil => simp
  | cons r roots ih => simp [ih]

theorem expanded_killing {n : ℕ} (u : Fin n → ℕ) (powers : PositiveRoot n → ℕ) :
    IsKillingWord u (expandedWord (killingRootList u) powers) := by
  intro r hr
  obtain ⟨s, hs, hr⟩ := List.mem_flatMap.mp hr
  have he : r = s := List.eq_of_mem_replicate hr
  subst r
  exact (mem_killingRootList u s).mp hs

private theorem blockProduct_congr {n : ℕ} (roots : List (PositiveRoot n))
    (a b : PositiveRoot n → ℕ) (h : ∀ r ∈ roots, a r = b r) :
    blockProduct roots a = blockProduct roots b := by
  unfold blockProduct
  congr 1
  apply List.map_congr_left
  intro r hr
  rw [h r hr]

def mergePowers {n : ℕ} (u : Fin n → ℕ) (a b : PositiveRoot n → ℕ) (r : PositiveRoot n) : ℕ :=
  if u r.val.1 < u r.val.2 then a r else b r

theorem ascentBlock_killingPowers {n : ℕ} (u : Fin n → ℕ)
    (b : PositiveRoot n → ℕ) (hb : KillingPowers u b) :
    blockProduct (ascentRootList u) b = 1 := by
  unfold blockProduct
  apply List.prod_eq_one
  intro z hz
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hz
  have hasc := (mem_ascentRootList u r).mp hr
  have he : b r = 0 := by
    by_contra h
    exact (Nat.not_lt.mpr (hb r (Nat.pos_of_ne_zero h))) hasc
  simp [he]

theorem ascentBlock_mul_killingMonomial {n : ℕ} (u : Fin n → ℕ)
    (a b : PositiveRoot n → ℕ) (hb : KillingPowers u b) :
    blockProduct (ascentRootList u) a * orderedRootMonomial (adaptedRootOrdering u) b =
      orderedRootMonomial (adaptedRootOrdering u) (mergePowers u a b) := by
  rw [adapted_monomial_split, ascentBlock_killingPowers u b hb, one_mul, adapted_monomial_split]
  congr 1
  · apply blockProduct_congr
    intro r hr
    simp [mergePowers, (mem_ascentRootList u r).mp hr]
  · apply blockProduct_congr
    intro r hr
    simp [mergePowers, Nat.not_lt.mpr ((mem_killingRootList u r).mp hr)]

abbrev HasKillingPower {n : ℕ} (u : Fin n → ℕ) (powers : PositiveRoot n → ℕ) : Prop :=
  ∃ r, u r.val.2 ≤ u r.val.1 ∧ 0 < powers r

/-- Exactly the PBW basis vectors that should be removed in the linear quotient. -/
def blockedPBWSpan {n : ℕ} (u : Fin n → ℕ) : Submodule ℂ (Enveloping n) :=
  Submodule.span ℂ {z | ∃ powers : PositiveRoot n → ℕ,
    HasKillingPower u powers ∧ z = orderedRootMonomial (adaptedRootOrdering u) powers}

private theorem ascentBlock_mul_mem_blocked {n : ℕ} (u : Fin n → ℕ)
    (a : PositiveRoot n → ℕ) {z : Enveloping n} (hz : z ∈ orderedKillingSpan u (adaptedRootOrdering u)) :
    blockProduct (ascentRootList u) a * z ∈ blockedPBWSpan u := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨b, hb, ⟨r, hr⟩, rfl⟩ := hz
    rw [ascentBlock_mul_killingMonomial u a b hb]
    apply Submodule.subset_span
    refine ⟨mergePowers u a b, ⟨r, hb r hr, ?_⟩, rfl⟩
    simpa [mergePowers, Nat.not_lt.mpr (hb r hr)] using hr
  | zero => simp
  | add x y hx hy ix iy => simpa only [mul_add] using (blockedPBWSpan u).add_mem ix iy
  | smul c x hx ix =>
    rw [mul_smul_comm]
    exact (blockedPBWSpan u).smul_mem c ix

/-- The difficult direction: a PBW monomial followed by a killing root
straightens into PBW monomials with nonempty killing block. -/
theorem pbwTrailing_le_blocked {n : ℕ} (u : Fin n → ℕ) :
    pbwTrailingKillingSpan u (adaptedRootOrdering u) ≤ blockedPBWSpan u := by
  apply Submodule.span_le.mpr
  rintro z ⟨powers, r, rfl⟩
  rw [adapted_monomial_split, mul_assoc]
  apply ascentBlock_mul_mem_blocked u powers
  have hs := killingOperator_mul_word_straightens u (adaptedRootOrdering u) r.val r.property
    (expandedWord (killingRootList u) powers) (expanded_killing u powers)
  simpa only [rootWord_expanded] using hs

private theorem killingWord_mem_linear {n : ℕ} (u : Fin n → ℕ)
    (roots : List (PositiveRoot n)) (hk : IsKillingWord u roots) (hn : 0 < roots.length) :
    rootWord roots ∈ linearLeftIdeal u := by
  induction roots using List.reverseRecOn with
  | nil => simp at hn
  | append_singleton roots r ih =>
    have hr := hk r (by simp)
    have hm : rootOperator r ∈ linearLeftIdeal u := Submodule.subset_span ⟨r, hr, rfl⟩
    simpa [rootWord] using (linearLeftIdeal u).smul_mem (rootWord roots) hm

theorem blocked_le_linear {n : ℕ} (u : Fin n → ℕ) :
    blockedPBWSpan u ≤ (linearLeftIdeal u).restrictScalars ℂ := by
  apply Submodule.span_le.mpr
  rintro z ⟨powers, ⟨r, hr, hp⟩, rfl⟩
  rw [adapted_monomial_split]
  have hmem : r ∈ expandedWord (killingRootList u) powers := by
    apply List.mem_flatMap.mpr
    exact ⟨r, (mem_killingRootList u r).mpr hr, List.mem_replicate.mpr ⟨by omega, rfl⟩⟩
  have hn : 0 < (expandedWord (killingRootList u) powers).length := List.length_pos_of_mem hmem
  have hh := killingWord_mem_linear u _ (expanded_killing u powers) hn
  rw [rootWord_expanded] at hh
  exact (linearLeftIdeal u).smul_mem _ hh

/-- Relative PBW ideal equality from the commutator relations and the
ordered PBW basis hypothesis, without a quotient-basis hypothesis. -/
theorem linearLeftIdeal_eq_blocked {n : ℕ} (u : Fin n → ℕ) (hpbw : HasOrderedPBWBasis n) :
    (linearLeftIdeal u).restrictScalars ℂ = blockedPBWSpan u := by
  apply le_antisymm
  · rw [linearLeftIdeal_eq_pbwTrailing u (adaptedRootOrdering u) hpbw]
    exact pbwTrailing_le_blocked u
  · exact blocked_le_linear u

end
end Schubert.RS.Representation
