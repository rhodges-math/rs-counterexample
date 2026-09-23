import Schubert.RS.JosephPolo.Heisenberg
import Schubert.RS.Compositions
import Schubert.RS.Representation.UpperRadicalDecomposition

namespace Schubert.RS.Representation
noncomputable section
open FinPermutation
set_option maxHeartbeats 1200000

theorem rootOperator_commute {n : ℕ} (r s : PositiveRoot n)
    (h : r.val.2 ≠ s.val.1) (h' : s.val.2 ≠ r.val.1) :
    Commute (rootOperator r) (rootOperator s) := by
  exact sub_eq_zero.mp (rootOperator_commutator_zero r s h h')

theorem root_pair_heisenberg {n : ℕ} {X : Type*} [AddCommGroup X] [Module ℂ X]
    (ρ : Enveloping n →ₐ[ℂ] Module.End ℂ X)
    (r s : PositiveRoot n) (h : r.val.2=s.val.1) :
    ρ (rootOperator r) * ρ (rootOperator s) =
      ρ (rootOperator s) * ρ (rootOperator r) + ρ (rootOperator (joinedRoot r s h)) ∧
    Commute (ρ (rootOperator s)) (ρ (rootOperator (joinedRoot r s h))) ∧
    Commute (ρ (rootOperator r)) (ρ (rootOperator (joinedRoot r s h))) := by
  refine ⟨?_, ?_, ?_⟩
  · have hc := congrArg ρ (rootOperator_commutator_forward r s h)
    simp only [map_sub, map_mul] at hc
    exact (sub_eq_iff_eq_add.mp hc).trans (add_comm _ _)
  · apply Commute.map _ ρ
    apply rootOperator_commute
    · exact ne_of_gt (joinedRoot r s h).property
    · exact ne_of_gt s.property
  · apply Commute.map _ ρ
    apply rootOperator_commute
    · exact ne_of_gt r.property
    · exact ne_of_gt (joinedRoot r s h).property

/-- Both roots entering an adjacent pair exchange their bounds on the
highest string vector of the universal presentation. -/
theorem jp_incoming_string_bounds {n : ℕ} (u : Composition n) (i : AdjacentPosition n)
    (hu : u i.left ≤ u i.right) (a : Fin n) (ha : a < i.left) :
    let r : PositiveRoot n := ⟨(a,i.left),ha⟩
    let s : PositiveRoot n := ⟨(a,i.right),ha.trans i.left_lt_right⟩
    let η := rootOperator (adjacentPositiveRoot i) ^ (u i.right-u i.left) • presentationGenerator u
    rootOperator r ^ (u i.right-u a+1) • η=0 ∧
    rootOperator s ^ (u i.left-u a+1) • η=0 := by
  let r : PositiveRoot n := ⟨(a,i.left),ha⟩
  let e := adjacentPositiveRoot i
  let s := joinedRoot r e rfl
  let ρ : Enveloping n →ₐ[ℂ] Module.End ℂ (PresentationQuotient u) :=
    Algebra.lsmul ℂ ℂ (PresentationQuotient u)
  obtain ⟨hc,hAC,hBC⟩ := root_pair_heisenberg ρ r e rfl
  have hpq : u i.right-u a+1 = (u i.left-u a+1)+(u i.right-u i.left) ∨
      u i.left-u a+1=1 := by
    by_cases h : u a ≤ u i.left
    · left; omega
    · right; omega
  have h := heisenberg_top_two_bounds (ρ (rootOperator e)) (ρ (rootOperator r))
    (ρ (rootOperator s)) hc hAC hBC (u i.right-u i.left)
    (u i.left-u a+1) (u i.right-u a+1) hpq (presentationGenerator u)
    (by rw [← map_pow]; exact jp_relation_kills_generator u e)
    (by rw [← map_pow]; exact jp_relation_kills_generator u r)
    (by rw [← map_pow]; exact jp_relation_kills_generator u s)
  simp only [← map_pow] at h
  exact h

/-- The corresponding exchange for roots leaving the adjacent pair.
The minus sign comes from the orientation of the matrix-unit bracket. -/
theorem jp_outgoing_string_bounds {n : ℕ} (u : Composition n) (i : AdjacentPosition n)
    (hu : u i.left ≤ u i.right) (b : Fin n) (hb : i.right<b) :
    let r : PositiveRoot n := ⟨(i.right,b),hb⟩
    let s : PositiveRoot n := ⟨(i.left,b),i.left_lt_right.trans hb⟩
    let η := rootOperator (adjacentPositiveRoot i) ^ (u i.right-u i.left) • presentationGenerator u
    rootOperator r ^ (u b-u i.left+1) • η=0 ∧
    rootOperator s ^ (u b-u i.right+1) • η=0 := by
  let e := adjacentPositiveRoot i
  let r : PositiveRoot n := ⟨(i.right,b),hb⟩
  let s := joinedRoot e r rfl
  let ρ : Enveloping n →ₐ[ℂ] Module.End ℂ (PresentationQuotient u) :=
    Algebra.lsmul ℂ ℂ (PresentationQuotient u)
  obtain ⟨hc,hBC,hEC⟩ := root_pair_heisenberg ρ e r rfl
  have hc' : ρ (rootOperator r) * (-(ρ (rootOperator e))) =
      (-(ρ (rootOperator e))) * ρ (rootOperator r) + ρ (rootOperator s) :=
    central_commutator_neg_orientation _ _ _ hc
  have hpq : u b-u i.left+1 = (u b-u i.right+1)+(u i.right-u i.left) ∨
      u b-u i.right+1=1 := by
    by_cases h : u i.right ≤ u b
    · left; omega
    · right; omega
  have h := heisenberg_top_two_bounds (-(ρ (rootOperator e))) (ρ (rootOperator r))
    (ρ (rootOperator s)) hc' hEC.neg_left hBC (u i.right-u i.left)
    (u b-u i.right+1) (u b-u i.left+1) hpq (presentationGenerator u)
    (by rw [neg_end_pow_apply, ← map_pow];
        change (-1 : ℂ)^_ • (rootOperator e^_ • presentationGenerator u)=0
        have he : rootOperator e^(u i.right-u i.left+1) • presentationGenerator u=0 :=
          jp_relation_kills_generator u e
        rw [he, smul_zero])
    (by rw [← map_pow]; exact jp_relation_kills_generator u r)
    (by rw [← map_pow]; exact jp_relation_kills_generator u s)
  have hn : (-1 : ℂ)^(u i.right-u i.left) ≠ 0 := pow_ne_zero _ (by norm_num)
  simp only [neg_end_pow_apply, map_smul, smul_eq_zero, hn, false_or, ← map_pow] at h
  exact h

end
end Schubert.RS.Representation
