import Schubert.RS.JosephPolo.RootPairRelations
import Schubert.RS.JosephPolo.HeisenbergMixed

namespace Schubert.RS.Representation
noncomputable section
open FinPermutation
set_option maxHeartbeats 1200000

/-- The nontrivial relation obtained by lowering an incoming long-root
power. It holds in the universal quotient before any flag comparison. -/
theorem jp_incoming_lowering_relation {n : ℕ} (u : Composition n) (i : AdjacentPosition n)
    (hu : u i.left ≤ u i.right) (a : Fin n) (ha : a < i.left) :
    let r : PositiveRoot n := ⟨(a,i.left),ha⟩
    let s : PositiveRoot n := ⟨(a,i.right),ha.trans i.left_lt_right⟩
    rootOperator s ^ (u i.right-u a) • (rootOperator r • presentationGenerator u)=0 := by
  let r : PositiveRoot n := ⟨(a,i.left),ha⟩
  let e := adjacentPositiveRoot i
  let s := joinedRoot r e rfl
  change rootOperator s ^ (u i.right-u a) • (rootOperator r • presentationGenerator u)=0
  by_cases h : u a ≤ u i.left
  · let ρ : Enveloping n →ₐ[ℂ] Module.End ℂ (PresentationQuotient u) :=
      Algebra.lsmul ℂ ℂ (PresentationQuotient u)
    obtain ⟨hc,hAC,hBC⟩ := root_pair_heisenberg ρ r e rfl
    have hz := heisenberg_central_boundary_kills (ρ (rootOperator e)) (ρ (rootOperator r))
      (ρ (rootOperator s)) hc hAC hBC (u i.right-u i.left) (u i.left-u a)
      (presentationGenerator u)
      (by rw [← map_pow]; exact jp_relation_kills_generator u e)
      (by rw [← map_pow]; exact jp_relation_kills_generator u r)
    have he : u i.right-u i.left+(u i.left-u a)=u i.right-u a := by omega
    rw [he, ← map_pow] at hz
    exact hz
  · have hr : rootOperator r • presentationGenerator u=0 :=
      killing_root_kills_generator u r (by dsimp [r]; omega)
    rw [hr, smul_zero]

/-- The corresponding relation for an outgoing long-root power. -/
theorem jp_outgoing_lowering_relation {n : ℕ} (u : Composition n) (i : AdjacentPosition n)
    (hu : u i.left ≤ u i.right) (b : Fin n) (hb : i.right < b) :
    let r : PositiveRoot n := ⟨(i.right,b),hb⟩
    let s : PositiveRoot n := ⟨(i.left,b),i.left_lt_right.trans hb⟩
    rootOperator s ^ (u b-u i.left) • (rootOperator r • presentationGenerator u)=0 := by
  let e := adjacentPositiveRoot i
  let r : PositiveRoot n := ⟨(i.right,b),hb⟩
  let s := joinedRoot e r rfl
  change rootOperator s ^ (u b-u i.left) • (rootOperator r • presentationGenerator u)=0
  by_cases h : u i.right ≤ u b
  · let ρ : Enveloping n →ₐ[ℂ] Module.End ℂ (PresentationQuotient u) :=
      Algebra.lsmul ℂ ℂ (PresentationQuotient u)
    obtain ⟨hc,hBC,hAC⟩ := root_pair_heisenberg ρ e r rfl
    have hc' := central_commutator_neg_orientation _ _ _ hc
    have hz := heisenberg_central_boundary_kills (-(ρ (rootOperator e))) (ρ (rootOperator r))
      (ρ (rootOperator s)) hc' hAC.neg_left hBC (u i.right-u i.left) (u b-u i.right)
      (presentationGenerator u)
      (by rw [neg_end_pow_apply, ← map_pow]
          have he : rootOperator e^(u i.right-u i.left+1) • presentationGenerator u=0 :=
            jp_relation_kills_generator u e
          change (-1 : ℂ)^_ • (rootOperator e^_ • presentationGenerator u)=0
          rw [he, smul_zero])
      (by rw [← map_pow]; exact jp_relation_kills_generator u r)
    have he : u i.right-u i.left+(u b-u i.right)=u b-u i.left := by omega
    rw [he, ← map_pow] at hz
    exact hz
  · have hr : rootOperator r • presentationGenerator u=0 :=
      killing_root_kills_generator u r (by dsimp [r]; omega)
    rw [hr, smul_zero]

end
end Schubert.RS.Representation
