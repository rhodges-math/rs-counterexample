import Schubert.RS.Family.HallEvaluation
import Schubert.RS.Family.ElementarySources
import Schubert.RS.Family.LaurentRelabel

/-! The two-source coefficient lemma for every matching of the early slots
with the late slots. The proof expands marked pairs, applies the early-capacity
bound, and counts the two possible cardinalities. -/

namespace Schubert.RS.Family
noncomputable section
variable {m p q : ℕ}

/-- Pair early slot i with late slot σ(i). The Laurent factor has sign and
orientation exactly as in the paper: 1 - t_late / t_early. -/
def matchedTargetNumerator (σ : Equiv.Perm (Fin m)) : SlotLaurent m :=
  ∏ i : Fin m, (1-AddMonoidAlgebra.single (positiveRoot (slotLeft (σ i)) (slotRight i)) 1)

@[simp] theorem matchedTargetNumerator_refl :
    matchedTargetNumerator (Equiv.refl (Fin m)) = targetNumerator m := rfl

def matchingSlotPerm (hm : 0<m) (σ : Equiv.Perm (Fin m)) : Equiv.Perm (Slot m) :=
  (slotSumEquiv hm).symm.trans
    ((Equiv.sumCongr (Equiv.refl (Fin m)) σ).trans (slotSumEquiv hm))

@[simp] theorem matchingSlotPerm_early (hm : 0<m) (σ : Equiv.Perm (Fin m)) (i : Fin m) :
    matchingSlotPerm hm σ (slotRight i)=slotRight i := by
  change matchingSlotPerm hm σ (slotSumEquiv hm (Sum.inl i))=_
  simp only [matchingSlotPerm,Equiv.trans_apply,Equiv.symm_apply_apply]
  rfl

@[simp] theorem matchingSlotPerm_late (hm : 0<m) (σ : Equiv.Perm (Fin m)) (i : Fin m) :
    matchingSlotPerm hm σ (slotLeft i)=slotLeft (σ i) := by
  change matchingSlotPerm hm σ (slotSumEquiv hm (Sum.inr i))=_
  simp only [matchingSlotPerm,Equiv.trans_apply,Equiv.symm_apply_apply]
  rfl

@[simp] theorem laurentRelabel_slotVariable (e : Equiv.Perm (Slot m)) (i : Slot m) :
    laurentRelabel e (slotVariable i)=slotVariable (e i) := by
  simp [slotVariable]

theorem relabel_targetNumerator (hm : 0<m) (σ : Equiv.Perm (Fin m)) :
    laurentRelabel (matchingSlotPerm hm σ) (targetNumerator m)=matchedTargetNumerator σ := by
  simp only [targetNumerator,matchedTargetNumerator,map_prod,map_sub,map_one,
    laurentRelabel_single,positiveRoot,map_sub,weightRelabel_single,
    matchingSlotPerm_early,matchingSlotPerm_late]

theorem relabel_earlyLatePolynomial (hm : 0<m) (hp : 0<p) (σ : Equiv.Perm (Fin m)) :
    laurentRelabel (matchingSlotPerm hm σ)
      (earlyLatePolynomial p (fun i => slotVariable (slotRight i))
        (fun i => slotVariable (slotLeft i))) =
      earlyLatePolynomial p (fun i => slotVariable (slotRight i))
        (fun i => slotVariable (slotLeft i)) := by
  change (laurentRelabel (matchingSlotPerm hm σ)).toRingHom
    (earlyLatePolynomial p (fun i => slotVariable (slotRight i))
      (fun i => slotVariable (slotLeft i))) = _
  rw [map_earlyLatePolynomial _ hp]
  change earlyLatePolynomial p
    (fun i => laurentRelabel (matchingSlotPerm hm σ) (slotVariable (slotRight i)))
    (fun i => laurentRelabel (matchingSlotPerm hm σ) (slotVariable (slotLeft i))) = _
  simp only [laurentRelabel_slotVariable,matchingSlotPerm_early,matchingSlotPerm_late]
  exact earlyLatePolynomial_permute_late (m:=m) (R:=SlotLaurent m) p
    (fun i => slotVariable (slotRight i)) (fun i => slotVariable (slotLeft i)) σ

/-- Exact finite expansion after the Hall polynomials have been computed. -/
theorem two_source_marked_expansion (hp : 0<p) (hq : 0<q) (h : p+q=m+1) :
    (targetNumerator m *
      earlyLatePolynomial p (fun i => slotVariable (slotRight i)) (fun i => slotVariable (slotLeft i)) *
      earlyLatePolynomial q (fun i => slotVariable (slotRight i)) (fun i => slotVariable (slotLeft i))).coeff
        (fun _ => 1) = ∑ t : BalancedPairedTerm m p q,(-1 : ℤ)^t.val.1.card := by
  rw [← hallPolynomial_elementary (by omega) hp,← hallPolynomial_elementary (by omega) hq]
  exact pairedHall_coefficient_marked_pairs (by omega) p q

/-- The paper's coefficient formula for any bijective early/late matching.
The coefficient is an integer difference, without a positivity assumption. -/
theorem two_source_count (hp : 0<p) (hq : 0<q) (h : p+q=m+1)
    (σ : Equiv.Perm (Fin m)) :
    (matchedTargetNumerator σ *
      earlyLatePolynomial p (fun i => slotVariable (slotRight i)) (fun i => slotVariable (slotLeft i)) *
      earlyLatePolynomial q (fun i => slotVariable (slotRight i)) (fun i => slotVariable (slotLeft i))).coeff
        (fun _ => 1) =
      2*(Nat.choose m (p-1) : ℤ)*Nat.choose m p - m*(Nat.choose (m-1) (p-1) : ℤ)^2 := by
  have hm : 0<m := by omega
  have he := laurentRelabel_coefficient_one (matchingSlotPerm hm σ)
    (targetNumerator m *
      earlyLatePolynomial p (fun i => slotVariable (slotRight i)) (fun i => slotVariable (slotLeft i)) *
      earlyLatePolynomial q (fun i => slotVariable (slotRight i)) (fun i => slotVariable (slotLeft i)))
  rw [map_mul,map_mul,relabel_targetNumerator,relabel_earlyLatePolynomial hm hp,
    relabel_earlyLatePolynomial hm hq] at he
  rw [he,two_source_marked_expansion hp hq h]
  exact marked_pair_signed_sum hp hq h

end
end Schubert.RS.Family
