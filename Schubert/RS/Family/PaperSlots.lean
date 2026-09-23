import Schubert.RS.Family.TwoSourceCount

/-! The two-source formula in the paper's ordinary target order: first all
early slots, then all late slots, with an arbitrary bijection between them. -/

namespace Schubert.RS.Family
noncomputable section
variable {m p q : ℕ}

def paperEarly (i : Fin m) : Fin (2*m) := ⟨i.val,by have hi:=i.isLt; omega⟩
def paperLate (i : Fin m) : Fin (2*m) := ⟨m+i.val,by have hi:=i.isLt; omega⟩

def paperTargetEquiv (hm : 0<m) : Slot m ≃ Fin (2*m) :=
  Fin.revPerm.trans (Fin.castOrderIso (by omega : 2*m-1+1=2*m)).toEquiv

@[simp] theorem paperTargetEquiv_early (hm : 0<m) (i : Fin m) :
    paperTargetEquiv hm (slotRight i)=paperEarly i := by
  apply Fin.ext
  have hi:=i.isLt
  simp [paperTargetEquiv,slotRight,slotLeft,paperEarly,Fin.rev]
  omega

@[simp] theorem paperTargetEquiv_late (hm : 0<m) (i : Fin m) :
    paperTargetEquiv hm (slotLeft i)=paperLate i.rev := by
  apply Fin.ext
  have hi:=i.isLt
  simp [paperTargetEquiv,slotLeft,paperLate,Fin.rev]
  omega

def paperVariable (i : Fin (2*m)) : Laurent (2*m) :=
  AddMonoidAlgebra.single (Pi.single i 1) 1

/-- The source polynomial displayed in the two-source lemma, in forward order. -/
def paperSourcePolynomial (m p : ℕ) : Laurent (2*m) :=
  earlyLatePolynomial p (fun i => paperVariable (paperEarly i))
    (fun i => paperVariable (paperLate i))

def paperTargetNumerator (σ : Equiv.Perm (Fin m)) : Laurent (2*m) :=
  ∏ i : Fin m, (1-AddMonoidAlgebra.single (positiveRoot (paperLate (σ i)) (paperEarly i)) 1)

@[simp] theorem paperRelabel_variable (hm : 0<m) (i : Slot m) :
    laurentRelabel (paperTargetEquiv hm) (slotVariable i)=paperVariable (paperTargetEquiv hm i) := by
  simp [slotVariable,paperVariable]

theorem paperRelabel_source (hm : 0<m) (hp : 0<p) :
    laurentRelabel (paperTargetEquiv hm)
      (earlyLatePolynomial p (fun i => slotVariable (slotRight i))
        (fun i => slotVariable (slotLeft i))) = paperSourcePolynomial m p := by
  change (laurentRelabel (paperTargetEquiv hm)).toRingHom
    (earlyLatePolynomial p (fun i => slotVariable (slotRight i))
      (fun i => slotVariable (slotLeft i))) = _
  rw [map_earlyLatePolynomial _ hp]
  change earlyLatePolynomial p
    (fun i => laurentRelabel (paperTargetEquiv hm) (slotVariable (slotRight i)))
    (fun i => laurentRelabel (paperTargetEquiv hm) (slotVariable (slotLeft i))) = _
  simp only [paperRelabel_variable,paperTargetEquiv_early,paperTargetEquiv_late]
  exact earlyLatePolynomial_permute_late (m:=m) (R:=Laurent (2*m)) p
    (fun i => paperVariable (paperEarly i)) (fun i => paperVariable (paperLate i)) Fin.revPerm

theorem paperRelabel_numerator (hm : 0<m) (σ : Equiv.Perm (Fin m)) :
    laurentRelabel (paperTargetEquiv hm)
      (matchedTargetNumerator (σ.trans Fin.revPerm)) = paperTargetNumerator σ := by
  simp only [matchedTargetNumerator,paperTargetNumerator,map_prod,map_sub,map_one,
    laurentRelabel_single,positiveRoot,map_sub,weightRelabel_single,
    paperTargetEquiv_early,paperTargetEquiv_late,Equiv.trans_apply,Fin.revPerm_apply,Fin.rev_rev]

/-- Literal forward-slot statement of the paper's two-source
lemma. Every bijective matching is allowed; p=1 and q=1 are included. -/
theorem paper_two_source_count (hp : 0<p) (hq : 0<q) (h : p+q=m+1)
    (σ : Equiv.Perm (Fin m)) :
    (paperSourcePolynomial m p * paperSourcePolynomial m q * paperTargetNumerator σ).coeff
      (fun _ => 1) =
      2*(Nat.choose m (p-1) : ℤ)*Nat.choose m p - m*(Nat.choose (m-1) (p-1) : ℤ)^2 := by
  have hm : 0<m := by omega
  have he := laurentRelabel_coefficient_one (paperTargetEquiv hm)
    (matchedTargetNumerator (σ.trans Fin.revPerm) *
      earlyLatePolynomial p (fun i => slotVariable (slotRight i)) (fun i => slotVariable (slotLeft i)) *
      earlyLatePolynomial q (fun i => slotVariable (slotRight i)) (fun i => slotVariable (slotLeft i)))
  rw [map_mul,map_mul,paperRelabel_numerator,paperRelabel_source hm hp,
    paperRelabel_source hm hq] at he
  rw [mul_assoc,mul_comm (paperTargetNumerator σ)
    (paperSourcePolynomial m p * paperSourcePolynomial m q)] at he
  rw [he]
  exact two_source_count hp hq h _

/-- The family's reversed target slots become the paper's forward slots.
The family pairs the first early slot with the last late slot, and so on. -/
theorem hall_coefficient_eq_paper (hm : 0<m) (hp : 0<p) (hq : 0<q) :
    (targetNumerator m * hallPolynomial (hallHeights hm p) slotVariable *
      hallPolynomial (hallHeights hm q) slotVariable).coeff (fun _ => 1) =
    (paperSourcePolynomial m p * paperSourcePolynomial m q *
      paperTargetNumerator Fin.revPerm).coeff (fun _ => 1) := by
  rw [hallPolynomial_elementary hm hp,hallPolynomial_elementary hm hq]
  have hn : laurentRelabel (paperTargetEquiv hm) (targetNumerator m) =
      paperTargetNumerator Fin.revPerm := by
    simpa only [matchedTargetNumerator,targetNumerator,Equiv.trans_apply,
      Fin.revPerm_apply,Fin.rev_rev] using paperRelabel_numerator hm Fin.revPerm
  have he := laurentRelabel_coefficient_one (paperTargetEquiv hm)
    (targetNumerator m *
      earlyLatePolynomial p (fun i => slotVariable (slotRight i)) (fun i => slotVariable (slotLeft i)) *
      earlyLatePolynomial q (fun i => slotVariable (slotRight i)) (fun i => slotVariable (slotLeft i)))
  rw [map_mul,map_mul,hn,paperRelabel_source hm hp,paperRelabel_source hm hq] at he
  simpa only [mul_assoc,mul_comm,mul_left_comm] using he.symm

end
end Schubert.RS.Family
