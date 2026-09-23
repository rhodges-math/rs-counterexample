import Schubert.RS.Family.SplitRoots
import Schubert.RS.Family.HallEvaluation

namespace Schubert.RS.Family
noncomputable section

abbrev SourceBLaurent (P : Parameters) := AddMonoidAlgebra (SlotLaurent P.m) (Weight (2*P.q-1))
abbrev SourceALaurent (P : Parameters) := AddMonoidAlgebra (SourceBLaurent P) (Weight (2*P.p-1))

def nestedLaurent (P : Parameters) : Laurent P.rank ≃+* SourceALaurent P :=
  ((splitLaurent P).trans AddMonoidAlgebra.curryRingEquiv).trans
    (AddMonoidAlgebra.mapRingEquiv (Weight (2*P.p-1)) AddMonoidAlgebra.curryRingEquiv)

theorem nestedLaurent_single (P : Parameters) (w : Weight P.rank) (z : ℤ) :
    nestedLaurent P (AddMonoidAlgebra.single w z)=
      AddMonoidAlgebra.single (splitWeight P w).1
        (AddMonoidAlgebra.single (splitWeight P w).2.1
          (AddMonoidAlgebra.single (splitWeight P w).2.2 z)) := by
  simp only [nestedLaurent,RingEquiv.trans_apply,splitLaurent_single,splitWeight,
    AddMonoidAlgebra.curryRingEquiv_single,AddMonoidAlgebra.mapRingEquiv_single]

theorem curry_coefficient {R α β : Type*} [Semiring R] [AddMonoid α] [AddMonoid β]
    (f : AddMonoidAlgebra R (α × β)) (a : α) (b : β) :
    ((AddMonoidAlgebra.curryRingEquiv f).coeff a).coeff b=f.coeff (a,b) := rfl

theorem nestedLaurent_coefficient (P : Parameters) (f : Laurent P.rank) (w : Weight P.rank) :
    (((nestedLaurent P f).coeff (splitWeight P w).1).coeff (splitWeight P w).2.1).coeff
      (splitWeight P w).2.2=f.coeff w := by
  unfold nestedLaurent
  rw [RingEquiv.trans_apply,AddMonoidAlgebra.coeff_mapRingEquiv,
    curry_coefficient,RingEquiv.trans_apply,curry_coefficient]
  exact splitLaurent_coefficient P f w

theorem nestedLaurent_residual_coefficient (P : Parameters) (f : Laurent P.rank) :
    (((nestedLaurent P f).coeff (fun _ => 1)).coeff (fun _ => 1)).coeff (fun _ => 1)=
      f.coeff (targetDifference P) := by
  have h:=nestedLaurent_coefficient P f (targetDifference P)
  rw [splitWeight_residual] at h
  exact h

end
end Schubert.RS.Family
