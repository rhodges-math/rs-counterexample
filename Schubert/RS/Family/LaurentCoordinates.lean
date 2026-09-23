import Schubert.RS.Family.Coordinates
import Schubert.RS.Family.RootWindow

/-! An actual additive lattice equivalence separating the two unequal
source classes and the reversed, inverted target slots. -/

namespace Schubert.RS.Family
noncomputable section

abbrev CoordinateIndex (P : Parameters) :=
  Fin (2*P.p-1) ⊕ (Fin (2*P.q-1) ⊕ Slot P.m)

def coordinateIndex (P : Parameters) : CoordinateIndex P → Fin P.rank
  | .inl i => sourceA P i
  | .inr (.inl i) => sourceB P i
  | .inr (.inr i) => target P i.rev

theorem coordinateIndex_bijective (P : Parameters) : Function.Bijective (coordinateIndex P) := by
  constructor
  · intro i j h
    rcases i with i | i | i <;> rcases j with j | j | j
    · exact congrArg Sum.inl ((sourceA_strictMono P).injective h)
    · exact False.elim (sourceA_ne_B P i j h)
    · exact False.elim (sourceA_ne_target P i j.rev h)
    · exact False.elim (sourceA_ne_B P j i h.symm)
    · exact congrArg (Sum.inr ∘ Sum.inl) ((sourceB_strictMono P).injective h)
    · exact False.elim (sourceB_ne_target P i j.rev h)
    · exact False.elim (sourceA_ne_target P j i.rev h.symm)
    · exact False.elim (sourceB_ne_target P j i.rev h.symm)
    · exact congrArg (Sum.inr ∘ Sum.inr) (Fin.rev_injective ((target_strictMono P).injective h))
  · intro i
    rcases coordinates_covered P i with ⟨j,h⟩ | ⟨j,h⟩ | ⟨j,h⟩
    · exact ⟨.inl j,h⟩
    · exact ⟨.inr (.inl j),h⟩
    · refine ⟨.inr (.inr j.rev),?_⟩
      simpa only [coordinateIndex,Fin.rev_rev] using h

def coordinateIndexEquiv (P : Parameters) : CoordinateIndex P ≃ Fin P.rank :=
  Equiv.ofBijective (coordinateIndex P) (coordinateIndex_bijective P)

def splitWeight (P : Parameters) (w : Weight P.rank) :
    Weight (2*P.p-1) × (Weight (2*P.q-1) × Weight (2*P.m-1+1)) :=
  (fun i => w (sourceA P i),(fun i => w (sourceB P i),fun i => -w (target P i.rev)))

def joinWeight (P : Parameters)
    (v : Weight (2*P.p-1) × (Weight (2*P.q-1) × Weight (2*P.m-1+1)))
    (i : Fin P.rank) : ℤ :=
  match (coordinateIndexEquiv P).symm i with
  | .inl j => v.1 j
  | .inr (.inl j) => v.2.1 j
  | .inr (.inr j) => -v.2.2 j

theorem joinWeight_at (P : Parameters)
    (v : Weight (2*P.p-1) × (Weight (2*P.q-1) × Weight (2*P.m-1+1))) (j : CoordinateIndex P) :
    joinWeight P v (coordinateIndex P j)=
      (match j with | .inl i => v.1 i | .inr (.inl i) => v.2.1 i | .inr (.inr i) => -v.2.2 i) := by
  change (match (coordinateIndexEquiv P).symm ((coordinateIndexEquiv P) j) with
    | .inl i => v.1 i | .inr (.inl i) => v.2.1 i | .inr (.inr i) => -v.2.2 i)=_
  rw [Equiv.symm_apply_apply]

theorem join_splitWeight (P : Parameters) (w : Weight P.rank) : joinWeight P (splitWeight P w)=w := by
  funext i
  obtain ⟨j,rfl⟩:=(coordinateIndex_bijective P).surjective i
  rw [joinWeight_at]
  rcases j with j | j | j <;> simp only [splitWeight,coordinateIndex,neg_neg]

theorem split_joinWeight (P : Parameters)
    (v : Weight (2*P.p-1) × (Weight (2*P.q-1) × Weight (2*P.m-1+1))) :
    splitWeight P (joinWeight P v)=v := by
  apply Prod.ext
  · funext j
    exact joinWeight_at P v (.inl j)
  · apply Prod.ext
    · funext j
      exact joinWeight_at P v (.inr (.inl j))
    · funext j
      have h:=joinWeight_at P v (.inr (.inr j))
      change -joinWeight P v (coordinateIndex P (.inr (.inr j)))=v.2.2 j
      rw [h,neg_neg]

def splitWeightEquiv (P : Parameters) :
    Weight P.rank ≃+ (Weight (2*P.p-1) × (Weight (2*P.q-1) × Weight (2*P.m-1+1))) where
  toFun:=splitWeight P
  invFun:=joinWeight P
  left_inv:=join_splitWeight P
  right_inv:=split_joinWeight P
  map_add' w v:=by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · funext i
        exact neg_add _ _

theorem splitWeight_residual (P : Parameters) :
    splitWeight P (targetDifference P)=(fun _ => 1,(fun _ => 1,fun _ => 1)) := by
  apply Prod.ext
  · funext i
    change (c P (sourceA P i) : ℤ)-a P (sourceA P i)-b P (sourceA P i)=1
    rw [residual_pattern]
    simp [sourceClass,sourceA_class]
  · apply Prod.ext
    · funext i
      change (c P (sourceB P i) : ℤ)-a P (sourceB P i)-b P (sourceB P i)=1
      rw [residual_pattern]
      simp [sourceClass,sourceB_class]
    · funext i
      change -((c P (target P i.rev) : ℤ)-a P (target P i.rev)-b P (target P i.rev))=1
      rw [residual_pattern]
      simp [target_not_source]

def splitLaurent (P : Parameters) : Laurent P.rank ≃+*
    AddMonoidAlgebra ℤ (Weight (2*P.p-1) × (Weight (2*P.q-1) × Weight (2*P.m-1+1))) :=
  AddMonoidAlgebra.mapDomainRingEquiv ℤ (splitWeightEquiv P)

theorem splitLaurent_single (P : Parameters) (w : Weight P.rank) (z : ℤ) :
    splitLaurent P (AddMonoidAlgebra.single w z)=AddMonoidAlgebra.single (splitWeight P w) z :=
  AddMonoidAlgebra.mapDomain_single

theorem splitLaurent_coefficient (P : Parameters) (f : Laurent P.rank) (w : Weight P.rank) :
    (splitLaurent P f).coeff (splitWeight P w)=f.coeff w := by
  change Finsupp.mapDomain (splitWeight P) f.coeff (splitWeight P w)=_
  exact Finsupp.mapDomain_apply (splitWeightEquiv P).injective _ _

end
end Schubert.RS.Family
