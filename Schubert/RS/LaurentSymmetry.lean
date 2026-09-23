import Schubert.RS.Laurent

/-! Coordinate symmetries and constant terms for the paper's duality pairing. -/

namespace Schubert.RS

open FinPermutation Schubert
noncomputable section
variable {n : ℕ}

def weightSwap (i : AdjacentPosition n) : Weight n ≃+ Weight n where
  toFun a j := a (adjacentTransposition i j)
  invFun a j := a (adjacentTransposition i j)
  left_inv a := by ext j; simp [adjacentTransposition]
  right_inv a := by ext j; simp [adjacentTransposition]
  map_add' a b := rfl

def laurentSwap (i : AdjacentPosition n) : Laurent n ≃+* Laurent n :=
  AddMonoidAlgebra.mapDomainRingEquiv ℤ (weightSwap i)

@[simp] theorem laurentSwap_single (i : AdjacentPosition n) (a : Weight n) (z : ℤ) :
    laurentSwap i (AddMonoidAlgebra.single a z) =
      AddMonoidAlgebra.single (weightSwap i a) z :=
  AddMonoidAlgebra.mapDomainRingEquiv_single _ _ _

@[simp] theorem constantTerm_laurentSwap (i : AdjacentPosition n) (p : Laurent n) :
    constantTerm (laurentSwap i p) = constantTerm p := by
  simp [constantTerm, laurentSwap]

@[simp] theorem laurentSwap_involutive (i : AdjacentPosition n) (p : Laurent n) :
    laurentSwap i (laurentSwap i p) = p := by
  exact (laurentSwap i).symm_apply_apply p

theorem constantTerm_swap_transfer (i : AdjacentPosition n) (p q : Laurent n) :
    constantTerm (laurentSwap i p * q) = constantTerm (p * laurentSwap i q) := by
  rw [← constantTerm_laurentSwap i (laurentSwap i p * q), map_mul,
    laurentSwap_involutive]

def reverseNegWeight : Weight n ≃+ Weight n where
  toFun a i := -a i.rev
  invFun a i := -a i.rev
  left_inv a := by ext i; simp
  right_inv a := by ext i; simp
  map_add' a b := by ext i; simp [add_comm]

/-- The involution J f(x)=f(x_n^(-1),...,x_1^(-1)). -/
def reverseNeg : Laurent n ≃+* Laurent n :=
  AddMonoidAlgebra.mapDomainRingEquiv ℤ reverseNegWeight

@[simp] theorem constantTerm_reverseNeg (p : Laurent n) :
    constantTerm (reverseNeg p) = constantTerm p := by
  simp [constantTerm, reverseNeg]

@[simp] theorem reverseNeg_involutive (p : Laurent n) :
    reverseNeg (reverseNeg p) = p := by
  exact reverseNeg.symm_apply_apply p

theorem constantTerm_reverseNeg_transfer (p q : Laurent n) :
    constantTerm (reverseNeg p * q) = constantTerm (p * reverseNeg q) := by
  rw [← constantTerm_reverseNeg (reverseNeg p * q), map_mul, reverseNeg_involutive]

end
end Schubert.RS
