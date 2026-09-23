import Schubert.RS.Representation.ParabolicRadicalNilpotence
import Schubert.RS.Representation.LieActionExponential
import Schubert.RS.WeylDenominator

namespace Schubert.RS.Representation
noncomputable section
open FinPermutation
attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 2000000

@[instance_reducible] def complexRationalModule (X : Type*) [AddCommGroup X] [Module ℂ X] :
    Module ℚ X := Module.compHom X (Rat.castHom ℂ)

local instance radicalRationalModule {n : ℕ} (i : AdjacentPosition n) : Module ℚ (radicalEndLie i) :=
  complexRationalModule _

theorem exp_of_square_zero {X : Type*} [AddCommGroup X] [Module ℂ X] [Module ℚ X]
    (D : Module.End ℂ X) (hD : D^2=0) : IsNilpotent.exp D = 1+D := by
  rw [IsNilpotent.exp_eq_sum hD]
  simp [Finset.sum_range_succ]

def radicalWeyl {n : ℕ} (i : AdjacentPosition n) : radicalEndLie i ≃ₗ[ℂ] radicalEndLie i :=
  nilpotentWeylEquiv (radicalRaisingEnd i) (radicalLoweringEnd i)
    (radicalRaisingEnd_nilpotent i) (radicalLoweringEnd_nilpotent i)

theorem radicalWeyl_val {n : ℕ} (i : AdjacentPosition n) (r : radicalEndLie i) :
    (radicalWeyl i r).val =
      r.val + ⁅(matrixUnitDerivation i.left i.right).toLinearMap,r.val⁆ -
        ⁅(matrixUnitDerivation i.right i.left).toLinearMap,
          r.val + ⁅(matrixUnitDerivation i.left i.right).toLinearMap,r.val⁆⁆ +
      ⁅(matrixUnitDerivation i.left i.right).toLinearMap,
        r.val + ⁅(matrixUnitDerivation i.left i.right).toLinearMap,r.val⁆ -
          ⁅(matrixUnitDerivation i.right i.left).toLinearMap,
            r.val + ⁅(matrixUnitDerivation i.left i.right).toLinearMap,r.val⁆⁆⁆ := by
  have hn : (-radicalLoweringEnd i)^2=0 := by rw [neg_sq,radicalLoweringEnd_sq]
  change (nilpotentWeylEquiv _ _ _ _ r).val = _
  rw [nilpotentWeylEquiv_apply,exp_of_square_zero _ (radicalRaisingEnd_sq i),exp_of_square_zero _ hn]
  simp only [sub_eq_add_neg]
  rfl

def radicalReflectedRoot {n : ℕ} (i : AdjacentPosition n) (r : RadicalRoot i) : RadicalRoot i :=
  ⟨⟨(adjacentTransposition i r.val.val.1,adjacentTransposition i r.val.val.2),
    ((adjacent_preserves_other_positive_pairs i r.val.val.1 r.val.val.2).mpr
      ⟨r.val.property,r.property⟩).1⟩,
    ((adjacent_preserves_other_positive_pairs i r.val.val.1 r.val.val.2).mpr
      ⟨r.val.property,r.property⟩).2⟩

def radicalWeylSign {n : ℕ} (i : AdjacentPosition n) (r : RadicalRoot i) : ℂ :=
  if r.val.val.1=i.left ∨ r.val.val.2=i.left then -1 else 1

theorem radicalWeyl_root {n : ℕ} (i : AdjacentPosition n) (r : RadicalRoot i) :
    radicalWeyl i (radicalEndRoot i r) =
      radicalWeylSign i r • radicalEndRoot i (radicalReflectedRoot i r) := by
  classical
  apply Subtype.ext
  rw [radicalWeyl_val]
  change _ = radicalWeylSign i r •
    (matrixUnitDerivation (adjacentTransposition i r.val.val.1)
      (adjacentTransposition i r.val.val.2)).toLinearMap
  have hne := i.left_ne_right
  have hil := i.left_lt_right
  have hp := r.val.property
  have hr := r.property
  have hab := ne_of_lt hp
  by_cases ha : r.val.val.1=i.left <;> by_cases hb : r.val.val.1=i.right <;>
    by_cases hc : r.val.val.2=i.left <;> by_cases hd : r.val.val.2=i.right <;>
    simp_all [radicalEndRoot,radicalWeylSign,adjacentTransposition,Equiv.swap_apply_def,
      Prod.ext_iff,lie_add,lie_sub,matrixUnitEnd_commutator,eq_comm]
  all_goals try omega
  all_goals
    apply LinearMap.ext
    intro p
    simp <;> abel

theorem radicalWeylSign_ne_zero {n : ℕ} (i : AdjacentPosition n) (r : RadicalRoot i) :
    radicalWeylSign i r ≠ 0 := by
  unfold radicalWeylSign
  split_ifs <;> norm_num

end
end Schubert.RS.Representation
