import Schubert.RS.Representation.ParabolicRadicalLie
import Schubert.RS.Representation.PrimitiveStringExtension

namespace Schubert.RS.Representation
noncomputable section
open FinPermutation
attribute [local instance 100] LieRing.ofAssociativeRing

theorem matrixUnitEnd_ad_square_zero {n : ℕ} (a b c d : Fin n)
    (hab : a≠b) (hcd : (c,d)≠(b,a)) :
    ⁅(matrixUnitDerivation a b).toLinearMap,
      ⁅(matrixUnitDerivation a b).toLinearMap,(matrixUnitDerivation c d).toLinearMap⁆⁆ = 0 := by
  classical
  rw [matrixUnitEnd_commutator]
  by_cases hbc : b=c <;> by_cases hda : d=a
  · exact (hcd (Prod.ext hbc.symm hda)).elim
  · subst c
    simp [hda,matrixUnitEnd_commutator,hab,Ne.symm hab]
  · subst d
    simp [hbc,matrixUnitEnd_commutator,hab,Ne.symm hab]
  · simp [hbc,hda]

def radicalRaisingEnd {n : ℕ} (i : AdjacentPosition n) : Module.End ℂ (radicalEndLie i) :=
  LieModule.toEnd ℂ _ (radicalEndLie i)
    (sl2RaisingElement (polynomialSl2Triple i.left i.right i.left_ne_right))

def radicalLoweringEnd {n : ℕ} (i : AdjacentPosition n) : Module.End ℂ (radicalEndLie i) :=
  LieModule.toEnd ℂ _ (radicalEndLie i)
    (sl2LoweringElement (polynomialSl2Triple i.left i.right i.left_ne_right))

private theorem radical_double_bracket_zero {n : ℕ} (i : AdjacentPosition n)
    (a b : Fin n) (hab : a≠b)
    (hr : ∀ r : RadicalRoot i, r.val.val≠(b,a))
    (A : Module.End ℂ (MatrixPolynomial n)) (hA : A∈radicalEndSpan i) :
    ⁅(matrixUnitDerivation a b).toLinearMap,⁅(matrixUnitDerivation a b).toLinearMap,A⁆⁆=0 := by
  induction hA using Submodule.span_induction with
  | mem A hA => obtain ⟨r,rfl⟩ := hA; exact matrixUnitEnd_ad_square_zero a b _ _ hab (hr r)
  | zero => simp only [lie_zero]
  | add A C hA hC ihA ihC => simp only [lie_add,ihA,ihC,add_zero]
  | smul c A hA ihA => simp only [lie_smul,ihA,smul_zero]

theorem radicalRaisingEnd_sq {n : ℕ} (i : AdjacentPosition n) : radicalRaisingEnd i ^ 2 = 0 := by
  apply LinearMap.ext
  intro r
  apply Subtype.ext
  change ⁅(matrixUnitDerivation i.left i.right).toLinearMap,
    ⁅(matrixUnitDerivation i.left i.right).toLinearMap,r.val⁆⁆=0
  apply radical_double_bracket_zero i i.left i.right i.left_ne_right _ r.val r.property
  intro s hs
  have hab := s.val.property
  have ha : s.val.val.1=i.right := congrArg Prod.fst hs
  have hb : s.val.val.2=i.left := congrArg Prod.snd hs
  rw [ha,hb] at hab
  exact (not_lt_of_ge (le_of_lt i.left_lt_right)) hab

theorem radicalLoweringEnd_sq {n : ℕ} (i : AdjacentPosition n) : radicalLoweringEnd i ^ 2 = 0 := by
  apply LinearMap.ext
  intro r
  apply Subtype.ext
  change ⁅(matrixUnitDerivation i.right i.left).toLinearMap,
    ⁅(matrixUnitDerivation i.right i.left).toLinearMap,r.val⁆⁆=0
  exact radical_double_bracket_zero i i.right i.left (Ne.symm i.left_ne_right)
    (fun s => s.property) r.val r.property

theorem radicalRaisingEnd_nilpotent {n : ℕ} (i : AdjacentPosition n) : IsNilpotent (radicalRaisingEnd i) :=
  ⟨2,radicalRaisingEnd_sq i⟩

theorem radicalLoweringEnd_nilpotent {n : ℕ} (i : AdjacentPosition n) : IsNilpotent (radicalLoweringEnd i) :=
  ⟨2,radicalLoweringEnd_sq i⟩

end
end Schubert.RS.Representation
