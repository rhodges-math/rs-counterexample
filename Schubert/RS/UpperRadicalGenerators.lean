import Schubert.RS.Representation.UpperRadicalDecomposition

namespace Schubert.RS.Representation
noncomputable section
open FinPermutation
attribute [local instance 100] LieRing.ofAssociativeRing

theorem upperSimpleCoefficient_root {n : ℕ} (i : AdjacentPosition n) (r : RadicalRoot i) :
    upperSimpleCoefficient i (rootBasis n r.val)=0 := by
  have hr : r.val≠adjacentPositiveRoot i := fun hh => r.property (congrArg Subtype.val hh)
  simp [upperSimpleCoefficient,Module.Basis.coord_apply,hr,Ne.symm hr]

theorem upperRadicalPart_root {n : ℕ} (i : AdjacentPosition n) (r : RadicalRoot i) :
    upperRadicalPart i (rootBasis n r.val)=radicalEndRoot i r := by
  apply Subtype.ext
  rw [upperRadicalPart_val,upperSimpleCoefficient_root,zero_smul,sub_zero,rootBasis_apply]
  rfl

theorem upperRadicalPart_surjective {n : ℕ} (i : AdjacentPosition n) :
    Function.Surjective (upperRadicalPart i) := by
  intro r
  have hle : radicalEndSpan i ≤
      ((upperRadicalPart i).range.map (radicalEndLie i).toSubmodule.subtype) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨s,rfl⟩
    exact ⟨radicalEndRoot i s,⟨rootBasis n s.val,upperRadicalPart_root i s⟩,rfl⟩
  obtain ⟨y,hy,he⟩ := hle r.property
  have hyr : y=r := Subtype.ext he
  subst y
  exact hy

theorem upperSimpleCoefficient_adjacent {n : ℕ} (i : AdjacentPosition n) :
    upperSimpleCoefficient i (rootBasis n (adjacentPositiveRoot i))=1 := by
  simp [upperSimpleCoefficient,Module.Basis.coord_apply]

theorem upperRadicalPart_adjacent {n : ℕ} (i : AdjacentPosition n) :
    upperRadicalPart i (rootBasis n (adjacentPositiveRoot i))=0 := by
  apply Subtype.ext
  rw [upperRadicalPart_val,upperSimpleCoefficient_adjacent,one_smul,rootBasis_apply]
  exact sub_self _

end
end Schubert.RS.Representation
