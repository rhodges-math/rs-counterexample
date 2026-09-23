import Schubert.RS.JosephPolo.ChainStrings

namespace Schubert.RS.Representation
noncomputable section
open FinPermutation
attribute [local instance] Classical.propDecidable

abbrev FixedFlagColumns {n : ℕ} (i : AdjacentPosition n) (k : Fin n) :=
  {C : FlagMinorRowSet k // i.left ∈ C.val ↔ i.right ∈ C.val}

abbrev RaisedFlagColumns {n : ℕ} (i : AdjacentPosition n) (k : Fin n) :=
  {C : FlagMinorRowSet k // i.left ∈ C.val ∧ i.right ∉ C.val}

/-- Every column is fixed, or is one of the two members of a uniquely
specified moving pair. The bit 0 denotes its raised member. -/
def flagColumnPartition {n : ℕ} (i : AdjacentPosition n) (k : Fin n) :
    FlagMinorRowSet k ≃ FixedFlagColumns i k ⊕ (RaisedFlagColumns i k × Fin 2) where
  toFun C :=
    if hf : i.left ∈ C.val ↔ i.right ∈ C.val then Sum.inl ⟨C,hf⟩
    else if ha : i.left ∈ C.val then
      Sum.inr (⟨C,ha,fun hb => hf ⟨fun _ => hb,fun _ => ha⟩⟩,0)
    else
      Sum.inr (⟨C.permute (Equiv.swap i.left i.right),by
        constructor
        · have hb : i.right ∈ C.val := by
            by_contra hb
            exact hf ⟨fun h => (ha h).elim,fun h => (hb h).elim⟩
          simpa [FlagMinorRowSet.mem_permute] using hb
        · simpa [FlagMinorRowSet.mem_permute] using ha⟩,1)
  invFun x := match x with
    | Sum.inl C => C.val
    | Sum.inr (C,b) => if b.val = 0 then C.val
      else C.val.permute (Equiv.swap i.left i.right)
  left_inv C := by
    by_cases hf : i.left ∈ C.val ↔ i.right ∈ C.val
    · simp only [dif_pos hf]
    · simp only [dif_neg hf]
      by_cases ha : i.left ∈ C.val
      · simp only [dif_pos ha,Fin.val_zero,ite_true]
      · simp only [dif_neg ha,Fin.val_one,one_ne_zero,ite_false]
        exact C.permute_swap_involutive _ _
  right_inv x := by
    rcases x with C | ⟨C,b⟩
    · simp only [dif_pos C.property]
    · have hf : ¬ (i.left ∈ C.val.val ↔ i.right ∈ C.val.val) :=
        fun h => C.property.2 (h.mp C.property.1)
      by_cases hb : b.val = 0
      · have he : b = 0 := Fin.ext hb
        subst b
        simp only [Fin.val_zero,ite_true,dif_neg hf,dif_pos C.property.1]
      · have he : b = 1 := Fin.ext (by have := b.isLt; omega)
        subst b
        have hDa : i.left ∉ (C.val.permute (Equiv.swap i.left i.right)).val := by
          simpa [FlagMinorRowSet.mem_permute] using C.property.2
        have hDb : i.right ∈ (C.val.permute (Equiv.swap i.left i.right)).val := by
          simpa [FlagMinorRowSet.mem_permute] using C.property.1
        have hDf : ¬ (i.left ∈ (C.val.permute (Equiv.swap i.left i.right)).val ↔
            i.right ∈ (C.val.permute (Equiv.swap i.left i.right)).val) :=
          fun h => hDa (h.mpr hDb)
        simp only [Fin.val_one,one_ne_zero,ite_false,dif_neg hDf,dif_neg hDa]
        congr 3
        exact C.val.permute_swap_involutive _ _

end
end Schubert.RS.Representation
