import RSCounterexample.Demazure.JosephPolo.TableauCharacterRecursion

/-!
# The base case of the tableau character

The shape weight of the column multiplicities counts columns of height at least `a`, the prefix row
sets of `w` have weight the extremal weight, and the only tuple with a defining chain below the
identity is the tuple of prefix rows; hence the tableau character at the identity is the monomial of
the shape weight (`flagTableauCharacter_refl`).
-/

open Schubert

namespace Demazure.FlagModule
noncomputable section
open FinPermutation
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem shapeWeight_columnMultiplicity {n d : ℕ} (h : Fin d → Fin n) (a : Fin n) :
    shapeWeight (columnMultiplicity h) a = ∑ j, if a ≤ h j then 1 else 0 := by
  unfold shapeWeight columnMultiplicity
  simpa [nsmul_eq_mul,mul_ite] using
    Fintype.sum_fiberwise' h (fun k => if a ≤ k then (1:ℕ) else 0)

theorem flagTupleWeight_prefix {n d : ℕ} (h : Fin d → Fin n) (w : FinPermutation n) :
    flagTupleWeight h (fun j => flagPrefixRows w (h j)) =
      extremalWeight (columnMultiplicity h) w := by
  funext a
  simp only [flagTupleWeight,mem_flagPrefixRows,extremalWeight,shapeWeight_columnMultiplicity]

theorem hasFlagDefiningChain_refl_iff {n d : ℕ} (h : Fin d → Fin n)
    (T : (j : Fin d) → FlagMinorRowSet (h j)) :
    HasFlagDefiningChain h T (Equiv.refl (Fin n)) ↔
      T = fun j => flagPrefixRows (Equiv.refl (Fin n)) (h j) := by
  constructor
  · rintro ⟨v,hm,hp,hb⟩
    funext j
    have hv : v j = Equiv.refl (Fin n) :=
      strongBruhat_antisymm (hb j) (refl_strongBruhatLE (v j))
    simpa only [hv] using (hp j).symm
  · intro hT
    subst T
    exact ⟨fun _ => Equiv.refl (Fin n),fun _ _ _ => strongBruhat_refl _,
      fun _ => rfl,fun _ => strongBruhat_refl _⟩

theorem flagTableauCharacter_refl {n d : ℕ} (h : Fin d → Fin n) :
    flagTableauCharacter h (Equiv.refl (Fin n)) =
      compositionMonomial (shapeWeight (columnMultiplicity h)) := by
  simp only [flagTableauCharacter,hasFlagDefiningChain_refl_iff,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true,flagTupleWeight_prefix]
  rfl

end
end Demazure.FlagModule
