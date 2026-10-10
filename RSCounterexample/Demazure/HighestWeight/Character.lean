import RSCounterexample.Demazure.HighestWeight.LongestDemazure
import RSCounterexample.Demazure.JosephPolo.FlagModulePresentation
import Mathlib.Data.Fin.Tuple.Sort

/-!
# The character of the flag-minor span

`V = flagOrbitSpan m` is the composition flag module of the increasing composition
`w₀λ = (λ_{n-1}, …, λ_0)` (`flagOrbitSpan_eq_compositionFlag`). By the Demazure character formula
it therefore has character `κ_{w₀λ}`, the Schur polynomial `s_λ`
(`flagOrbitSpan_hasTorusCharacter`).
-/

open Schubert

namespace Demazure.HighestWeight

open FlagModule

noncomputable section

variable {n : ℕ}

/-- The diagonal torus acting on the flag-minor span. -/
def flagOrbitTorus (m : ColumnShape n) : DiagonalTorus n →* Module.End ℂ (flagOrbitSpan m) where
  toFun t :=
    { toFun := fun p => ⟨polynomialTorus n t p.val, flagOrbitSpan_torus_stable m t _ p.property⟩
      map_add' p q := Subtype.ext ((polynomialTorus n t).map_add p.val q.val)
      map_smul' c p := Subtype.ext ((polynomialTorus n t).map_smul c p.val) }
  map_one' := by
    apply LinearMap.ext
    intro p
    apply Subtype.ext
    change polynomialTorus n 1 p.val = p.val
    rw [map_one]
    rfl
  map_mul' s t := by
    apply LinearMap.ext
    intro p
    apply Subtype.ext
    change polynomialTorus n (s * t) p.val = polynomialTorus n s (polynomialTorus n t p.val)
    rw [map_mul]
    rfl

@[simp] theorem flagOrbitTorus_val (m : ColumnShape n) (t : DiagonalTorus n)
    (p : flagOrbitSpan m) : (flagOrbitTorus m t p).val = polynomialTorus n t p.val := rfl

/-- Column multiplicities are recovered from the dominant weight. -/
theorem columnsOfWeight_shapeWeight (m : ColumnShape n) : columnsOfWeight (shapeWeight m) = m := by
  induction n with
  | zero => funext i; exact i.elim0
  | succ n ih =>
    have htail : (fun i : Fin n => shapeWeight m i.succ) = shapeWeight (Fin.tail m) := by
      funext i
      have h := shapeWeight_cons_succ (m 0) (Fin.tail m) i
      rwa [Fin.cons_self_tail] at h
    have h0 : shapeWeight m 0 = m 0 + ∑ i, Fin.tail m i := by
      have h := shapeWeight_cons_zero (m 0) (Fin.tail m)
      rwa [Fin.cons_self_tail] at h
    show Fin.cons (shapeWeight m 0 - ∑ i, columnsOfWeight (fun i : Fin n => shapeWeight m i.succ) i)
      (columnsOfWeight (fun i : Fin n => shapeWeight m i.succ)) = m
    rw [htail, ih, h0, Nat.add_sub_cancel]
    exact Fin.cons_self_tail m

/-- The increasing composition `w₀λ`. -/
def reversedWeight (m : ColumnShape n) : Composition n := fun i => shapeWeight m (Fin.rev i)

theorem reversedWeight_monotone (m : ColumnShape n) : Monotone (reversedWeight m) :=
  fun _ _ hij => shapeWeight_antitone m (Fin.rev_le_rev.mpr hij)

theorem dominantComposition_reversedWeight (m : ColumnShape n) :
    dominantComposition (reversedWeight m) = shapeWeight m := by
  have hmono : @Monotone (Fin n) ℕᵒᵈ _ _ (reversedWeight m ∘ Fin.revPerm) := by
    intro i j hij
    change shapeWeight m (Fin.rev (Fin.revPerm j)) ≤ shapeWeight m (Fin.rev (Fin.revPerm i))
    rw [Fin.revPerm_apply, Fin.revPerm_apply, Fin.rev_rev, Fin.rev_rev]
    exact shapeWeight_antitone m hij
  have h := (Tuple.comp_sort_eq_comp_iff_monotone (α := ℕᵒᵈ) (f := reversedWeight m)
    (σ := Fin.revPerm)).mpr hmono
  funext i
  have hi : reversedWeight m (Fin.revPerm i) =
      reversedWeight m (compositionPermutation (reversedWeight m) i) := congrFun h i
  rw [dominantComposition, ← hi, Fin.revPerm_apply, reversedWeight, Fin.rev_rev]

theorem compositionShape_reversedWeight (m : ColumnShape n) :
    compositionShape (reversedWeight m) = m := by
  rw [compositionShape, dominantComposition_reversedWeight, columnsOfWeight_shapeWeight]

/-- The flag-minor span is the composition flag module of `w₀λ`. -/
theorem flagOrbitSpan_eq_compositionFlag (m : ColumnShape n) :
    flagOrbitSpan m = compositionFlag (reversedWeight m) := by
  have h := flagOrbitSpan_eq_flagDemazure_of_monotone (compositionShape (reversedWeight m))
    (compositionPermutation (reversedWeight m))
    (by rw [composition_extremalWeight]; exact reversedWeight_monotone m)
  rw [compositionShape_reversedWeight] at h
  rw [h, compositionFlag, compositionShape_reversedWeight]

/-- The character of the flag-minor span is `κ_{w₀λ} = s_λ`. -/
theorem flagOrbitSpan_hasTorusCharacter (m : ColumnShape n) :
    HasTorusCharacter (flagOrbitTorus m) (key (fun i => shapeWeight m (Fin.rev i))) := by
  have hc := (compositionFlagJosephPolo_and_character (reversedWeight m)).2
  intro w
  change _ = (toLaurent (key (reversedWeight m))).coeff w
  rw [← hc w]
  exact_mod_cast torusWeightSpace_finrank_eq (flagOrbitTorus m)
    (compositionFlagTorus (reversedWeight m))
    (LinearEquiv.ofEq _ _ (flagOrbitSpan_eq_compositionFlag m)) (fun _ _ => rfl) w

end
end Demazure.HighestWeight
