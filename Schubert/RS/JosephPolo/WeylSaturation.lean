import Schubert.RS.JosephPolo.CoordinateRestriction
import Schubert.RS.Representation.AdjacentSaturation

namespace Schubert.RS.Representation
noncomputable section
open FinPermutation

/-- A Weyl descent suffices even when the corresponding weight entries tie. -/
theorem adjacent_lowering_flagDemazure_stable_of_inverse_descent {n : ℕ}
    (m : ColumnShape n) (w : Equiv.Perm (Fin n)) (i : AdjacentPosition n)
    (h : w.symm i.right < w.symm i.left)
    {p : MatrixPolynomial n} (hp : p ∈ flagDemazure m w) :
    matrixUnitDerivation i.right i.left p ∈ flagDemazure m w := by
  apply cyclic_core_stability (flagDemazure m w) (extremalFlag m w)
    (fun r : PositiveRoot n => (matrixUnitDerivation r.val.1 r.val.2).toLinearMap)
    (matrixUnitDerivation i.right i.left).toLinearMap
    (fun Q hp hQ => upperCyclic_le_of_root_stable _ Q hp hQ)
    (upperCyclic_seed _) (fun r x hx => upperCyclic_root_stable _ r hx) _ _ hp
  · change matrixUnitDerivation i.right i.left (rowRename w (highestFlag m)) ∈ flagDemazure m w
    rw [matrixUnitDerivation_rowRename]
    have hz := rootDerivation_highestFlag ⟨(w.symm i.right,w.symm i.left),h⟩ m
    change matrixUnitDerivation (w.symm i.right) (w.symm i.left) (highestFlag m) = 0 at hz
    rw [hz,map_zero]
    exact Submodule.zero_mem _
  · intro r x hx
    exact adjacent_lower_upper_commutator_mem i r (flagDemazure m w) x
      (fun s => upperCyclic_root_stable _ s hx) (fun j => diagonal_flagDemazure_stable m w j hx)

/-- Actual polynomial saturation at a Weyl descent, including singular weights. -/
theorem flagDemazure_adjacent_saturation_of_inverse_descent {n : ℕ}
    (m : ColumnShape n) (w : Equiv.Perm (Fin n)) (i : AdjacentPosition n)
    (h : w.symm i.right < w.symm i.left) :
    loweringSaturation i.left i.right (flagDemazure m (Equiv.swap i.left i.right * w)) =
      flagDemazure m w := by
  have hw : extremalWeight m w i.left ≤ extremalWeight m w i.right :=
    shapeWeight_antitone m h.le
  apply le_antisymm
  · apply loweringSaturation_le_of_stable _ _ _ _
      (flagDemazure_reflection_le m w ⟨(i.left,i.right),i.left_lt_right⟩ hw)
    intro p hp
    exact adjacent_lowering_flagDemazure_stable_of_inverse_descent m w i h hp
  · apply upperCyclic_le_of_root_stable
    · rcases hw.eq_or_lt with he | hlt
      · have heq : flagDemazure m (Equiv.swap i.left i.right * w) = flagDemazure m w := by
          apply flagDemazure_eq_of_weight_eq
          rw [extremalWeight_swap_mul]
          funext j
          exact Equiv.apply_swap_eq_self he j
        rw [heq]
        exact le_loweringSaturation _ _ _ (upperCyclic_seed _)
      · exact extremalFlag_mem_loweringSaturation m w i.left i.right hlt
    · intro r p hp
      apply loweringSaturation_upper_stable i _ _ _ r hp
      · intro s q hq
        exact upperCyclic_root_stable _ s hq
      · intro j q hq
        exact diagonal_flagDemazure_stable _ _ j hq

theorem loweringSaturation_mono {n : ℕ} (a b : Fin n)
    {M N : Submodule ℂ (MatrixPolynomial n)} (h : M ≤ N) :
    loweringSaturation a b M ≤ loweringSaturation a b N :=
  loweringSaturation_le_of_stable a b M _ (h.trans (le_loweringSaturation a b N))
    (fun _ hp => loweringSaturation_lower_stable a b N hp)

end
end Schubert.RS.Representation
