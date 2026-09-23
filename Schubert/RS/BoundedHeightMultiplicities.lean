import Schubert.RS.HeightMultiplicities

/-! A cutoff at least the requested degree retains all height multiplicities. -/

namespace Schubert.RS.HallLattice
noncomputable section

abbrev BoundedMultiplicities (k y B : ℕ) :=
  {e : Fin (y+1) → Fin (B+1) // ∑ h, (e h).val = k}

def boundedHeightMultiplicityEquiv (k y B : ℕ) (hk : k ≤ B) :
    WeakHeights k y ≃ BoundedMultiplicities k y B where
  toFun r :=
    ⟨fun h => ⟨(heightMultiplicityEquiv k y r).val h, by
      have hs := Finset.single_le_sum (fun h _ => Nat.zero_le ((heightMultiplicityEquiv k y r).val h))
        (Finset.mem_univ h)
      rw [(heightMultiplicityEquiv k y r).property] at hs
      omega⟩, (heightMultiplicityEquiv k y r).property⟩
  invFun e := (heightMultiplicityEquiv k y).symm ⟨fun h => (e.val h).val, e.property⟩
  left_inv r := (heightMultiplicityEquiv k y).symm_apply_apply r
  right_inv e := by
    apply Subtype.ext
    funext h
    apply Fin.ext
    exact congrArg (fun e => e.val h) ((heightMultiplicityEquiv k y).apply_symm_apply
      ⟨fun h => (e.val h).val, e.property⟩)

theorem boundedHeightMultiplicity_weight {R : Type*} [CommMonoid R]
    (k y B : ℕ) (hk : k ≤ B) (slot : Fin (y+1) → R) (r : WeakHeights k y) :
    (∏ q, slot (r.val q)) =
      ∏ h, slot h ^ ((boundedHeightMultiplicityEquiv k y B hk r).val h).val :=
  heightMultiplicity_weight slot r

theorem boundedMultiplicity_sum {R : Type*} [CommSemiring R]
    (k y B : ℕ) (hk : k ≤ B) (slot : Fin (y+1) → R) :
    (∑ e : BoundedMultiplicities k y B, ∏ h, slot h ^ (e.val h).val) =
      ∑ r : WeakHeights k y, ∏ q, slot (r.val q) := by
  classical
  rw [← Equiv.sum_comp (boundedHeightMultiplicityEquiv k y B hk)
    (fun e => ∏ h, slot h ^ (e.val h).val)]
  apply Finset.sum_congr rfl
  intro r _
  exact (boundedHeightMultiplicity_weight k y B hk slot r).symm

end
end Schubert.RS.HallLattice
