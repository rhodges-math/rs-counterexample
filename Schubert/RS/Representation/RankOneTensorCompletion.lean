import Schubert.RS.Representation.RankOneTensorAdjunction

namespace Schubert.RS.Representation
noncomputable section
universe u v
open LieModule Module TensorProduct

variable {L : Type v} [LieRing L] [LieAlgebra ℂ L]
  {M X : Type u} [AddCommGroup M] [Module ℂ M]
  [AddCommGroup X] [Module ℂ X] [LieRingModule L X] [LieModule ℂ L X]
  [Module.Finite ℂ X] {e h : L} {E H : Module.End ℂ M} {ι : M →ₗ[ℂ] X}
  (C : IsRankOneCompletion e h E H ι)
  (R : Type u) [AddCommGroup R] [Module ℂ R] [LieRingModule L R]
  [LieModule ℂ L R] [Module.Finite ℂ R]

include C in
/-- Tensor identity for an actual finite completion. Tensoring an integrable
factor preserves the universal extension property and the injective boundary.
This is conditional on the exhibited completion; it asserts no existence
for an arbitrary source Borel module. -/
theorem IsRankOneCompletion.tensor :
    IsRankOneCompletion e h (tensorBorelOperator (R := R) e E)
      (tensorBorelOperator (R := R) h H) (ι.lTensor R) where
  injective := Module.Flat.lTensor_preserves_injective_linearMap ι C.injective
  map_e := tensorBoundary_intertwines e E ι C.map_e
  map_h := tensorBoundary_intertwines h H ι C.map_h
  universal := by
    intro N _ _ _ _ _ g ge gh
    let gc := tensorFlipCurry g
    have gce : ∀ m, gc (E m) = ⁅e,gc m⁆ := tensorFlipCurry_intertwines e E g ge
    have gch : ∀ m, gc (H m) = ⁅h,gc m⁆ := tensorFlipCurry_intertwines h H g gh
    let F := C.lift gc gce gch
    let Φ := tensorFlipLiftLie F
    have hΦ : ∀ z, Φ (ι.lTensor R z) = g z := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul r m =>
          change tensorFlipLiftLie F (ι.lTensor R (r ⊗ₜ[ℂ] m)) = g (r ⊗ₜ[ℂ] m)
          rw [LinearMap.lTensor_tmul,tensorFlipLiftLie_tmul]
          exact LinearMap.congr_fun (C.lift_boundary gc gce gch m) r
      | add z w hz hw => simp only [map_add,hz,hw]
    refine ⟨Φ,hΦ,?_⟩
    intro Ψ hΨ
    apply tensorFlipCurryLie_injective
    apply C.hom_ext
    intro m
    apply LinearMap.ext
    intro r
    change Ψ (r ⊗ₜ[ℂ] ι m) = Φ (r ⊗ₜ[ℂ] ι m)
    exact (hΨ (r ⊗ₜ[ℂ] m)).trans (hΦ (r ⊗ₜ[ℂ] m)).symm

end
end Schubert.RS.Representation
