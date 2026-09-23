import Schubert.RS.Representation.RankOneCompletion
import Mathlib.Algebra.Lie.Submodule

namespace Schubert.RS.Representation
noncomputable section
universe u v

variable {L : Type v} [LieRing L] [LieAlgebra ℂ L]
  {M X : Type u} [AddCommGroup M] [Module ℂ M]
  [AddCommGroup X] [Module ℂ X] [LieRingModule L X] [LieModule ℂ L X]
  [Module.Finite ℂ X] {e h : L} {E H : Module.End ℂ M} {ι : M →ₗ[ℂ] X}
  (C : IsRankOneCompletion e h E H ι)

include C in
/-- The boundary generates its actual universal completion as a Lie module.
This follows from universality into the generated submodule, not dimensions. -/
theorem IsRankOneCompletion.submodule_eq_top (Y : LieSubmodule ℂ L X)
    (hY : ∀ m, ι m∈Y) : Y=⊤ := by
  let g : M →ₗ[ℂ] Y := ι.codRestrict Y.toSubmodule hY
  have ge : ∀ m, g (E m)=⁅e,g m⁆ := by
    intro m
    apply Subtype.ext
    exact C.map_e m
  have gh : ∀ m, g (H m)=⁅h,g m⁆ := by
    intro m
    apply Subtype.ext
    exact C.map_h m
  let Φ := C.lift g ge gh
  have hΦ : Y.incl.comp Φ=(LieModuleHom.id : X →ₗ⁅ℂ,L⁆ X) := by
    apply C.hom_ext
    intro m
    change (Φ (ι m):X)=ι m
    rw [IsRankOneCompletion.lift_boundary]
    rfl
  apply top_unique
  intro x hx
  have hh := LieModuleHom.congr_fun hΦ x
  change (Φ x:X)=x at hh
  rw [← hh]
  exact (Φ x).property

include C in
theorem IsRankOneCompletion.mem_of_boundary (Y : LieSubmodule ℂ L X)
    (hY : ∀ m, ι m∈Y) (x : X) : x∈Y := by
  rw [C.submodule_eq_top Y hY]
  trivial

end
end Schubert.RS.Representation
