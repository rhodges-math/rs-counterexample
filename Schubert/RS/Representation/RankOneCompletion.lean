import Mathlib.Algebra.Lie.TensorProduct
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Data.Complex.Basic

namespace Schubert.RS.Representation
noncomputable section
universe u v
open LieModule Module TensorProduct

variable {L : Type v} [LieRing L] [LieAlgebra ℂ L]
  {M X : Type u} [AddCommGroup M] [Module ℂ M]
  [AddCommGroup X] [Module ℂ X] [LieRingModule L X] [LieModule ℂ L X]

/-- A finite rank-one completion, specified by its actual boundary and
universal property. Existence is deliberately not part of this interface.
For sl₂, `e,h` are its raising and Cartan elements and `E,H` are the Borel
operators on the source. All quantified targets are finite actual Lie modules. -/
structure IsRankOneCompletion (e h : L) (E H : Module.End ℂ M)
    (ι : M →ₗ[ℂ] X) [LieModule ℂ L X] [Module.Finite ℂ X] : Prop where
  injective : Function.Injective ι
  map_e : ∀ m, ι (E m) = ⁅e,ι m⁆
  map_h : ∀ m, ι (H m) = ⁅h,ι m⁆
  universal : ∀ (N : Type u) [AddCommGroup N] [Module ℂ N]
    [LieRingModule L N] [LieModule ℂ L N] [Module.Finite ℂ N]
    (g : M →ₗ[ℂ] N),
    (∀ m, g (E m) = ⁅e,g m⁆) → (∀ m, g (H m) = ⁅h,g m⁆) →
    ∃! Φ : X →ₗ⁅ℂ,L⁆ N, ∀ m, Φ (ι m) = g m

namespace IsRankOneCompletion
variable [Module.Finite ℂ X] {e h : L} {E H : Module.End ℂ M} {ι : M →ₗ[ℂ] X}
  (C : IsRankOneCompletion e h E H ι)
  {N : Type u} [AddCommGroup N] [Module ℂ N] [LieRingModule L N]
  [LieModule ℂ L N] [Module.Finite ℂ N]

def lift (g : M →ₗ[ℂ] N)
    (he : ∀ m, g (E m) = ⁅e,g m⁆) (hh : ∀ m, g (H m) = ⁅h,g m⁆) : X →ₗ⁅ℂ,L⁆ N :=
  Classical.choose (C.universal N g he hh)

theorem lift_boundary (g : M →ₗ[ℂ] N)
    (he : ∀ m, g (E m) = ⁅e,g m⁆) (hh : ∀ m, g (H m) = ⁅h,g m⁆) (m : M) :
    C.lift g he hh (ι m) = g m :=
  (Classical.choose_spec (C.universal N g he hh)).1 m

include C in
theorem hom_ext {Φ Ψ : X →ₗ⁅ℂ,L⁆ N}
    (hh : ∀ m, Φ (ι m) = Ψ (ι m)) : Φ = Ψ := by
  let g := Φ.toLinearMap.comp ι
  have he : ∀ m, g (E m) = ⁅e,g m⁆ := by
    intro m
    change Φ (ι (E m)) = ⁅e,Φ (ι m)⁆
    rw [C.map_e,Φ.map_lie]
  have hh' : ∀ m, g (H m) = ⁅h,g m⁆ := by
    intro m
    change Φ (ι (H m)) = ⁅h,Φ (ι m)⁆
    rw [C.map_h,Φ.map_lie]
  obtain ⟨F,hF,hu⟩ := C.universal N g he hh'
  exact (hu Φ (fun _ => rfl)).trans (hu Ψ (fun m => (hh m).symm)).symm

end IsRankOneCompletion
end
end Schubert.RS.Representation
