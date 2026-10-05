import Schubert.FlagVarieties.Schubert.PreimageLattice
import Schubert.FlagVarieties.Normality.OrbitIdealComparison
import Schubert.Demazure.SchubertUnions.Character

/-!
# The preimage of a Schubert union in `GLₙ`, and the ring model

Over an infinite field `K` the ideal of `π⁻¹(X_S) ⊆ GLₙ` is the ideal of functions vanishing on
`⋃_{w ∈ S} B ẇ B` (`FlagVarieties.preimageIdeal_schubertUnion_eq_orbitIdeal`). It combines
`FlagVarieties.preimageIdeal_schubertUnion` with
`FlagVarieties.PointModel.orbitIdeal_eq_iInf_schubertOrbitIdeal`.
Over `ℂ` it is `FlagVarieties.preimageIdeal_schubertUnion_eq_orbitIdeal_complex`.
-/

noncomputable section

namespace FlagVarieties

universe u

/-- **`π⁻¹(X_S)` is the closure of `⋃_{w ∈ S} B ẇ B`**, over an infinite field. -/
theorem preimageIdeal_schubertUnion_eq_orbitIdeal (K : Type u) [Field K] [Infinite K] (n : ℕ)
    (S : Finset (Equiv.Perm (Fin n))) :
    preimageIdeal K n (schubertUnion K n S) = PointModel.orbitIdeal K S := by
  have : Module.Free K (BorelCoord K n) := Module.Free.of_divisionRing K _
  have : Module.Flat K (BorelCoord K n) := Module.Flat.of_free
  rw [preimageIdeal_schubertUnion, PointModel.orbitIdeal_eq_iInf_schubertOrbitIdeal]

/-- **The preimage of a Schubert union, over `ℂ`**: for a nonempty lower set `S`, the ideal of
`π⁻¹(X_S)` is the ideal of functions vanishing on `⋃_{w ∈ S} B ẇ B`. -/
theorem preimageIdeal_schubertUnion_eq_orbitIdeal_complex (n : ℕ) :
    ∀ S : Finset (Equiv.Perm (Fin n)), S.Nonempty → Demazure.SchubertUnions.BruhatLower S →
      preimageIdeal ℂ n (schubertUnion ℂ n S) = PointModel.Complex.orbitIdeal S := fun S _ _ => by
  have : Infinite ℂ := Infinite.of_injective (Nat.cast : ℕ → ℂ) Nat.cast_injective
  exact preimageIdeal_schubertUnion_eq_orbitIdeal ℂ n S

end FlagVarieties
