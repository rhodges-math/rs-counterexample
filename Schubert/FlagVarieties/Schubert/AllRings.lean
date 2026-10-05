import Schubert.FlagVarieties.Schubert.PreimageLattice
import Schubert.FlagVarieties.LineBundle.BorelFlat

/-!
# Preimages of Schubert varieties over every commutative ring

Since `𝒪(B)` is flat over every `R` (`FlagVarieties.instFlatBorelCoord`), the orbit map
`π : GLₙ ⟶ Flₙ` is flat, and preimages of Schubert varieties are computed over every commutative
ring:

* `FlagVarieties.preimageIdeal_schubertVariety_commRing`: `π⁻¹(X_w)` is the closure of `B ẇ B`;
* `FlagVarieties.preimageIdeal_schubertUnion_commRing`: `π⁻¹(X_S) = ⋃_{w ∈ S} closure(B ẇ B)`.
-/

namespace FlagVarieties

universe u

variable (R : Type u) [CommRing R] (n : ℕ)

/-- **The orbit map `π : GLₙ ⟶ Flₙ` is flat**, over every commutative ring. -/
theorem flat_orbitMap_commRing : AlgebraicGeometry.Flat (FlagScheme.orbitMap R n) :=
  inferInstance

/-- **`π⁻¹(X_w)` is the closure of `B ẇ B`**, over every commutative ring. -/
theorem preimageIdeal_schubertVariety_commRing :
    ∀ w, preimageIdeal R n (schubertVariety R n w) = schubertOrbitIdeal R n w :=
  preimageIdeal_schubertVariety R n

/-- **The ideal of `π⁻¹(X_S)` is `⋂_{w ∈ S}` of the orbit ideals**, over every commutative ring. -/
theorem preimageIdeal_schubertUnion_commRing (S : Finset (Equiv.Perm (Fin n))) :
    preimageIdeal R n (schubertUnion R n S) = ⨅ w ∈ S, schubertOrbitIdeal R n w :=
  preimageIdeal_schubertUnion R n S

end FlagVarieties
