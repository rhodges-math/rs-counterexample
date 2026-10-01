import Schubert.RS.Quiver.Multiplicity

/-!
# Saturation of quiver multiplicities

STATUS: proved in this library: `Schubert.RS.quiverSaturation_holds`
(`Schubert/RS/Quiver/Saturation.lean`, from the library `Schubert/QuiverInvariants`).

For a quiver without oriented cycles, a dimension vector and a dominant weight `λ` of
`∏_p GL(dim p)`, the multiplicities `m_Q(λ)` of the irreducible modules in the coordinate ring of
the representation space are saturated: `m_Q(N λ) > 0` for some `N ≥ 1` implies `m_Q(λ) > 0`.

This is the theorem of Derksen and Weyman on semi-invariants of quivers, in the form for
multiplicities in the coordinate ring (H. Derksen, J. Weyman, *Semi-invariants of quivers and
saturation for Littlewood–Richardson coefficients*, J. Amer. Math. Soc. 13 (2000);
V. Baldoni, M. Vergne, M. Walter, *Horn conditions for quiver subrepresentations and the moment
map*, arXiv:1901.07194, §8; M. Vergne, M. Walter, arXiv:2303.14821, §1).

The multiplicity is `Schubert.RS.Quiver.ForwardQuiver.multiplicity`. Listing the vertices in a
topological order loses no generality, so `ForwardQuiver` covers every acyclic quiver.
-/

open Schubert.RS.Quiver

namespace Schubert.RS

/-- **Saturation of quiver multiplicities.** Let `Q` be a quiver without oriented cycles, with its
vertices listed in a topological order, and let `lam` be a dominant weight of `∏_p GL(dim p)`. If
the multiplicity of the irreducible module with highest weight `N • lam` in the coordinate ring of
the representation space is positive for some `N ≥ 1`, then so is the multiplicity for `lam`. -/
def QuiverSaturation : Prop :=
  ∀ (Q : ForwardQuiver) (lam : Q.Weight), Q.IsDominant lam →
    ∀ N : ℕ, 0 < N → 0 < Q.multiplicity (N • lam) → 0 < Q.multiplicity lam

end Schubert.RS
