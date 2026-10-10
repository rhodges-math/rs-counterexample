import RSCounterexample.FlagVarieties.Richardson.Basic
import RSCounterexample.FlagVarieties.Richardson.Points
import RSCounterexample.FlagVarieties.Richardson.Translation

/-!
# Opposite Schubert varieties and Richardson varieties

* `Basic` (namespace `FlagVarieties`, over a commutative ring `R`): the opposite Borel subgroup
  scheme `OppBorelScheme R n` (`oppBorelIdeal`, `oppBorelInclusion`); the opposite Schubert
  variety `oppositeSchubertVariety R n w`, the scheme-theoretic image of `B⁻ ⟶ Fl_n`,
  `b ↦ b · ẇE•`; `oppositeSchubertUnion`; the Richardson variety
  `richardsonVariety R n w v = X_w ⊔ X^v` (scheme-theoretic intersection).
* `Points` (namespace `FlagVarieties.PointModel`, over a field `K`, in the ring model):
  `oppBruhatCell`, `oppOrbitSet`, `richardsonSet`; disjointness of the opposite cells; Deodhar's
  inequality `B u̇ B ∩ B⁻ u̇' B ≠ ∅ → u' ≤ u`; **`richardsonSet_nonempty_iff`**
  (`X_w ∩ X^v ≠ ∅ ⟺ v ≤ w`); torus-fixed points `isTorusFixed_iff` and
  **`isTorusFixed_mem_richardsonSet_iff`** (`u̇ B`, `v ≤ u ≤ w`; characteristic `0`).
* `Schemes` (namespace `FlagVarieties.Richardson`, scheme level, via the Plücker morphisms):
  **`richardsonVariety_eq_top`** (`v ≰ w → X_w ∩ X^v = ∅`, any ring),
  **`richardsonVariety_ne_top_iff`** (`X_w ∩ X^v ≠ ∅ ⟺ v ≤ w`, characteristic `0`), and the
  `T`-fixed points: `schubertVariety_le_ker_permFlag_iff` (`u̇E• ∈ X_w ⟺ u ≤ w`),
  `le_of_richardsonVariety_le_ker_permFlag` (`u̇E• ∈ X_w ∩ X^v → v ≤ u ≤ w`),
  `richardsonVariety_le_ker_permFlag` (`v̇E• ∈ X_w ∩ X^v` for `v ≤ w`).
* `Translation` (namespace `FlagVarieties.Richardson`): translation `translate R g` by
  `g ∈ GL_n(R)` through the action, an automorphism over `R` (`translateIso`); the involution
  `translateW₀`; **`oppositeSchubertVariety_eq_map`** (`X^v = t_{w₀}(X_{w₀ v})`, from
  `B⁻ = ẇ₀ B ẇ₀`); in characteristic `0`: **`oppositeSchubertVariety_le_iff`** (opposite closure
  relation, `X^u ⊆ X^v ⟺ v ≤ u`), `oppositeSchubertVariety_le_ker_permFlag_iff`
  (`u̇E• ∈ X^v ⟺ v ≤ u`), **`richardsonVariety_le_ker_permFlag_iff`** (the `T`-fixed points of
  `X_w ∩ X^v` are the `u̇E•` with `v ≤ u ≤ w`).
-/
