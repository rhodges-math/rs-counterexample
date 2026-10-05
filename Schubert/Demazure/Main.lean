import Schubert.Demazure.SchubertUnions.AtomCharacter
import Schubert.Demazure.SchubertUnions.BruhatRefinement
import Schubert.Demazure.SchubertUnions.Character
import Schubert.Demazure.SchubertUnions.Coset
import Schubert.Demazure.SchubertUnions.OrbitDuality
import Schubert.Demazure.SchubertUnions.RightKey
import Schubert.Demazure.Filtrations.SchubertLayerCharacters
import Schubert.Demazure.HighestWeight.Main
import Schubert.Demazure.HighestWeight.GLRepBridge

/-!
# The Demazure library: flag minors, Demazure modules, keys, atoms and standard monomials

`Schubert.Demazure` is the type-A standard-monomial layer over `ℂ`, in the polynomial model
`MatrixPolynomial n = ℂ[x_ij]`. It imports only Mathlib, Tau Ceti, `Schubert.GLRep` and
`Schubert.TypeA`. Namespace `Demazure`.

## Flag minors and Demazure modules (`Demazure.FlagModule`)

* `flagMinor`, `flagRowMinor k s`: the minor with rows `s` and columns `0, …, k`;
  `FlagMinorRowSet k`, `flagColumnProduct h T`: ordered products of flag minors.
* `extremalFlag m w`, `flagDemazure m w`: the Demazure module `D_w(λ) = U(𝔫⁺) · v_{wλ}`.
* `HasFlagDefiningChain h T w`: defining chains; `flagColumnProduct_linearIndependent_on_union`:
  standard-monomial independence on unions of orbits `U · ẇ`.
* `flagOrbitRestriction w`: restriction of polynomials to the orbit `U · ẇ`.

## Unions of Schubert varieties (`Demazure.SchubertUnions`)

* `demazureUnion m S = Σ_{w ∈ S} D_w(λ)`, `chainSet h S`, `unionRestriction S`;
  `demazureUnionDuality`: `D_S^∨ ≅` restrictions of flag-minor products to `⋃_{w ∈ S} U · ẇ`.
* `finrank_demazureUnion_eq`, `finrank_demazureUnion_inf_eq`: for a Bruhat ideal `S`
  (`BruhatLower S`), `dim (D_S)_μ = #{T ∈ chainSet h S | wt T = μ}`, for any column order `h`.
* `exists_rightKey`: right keys; `demazureUnion_inf`: `D_J ∩ D_K = D_{J ∩ K}`.
* `flagDemazure_hasTorusCharacter`: `ch D_w(λ) = κ_{wλ}`; `key_eq_sum_atom`: the Bruhat refinement
  `κ_{σλ} = Σ_{u ≤ σ} 𝒜_{uλ}`; `chainCharacter_boundary`: `ch D_{∂σ} = κ - 𝒜`.

## The flag-minor model of `V(λ)` (`Demazure.HighestWeight`)

* `flagOrbitSpan m`, `flagOrbitRepresentation m`: the irreducible representation of highest weight
  `λ = shapeWeight m`; uniqueness `nonempty_equiv_flagOrbitRepresentation`.
* `nonempty_equiv_flagOrbitRepresentation_irrep`: the Weyl module `GLRep.irrep ℂ n ν` of
  `Schubert.GLRep` is equivalent to the flag-minor model.
-/
