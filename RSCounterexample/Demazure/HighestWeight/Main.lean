import RSCounterexample.Demazure.HighestWeight.Irreducible
import RSCounterexample.Demazure.HighestWeight.Character
import RSCounterexample.Demazure.HighestWeight.Integration

/-!
# Endpoints: the flag-minor span is the irreducible module `V(λ)`

Namespace `Demazure.HighestWeight`. Here `V = flagOrbitSpan m` is the `GL_n(ℂ)`-span of the
highest flag polynomial `v_λ = highestFlag m`, with `λ = shapeWeight m`.

* Stability (E1): `isGLStable_iff_isLieStable`, `flagOrbitSpan_isGLStable`,
  `flagOrbitSpan_isLieStable`, `flagOrbitSpan_torus_stable`; every Demazure module lies in `V`:
  `flagDemazure_le_flagOrbitSpan`.
* E2: `V = D_{w₀}(λ)`: `flagOrbitSpan_eq_flagDemazure_longest`, and more generally
  `flagOrbitSpan_eq_flagDemazure_of_monotone`.
* E3: `V = U(𝔫⁻)·v_λ`: `flagOrbitSpan_eq_lowerCyclic`.
* E4: `v_λ` has weight `λ` and is killed by `𝔫⁺`, and the weight-`λ` space of `V` is `ℂ·v_λ`:
  `highestFlag_mem_weightSpace`, `highestFlag_upper_invariant`, `flagOrbitSpan_inf_weightSpace`.
* Character `s_λ = κ_{w₀λ}`: `flagOrbitSpan_hasTorusCharacter`.
* E5: the Fischer inner product, with `E_ab` adjoint to `E_ba`: `fischer_matrixUnitDerivation`.
* E6: the `𝔫⁺`-invariants of `V` are `ℂ·v_λ` (`flagOrbitSpan_upperInvariants`), and `V` is
  irreducible for `gl_n` and for `GL_n(ℂ)` (`flagOrbitSpan_irreducible_lie`,
  `flagOrbitSpan_irreducible`).
* E7, uniqueness of the irreducible module with highest weight `λ`:
  - abstractly, two irreducible `gl_n`-modules with nonzero highest-weight vectors of the same
    weight are isomorphic (`exists_equiv_of_isHighestWeightVector`);
  - for `GLModule`s (finite-dimensional `gl_n`-modules spanned by integral weight spaces), the
    flag-minor model `flagOrbitModule m` is irreducible (`flagOrbitModule_isIrreducible`), and every
    irreducible `GLModule` with a highest-weight vector of weight `λ` is isomorphic to it
    (`nonempty_iso_flagOrbitModule`, `exists_iso_flagOrbitModule`).
* Mathlib representations of `GL_n(ℂ)`:
  - the flag-minor span is an irreducible `Representation ℂ (GL (Fin n) ℂ)`
    (`flagOrbitRepresentation`, `flagOrbitRepresentation_isIrreducible`), integrating
    `flagOrbitModule m` (`flagOrbitModule_integrates`);
  - an irreducible representation integrating a `GLModule` with a highest-weight vector of weight
    `λ` is equivalent to it (`nonempty_equiv_flagOrbitRepresentation`).
-/
