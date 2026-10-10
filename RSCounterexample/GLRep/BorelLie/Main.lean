import RSCounterexample.GLRep.BorelLie.Brackets
import RSCounterexample.GLRep.BorelLie.BModule
import RSCounterexample.GLRep.BorelLie.SectionModule

/-!
# The `B ↔ (𝔫⁺, T)` dictionary for arbitrary rational `B`-representations

Namespace `GLRep`, building on `GLRep/Borel/*` (`BorelLie.lean`: the differentials
`D_ab = dρ(E_ab)` of a rational representation of `B` in characteristic `0`, `forall_mem_iff`,
`forall_intertwining_iff`, `conj_borelLie`).

* `Brackets` (over an infinite field of characteristic `0`): the `D_ab` satisfy the relations of
  the matrix units of `𝔫⁺`, `borelLie_comm` (`[D_ab, D_cd] = 0` for `b ≠ c`, `a ≠ d`) and
  `borelLie_bracket` (`[D_ab, D_bc] = D_ac`); generation by the simple roots,
  `forall_mem_iff_simple` and `forall_intertwining_iff_simple` (`B`-stability and
  `B`-equivariance are tested on the torus and the `D_{a,a+1}`).
* `BModule` (over `ℂ`): **the functor to the `BModule`s of the Demazure library**,
  `IsRationalBorelRep.toBModule : BModule n` (`𝔫⁺` acting by the Lie algebra map
  `nil X = Σ_{a<b} X_ab D_ab`, the torus through `B`), with the dictionary
  `forall_mem_iff_bModule` / `subrepresentationOrderIso` (subrepresentations = `B`-submodules),
  `forall_intertwining_iff_bModule` / `homEquiv` (intertwiners = `B`-module homomorphisms),
  `isoEquiv` (equivalences = `B`-module isomorphisms).
* `SectionModule`: `sectionBModule m hS` is the image of `H⁰(X_S, 𝓛(−λ))` under the functor
  (`sectionBModuleIsoToBModule`, `sectionBModule_nil_eq`), hence
  `toBModuleIsoDual : toBModule (H⁰(X_S, 𝓛(−λ))) ≃ᴮ (demazureUnionModule m S)^∨`.

Not formalized: the differential of the torus action (the `𝔱`-part of `𝔟 = 𝔱 ⊕ 𝔫⁺`); the `BModule`s
of the Demazure library use the group torus, so the `(𝔫⁺, T)` form above is the one needed.
-/
