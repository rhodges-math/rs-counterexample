import RSCounterexample.Paper.Family.FiltrationCorollary
import RSCounterexample.Paper.Filtrations.SectionRestriction

/-!
# Endpoints: Corollary 1.2 (filtrations of `P(−a) ⊗ P(−b)`)

Corollary 1.2 (`cor:intro-filtrations`) of the paper: for the family of Theorem 1.1 with
`(p − 2)(q − 2) > 2`, the `B`-module `P(−a) ⊗ P(−b)` admits neither a relative Schubert
filtration nor a Schubert filtration in Polo's sense; in particular this happens in type `A₂₇`.

How the paper's wording is formalized (namespace `Schubert.RS.Filtrations`, file
`Filtrations/Definitions.lean`):
* "`M` admits a relative Schubert filtration": `HasRelativeSchubertFiltration M`, a finite chain
  of `B`-submodules whose layers are isomorphic to minimal relative Schubert modules `Q(ν)`
  [van der Kallen].
* "`M` admits a Schubert filtration in Polo's sense (layers from unions)":
  `HasSchubertFiltration M`, a finite chain of `B`-submodules whose layers are isomorphic to
  section modules `H⁰(X_S, 𝓛(η))` over unions `X_S` of Schubert varieties, for antidominant `η`
  [Polo, 2.8].
* Over `SL_n` (file `Filtrations/SpecialLinear.lean`): `HasSLRelativeSchubertFiltration M` and
  `HasSLSchubertFiltration M` filter the restriction of `M` to the Borel subgroup of `SL_n`, with
  layers isomorphic as `B_SL`-modules to the same modules. These notions are weaker than the
  `GL_n` ones (`HasRelativeSchubertFiltration.hasSL`, `HasSchubertFiltration.hasSL`).

Statements, namespace `Schubert.RS.Family` (file `Family/FiltrationCorollary.lean`):
* `familyTensor P`, the module `P(−a) ⊗ P(−b)`, has character `κ_a κ_b`:
  `familyTensor_hasCharacter`.
* Each factor has an excellent filtration: `factors_hasExcellentFiltration`.
* Corollary 1.2: `not_hasRelativeSchubertFiltration`, `not_hasSchubertFiltration`, and over
  `SL_n`, `not_hasSLRelativeSchubertFiltration`, `not_hasSLSchubertFiltration`.
* Type `A_{4(p+q)−5}`: `rank_sub_one`. Type `A₂₇` at `(p, q) = (3, 5)`, `δ ≥ 8`:
  `typeA27_filtration_failure`.

Ingredients, namespace `Schubert.RS.Filtrations`:
* (1.7): `ch P(−u) = κ_u` (`dualJoseph_hasCharacter`) and `ch Q(−u) = 𝒜_u`
  (`minRelSchubert_hasCharacter`); the weight `ν` occurs in `Q(ν)`
  (`minRelSchubert_weightSpace_ne_bot`).
* The characters of Polo's layers are twisted sums of atoms, the character form of van der
  Kallen's Proposition 2.3.11: `schubertSectionModule_hasCharacter`.
* The obstruction: `atomPositive_of_hasRelativeSchubertFiltration`,
  `atomPositive_of_hasSchubertFiltration`, and over `SL_n`,
  `atomPositive_of_hasSLRelativeSchubertFiltration`, `atomPositive_of_hasSLSchubertFiltration`.
* The section module over `X_S` is the space of restrictions of flag-minor products to the union
  of the orbits `U·w`, `w ∈ S`: `sectionModuleOf_restrictionEquiv` and
  `sectionModuleOf_restrictionEquiv_apply`.
-/
