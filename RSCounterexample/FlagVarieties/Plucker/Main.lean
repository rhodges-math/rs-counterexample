import RSCounterexample.FlagVarieties.Plucker.Coordinates
import RSCounterexample.FlagVarieties.Plucker.ClosedImmersion
import RSCounterexample.FlagVarieties.Plucker.OrbitMapCoordinates

/-!
# Plücker coordinates and the Plücker embedding

**Ring and point level** (`Coordinates`, namespace `FlagVarieties.PointModel`, over a
field `K`):

* `pluckerVector`, `card_flagMinorRowSet` (`n.choose (k + 1)` coordinates in height `k`),
  `pluckerVector_ne_zero`.
* **`pluckerVector_proportional_iff`**: the Plücker map `GL_n(K)/B → ∏_k ℙ(∧^{k+1} Kⁿ)` is well
  defined and injective (point-level Plücker embedding of `Fl_n(K)`).
* **`𝒪(1) ↔ 𝓛(-ϖ_k)`** (characteristic `0`): `pluckerBasis` (the Plücker coordinates are a basis of
  `A_{ϖ_k}`), `pluckerSectionsEquiv` / `pluckerSectionBasis` (and of `H⁰(Fl_n, 𝓛(-ϖ_k))`; the
  hypothesis-free forms are in `Normality/Unconditional`), `finrank_sections_single`
  (`= n.choose (k + 1)`).

**Scheme level** (namespace `FlagVarieties.Plucker`, over a commutative ring `R`):

* `ProjSpace`: `projSpace R σ = Proj R[X_i : i ∈ σ]`, and `fromSections φ s h : X ⟶ ℙ(R^σ)` from a
  family of global sections generating the unit ideal (a trivialized rank-one quotient of `𝒪^σ`),
  with the preimages of the standard charts, invariance under a common unit and naturality.
* `AffineChart`: the structure morphism `projToSpec` (proper for finite `σ`); over `Spec C` with a
  unit coordinate, `fromSections` factors through the standard chart by an explicit ring map.
* `Morphism`: the big cells as an open cover of `Fl_n` and the glueing `glued` of morphisms given on
  each big cell by matrix sections that scale by units under upper triangular matrices.
* `Minors`: flag minors over a commutative ring; the big cell criterion by minors
  (`inBigCell_matrixFlag_iff_minor`) and the entries of `u` as minors of `ẇ u` (`entry_eq_minor`).
* `Embedding`: **`plucker R n k : Fl_n ⟶ ℙ(∧^{k+1} R^n)`** and the Segre–Plücker morphism
  **`pluckerSegre R n : Fl_n ⟶ ℙ(⊗_k ∧^{k+1} R^n)`**; on a big cell the latter is `Spec` of a
  surjection onto the chart ring (`exists_chart_surjective`: the chart coordinates are ratios of
  Plücker coordinates).
* `ClosedImmersion`: `pluckerSegre_preimage_chart` (the preimage of `D₊(p_{T_v})` is the big cell
  of `v`) and **`isClosedImmersion_pluckerSegre`**: the Plücker embedding is a closed immersion.
* `Identity`: on points, the flag of an invertible `g` goes to its Plücker coordinates
  (`ofRingFlag_plucker`); **`specOrbitMap_plucker`**: `π ≫ plucker R n k` is given by the flag
  minors of the generic matrix of `GL_n`; over a field, `pluckerSectionBasis_apply`: the Plücker
  basis of `H⁰(Fl_n, 𝓛(-ϖ_k))` is the family of these pulled-back coordinates.

Not formalized: `X_S` as a multi-`Proj` of `A/I_S`, `𝒪(1)` as a line bundle
on `Proj` (Mathlib has no twisting sheaves at our pin), hence the identification of its pullback
with `𝓛(-ϖ_k)` beyond the level of sections; the product map into the fibre product `∏_k ℙ`.
-/
