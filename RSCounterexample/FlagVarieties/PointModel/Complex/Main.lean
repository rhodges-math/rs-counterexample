import RSCounterexample.FlagVarieties.PointModel.Complex.BorelWeil
import RSCounterexample.FlagVarieties.PointModel.Complex.SectionBasis
import RSCounterexample.FlagVarieties.PointModel.Complex.ClosureRelation

/-!
# Normality of Schubert unions in type A (ring form)

Projective normality over `ℂ`, purely in the rings `ℂ[x_ij] ⊆ 𝒪(GL_n)`.
Namespace `FlagVarieties.PointModel.Complex`.

## Setting (`Basic`)

* `GLCoord n = 𝒪(GL_n)` (Tau Ceti's `TauCeti.GeneralLinear.CoordinateRing ℂ n`), evaluation
  `glEval g` at `g ∈ GL_n(ℂ)`; `IsBorel b` (upper triangular); `bruhatCell w = B ẇ B`;
  `orbitSet S = ⋃_{w ∈ S} B ẇ B = π⁻¹ X_S`; `orbitIdeal S` (functions vanishing there);
  `IsSemiInvOn Z η t` (`t(g b) = η(b) t(g)`); `GlobalSectionsConstant w`
  (`Γ(X_w, 𝒪) = ℂ`).

## The flag-minor algebra (`MinorSpan`, `MinorEval`, `VanishingIntersection`, `ChainCount`,
`HyperplaneSection`)

* `minorSpan m = A_λ` (`λ = shapeWeight m`), equal to the Demazure library's `flagSpan h`
  (`minorSpan_columnMultiplicity`).
* `vanishSpan m S = I_S^A ∩ A_λ`; `mem_vanishSpan`: it is the pointwise vanishing ideal on
  `orbitSet S`.
* `finrank_vanishSpan_add`: `dim (I_S^A ∩ A_λ) + #chainSet h S = dim A_λ` (the Demazure library's
  dimension count).
* **Intersection identity** `vanishSpan_inter`; **hyperplane-section identity**
  `vanishSpan_hyperplaneSectionSet`, with the chain bijection `card_chainSet_lowerSet`.

## Big cells (`Chart`, `UnitIdeal`)

* `chartMatrix v g = g β(g)`, entries ratios of flag minors; `exists_homogenization`.
* `exists_mem_bruhatCell` (Bruhat decomposition), `exists_partition_of_unity` (the `f_v^K` generate
  the unit ideal; Nullstellensatz).

## Main results

* `schubertUnion_normality` (**projective normality**): for a Bruhat ideal `S`, every function
  semi-invariant of weight `λ` on `π⁻¹ X_S` agrees there with an element of `A_λ`.
* `Sections`: `sectionSpace S η` (ring model of `H⁰(X_S, 𝓛(-η))`), `minorRestriction` with kernel
  `I_S^A ∩ A_λ` and surjective (`minorRestriction_surjective`), `finrank_sectionSpace`.
* `SectionBasis`: the standard-monomial basis `sectionBasis` and the torus weights
  `evalAt_diagonal_mul_flagColumnProduct`.
* `BorelWeil`: `borelWeil`, `semiInvSpace_univ`, `finrank_globalSections`.
* `ClosureRelation`: `cellIdeal_le_cellIdeal`, `orbitIdeal_lowerSet` (`π⁻¹ X_w` has the ideal of the
  single cell `B ẇ B`).

All theorems that need `GlobalSectionsConstant` take
`hglobalSections : ∀ w, GlobalSectionsConstant w` as an explicit hypothesis (the suffix
`_of_globalSectionsConstant`); `Normality/Unconditional` gives the hypothesis-free forms under the
plain names.
-/
