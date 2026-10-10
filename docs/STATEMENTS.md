# Statements of the paper and their Lean counterparts

Each labelled statement of *Counterexamples to the Reiner–Shimozono conjecture and the
failure of Schubert filtrations* (Reuven Hodges, 2026),
[arXiv:2609.28169](https://arxiv.org/abs/2609.28169), with its status and the Lean
declarations that formalize it, in the order of the paper. The index also covers the
displayed identities of the introduction, and the three standard results the paper cites for
Theorems 1.4 and 5.3, which are proved here. Numbers are those printed in the paper
(arXiv:2609.28169v2), and labels are its LaTeX labels; a statement without a number is given
with its section. A short note follows a statement whose Lean statement or proof differs from
the paper. Names are shown without the prefix `Schubert.RS.`; paths are relative to the
repository root.

| Statement | Label | Status |
| --- | --- | --- |
| Equation (1.3) | `eq:intro-bru-refinement` | formalized |
| Theorem 1.1 | `thm:intro-family` | formalized |
| Equation (1.7) | `eq:intro-geometric-characters` | formalized |
| Corollary 1.2 | `cor:intro-filtrations` | formalized |
| Corollary 1.3 | `cor:intro-lascoux` | formalized |
| Equation (1.8) | `eq:intro-duality` | formalized |
| Theorem 1.4 | `thm:intro-quiver-polytope` | formalized |
| Corollary 1.5 | `cor:intro-quiver-density` | formalized |
| Lemma 2.4 | `lem:duality` | formalized |
| Proposition 2.13 | `prop:window` | formalized |
| Lemma 3.1 | `lem:hall-determinant` | formalized |
| Lemma 3.8 | `lem:hall-flags` | formalized |
| Definition 3.9 | `def:paired-target` | formalized |
| Proposition 3.11 | `prop:paired-reduction` | formalized |
| Lemma 4.1 | `lem:two-source-count` | formalized |
| Definition 5.1 | `def:quiver-triple` | formalized |
| Theorem 5.3 | `thm:quiver-coefficient` | formalized |
| Multiplicities of polynomial representations of products of general linear groups from their characters (Section 5.1) | — | formalized |
| Saturation of quiver multiplicities (Derksen–Weyman; Section 5.1) | — | formalized |
| Polynomial-time rational feasibility of integer linear systems (Section 5.1) | — | formalized |
| Proposition 5.8 | `prop:quiver-two-source` | formalized |

## Statements

### Equation (1.3) (`eq:intro-bru-refinement`)

Status: **formalized**

Cited in the paper and proved here, by induction on the length of $\sigma$.

- `SchubertUnions.key_eq_sum_atom` ([RSCounterexample/Paper/SchubertUnions/BruhatRefinement.lean](../RSCounterexample/Paper/SchubertUnions/BruhatRefinement.lean))

### Theorem 1.1 (`thm:intro-family`)

Status: **formalized**

Here $\[\mathcal A\_c\]f$ is defined by the right side of (2.5) and shown to be the coefficient of $\mathcal A\_c$ in the atom expansion of $f$.

- `Family.atomCoefficient_eq` ([RSCounterexample/Paper/Family/Main.lean](../RSCounterexample/Paper/Family/Main.lean))
- `Family.atomCoefficient_factorization` ([RSCounterexample/Paper/Family/Main.lean](../RSCounterexample/Paper/Family/Main.lean))
- `Family.atomCoefficient_neg_iff` ([RSCounterexample/Paper/Family/Main.lean](../RSCounterexample/Paper/Family/Main.lean))
- `Family.existsUnique_atomExpansion` ([RSCounterexample/Paper/Family/Main.lean](../RSCounterexample/Paper/Family/Main.lean))
- `Family.not_atomPositive` ([RSCounterexample/Paper/Family/Main.lean](../RSCounterexample/Paper/Family/Main.lean))
- `Family.rank28_atomCoefficient` ([RSCounterexample/Paper/Family/Main.lean](../RSCounterexample/Paper/Family/Main.lean))
- `Family.rank28_not_atomPositive` ([RSCounterexample/Paper/Family/Main.lean](../RSCounterexample/Paper/Family/Main.lean))
- `Family.reiner_shimozono_false` ([RSCounterexample/Paper/Family/Main.lean](../RSCounterexample/Paper/Family/Main.lean))
- `Family.atomCoefficient_eq_narayana` ([RSCounterexample/Paper/Family/Extras.lean](../RSCounterexample/Paper/Family/Extras.lean))
- `Family.atomCoefficient_eq_paper` ([RSCounterexample/Paper/Family/Extras.lean](../RSCounterexample/Paper/Family/Extras.lean))
- `Family.atomCoefficient_threeFive` ([RSCounterexample/Paper/Family/Extras.lean](../RSCounterexample/Paper/Family/Extras.lean))
- `Family.atomCoefficient_fourFour` ([RSCounterexample/Paper/Family/Extras.lean](../RSCounterexample/Paper/Family/Extras.lean))
- `Family.isLeast_rank_of_negative` ([RSCounterexample/Paper/Family/Extras.lean](../RSCounterexample/Paper/Family/Extras.lean))
- `Family.narayana` ([RSCounterexample/Paper/Family/Narayana.lean](../RSCounterexample/Paper/Family/Narayana.lean))
- `Family.Parameters` ([RSCounterexample/Paper/Family/Data.lean](../RSCounterexample/Paper/Family/Data.lean))
- `Family.a` ([RSCounterexample/Paper/Family/Data.lean](../RSCounterexample/Paper/Family/Data.lean))
- `Family.b` ([RSCounterexample/Paper/Family/Data.lean](../RSCounterexample/Paper/Family/Data.lean))
- `Family.c` ([RSCounterexample/Paper/Family/Data.lean](../RSCounterexample/Paper/Family/Data.lean))
- `atomCoefficient_spec` ([RSCounterexample/Paper/AtomCoefficientSpec.lean](../RSCounterexample/Paper/AtomCoefficientSpec.lean))
- `atomCoefficient_eq_of_expansion` ([RSCounterexample/Paper/AtomCoefficientSpec.lean](../RSCounterexample/Paper/AtomCoefficientSpec.lean))
- `Family.isHallTriple_family` ([RSCounterexample/Paper/Family/HallPartition.lean](../RSCounterexample/Paper/Family/HallPartition.lean))
- `Family.atomCoefficient_eq_paired` ([RSCounterexample/Paper/Family/HallPartition.lean](../RSCounterexample/Paper/Family/HallPartition.lean))

### Equation (1.7) (`eq:intro-geometric-characters`)

Status: **formalized**

The proof uses standard-monomial bases and restriction to the Schubert boundary, instead of the Demazure recurrence and van der Kallen's exact sequence.

- `FlagVarieties.ch_dualJoseph_negWeight` ([RSCounterexample/FlagVarieties/Modules/Geometric.lean](../RSCounterexample/FlagVarieties/Modules/Geometric.lean))
- `Geometric.ch_geometricMinimalRelativeSchubert_negWeight` ([RSCounterexample/Paper/Geometric/SchemeRelative.lean](../RSCounterexample/Paper/Geometric/SchemeRelative.lean))
- `Geometric.geometricMinimalRelativeSchubert_weightSpace_ne_bot` ([RSCounterexample/Paper/Geometric/SchemeRelative.lean](../RSCounterexample/Paper/Geometric/SchemeRelative.lean))

Algebraic model:

- `Filtrations.dualJoseph_hasCharacter` ([RSCounterexample/Paper/Filtrations/SectionModules.lean](../RSCounterexample/Paper/Filtrations/SectionModules.lean))
- `Filtrations.minRelSchubert_hasCharacter` ([RSCounterexample/Paper/Filtrations/RelativeSchubertCharacters.lean](../RSCounterexample/Paper/Filtrations/RelativeSchubertCharacters.lean))

### Corollary 1.2 (`cor:intro-filtrations`)

Status: **formalized**

Here $X\_w$ is the scheme-theoretic image of $b\mapsto bwB$ in the flag scheme over $\mathbb C$. In Polo's case the proof uses the characters of the layers instead of van der Kallen's Proposition 2.3.11.

- `Geometric.not_hasGeometricRelativeSchubertFiltration` ([RSCounterexample/Paper/Geometric/SchemeRelative.lean](../RSCounterexample/Paper/Geometric/SchemeRelative.lean))
- `Geometric.not_hasGeometricSchubertFiltration` ([RSCounterexample/Paper/Geometric/SchemeCorollary.lean](../RSCounterexample/Paper/Geometric/SchemeCorollary.lean))
- `Geometric.not_hasGeometricSLRelativeSchubertFiltration` ([RSCounterexample/Paper/Geometric/SchemeRelative.lean](../RSCounterexample/Paper/Geometric/SchemeRelative.lean))
- `Geometric.not_hasGeometricSLSchubertFiltration` ([RSCounterexample/Paper/Geometric/SchemeRelative.lean](../RSCounterexample/Paper/Geometric/SchemeRelative.lean))
- `Geometric.typeA27_geometricFiltration_failure` ([RSCounterexample/Paper/Geometric/SchemeRelative.lean](../RSCounterexample/Paper/Geometric/SchemeRelative.lean))
- `Geometric.geometricFamilyTensor` ([RSCounterexample/Paper/Geometric/SchemeCorollary.lean](../RSCounterexample/Paper/Geometric/SchemeCorollary.lean))
- `Geometric.ch_geometricFamilyTensor` ([RSCounterexample/Paper/Geometric/SchemeCorollary.lean](../RSCounterexample/Paper/Geometric/SchemeCorollary.lean))
- `FlagVarieties.dualJoseph` ([RSCounterexample/FlagVarieties/Modules/Geometric.lean](../RSCounterexample/FlagVarieties/Modules/Geometric.lean))
- `Geometric.geometricMinimalRelativeSchubert` ([RSCounterexample/Paper/Geometric/SchemeRelative.lean](../RSCounterexample/Paper/Geometric/SchemeRelative.lean))
- `Geometric.geometricBoundaryRestrict` ([RSCounterexample/Paper/Geometric/SchemeRelative.lean](../RSCounterexample/Paper/Geometric/SchemeRelative.lean))
- `Geometric.IsGeometricSchubertLayer` ([RSCounterexample/Paper/Geometric/SchemeCorollary.lean](../RSCounterexample/Paper/Geometric/SchemeCorollary.lean))
- `Geometric.IsGeometricMinimalRelativeSchubertLayer` ([RSCounterexample/Paper/Geometric/SchemeRelative.lean](../RSCounterexample/Paper/Geometric/SchemeRelative.lean))
- `Geometric.HasGeometricRelativeSchubertFiltration` ([RSCounterexample/Paper/Geometric/SchemeRelative.lean](../RSCounterexample/Paper/Geometric/SchemeRelative.lean))
- `Geometric.HasGeometricSchubertFiltration` ([RSCounterexample/Paper/Geometric/SchemeRelative.lean](../RSCounterexample/Paper/Geometric/SchemeRelative.lean))
- `Geometric.HasGeometricSLRelativeSchubertFiltration` ([RSCounterexample/Paper/Geometric/SchemeRelative.lean](../RSCounterexample/Paper/Geometric/SchemeRelative.lean))
- `Geometric.HasGeometricSLSchubertFiltration` ([RSCounterexample/Paper/Geometric/SchemeRelative.lean](../RSCounterexample/Paper/Geometric/SchemeRelative.lean))
- `FlagVarieties.schubertVariety` ([RSCounterexample/FlagVarieties/Schubert/Basic.lean](../RSCounterexample/FlagVarieties/Schubert/Basic.lean))
- `FlagVarieties.schubertUnion` ([RSCounterexample/FlagVarieties/Schubert/Basic.lean](../RSCounterexample/FlagVarieties/Schubert/Basic.lean))
- `FlagVarieties.schubertBoundary` ([RSCounterexample/FlagVarieties/Schubert/Basic.lean](../RSCounterexample/FlagVarieties/Schubert/Basic.lean))
- `FlagVarieties.lineBundle` ([RSCounterexample/FlagVarieties/LineBundle/Basic.lean](../RSCounterexample/FlagVarieties/LineBundle/Basic.lean))
- `FlagVarieties.sections` ([RSCounterexample/FlagVarieties/LineBundle/Basic.lean](../RSCounterexample/FlagVarieties/LineBundle/Basic.lean))
- `FlagVarieties.sectionsRep` ([RSCounterexample/FlagVarieties/LineBundle/BorelRep.lean](../RSCounterexample/FlagVarieties/LineBundle/BorelRep.lean))
- `FlagVarieties.sectionsEquivSemiInvariants` ([RSCounterexample/FlagVarieties/LineBundle/SectionsAsSemiInvariants.lean](../RSCounterexample/FlagVarieties/LineBundle/SectionsAsSemiInvariants.lean))
- `FlagVarieties.sectionsRestrict` ([RSCounterexample/FlagVarieties/LineBundle/SectionsRestriction.lean](../RSCounterexample/FlagVarieties/LineBundle/SectionsRestriction.lean))
- `FlagVarieties.sectionsRestrictHom_eq_sectionsRestrict` ([RSCounterexample/FlagVarieties/LineBundle/SectionsRestriction.lean](../RSCounterexample/FlagVarieties/LineBundle/SectionsRestriction.lean))
- `FlagVarieties.preimageIdeal_schubertUnion_eq_orbitIdeal_complex` ([RSCounterexample/FlagVarieties/Schubert/UnionPreimage.lean](../RSCounterexample/FlagVarieties/Schubert/UnionPreimage.lean))
- `FlagVarieties.globalSectionsConstant_complex` ([RSCounterexample/FlagVarieties/Schubert/GlobalSectionsRingForm.lean](../RSCounterexample/FlagVarieties/Schubert/GlobalSectionsRingForm.lean))
- `FlagVarieties.geometricSectionEquiv` ([RSCounterexample/FlagVarieties/Modules/Geometric.lean](../RSCounterexample/FlagVarieties/Modules/Geometric.lean))
- `FlagVarieties.dualJosephEquiv` ([RSCounterexample/FlagVarieties/Modules/Geometric.lean](../RSCounterexample/FlagVarieties/Modules/Geometric.lean))
- `Geometric.geometricMinimalRelativeSchubertEquiv` ([RSCounterexample/Paper/Geometric/SchemeRelative.lean](../RSCounterexample/Paper/Geometric/SchemeRelative.lean))
- `Geometric.isGeometricSchubertLayer_iff` ([RSCounterexample/Paper/Geometric/SchemeCorollary.lean](../RSCounterexample/Paper/Geometric/SchemeCorollary.lean))
- `Geometric.isGeometricMinimalRelativeSchubertLayer_iff` ([RSCounterexample/Paper/Geometric/SchemeRelative.lean](../RSCounterexample/Paper/Geometric/SchemeRelative.lean))
- `FlagVarieties.sectionBModuleIso` ([RSCounterexample/FlagVarieties/Modules/BModuleModel.lean](../RSCounterexample/FlagVarieties/Modules/BModuleModel.lean))

Algebraic model:

- `Family.not_hasRelativeSchubertFiltration` ([RSCounterexample/Paper/Family/FiltrationCorollary.lean](../RSCounterexample/Paper/Family/FiltrationCorollary.lean))
- `Family.not_hasSchubertFiltration` ([RSCounterexample/Paper/Family/FiltrationCorollary.lean](../RSCounterexample/Paper/Family/FiltrationCorollary.lean))
- `Family.not_hasSLRelativeSchubertFiltration` ([RSCounterexample/Paper/Family/FiltrationCorollary.lean](../RSCounterexample/Paper/Family/FiltrationCorollary.lean))
- `Family.not_hasSLSchubertFiltration` ([RSCounterexample/Paper/Family/FiltrationCorollary.lean](../RSCounterexample/Paper/Family/FiltrationCorollary.lean))
- `Family.rank_sub_one` ([RSCounterexample/Paper/Family/FiltrationCorollary.lean](../RSCounterexample/Paper/Family/FiltrationCorollary.lean))
- `Family.typeA27_filtration_failure` ([RSCounterexample/Paper/Family/FiltrationCorollary.lean](../RSCounterexample/Paper/Family/FiltrationCorollary.lean))
- `Family.factors_hasExcellentFiltration` ([RSCounterexample/Paper/Family/FiltrationCorollary.lean](../RSCounterexample/Paper/Family/FiltrationCorollary.lean))
- `Family.familyTensor` ([RSCounterexample/Paper/Family/FiltrationCorollary.lean](../RSCounterexample/Paper/Family/FiltrationCorollary.lean))
- `Family.familyTensor_hasCharacter` ([RSCounterexample/Paper/Family/FiltrationCorollary.lean](../RSCounterexample/Paper/Family/FiltrationCorollary.lean))
- `Filtrations.HasRelativeSchubertFiltration` ([RSCounterexample/Paper/Filtrations/Definitions.lean](../RSCounterexample/Paper/Filtrations/Definitions.lean))
- `Filtrations.HasSchubertFiltration` ([RSCounterexample/Paper/Filtrations/Definitions.lean](../RSCounterexample/Paper/Filtrations/Definitions.lean))
- `Filtrations.HasExcellentFiltration` ([RSCounterexample/Paper/Filtrations/Definitions.lean](../RSCounterexample/Paper/Filtrations/Definitions.lean))
- `Filtrations.HasSLRelativeSchubertFiltration` ([RSCounterexample/Paper/Filtrations/SpecialLinear.lean](../RSCounterexample/Paper/Filtrations/SpecialLinear.lean))
- `Filtrations.HasSLSchubertFiltration` ([RSCounterexample/Paper/Filtrations/SpecialLinear.lean](../RSCounterexample/Paper/Filtrations/SpecialLinear.lean))
- `Filtrations.schubertSectionModule` ([RSCounterexample/Paper/Filtrations/SectionModules.lean](../RSCounterexample/Paper/Filtrations/SectionModules.lean))
- `Filtrations.dualJoseph` ([RSCounterexample/Paper/Filtrations/SectionModules.lean](../RSCounterexample/Paper/Filtrations/SectionModules.lean))
- `Filtrations.minRelSchubert` ([RSCounterexample/Paper/Filtrations/SectionModules.lean](../RSCounterexample/Paper/Filtrations/SectionModules.lean))
- `HighestWeight.flagOrbitSpan_irreducible` ([RSCounterexample/Paper/HighestWeight/Irreducible.lean](../RSCounterexample/Paper/HighestWeight/Irreducible.lean))

### Corollary 1.3 (`cor:intro-lascoux`)

Status: **formalized**

Here Lascoux polynomials and atoms are defined by the operators $\pi\_i^{(\beta)}f=\pi\_i((1+\beta x\_{i+1})f)$ and $\pi\_i^{(\beta)}-1$. The statement also covers coefficients in $\mathbb Z\[\beta\]$ that are nonnegative at $\beta=0$.

- `Family.not_lascouxAtomPositive` ([RSCounterexample/Paper/Family/LascouxCorollary.lean](../RSCounterexample/Paper/Family/LascouxCorollary.lean))
- `Family.no_lascouxExpansion_nonnegAtZero` ([RSCounterexample/Paper/Family/LascouxCorollary.lean](../RSCounterexample/Paper/Family/LascouxCorollary.lean))
- `Family.rank28_not_lascouxAtomPositive` ([RSCounterexample/Paper/Family/LascouxCorollary.lean](../RSCounterexample/Paper/Family/LascouxCorollary.lean))
- `Family.lascoux_product_positivity_false` ([RSCounterexample/Paper/Family/LascouxCorollary.lean](../RSCounterexample/Paper/Family/LascouxCorollary.lean))
- `betaIsobaric` ([RSCounterexample/Paper/Lascoux/Operators.lean](../RSCounterexample/Paper/Lascoux/Operators.lean))
- `betaAtomOperator` ([RSCounterexample/Paper/Lascoux/Operators.lean](../RSCounterexample/Paper/Lascoux/Operators.lean))
- `lascoux` ([RSCounterexample/Paper/Lascoux/Polynomials.lean](../RSCounterexample/Paper/Lascoux/Polynomials.lean))
- `lascouxAtom` ([RSCounterexample/Paper/Lascoux/Polynomials.lean](../RSCounterexample/Paper/Lascoux/Polynomials.lean))
- `betaZero_lascoux` ([RSCounterexample/Paper/Lascoux/Polynomials.lean](../RSCounterexample/Paper/Lascoux/Polynomials.lean))
- `betaZero_lascouxAtom` ([RSCounterexample/Paper/Lascoux/Polynomials.lean](../RSCounterexample/Paper/Lascoux/Polynomials.lean))
- `LascouxAtomPositive` ([RSCounterexample/Paper/Lascoux/Positivity.lean](../RSCounterexample/Paper/Lascoux/Positivity.lean))

### Equation (1.8) (`eq:intro-duality`)

Status: **formalized**

- `atomCoefficient_eq_rectangleCoefficient` ([RSCounterexample/Paper/AtomCoefficients.lean](../RSCounterexample/Paper/AtomCoefficients.lean))

### Theorem 1.4 (`thm:intro-quiver-polytope`)

Status: **formalized**

Vergne–Walter's lattice-point count, cited in the paper, is proved here through the Cauchy identity and the Littlewood–Richardson rule. Polynomial time means membership in the class $\mathrm{FP}$ of complexitylib, on binary encodings.

- `Quiver.Flat.quiverPolytope` ([RSCounterexample/Paper/Quiver/Polytope/Flat.lean](../RSCounterexample/Paper/Quiver/Polytope/Flat.lean))
- `Quiver.Flat.quiverTheorem_identity` ([RSCounterexample/Paper/Main/Unconditional.lean](../RSCounterexample/Paper/Main/Unconditional.lean))
- `Quiver.Flat.quiverTheorem_counts` ([RSCounterexample/Paper/Quiver/Polytope/Counts.lean](../RSCounterexample/Paper/Quiver/Polytope/Counts.lean))
- `Quiver.Flat.quiverPolytope_card` ([RSCounterexample/Paper/Quiver/Polytope/Counts.lean](../RSCounterexample/Paper/Quiver/Polytope/Counts.lean))
- `Quiver.Flat.finiteDimensional_canonicalHom` ([RSCounterexample/Paper/Quiver/Polytope/Counts.lean](../RSCounterexample/Paper/Quiver/Polytope/Counts.lean))
- `Quiver.Flat.quiverPolytope_bounded` ([RSCounterexample/Paper/Quiver/Polytope/Bounded.lean](../RSCounterexample/Paper/Quiver/Polytope/Bounded.lean))
- `Quiver.Flat.quiverCoefficient_pos_iff_realPoint` ([RSCounterexample/Paper/Main/Unconditional.lean](../RSCounterexample/Paper/Main/Unconditional.lean))
- `Quiver.Flat.quiverCoefficient_pos_iff_ratPoint` ([RSCounterexample/Paper/Main/Unconditional.lean](../RSCounterexample/Paper/Main/Unconditional.lean))
- `Quiver.Flat.quiverCoefficient_pos_iff_nonempty` ([RSCounterexample/Paper/Quiver/Polytope/Positivity.lean](../RSCounterexample/Paper/Quiver/Polytope/Positivity.lean))
- `Quiver.Flat.quiverCoefficient_pos_iff_ratFeasible` ([RSCounterexample/Paper/Quiver/Polytope/Positivity.lean](../RSCounterexample/Paper/Quiver/Polytope/Positivity.lean))
- `Quiver.Flat.nonempty_of_quiverCoefficient_pos` ([RSCounterexample/Paper/Quiver/Polytope/Positivity.lean](../RSCounterexample/Paper/Quiver/Polytope/Positivity.lean))
- `Quiver.Flat.quiverPolytope_nonempty_iff_exists_nsmul_pos` ([RSCounterexample/Paper/Quiver/Polytope/Scaling.lean](../RSCounterexample/Paper/Quiver/Polytope/Scaling.lean))
- `Quiver.Flat.quiverPolytope_ratFeasible_iff_exists_nsmul_pos` ([RSCounterexample/Paper/Quiver/Polytope/Scaling.lean](../RSCounterexample/Paper/Quiver/Polytope/Scaling.lean))
- `Quiver.Flat.atomCoefficient_nsmul_eq_card` ([RSCounterexample/Paper/Quiver/Polytope/Scaling.lean](../RSCounterexample/Paper/Quiver/Polytope/Scaling.lean))
- `quiverSaturation_holds` ([RSCounterexample/Paper/Quiver/Saturation.lean](../RSCounterexample/Paper/Quiver/Saturation.lean))
- `Quiver.atomCoefficient_eq_multiplicity` ([RSCounterexample/Paper/Quiver/Extraction.lean](../RSCounterexample/Paper/Quiver/Extraction.lean))
- `Algorithms.quiverTriple_recognition` ([RSCounterexample/Paper/Complexity/Recognition.lean](../RSCounterexample/Paper/Complexity/Recognition.lean))
- `Algorithms.quiverPolytope_construction` ([RSCounterexample/Paper/Complexity/Construction.lean](../RSCounterexample/Paper/Complexity/Construction.lean))
- `Algorithms.quiverPolytope_size` ([RSCounterexample/Paper/Complexity/Decide.lean](../RSCounterexample/Paper/Complexity/Decide.lean))
- `Algorithms.quiverPositivity_decision_polyTime` ([RSCounterexample/Paper/Main/Unconditional.lean](../RSCounterexample/Paper/Main/Unconditional.lean))
- `Algorithms.quiverPositivity_decision` ([RSCounterexample/Paper/Complexity/Decision.lean](../RSCounterexample/Paper/Complexity/Decision.lean))
- `Algorithms.quiverPositivity_decision_of_saturation` ([RSCounterexample/Paper/Main/Unconditional.lean](../RSCounterexample/Paper/Main/Unconditional.lean))
- `Algorithms.quiverPositivity_decision_of_criterion` ([RSCounterexample/Paper/Main/Unconditional.lean](../RSCounterexample/Paper/Main/Unconditional.lean))
- `Algorithms.quiverPositivity_decision_of_iff` ([RSCounterexample/Paper/Complexity/Decide.lean](../RSCounterexample/Paper/Complexity/Decide.lean))
- `Algorithms.encodeTriple` ([RSCounterexample/Paper/Complexity/Encoding.lean](../RSCounterexample/Paper/Complexity/Encoding.lean))
- `Algorithms.IsQuiverTripleList` ([RSCounterexample/Paper/Complexity/Encoding.lean](../RSCounterexample/Paper/Complexity/Encoding.lean))
- `Algorithms.binarySize_le_length` ([RSCounterexample/Paper/Complexity/Encoding.lean](../RSCounterexample/Paper/Complexity/Encoding.lean))
- `Algorithms.length_le_binarySize` ([RSCounterexample/Paper/Complexity/Encoding.lean](../RSCounterexample/Paper/Complexity/Encoding.lean))
- `Algorithms.exists_not_mem_FP` ([RSCounterexample/Paper/Complexity/Sanity.lean](../RSCounterexample/Paper/Complexity/Sanity.lean))
- `Algorithms.exists_mem_P_not_mem_DTIME` ([RSCounterexample/Paper/Complexity/Sanity.lean](../RSCounterexample/Paper/Complexity/Sanity.lean))

### Corollary 1.5 (`cor:intro-quiver-density`)

Status: **formalized**

The lower bound counts integer points near a scaled seed directly, instead of perturbing the seed over the reals.

- `Quiver.Density.card_positiveQuiverTriples_isTheta` ([RSCounterexample/Paper/Quiver/Density/Count.lean](../RSCounterexample/Paper/Quiver/Density/Count.lean))
- `Quiver.Density.positiveQuiverTriples_proportion` ([RSCounterexample/Paper/Quiver/Density/Count.lean](../RSCounterexample/Paper/Quiver/Density/Count.lean))
- `Quiver.Density.positiveQuiverTriples` ([RSCounterexample/Paper/Quiver/Density/Count.lean](../RSCounterexample/Paper/Quiver/Density/Count.lean))

### Lemma 2.4 (`lem:duality`)

Status: **formalized**

Fu–Lascoux's duality (2.3), cited in the paper, is proved here by induction on length.

- `atomCoefficient_eq_rectangleCoefficient` ([RSCounterexample/Paper/AtomCoefficients.lean](../RSCounterexample/Paper/AtomCoefficients.lean))
- `rectangleCoefficient` ([RSCounterexample/Paper/RectangleCoefficient.lean](../RSCounterexample/Paper/RectangleCoefficient.lean))
- `keyAtom_orthogonality` ([RSCounterexample/Paper/GlobalDuality.lean](../RSCounterexample/Paper/GlobalDuality.lean))
- `Representation.compositionFlagJosephPolo` ([RSCounterexample/Paper/JosephPolo/GeneralTheorem.lean](../RSCounterexample/Paper/JosephPolo/GeneralTheorem.lean))
- `Representation.compositionFlagDemazureCharacter` ([RSCounterexample/Paper/JosephPolo/GeneralTheorem.lean](../RSCounterexample/Paper/JosephPolo/GeneralTheorem.lean))
- `Representation.orderedPBWBasis_exists` ([RSCounterexample/Paper/PBW/Theorem.lean](../RSCounterexample/Paper/PBW/Theorem.lean))
- `atomCoefficient_eq_rectangleCoefficient'` ([RSCounterexample/Paper/AtomCoefficientSpec.lean](../RSCounterexample/Paper/AtomCoefficientSpec.lean))

### Proposition 2.13 (`prop:window`)

Status: **formalized**

Joseph's presentation (2.15), the Demazure character formula and the PBW theorem, cited in the paper, are proved here.

- `Window.window_rational_extraction` ([RSCounterexample/Paper/Window/General.lean](../RSCounterexample/Paper/Window/General.lean))
- `Window.window_product_indep` ([RSCounterexample/Paper/Window/General.lean](../RSCounterexample/Paper/Window/General.lean))
- `Window.Hypotheses` ([RSCounterexample/Paper/Window/Basic.lean](../RSCounterexample/Paper/Window/Basic.lean))
- `Window.WindowInequality` ([RSCounterexample/Paper/Window/Basic.lean](../RSCounterexample/Paper/Window/Basic.lean))
- `Window.prefixHeight` ([RSCounterexample/Paper/Window/Basic.lean](../RSCounterexample/Paper/Window/Basic.lean))
- `Window.cmp` ([RSCounterexample/Paper/Window/Basic.lean](../RSCounterexample/Paper/Window/Basic.lean))
- `Window.hypotheses_iff_of_le` ([RSCounterexample/Paper/Window/Basic.lean](../RSCounterexample/Paper/Window/Basic.lean))

### Lemma 3.1 (`lem:hall-determinant`)

Status: **formalized**

Gessel's flagged Jacobi–Trudi identity (3.6), cited in the paper, is proved here by a lattice-path involution.

- `Hall.hall_determinant` ([RSCounterexample/Paper/Hall/Determinant.lean](../RSCounterexample/Paper/Hall/Determinant.lean))
- `Hall.hallProduct` ([RSCounterexample/Paper/Hall/Determinant.lean](../RSCounterexample/Paper/Hall/Determinant.lean))
- `Hall.hallMatrix` ([RSCounterexample/Paper/Hall/Determinant.lean](../RSCounterexample/Paper/Hall/Determinant.lean))
- `Hall.completeH` ([RSCounterexample/Paper/Hall/Determinant.lean](../RSCounterexample/Paper/Hall/Determinant.lean))
- `Hall.hallSum` ([RSCounterexample/Paper/Hall/Determinant.lean](../RSCounterexample/Paper/Hall/Determinant.lean))
- `Hall.IsHallAdmissible` ([RSCounterexample/Paper/Hall/Admissible.lean](../RSCounterexample/Paper/Hall/Admissible.lean))
- `HallLattice.hall_determinant` ([RSCounterexample/Paper/HallDeterminant.lean](../RSCounterexample/Paper/HallDeterminant.lean))
- `hall_source_extraction` ([RSCounterexample/Paper/HallSourceExtraction.lean](../RSCounterexample/Paper/HallSourceExtraction.lean))

### Lemma 3.8 (`lem:hall-flags`)

Status: **formalized**

- `Hall.hall_flags` ([RSCounterexample/Paper/Hall/Admissible.lean](../RSCounterexample/Paper/Hall/Admissible.lean))
- `Hall.hallFlag` ([RSCounterexample/Paper/Hall/Admissible.lean](../RSCounterexample/Paper/Hall/Admissible.lean))
- `Hall.firstAbove` ([RSCounterexample/Paper/Hall/Admissible.lean](../RSCounterexample/Paper/Hall/Admissible.lean))
- `Hall.isHallAdmissible_iff_flags` ([RSCounterexample/Paper/Hall/Admissible.lean](../RSCounterexample/Paper/Hall/Admissible.lean))

### Definition 3.9 (`def:paired-target`)

Status: **formalized**

- `Hall.HallPartition` ([RSCounterexample/Paper/Hall/Partition.lean](../RSCounterexample/Paper/Hall/Partition.lean))
- `Hall.IsHallTriple` ([RSCounterexample/Paper/Hall/Partition.lean](../RSCounterexample/Paper/Hall/Partition.lean))
- `Hall.isHallTriple_iff` ([RSCounterexample/Paper/Hall/Partition.lean](../RSCounterexample/Paper/Hall/Partition.lean))
- `Hall.HallPartition.changeN` ([RSCounterexample/Paper/Hall/Partition.lean](../RSCounterexample/Paper/Hall/Partition.lean))
- `Family.familyHallPartition` ([RSCounterexample/Paper/Family/HallPartition.lean](../RSCounterexample/Paper/Family/HallPartition.lean))
- `Family.isHallTriple_family` ([RSCounterexample/Paper/Family/HallPartition.lean](../RSCounterexample/Paper/Family/HallPartition.lean))

### Proposition 3.11 (`prop:paired-reduction`)

Status: **formalized**

- `Hall.paired_reduction` ([RSCounterexample/Paper/Hall/Reduction.lean](../RSCounterexample/Paper/Hall/Reduction.lean))
- `Hall.tVar` ([RSCounterexample/Paper/Hall/Reduction.lean](../RSCounterexample/Paper/Hall/Reduction.lean))
- `Hall.HallPartition.q` ([RSCounterexample/Paper/Hall/Partition.lean](../RSCounterexample/Paper/Hall/Partition.lean))
- `Hall.HallPartition.pairs` ([RSCounterexample/Paper/Hall/Partition.lean](../RSCounterexample/Paper/Hall/Partition.lean))
- `Hall.HallPartition.height` ([RSCounterexample/Paper/Hall/Partition.lean](../RSCounterexample/Paper/Hall/Partition.lean))
- `Hall.HallPartition.flag` ([RSCounterexample/Paper/Hall/Partition.lean](../RSCounterexample/Paper/Hall/Partition.lean))
- `Hall.HallPartition.blockPolynomial` ([RSCounterexample/Paper/Hall/Partition.lean](../RSCounterexample/Paper/Hall/Partition.lean))
- `Hall.HallPartition.m_eq_sum_card` ([RSCounterexample/Paper/Hall/Partition.lean](../RSCounterexample/Paper/Hall/Partition.lean))
- `double_source_extraction` ([RSCounterexample/Paper/DoubleSourceExtraction.lean](../RSCounterexample/Paper/DoubleSourceExtraction.lean))
- `Hall.paired_reduction_of_isHallTriple` ([RSCounterexample/Paper/Hall/Reduction.lean](../RSCounterexample/Paper/Hall/Reduction.lean))
- `Family.atomCoefficient_eq_paired` ([RSCounterexample/Paper/Family/HallPartition.lean](../RSCounterexample/Paper/Family/HallPartition.lean))

### Lemma 4.1 (`lem:two-source-count`)

Status: **formalized**

- `Family.two_source_count` ([RSCounterexample/Paper/Family/TwoSourceCount.lean](../RSCounterexample/Paper/Family/TwoSourceCount.lean))

### Definition 5.1 (`def:quiver-triple`)

Status: **formalized**

- `Quiver.IsQuiverTriple` ([RSCounterexample/Paper/Quiver/Triple/Basic.lean](../RSCounterexample/Paper/Quiver/Triple/Basic.lean))
- `Quiver.IsQuiverPartition` ([RSCounterexample/Paper/Quiver/Triple/Basic.lean](../RSCounterexample/Paper/Quiver/Triple/Basic.lean))
- `Quiver.isQuiverPartition_iff_of_le` ([RSCounterexample/Paper/Quiver/Triple/Basic.lean](../RSCounterexample/Paper/Quiver/Triple/Basic.lean))
- `Quiver.isQuiverTriple_iff_canonical` ([RSCounterexample/Paper/Quiver/Triple/Canonical.lean](../RSCounterexample/Paper/Quiver/Triple/Canonical.lean))
- `Quiver.IsQuiverPartition.eq_canonical` ([RSCounterexample/Paper/Quiver/Triple/Canonical.lean](../RSCounterexample/Paper/Quiver/Triple/Canonical.lean))
- `Quiver.instDecidableIsQuiverTriple` ([RSCounterexample/Paper/Quiver/Triple/Canonical.lean](../RSCounterexample/Paper/Quiver/Triple/Canonical.lean))
- `Algorithms.IsQuiverTripleList` ([RSCounterexample/Paper/Complexity/Encoding.lean](../RSCounterexample/Paper/Complexity/Encoding.lean))

### Theorem 5.3 (`thm:quiver-coefficient`)

Status: **formalized**

Here the irreducible representations $V\_p^{\lambda^{(p)}}$ are spanned by the translates of products of flag minors, twisted by a power of the determinant.

- `Quiver.atomCoefficient_eq_finrank_quiverHom` ([RSCounterexample/Paper/Main/Unconditional.lean](../RSCounterexample/Paper/Main/Unconditional.lean))
- `Quiver.atomCoefficient_eq_finrank_hom` ([RSCounterexample/Paper/Quiver/HomSpace.lean](../RSCounterexample/Paper/Quiver/HomSpace.lean))
- `Quiver.finiteDimensional_quiverHom` ([RSCounterexample/Paper/Quiver/HomSpace.lean](../RSCounterexample/Paper/Quiver/HomSpace.lean))
- `Quiver.atomCoefficient_eq_multiplicity` ([RSCounterexample/Paper/Quiver/Extraction.lean](../RSCounterexample/Paper/Quiver/Extraction.lean))
- `Quiver.atomCoefficient_nonneg` ([RSCounterexample/Paper/Quiver/Polytope/Positivity.lean](../RSCounterexample/Paper/Quiver/Polytope/Positivity.lean))
- `Quiver.quiverOf` ([RSCounterexample/Paper/Quiver/OfTriple.lean](../RSCounterexample/Paper/Quiver/OfTriple.lean))
- `Quiver.leviWeight` ([RSCounterexample/Paper/Quiver/OfTriple.lean](../RSCounterexample/Paper/Quiver/OfTriple.lean))
- `Quiver.ForwardQuiver.multiplicity` ([RSCounterexample/Paper/Quiver/Multiplicity.lean](../RSCounterexample/Paper/Quiver/Multiplicity.lean))
- `GL.ratLeviIrrep` ([RSCounterexample/Paper/GL/Basic.lean](../RSCounterexample/Paper/GL/Basic.lean))

### Multiplicities of polynomial representations of products of general linear groups from their characters (Section 5.1)

Status: **formalized**

Cited in the paper and proved here, by the Casimir element of $\mathfrak{gl}\_n$ and the Weyl character formula.

- `GLCharacterMultiplicity` ([RSCounterexample/Paper/Statements/GLCharacterMultiplicity.lean](../RSCounterexample/Paper/Statements/GLCharacterMultiplicity.lean))
- `glCharacterMultiplicity_holds` ([RSCounterexample/Paper/GL/CharacterMultiplicity.lean](../RSCounterexample/Paper/GL/CharacterMultiplicity.lean))
- `GLRep.IsPolynomialLeviRep.exists_leviCharacter_eq_sum` ([RSCounterexample/GLRep/Levi/Multiplicity.lean](../RSCounterexample/GLRep/Levi/Multiplicity.lean))
- `GLRep.alternant_mul_glCharacter_of_isGlHighestWeightVector` ([RSCounterexample/GLRep/Weyl/WeylCharacter.lean](../RSCounterexample/GLRep/Weyl/WeylCharacter.lean))
- `GLRep.IsPolynomialRep.isSemisimpleRepresentation` ([RSCounterexample/GLRep/HighestWeight/CompleteReducibility.lean](../RSCounterexample/GLRep/HighestWeight/CompleteReducibility.lean))
- `GLRep.isIrreducible_irrep` ([RSCounterexample/GLRep/HighestWeight/WeylModule.lean](../RSCounterexample/GLRep/HighestWeight/WeylModule.lean))
- `GLRep.character_irrep` ([RSCounterexample/GLRep/HighestWeight/WeylModule.lean](../RSCounterexample/GLRep/HighestWeight/WeylModule.lean))
- `GLRep.IsPolynomialRep.exists_nonempty_equiv_irrep` ([RSCounterexample/GLRep/HighestWeight/WeylModule.lean](../RSCounterexample/GLRep/HighestWeight/WeylModule.lean))
- `GLRep.IsPolynomialRep.nonempty_equiv_of_character_eq` ([RSCounterexample/GLRep/HighestWeight/Classification.lean](../RSCounterexample/GLRep/HighestWeight/Classification.lean))
- `GLRep.finrank_intertwiningMap_irrep_self` ([RSCounterexample/GLRep/HighestWeight/WeylModule.lean](../RSCounterexample/GLRep/HighestWeight/WeylModule.lean))
- `GLRep.finrank_intertwiningMap_irrep_of_ne` ([RSCounterexample/GLRep/HighestWeight/WeylModule.lean](../RSCounterexample/GLRep/HighestWeight/WeylModule.lean))
- `GLRep.IsPolynomialRep.character_eq_diagramSchurPoly` ([RSCounterexample/GLRep/Weyl/GroupCharacter.lean](../RSCounterexample/GLRep/Weyl/GroupCharacter.lean))
- `GLRep.IsPolynomialRep.exists_character_eq_sum` ([RSCounterexample/GLRep/Multiplicity/GL.lean](../RSCounterexample/GLRep/Multiplicity/GL.lean))
- `GLRep.IsRationalRep.isSemisimpleRepresentation` ([RSCounterexample/GLRep/Rational/GL.lean](../RSCounterexample/GLRep/Rational/GL.lean))
- `GLRep.IsRationalRep.exists_nonempty_equiv_ratIrrep` ([RSCounterexample/GLRep/Rational/GL.lean](../RSCounterexample/GLRep/Rational/GL.lean))
- `GLRep.IsRationalRep.exists_ratCharacter_eq_sum` ([RSCounterexample/GLRep/Rational/GL.lean](../RSCounterexample/GLRep/Rational/GL.lean))
- `GLRep.IsRationalLeviRep.exists_ratLeviCharacter_eq_sum` ([RSCounterexample/GLRep/Rational/Levi.lean](../RSCounterexample/GLRep/Rational/Levi.lean))

Theorems that use it:

- `Quiver.ForwardQuiver.finrank_ratLeviIrrep_coordRep_eq_multiplicity` ([RSCounterexample/Paper/Main/Unconditional.lean](../RSCounterexample/Paper/Main/Unconditional.lean))
- `Quiver.atomCoefficient_eq_finrank_quiverHom` ([RSCounterexample/Paper/Main/Unconditional.lean](../RSCounterexample/Paper/Main/Unconditional.lean))
- `Quiver.Flat.quiverTheorem_identity` ([RSCounterexample/Paper/Main/Unconditional.lean](../RSCounterexample/Paper/Main/Unconditional.lean))

### Saturation of quiver multiplicities (Derksen–Weyman; Section 5.1)

Status: **formalized**

Cited in the paper and proved here, from the results of King and Schofield through the criterion of Baldoni–Vergne–Walter.

- `QuiverSaturation` ([RSCounterexample/Paper/Statements/QuiverSaturation.lean](../RSCounterexample/Paper/Statements/QuiverSaturation.lean))
- `quiverSaturation_holds` ([RSCounterexample/Paper/Quiver/Saturation.lean](../RSCounterexample/Paper/Quiver/Saturation.lean))
- `QuiverInvariants.FQuiver.exists_semiInvariant_of_nsmul` ([RSCounterexample/QuiverInvariants/Saturation.lean](../RSCounterexample/QuiverInvariants/Saturation.lean))
- `QuiverInvariants.FQuiver.exists_generalQuot_euler_add_extDim_nonpos` ([RSCounterexample/QuiverInvariants/Schofield.lean](../RSCounterexample/QuiverInvariants/Schofield.lean))
- `QuiverInvariants.FQuiver.isGreatest_genericExt` ([RSCounterexample/QuiverInvariants/Schofield.lean](../RSCounterexample/QuiverInvariants/Schofield.lean))
- `QuiverInvariants.FQuiver.exists_extDim_eq_zero` ([RSCounterexample/QuiverInvariants/Schofield.lean](../RSCounterexample/QuiverInvariants/Schofield.lean))
- `QuiverInvariants.FQuiver.IsSemiInvariant.sum_mul_nonneg_of_generalQuot` ([RSCounterexample/QuiverInvariants/King.lean](../RSCounterexample/QuiverInvariants/King.lean))
- `QuiverInvariants.FQuiver.exists_semiInvariant_iff` ([RSCounterexample/QuiverInvariants/Saturation.lean](../RSCounterexample/QuiverInvariants/Saturation.lean))
- `Quiver.ForwardQuiver.multiplicity_flag` ([RSCounterexample/Paper/Quiver/Flag.lean](../RSCounterexample/Paper/Quiver/Flag.lean))
- `Quiver.ForwardQuiver.multiplicity_const_pos_iff` ([RSCounterexample/Paper/Quiver/SemiInvariant.lean](../RSCounterexample/Paper/Quiver/SemiInvariant.lean))
- `quiverSaturation_of_semiInvariant` ([RSCounterexample/Paper/Quiver/Saturation.lean](../RSCounterexample/Paper/Quiver/Saturation.lean))

Theorems that use it:

- `Algorithms.quiverPositivity_decision_polyTime` ([RSCounterexample/Paper/Main/Unconditional.lean](../RSCounterexample/Paper/Main/Unconditional.lean))
- `Quiver.ForwardQuiver.multiplicity_pos_of_nsmul_pos` ([RSCounterexample/Paper/Main/Unconditional.lean](../RSCounterexample/Paper/Main/Unconditional.lean))
- `Quiver.Flat.quiverCoefficient_pos_iff_realPoint` ([RSCounterexample/Paper/Main/Unconditional.lean](../RSCounterexample/Paper/Main/Unconditional.lean))
- `Quiver.Flat.quiverCoefficient_pos_iff_ratPoint` ([RSCounterexample/Paper/Main/Unconditional.lean](../RSCounterexample/Paper/Main/Unconditional.lean))

### Polynomial-time rational feasibility of integer linear systems (Section 5.1)

Status: **formalized**

Cited in the paper and proved here, by a projection-and-rescaling algorithm of Chubanov type in exact integer arithmetic.

- `PolyTimeRationalFeasibility` ([RSCounterexample/Paper/Statements/PolyTimeRationalFeasibility.lean](../RSCounterexample/Paper/Statements/PolyTimeRationalFeasibility.lean))
- `polyTimeRationalFeasibility_holds` ([RSCounterexample/Paper/Complexity/RationalFeasibility.lean](../RSCounterexample/Paper/Complexity/RationalFeasibility.lean))
- `LinearProgramming.exists_mem_FP_feasible` ([RSCounterexample/LinearProgramming/Feasibility.lean](../RSCounterexample/LinearProgramming/Feasibility.lean))
- `LinearProgramming.decideFeasible_iff` ([RSCounterexample/LinearProgramming/Chubanov/Decide.lean](../RSCounterexample/LinearProgramming/Chubanov/Decide.lean))
- `LinearProgramming.chubanov_iff` ([RSCounterexample/LinearProgramming/Chubanov/Algorithm.lean](../RSCounterexample/LinearProgramming/Chubanov/Algorithm.lean))

Theorems that use it:

- `Algorithms.quiverPositivity_decision_of_criterion` ([RSCounterexample/Paper/Main/Unconditional.lean](../RSCounterexample/Paper/Main/Unconditional.lean))
- `Algorithms.quiverPositivity_decision_of_saturation` ([RSCounterexample/Paper/Main/Unconditional.lean](../RSCounterexample/Paper/Main/Unconditional.lean))

### Proposition 5.8 (`prop:quiver-two-source`)

Status: **formalized**

Polynomial time means membership in the class $\mathrm{FP}$ of complexitylib, on unary encodings; the algorithm is a dynamic program instead of the Pieri recurrence.

- `Quiver.twoSource_isQuiverPartition` ([RSCounterexample/Paper/Quiver/TwoSource.lean](../RSCounterexample/Paper/Quiver/TwoSource.lean))
- `Quiver.twoSource_eq_weylProjector` ([RSCounterexample/Paper/Quiver/TwoSource.lean](../RSCounterexample/Paper/Quiver/TwoSource.lean))
- `Quiver.twoSource_eq_kostka` ([RSCounterexample/Paper/Quiver/TwoSource.lean](../RSCounterexample/Paper/Quiver/TwoSource.lean))
- `Quiver.twoSource_pos_iff` ([RSCounterexample/Paper/Quiver/TwoSource.lean](../RSCounterexample/Paper/Quiver/TwoSource.lean))
- `Algorithms.twoSource_coefficient_computable` ([RSCounterexample/Paper/Complexity/TwoSourceAlgorithm.lean](../RSCounterexample/Paper/Complexity/TwoSourceAlgorithm.lean))
- `Algorithms.encodeTripleUnary` ([RSCounterexample/Paper/Complexity/UnaryEncoding.lean](../RSCounterexample/Paper/Complexity/UnaryEncoding.lean))
- `Algorithms.length_encodeTripleUnary_ofFn` ([RSCounterexample/Paper/Complexity/UnaryEncoding.lean](../RSCounterexample/Paper/Complexity/UnaryEncoding.lean))
- `Algorithms.encodeTripleUnary_injective` ([RSCounterexample/Paper/Complexity/UnaryEncoding.lean](../RSCounterexample/Paper/Complexity/UnaryEncoding.lean))
- `Algorithms.twoSource_eq_count` ([RSCounterexample/Paper/Complexity/TwoSourceCoefficient.lean](../RSCounterexample/Paper/Complexity/TwoSourceCoefficient.lean))
