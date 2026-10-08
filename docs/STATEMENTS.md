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

- `SchubertUnions.key_eq_sum_atom` ([Schubert/RS/SchubertUnions/BruhatRefinement.lean](../Schubert/RS/SchubertUnions/BruhatRefinement.lean))

### Theorem 1.1 (`thm:intro-family`)

Status: **formalized**

Here $\[\mathcal A\_c\]f$ is defined by the right side of (2.5) and shown to be the coefficient of $\mathcal A\_c$ in the atom expansion of $f$.

- `Family.atomCoefficient_eq` ([Schubert/RS/Family/Main.lean](../Schubert/RS/Family/Main.lean))
- `Family.atomCoefficient_factorization` ([Schubert/RS/Family/Main.lean](../Schubert/RS/Family/Main.lean))
- `Family.atomCoefficient_neg_iff` ([Schubert/RS/Family/Main.lean](../Schubert/RS/Family/Main.lean))
- `Family.existsUnique_atomExpansion` ([Schubert/RS/Family/Main.lean](../Schubert/RS/Family/Main.lean))
- `Family.not_atomPositive` ([Schubert/RS/Family/Main.lean](../Schubert/RS/Family/Main.lean))
- `Family.rank28_atomCoefficient` ([Schubert/RS/Family/Main.lean](../Schubert/RS/Family/Main.lean))
- `Family.rank28_not_atomPositive` ([Schubert/RS/Family/Main.lean](../Schubert/RS/Family/Main.lean))
- `Family.reiner_shimozono_false` ([Schubert/RS/Family/Main.lean](../Schubert/RS/Family/Main.lean))
- `Family.atomCoefficient_eq_narayana` ([Schubert/RS/Family/Extras.lean](../Schubert/RS/Family/Extras.lean))
- `Family.atomCoefficient_eq_paper` ([Schubert/RS/Family/Extras.lean](../Schubert/RS/Family/Extras.lean))
- `Family.atomCoefficient_threeFive` ([Schubert/RS/Family/Extras.lean](../Schubert/RS/Family/Extras.lean))
- `Family.atomCoefficient_fourFour` ([Schubert/RS/Family/Extras.lean](../Schubert/RS/Family/Extras.lean))
- `Family.isLeast_rank_of_negative` ([Schubert/RS/Family/Extras.lean](../Schubert/RS/Family/Extras.lean))
- `Family.narayana` ([Schubert/RS/Family/Narayana.lean](../Schubert/RS/Family/Narayana.lean))
- `Family.Parameters` ([Schubert/RS/Family/Data.lean](../Schubert/RS/Family/Data.lean))
- `Family.a` ([Schubert/RS/Family/Data.lean](../Schubert/RS/Family/Data.lean))
- `Family.b` ([Schubert/RS/Family/Data.lean](../Schubert/RS/Family/Data.lean))
- `Family.c` ([Schubert/RS/Family/Data.lean](../Schubert/RS/Family/Data.lean))
- `atomCoefficient_spec` ([Schubert/RS/AtomCoefficientSpec.lean](../Schubert/RS/AtomCoefficientSpec.lean))
- `atomCoefficient_eq_of_expansion` ([Schubert/RS/AtomCoefficientSpec.lean](../Schubert/RS/AtomCoefficientSpec.lean))
- `Family.isHallTriple_family` ([Schubert/RS/Family/HallPartition.lean](../Schubert/RS/Family/HallPartition.lean))
- `Family.atomCoefficient_eq_paired` ([Schubert/RS/Family/HallPartition.lean](../Schubert/RS/Family/HallPartition.lean))

### Equation (1.7) (`eq:intro-geometric-characters`)

Status: **formalized**

The proof uses standard-monomial bases and restriction to the Schubert boundary, instead of the Demazure recurrence and van der Kallen's exact sequence.

- `FlagVarieties.ch_dualJoseph_negWeight` ([Schubert/FlagVarieties/Modules/Geometric.lean](../Schubert/FlagVarieties/Modules/Geometric.lean))
- `Geometric.ch_geometricMinimalRelativeSchubert_negWeight` ([Schubert/RS/Geometric/SchemeRelative.lean](../Schubert/RS/Geometric/SchemeRelative.lean))
- `Geometric.geometricMinimalRelativeSchubert_weightSpace_ne_bot` ([Schubert/RS/Geometric/SchemeRelative.lean](../Schubert/RS/Geometric/SchemeRelative.lean))

Algebraic model:

- `Filtrations.dualJoseph_hasCharacter` ([Schubert/RS/Filtrations/SectionModules.lean](../Schubert/RS/Filtrations/SectionModules.lean))
- `Filtrations.minRelSchubert_hasCharacter` ([Schubert/RS/Filtrations/RelativeSchubertCharacters.lean](../Schubert/RS/Filtrations/RelativeSchubertCharacters.lean))

### Corollary 1.2 (`cor:intro-filtrations`)

Status: **formalized**

Here $X\_w$ is the scheme-theoretic image of $b\mapsto bwB$ in the flag scheme over $\mathbb C$. In Polo's case the proof uses the characters of the layers instead of van der Kallen's Proposition 2.3.11.

- `Geometric.not_hasGeometricRelativeSchubertFiltration` ([Schubert/RS/Geometric/SchemeRelative.lean](../Schubert/RS/Geometric/SchemeRelative.lean))
- `Geometric.not_hasGeometricSchubertFiltration` ([Schubert/RS/Geometric/SchemeCorollary.lean](../Schubert/RS/Geometric/SchemeCorollary.lean))
- `Geometric.not_hasGeometricSLRelativeSchubertFiltration` ([Schubert/RS/Geometric/SchemeRelative.lean](../Schubert/RS/Geometric/SchemeRelative.lean))
- `Geometric.not_hasGeometricSLSchubertFiltration` ([Schubert/RS/Geometric/SchemeRelative.lean](../Schubert/RS/Geometric/SchemeRelative.lean))
- `Geometric.typeA27_geometricFiltration_failure` ([Schubert/RS/Geometric/SchemeRelative.lean](../Schubert/RS/Geometric/SchemeRelative.lean))
- `Geometric.geometricFamilyTensor` ([Schubert/RS/Geometric/SchemeCorollary.lean](../Schubert/RS/Geometric/SchemeCorollary.lean))
- `Geometric.ch_geometricFamilyTensor` ([Schubert/RS/Geometric/SchemeCorollary.lean](../Schubert/RS/Geometric/SchemeCorollary.lean))
- `FlagVarieties.dualJoseph` ([Schubert/FlagVarieties/Modules/Geometric.lean](../Schubert/FlagVarieties/Modules/Geometric.lean))
- `Geometric.geometricMinimalRelativeSchubert` ([Schubert/RS/Geometric/SchemeRelative.lean](../Schubert/RS/Geometric/SchemeRelative.lean))
- `Geometric.geometricBoundaryRestrict` ([Schubert/RS/Geometric/SchemeRelative.lean](../Schubert/RS/Geometric/SchemeRelative.lean))
- `Geometric.IsGeometricSchubertLayer` ([Schubert/RS/Geometric/SchemeCorollary.lean](../Schubert/RS/Geometric/SchemeCorollary.lean))
- `Geometric.IsGeometricMinimalRelativeSchubertLayer` ([Schubert/RS/Geometric/SchemeRelative.lean](../Schubert/RS/Geometric/SchemeRelative.lean))
- `Geometric.HasGeometricRelativeSchubertFiltration` ([Schubert/RS/Geometric/SchemeRelative.lean](../Schubert/RS/Geometric/SchemeRelative.lean))
- `Geometric.HasGeometricSchubertFiltration` ([Schubert/RS/Geometric/SchemeRelative.lean](../Schubert/RS/Geometric/SchemeRelative.lean))
- `Geometric.HasGeometricSLRelativeSchubertFiltration` ([Schubert/RS/Geometric/SchemeRelative.lean](../Schubert/RS/Geometric/SchemeRelative.lean))
- `Geometric.HasGeometricSLSchubertFiltration` ([Schubert/RS/Geometric/SchemeRelative.lean](../Schubert/RS/Geometric/SchemeRelative.lean))
- `FlagVarieties.schubertVariety` ([Schubert/FlagVarieties/Schubert/Basic.lean](../Schubert/FlagVarieties/Schubert/Basic.lean))
- `FlagVarieties.schubertUnion` ([Schubert/FlagVarieties/Schubert/Basic.lean](../Schubert/FlagVarieties/Schubert/Basic.lean))
- `FlagVarieties.schubertBoundary` ([Schubert/FlagVarieties/Schubert/Basic.lean](../Schubert/FlagVarieties/Schubert/Basic.lean))
- `FlagVarieties.lineBundle` ([Schubert/FlagVarieties/LineBundle/Basic.lean](../Schubert/FlagVarieties/LineBundle/Basic.lean))
- `FlagVarieties.sections` ([Schubert/FlagVarieties/LineBundle/Basic.lean](../Schubert/FlagVarieties/LineBundle/Basic.lean))
- `FlagVarieties.sectionsRep` ([Schubert/FlagVarieties/LineBundle/BorelRep.lean](../Schubert/FlagVarieties/LineBundle/BorelRep.lean))
- `FlagVarieties.sectionsEquivSemiInvariants` ([Schubert/FlagVarieties/LineBundle/SectionsAsSemiInvariants.lean](../Schubert/FlagVarieties/LineBundle/SectionsAsSemiInvariants.lean))
- `FlagVarieties.sectionsRestrict` ([Schubert/FlagVarieties/LineBundle/SectionsRestriction.lean](../Schubert/FlagVarieties/LineBundle/SectionsRestriction.lean))
- `FlagVarieties.sectionsRestrictHom_eq_sectionsRestrict` ([Schubert/FlagVarieties/LineBundle/SectionsRestriction.lean](../Schubert/FlagVarieties/LineBundle/SectionsRestriction.lean))
- `FlagVarieties.preimageIdeal_schubertUnion_eq_orbitIdeal_complex` ([Schubert/FlagVarieties/Schubert/UnionPreimage.lean](../Schubert/FlagVarieties/Schubert/UnionPreimage.lean))
- `FlagVarieties.globalSectionsConstant_complex` ([Schubert/FlagVarieties/Schubert/GlobalSectionsRingForm.lean](../Schubert/FlagVarieties/Schubert/GlobalSectionsRingForm.lean))
- `FlagVarieties.geometricSectionEquiv` ([Schubert/FlagVarieties/Modules/Geometric.lean](../Schubert/FlagVarieties/Modules/Geometric.lean))
- `FlagVarieties.dualJosephEquiv` ([Schubert/FlagVarieties/Modules/Geometric.lean](../Schubert/FlagVarieties/Modules/Geometric.lean))
- `Geometric.geometricMinimalRelativeSchubertEquiv` ([Schubert/RS/Geometric/SchemeRelative.lean](../Schubert/RS/Geometric/SchemeRelative.lean))
- `Geometric.isGeometricSchubertLayer_iff` ([Schubert/RS/Geometric/SchemeCorollary.lean](../Schubert/RS/Geometric/SchemeCorollary.lean))
- `Geometric.isGeometricMinimalRelativeSchubertLayer_iff` ([Schubert/RS/Geometric/SchemeRelative.lean](../Schubert/RS/Geometric/SchemeRelative.lean))
- `FlagVarieties.sectionBModuleIso` ([Schubert/FlagVarieties/Modules/BModuleModel.lean](../Schubert/FlagVarieties/Modules/BModuleModel.lean))

Algebraic model:

- `Family.not_hasRelativeSchubertFiltration` ([Schubert/RS/Family/FiltrationCorollary.lean](../Schubert/RS/Family/FiltrationCorollary.lean))
- `Family.not_hasSchubertFiltration` ([Schubert/RS/Family/FiltrationCorollary.lean](../Schubert/RS/Family/FiltrationCorollary.lean))
- `Family.not_hasSLRelativeSchubertFiltration` ([Schubert/RS/Family/FiltrationCorollary.lean](../Schubert/RS/Family/FiltrationCorollary.lean))
- `Family.not_hasSLSchubertFiltration` ([Schubert/RS/Family/FiltrationCorollary.lean](../Schubert/RS/Family/FiltrationCorollary.lean))
- `Family.rank_sub_one` ([Schubert/RS/Family/FiltrationCorollary.lean](../Schubert/RS/Family/FiltrationCorollary.lean))
- `Family.typeA27_filtration_failure` ([Schubert/RS/Family/FiltrationCorollary.lean](../Schubert/RS/Family/FiltrationCorollary.lean))
- `Family.factors_hasExcellentFiltration` ([Schubert/RS/Family/FiltrationCorollary.lean](../Schubert/RS/Family/FiltrationCorollary.lean))
- `Family.familyTensor` ([Schubert/RS/Family/FiltrationCorollary.lean](../Schubert/RS/Family/FiltrationCorollary.lean))
- `Family.familyTensor_hasCharacter` ([Schubert/RS/Family/FiltrationCorollary.lean](../Schubert/RS/Family/FiltrationCorollary.lean))
- `Filtrations.HasRelativeSchubertFiltration` ([Schubert/RS/Filtrations/Definitions.lean](../Schubert/RS/Filtrations/Definitions.lean))
- `Filtrations.HasSchubertFiltration` ([Schubert/RS/Filtrations/Definitions.lean](../Schubert/RS/Filtrations/Definitions.lean))
- `Filtrations.HasExcellentFiltration` ([Schubert/RS/Filtrations/Definitions.lean](../Schubert/RS/Filtrations/Definitions.lean))
- `Filtrations.HasSLRelativeSchubertFiltration` ([Schubert/RS/Filtrations/SpecialLinear.lean](../Schubert/RS/Filtrations/SpecialLinear.lean))
- `Filtrations.HasSLSchubertFiltration` ([Schubert/RS/Filtrations/SpecialLinear.lean](../Schubert/RS/Filtrations/SpecialLinear.lean))
- `Filtrations.schubertSectionModule` ([Schubert/RS/Filtrations/SectionModules.lean](../Schubert/RS/Filtrations/SectionModules.lean))
- `Filtrations.dualJoseph` ([Schubert/RS/Filtrations/SectionModules.lean](../Schubert/RS/Filtrations/SectionModules.lean))
- `Filtrations.minRelSchubert` ([Schubert/RS/Filtrations/SectionModules.lean](../Schubert/RS/Filtrations/SectionModules.lean))
- `HighestWeight.flagOrbitSpan_irreducible` ([Schubert/RS/HighestWeight/Irreducible.lean](../Schubert/RS/HighestWeight/Irreducible.lean))

### Corollary 1.3 (`cor:intro-lascoux`)

Status: **formalized**

Here Lascoux polynomials and atoms are defined by the operators $\pi\_i^{(\beta)}f=\pi\_i((1+\beta x\_{i+1})f)$ and $\pi\_i^{(\beta)}-1$. The statement also covers coefficients in $\mathbb Z\[\beta\]$ that are nonnegative at $\beta=0$.

- `Family.not_lascouxAtomPositive` ([Schubert/RS/Family/LascouxCorollary.lean](../Schubert/RS/Family/LascouxCorollary.lean))
- `Family.no_lascouxExpansion_nonnegAtZero` ([Schubert/RS/Family/LascouxCorollary.lean](../Schubert/RS/Family/LascouxCorollary.lean))
- `Family.rank28_not_lascouxAtomPositive` ([Schubert/RS/Family/LascouxCorollary.lean](../Schubert/RS/Family/LascouxCorollary.lean))
- `Family.lascoux_product_positivity_false` ([Schubert/RS/Family/LascouxCorollary.lean](../Schubert/RS/Family/LascouxCorollary.lean))
- `betaIsobaric` ([Schubert/RS/Lascoux/Operators.lean](../Schubert/RS/Lascoux/Operators.lean))
- `betaAtomOperator` ([Schubert/RS/Lascoux/Operators.lean](../Schubert/RS/Lascoux/Operators.lean))
- `lascoux` ([Schubert/RS/Lascoux/Polynomials.lean](../Schubert/RS/Lascoux/Polynomials.lean))
- `lascouxAtom` ([Schubert/RS/Lascoux/Polynomials.lean](../Schubert/RS/Lascoux/Polynomials.lean))
- `betaZero_lascoux` ([Schubert/RS/Lascoux/Polynomials.lean](../Schubert/RS/Lascoux/Polynomials.lean))
- `betaZero_lascouxAtom` ([Schubert/RS/Lascoux/Polynomials.lean](../Schubert/RS/Lascoux/Polynomials.lean))
- `LascouxAtomPositive` ([Schubert/RS/Lascoux/Positivity.lean](../Schubert/RS/Lascoux/Positivity.lean))

### Equation (1.8) (`eq:intro-duality`)

Status: **formalized**

- `atomCoefficient_eq_rectangleCoefficient` ([Schubert/RS/AtomCoefficients.lean](../Schubert/RS/AtomCoefficients.lean))

### Theorem 1.4 (`thm:intro-quiver-polytope`)

Status: **formalized**

Vergne–Walter's lattice-point count, cited in the paper, is proved here through the Cauchy identity and the Littlewood–Richardson rule. Polynomial time means membership in the class $\mathrm{FP}$ of complexitylib, on binary encodings.

- `Quiver.Flat.quiverPolytope` ([Schubert/RS/Quiver/Polytope/Flat.lean](../Schubert/RS/Quiver/Polytope/Flat.lean))
- `Quiver.Flat.quiverTheorem_identity` ([Schubert/RS/Main/Unconditional.lean](../Schubert/RS/Main/Unconditional.lean))
- `Quiver.Flat.quiverTheorem_counts` ([Schubert/RS/Quiver/Polytope/Counts.lean](../Schubert/RS/Quiver/Polytope/Counts.lean))
- `Quiver.Flat.quiverPolytope_card` ([Schubert/RS/Quiver/Polytope/Counts.lean](../Schubert/RS/Quiver/Polytope/Counts.lean))
- `Quiver.Flat.finiteDimensional_canonicalHom` ([Schubert/RS/Quiver/Polytope/Counts.lean](../Schubert/RS/Quiver/Polytope/Counts.lean))
- `Quiver.Flat.quiverPolytope_bounded` ([Schubert/RS/Quiver/Polytope/Bounded.lean](../Schubert/RS/Quiver/Polytope/Bounded.lean))
- `Quiver.Flat.quiverCoefficient_pos_iff_realPoint` ([Schubert/RS/Main/Unconditional.lean](../Schubert/RS/Main/Unconditional.lean))
- `Quiver.Flat.quiverCoefficient_pos_iff_ratPoint` ([Schubert/RS/Main/Unconditional.lean](../Schubert/RS/Main/Unconditional.lean))
- `Quiver.Flat.quiverCoefficient_pos_iff_nonempty` ([Schubert/RS/Quiver/Polytope/Positivity.lean](../Schubert/RS/Quiver/Polytope/Positivity.lean))
- `Quiver.Flat.quiverCoefficient_pos_iff_ratFeasible` ([Schubert/RS/Quiver/Polytope/Positivity.lean](../Schubert/RS/Quiver/Polytope/Positivity.lean))
- `Quiver.Flat.nonempty_of_quiverCoefficient_pos` ([Schubert/RS/Quiver/Polytope/Positivity.lean](../Schubert/RS/Quiver/Polytope/Positivity.lean))
- `Quiver.Flat.quiverPolytope_nonempty_iff_exists_nsmul_pos` ([Schubert/RS/Quiver/Polytope/Scaling.lean](../Schubert/RS/Quiver/Polytope/Scaling.lean))
- `Quiver.Flat.quiverPolytope_ratFeasible_iff_exists_nsmul_pos` ([Schubert/RS/Quiver/Polytope/Scaling.lean](../Schubert/RS/Quiver/Polytope/Scaling.lean))
- `Quiver.Flat.atomCoefficient_nsmul_eq_card` ([Schubert/RS/Quiver/Polytope/Scaling.lean](../Schubert/RS/Quiver/Polytope/Scaling.lean))
- `quiverSaturation_holds` ([Schubert/RS/Quiver/Saturation.lean](../Schubert/RS/Quiver/Saturation.lean))
- `Quiver.atomCoefficient_eq_multiplicity` ([Schubert/RS/Quiver/Extraction.lean](../Schubert/RS/Quiver/Extraction.lean))
- `Algorithms.quiverTriple_recognition` ([Schubert/RS/Complexity/Recognition.lean](../Schubert/RS/Complexity/Recognition.lean))
- `Algorithms.quiverPolytope_construction` ([Schubert/RS/Complexity/Construction.lean](../Schubert/RS/Complexity/Construction.lean))
- `Algorithms.quiverPolytope_size` ([Schubert/RS/Complexity/Decide.lean](../Schubert/RS/Complexity/Decide.lean))
- `Algorithms.quiverPositivity_decision_polyTime` ([Schubert/RS/Main/Unconditional.lean](../Schubert/RS/Main/Unconditional.lean))
- `Algorithms.quiverPositivity_decision` ([Schubert/RS/Complexity/Decision.lean](../Schubert/RS/Complexity/Decision.lean))
- `Algorithms.quiverPositivity_decision_of_saturation` ([Schubert/RS/Main/Unconditional.lean](../Schubert/RS/Main/Unconditional.lean))
- `Algorithms.quiverPositivity_decision_of_criterion` ([Schubert/RS/Main/Unconditional.lean](../Schubert/RS/Main/Unconditional.lean))
- `Algorithms.quiverPositivity_decision_of_iff` ([Schubert/RS/Complexity/Decide.lean](../Schubert/RS/Complexity/Decide.lean))
- `Algorithms.encodeTriple` ([Schubert/RS/Complexity/Encoding.lean](../Schubert/RS/Complexity/Encoding.lean))
- `Algorithms.IsQuiverTripleList` ([Schubert/RS/Complexity/Encoding.lean](../Schubert/RS/Complexity/Encoding.lean))
- `Algorithms.binarySize_le_length` ([Schubert/RS/Complexity/Encoding.lean](../Schubert/RS/Complexity/Encoding.lean))
- `Algorithms.length_le_binarySize` ([Schubert/RS/Complexity/Encoding.lean](../Schubert/RS/Complexity/Encoding.lean))
- `Algorithms.exists_not_mem_FP` ([Schubert/RS/Complexity/Sanity.lean](../Schubert/RS/Complexity/Sanity.lean))
- `Algorithms.exists_mem_P_not_mem_DTIME` ([Schubert/RS/Complexity/Sanity.lean](../Schubert/RS/Complexity/Sanity.lean))

### Corollary 1.5 (`cor:intro-quiver-density`)

Status: **formalized**

The lower bound counts integer points near a scaled seed directly, instead of perturbing the seed over the reals.

- `Quiver.Density.card_positiveQuiverTriples_isTheta` ([Schubert/RS/Quiver/Density/Count.lean](../Schubert/RS/Quiver/Density/Count.lean))
- `Quiver.Density.positiveQuiverTriples_proportion` ([Schubert/RS/Quiver/Density/Count.lean](../Schubert/RS/Quiver/Density/Count.lean))
- `Quiver.Density.positiveQuiverTriples` ([Schubert/RS/Quiver/Density/Count.lean](../Schubert/RS/Quiver/Density/Count.lean))

### Lemma 2.4 (`lem:duality`)

Status: **formalized**

Fu–Lascoux's duality (2.3), cited in the paper, is proved here by induction on length.

- `atomCoefficient_eq_rectangleCoefficient` ([Schubert/RS/AtomCoefficients.lean](../Schubert/RS/AtomCoefficients.lean))
- `rectangleCoefficient` ([Schubert/RS/RectangleCoefficient.lean](../Schubert/RS/RectangleCoefficient.lean))
- `keyAtom_orthogonality` ([Schubert/RS/GlobalDuality.lean](../Schubert/RS/GlobalDuality.lean))
- `Representation.compositionFlagJosephPolo` ([Schubert/RS/JosephPolo/GeneralTheorem.lean](../Schubert/RS/JosephPolo/GeneralTheorem.lean))
- `Representation.compositionFlagDemazureCharacter` ([Schubert/RS/JosephPolo/GeneralTheorem.lean](../Schubert/RS/JosephPolo/GeneralTheorem.lean))
- `Representation.orderedPBWBasis_exists` ([Schubert/RS/PBW/Theorem.lean](../Schubert/RS/PBW/Theorem.lean))
- `atomCoefficient_eq_rectangleCoefficient'` ([Schubert/RS/AtomCoefficientSpec.lean](../Schubert/RS/AtomCoefficientSpec.lean))

### Proposition 2.13 (`prop:window`)

Status: **formalized**

Joseph's presentation (2.15), the Demazure character formula and the PBW theorem, cited in the paper, are proved here.

- `Window.window_rational_extraction` ([Schubert/RS/Window/General.lean](../Schubert/RS/Window/General.lean))
- `Window.window_product_indep` ([Schubert/RS/Window/General.lean](../Schubert/RS/Window/General.lean))
- `Window.Hypotheses` ([Schubert/RS/Window/Basic.lean](../Schubert/RS/Window/Basic.lean))
- `Window.WindowInequality` ([Schubert/RS/Window/Basic.lean](../Schubert/RS/Window/Basic.lean))
- `Window.prefixHeight` ([Schubert/RS/Window/Basic.lean](../Schubert/RS/Window/Basic.lean))
- `Window.cmp` ([Schubert/RS/Window/Basic.lean](../Schubert/RS/Window/Basic.lean))
- `Window.hypotheses_iff_of_le` ([Schubert/RS/Window/Basic.lean](../Schubert/RS/Window/Basic.lean))

### Lemma 3.1 (`lem:hall-determinant`)

Status: **formalized**

Gessel's flagged Jacobi–Trudi identity (3.6), cited in the paper, is proved here by a lattice-path involution.

- `Hall.hall_determinant` ([Schubert/RS/Hall/Determinant.lean](../Schubert/RS/Hall/Determinant.lean))
- `Hall.hallProduct` ([Schubert/RS/Hall/Determinant.lean](../Schubert/RS/Hall/Determinant.lean))
- `Hall.hallMatrix` ([Schubert/RS/Hall/Determinant.lean](../Schubert/RS/Hall/Determinant.lean))
- `Hall.completeH` ([Schubert/RS/Hall/Determinant.lean](../Schubert/RS/Hall/Determinant.lean))
- `Hall.hallSum` ([Schubert/RS/Hall/Determinant.lean](../Schubert/RS/Hall/Determinant.lean))
- `Hall.IsHallAdmissible` ([Schubert/RS/Hall/Admissible.lean](../Schubert/RS/Hall/Admissible.lean))
- `HallLattice.hall_determinant` ([Schubert/RS/HallDeterminant.lean](../Schubert/RS/HallDeterminant.lean))
- `hall_source_extraction` ([Schubert/RS/HallSourceExtraction.lean](../Schubert/RS/HallSourceExtraction.lean))

### Lemma 3.8 (`lem:hall-flags`)

Status: **formalized**

- `Hall.hall_flags` ([Schubert/RS/Hall/Admissible.lean](../Schubert/RS/Hall/Admissible.lean))
- `Hall.hallFlag` ([Schubert/RS/Hall/Admissible.lean](../Schubert/RS/Hall/Admissible.lean))
- `Hall.firstAbove` ([Schubert/RS/Hall/Admissible.lean](../Schubert/RS/Hall/Admissible.lean))
- `Hall.isHallAdmissible_iff_flags` ([Schubert/RS/Hall/Admissible.lean](../Schubert/RS/Hall/Admissible.lean))

### Definition 3.9 (`def:paired-target`)

Status: **formalized**

- `Hall.HallPartition` ([Schubert/RS/Hall/Partition.lean](../Schubert/RS/Hall/Partition.lean))
- `Hall.IsHallTriple` ([Schubert/RS/Hall/Partition.lean](../Schubert/RS/Hall/Partition.lean))
- `Hall.isHallTriple_iff` ([Schubert/RS/Hall/Partition.lean](../Schubert/RS/Hall/Partition.lean))
- `Hall.HallPartition.changeN` ([Schubert/RS/Hall/Partition.lean](../Schubert/RS/Hall/Partition.lean))
- `Family.familyHallPartition` ([Schubert/RS/Family/HallPartition.lean](../Schubert/RS/Family/HallPartition.lean))
- `Family.isHallTriple_family` ([Schubert/RS/Family/HallPartition.lean](../Schubert/RS/Family/HallPartition.lean))

### Proposition 3.11 (`prop:paired-reduction`)

Status: **formalized**

- `Hall.paired_reduction` ([Schubert/RS/Hall/Reduction.lean](../Schubert/RS/Hall/Reduction.lean))
- `Hall.tVar` ([Schubert/RS/Hall/Reduction.lean](../Schubert/RS/Hall/Reduction.lean))
- `Hall.HallPartition.q` ([Schubert/RS/Hall/Partition.lean](../Schubert/RS/Hall/Partition.lean))
- `Hall.HallPartition.pairs` ([Schubert/RS/Hall/Partition.lean](../Schubert/RS/Hall/Partition.lean))
- `Hall.HallPartition.height` ([Schubert/RS/Hall/Partition.lean](../Schubert/RS/Hall/Partition.lean))
- `Hall.HallPartition.flag` ([Schubert/RS/Hall/Partition.lean](../Schubert/RS/Hall/Partition.lean))
- `Hall.HallPartition.blockPolynomial` ([Schubert/RS/Hall/Partition.lean](../Schubert/RS/Hall/Partition.lean))
- `Hall.HallPartition.m_eq_sum_card` ([Schubert/RS/Hall/Partition.lean](../Schubert/RS/Hall/Partition.lean))
- `double_source_extraction` ([Schubert/RS/DoubleSourceExtraction.lean](../Schubert/RS/DoubleSourceExtraction.lean))
- `Hall.paired_reduction_of_isHallTriple` ([Schubert/RS/Hall/Reduction.lean](../Schubert/RS/Hall/Reduction.lean))
- `Family.atomCoefficient_eq_paired` ([Schubert/RS/Family/HallPartition.lean](../Schubert/RS/Family/HallPartition.lean))

### Lemma 4.1 (`lem:two-source-count`)

Status: **formalized**

- `Family.two_source_count` ([Schubert/RS/Family/TwoSourceCount.lean](../Schubert/RS/Family/TwoSourceCount.lean))

### Definition 5.1 (`def:quiver-triple`)

Status: **formalized**

- `Quiver.IsQuiverTriple` ([Schubert/RS/Quiver/Triple/Basic.lean](../Schubert/RS/Quiver/Triple/Basic.lean))
- `Quiver.IsQuiverPartition` ([Schubert/RS/Quiver/Triple/Basic.lean](../Schubert/RS/Quiver/Triple/Basic.lean))
- `Quiver.isQuiverPartition_iff_of_le` ([Schubert/RS/Quiver/Triple/Basic.lean](../Schubert/RS/Quiver/Triple/Basic.lean))
- `Quiver.isQuiverTriple_iff_canonical` ([Schubert/RS/Quiver/Triple/Canonical.lean](../Schubert/RS/Quiver/Triple/Canonical.lean))
- `Quiver.IsQuiverPartition.eq_canonical` ([Schubert/RS/Quiver/Triple/Canonical.lean](../Schubert/RS/Quiver/Triple/Canonical.lean))
- `Quiver.instDecidableIsQuiverTriple` ([Schubert/RS/Quiver/Triple/Canonical.lean](../Schubert/RS/Quiver/Triple/Canonical.lean))
- `Algorithms.IsQuiverTripleList` ([Schubert/RS/Complexity/Encoding.lean](../Schubert/RS/Complexity/Encoding.lean))

### Theorem 5.3 (`thm:quiver-coefficient`)

Status: **formalized**

Here the irreducible representations $V\_p^{\lambda^{(p)}}$ are spanned by the translates of products of flag minors, twisted by a power of the determinant.

- `Quiver.atomCoefficient_eq_finrank_quiverHom` ([Schubert/RS/Main/Unconditional.lean](../Schubert/RS/Main/Unconditional.lean))
- `Quiver.atomCoefficient_eq_finrank_hom` ([Schubert/RS/Quiver/HomSpace.lean](../Schubert/RS/Quiver/HomSpace.lean))
- `Quiver.finiteDimensional_quiverHom` ([Schubert/RS/Quiver/HomSpace.lean](../Schubert/RS/Quiver/HomSpace.lean))
- `Quiver.atomCoefficient_eq_multiplicity` ([Schubert/RS/Quiver/Extraction.lean](../Schubert/RS/Quiver/Extraction.lean))
- `Quiver.atomCoefficient_nonneg` ([Schubert/RS/Quiver/Polytope/Positivity.lean](../Schubert/RS/Quiver/Polytope/Positivity.lean))
- `Quiver.quiverOf` ([Schubert/RS/Quiver/OfTriple.lean](../Schubert/RS/Quiver/OfTriple.lean))
- `Quiver.leviWeight` ([Schubert/RS/Quiver/OfTriple.lean](../Schubert/RS/Quiver/OfTriple.lean))
- `Quiver.ForwardQuiver.multiplicity` ([Schubert/RS/Quiver/Multiplicity.lean](../Schubert/RS/Quiver/Multiplicity.lean))
- `GL.ratLeviIrrep` ([Schubert/RS/GL/Basic.lean](../Schubert/RS/GL/Basic.lean))

### Multiplicities of polynomial representations of products of general linear groups from their characters (Section 5.1)

Status: **formalized**

Cited in the paper and proved here, by the Casimir element of $\mathfrak{gl}\_n$ and the Weyl character formula.

- `GLCharacterMultiplicity` ([Schubert/RS/Statements/GLCharacterMultiplicity.lean](../Schubert/RS/Statements/GLCharacterMultiplicity.lean))
- `glCharacterMultiplicity_holds` ([Schubert/RS/GL/CharacterMultiplicity.lean](../Schubert/RS/GL/CharacterMultiplicity.lean))
- `GLRep.IsPolynomialLeviRep.exists_leviCharacter_eq_sum` ([Schubert/GLRep/Levi/Multiplicity.lean](../Schubert/GLRep/Levi/Multiplicity.lean))
- `GLRep.alternant_mul_glCharacter_of_isGlHighestWeightVector` ([Schubert/GLRep/Weyl/WeylCharacter.lean](../Schubert/GLRep/Weyl/WeylCharacter.lean))
- `GLRep.IsPolynomialRep.isSemisimpleRepresentation` ([Schubert/GLRep/HighestWeight/CompleteReducibility.lean](../Schubert/GLRep/HighestWeight/CompleteReducibility.lean))
- `GLRep.isIrreducible_irrep` ([Schubert/GLRep/HighestWeight/WeylModule.lean](../Schubert/GLRep/HighestWeight/WeylModule.lean))
- `GLRep.character_irrep` ([Schubert/GLRep/HighestWeight/WeylModule.lean](../Schubert/GLRep/HighestWeight/WeylModule.lean))
- `GLRep.IsPolynomialRep.exists_nonempty_equiv_irrep` ([Schubert/GLRep/HighestWeight/WeylModule.lean](../Schubert/GLRep/HighestWeight/WeylModule.lean))
- `GLRep.IsPolynomialRep.nonempty_equiv_of_character_eq` ([Schubert/GLRep/HighestWeight/Classification.lean](../Schubert/GLRep/HighestWeight/Classification.lean))
- `GLRep.finrank_intertwiningMap_irrep_self` ([Schubert/GLRep/HighestWeight/WeylModule.lean](../Schubert/GLRep/HighestWeight/WeylModule.lean))
- `GLRep.finrank_intertwiningMap_irrep_of_ne` ([Schubert/GLRep/HighestWeight/WeylModule.lean](../Schubert/GLRep/HighestWeight/WeylModule.lean))
- `GLRep.IsPolynomialRep.character_eq_diagramSchurPoly` ([Schubert/GLRep/Weyl/GroupCharacter.lean](../Schubert/GLRep/Weyl/GroupCharacter.lean))
- `GLRep.IsPolynomialRep.exists_character_eq_sum` ([Schubert/GLRep/Multiplicity/GL.lean](../Schubert/GLRep/Multiplicity/GL.lean))
- `GLRep.IsRationalRep.isSemisimpleRepresentation` ([Schubert/GLRep/Rational/GL.lean](../Schubert/GLRep/Rational/GL.lean))
- `GLRep.IsRationalRep.exists_nonempty_equiv_ratIrrep` ([Schubert/GLRep/Rational/GL.lean](../Schubert/GLRep/Rational/GL.lean))
- `GLRep.IsRationalRep.exists_ratCharacter_eq_sum` ([Schubert/GLRep/Rational/GL.lean](../Schubert/GLRep/Rational/GL.lean))
- `GLRep.IsRationalLeviRep.exists_ratLeviCharacter_eq_sum` ([Schubert/GLRep/Rational/Levi.lean](../Schubert/GLRep/Rational/Levi.lean))

Theorems that use it:

- `Quiver.ForwardQuiver.finrank_ratLeviIrrep_coordRep_eq_multiplicity` ([Schubert/RS/Main/Unconditional.lean](../Schubert/RS/Main/Unconditional.lean))
- `Quiver.atomCoefficient_eq_finrank_quiverHom` ([Schubert/RS/Main/Unconditional.lean](../Schubert/RS/Main/Unconditional.lean))
- `Quiver.Flat.quiverTheorem_identity` ([Schubert/RS/Main/Unconditional.lean](../Schubert/RS/Main/Unconditional.lean))

### Saturation of quiver multiplicities (Derksen–Weyman; Section 5.1)

Status: **formalized**

Cited in the paper and proved here, from the results of King and Schofield through the criterion of Baldoni–Vergne–Walter.

- `QuiverSaturation` ([Schubert/RS/Statements/QuiverSaturation.lean](../Schubert/RS/Statements/QuiverSaturation.lean))
- `quiverSaturation_holds` ([Schubert/RS/Quiver/Saturation.lean](../Schubert/RS/Quiver/Saturation.lean))
- `QuiverInvariants.FQuiver.exists_semiInvariant_of_nsmul` ([Schubert/QuiverInvariants/Saturation.lean](../Schubert/QuiverInvariants/Saturation.lean))
- `QuiverInvariants.FQuiver.exists_generalQuot_euler_add_extDim_nonpos` ([Schubert/QuiverInvariants/Schofield.lean](../Schubert/QuiverInvariants/Schofield.lean))
- `QuiverInvariants.FQuiver.isGreatest_genericExt` ([Schubert/QuiverInvariants/Schofield.lean](../Schubert/QuiverInvariants/Schofield.lean))
- `QuiverInvariants.FQuiver.exists_extDim_eq_zero` ([Schubert/QuiverInvariants/Schofield.lean](../Schubert/QuiverInvariants/Schofield.lean))
- `QuiverInvariants.FQuiver.IsSemiInvariant.sum_mul_nonneg_of_generalQuot` ([Schubert/QuiverInvariants/King.lean](../Schubert/QuiverInvariants/King.lean))
- `QuiverInvariants.FQuiver.exists_semiInvariant_iff` ([Schubert/QuiverInvariants/Saturation.lean](../Schubert/QuiverInvariants/Saturation.lean))
- `Quiver.ForwardQuiver.multiplicity_flag` ([Schubert/RS/Quiver/Flag.lean](../Schubert/RS/Quiver/Flag.lean))
- `Quiver.ForwardQuiver.multiplicity_const_pos_iff` ([Schubert/RS/Quiver/SemiInvariant.lean](../Schubert/RS/Quiver/SemiInvariant.lean))
- `quiverSaturation_of_semiInvariant` ([Schubert/RS/Quiver/Saturation.lean](../Schubert/RS/Quiver/Saturation.lean))

Theorems that use it:

- `Algorithms.quiverPositivity_decision_polyTime` ([Schubert/RS/Main/Unconditional.lean](../Schubert/RS/Main/Unconditional.lean))
- `Quiver.ForwardQuiver.multiplicity_pos_of_nsmul_pos` ([Schubert/RS/Main/Unconditional.lean](../Schubert/RS/Main/Unconditional.lean))
- `Quiver.Flat.quiverCoefficient_pos_iff_realPoint` ([Schubert/RS/Main/Unconditional.lean](../Schubert/RS/Main/Unconditional.lean))
- `Quiver.Flat.quiverCoefficient_pos_iff_ratPoint` ([Schubert/RS/Main/Unconditional.lean](../Schubert/RS/Main/Unconditional.lean))

### Polynomial-time rational feasibility of integer linear systems (Section 5.1)

Status: **formalized**

Cited in the paper and proved here, by a projection-and-rescaling algorithm of Chubanov type in exact integer arithmetic.

- `PolyTimeRationalFeasibility` ([Schubert/RS/Statements/PolyTimeRationalFeasibility.lean](../Schubert/RS/Statements/PolyTimeRationalFeasibility.lean))
- `polyTimeRationalFeasibility_holds` ([Schubert/RS/Complexity/RationalFeasibility.lean](../Schubert/RS/Complexity/RationalFeasibility.lean))
- `LinearProgramming.exists_mem_FP_feasible` ([Schubert/LinearProgramming/Feasibility.lean](../Schubert/LinearProgramming/Feasibility.lean))
- `LinearProgramming.decideFeasible_iff` ([Schubert/LinearProgramming/Chubanov/Decide.lean](../Schubert/LinearProgramming/Chubanov/Decide.lean))
- `LinearProgramming.chubanov_iff` ([Schubert/LinearProgramming/Chubanov/Algorithm.lean](../Schubert/LinearProgramming/Chubanov/Algorithm.lean))

Theorems that use it:

- `Algorithms.quiverPositivity_decision_of_criterion` ([Schubert/RS/Main/Unconditional.lean](../Schubert/RS/Main/Unconditional.lean))
- `Algorithms.quiverPositivity_decision_of_saturation` ([Schubert/RS/Main/Unconditional.lean](../Schubert/RS/Main/Unconditional.lean))

### Proposition 5.8 (`prop:quiver-two-source`)

Status: **formalized**

Polynomial time means membership in the class $\mathrm{FP}$ of complexitylib, on unary encodings; the algorithm is a dynamic program instead of the Pieri recurrence.

- `Quiver.twoSource_isQuiverPartition` ([Schubert/RS/Quiver/TwoSource.lean](../Schubert/RS/Quiver/TwoSource.lean))
- `Quiver.twoSource_eq_weylProjector` ([Schubert/RS/Quiver/TwoSource.lean](../Schubert/RS/Quiver/TwoSource.lean))
- `Quiver.twoSource_eq_kostka` ([Schubert/RS/Quiver/TwoSource.lean](../Schubert/RS/Quiver/TwoSource.lean))
- `Quiver.twoSource_pos_iff` ([Schubert/RS/Quiver/TwoSource.lean](../Schubert/RS/Quiver/TwoSource.lean))
- `Algorithms.twoSource_coefficient_computable` ([Schubert/RS/Complexity/TwoSourceAlgorithm.lean](../Schubert/RS/Complexity/TwoSourceAlgorithm.lean))
- `Algorithms.encodeTripleUnary` ([Schubert/RS/Complexity/UnaryEncoding.lean](../Schubert/RS/Complexity/UnaryEncoding.lean))
- `Algorithms.length_encodeTripleUnary_ofFn` ([Schubert/RS/Complexity/UnaryEncoding.lean](../Schubert/RS/Complexity/UnaryEncoding.lean))
- `Algorithms.encodeTripleUnary_injective` ([Schubert/RS/Complexity/UnaryEncoding.lean](../Schubert/RS/Complexity/UnaryEncoding.lean))
- `Algorithms.twoSource_eq_count` ([Schubert/RS/Complexity/TwoSourceCoefficient.lean](../Schubert/RS/Complexity/TwoSourceCoefficient.lean))
