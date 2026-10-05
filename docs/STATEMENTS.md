# Statements of the paper and their Lean counterparts

Each labelled statement of R. Hodges, *Counterexamples to the Reiner–Shimozono
conjecture and the failure of Schubert filtrations*
([arXiv:2609.28169](https://arxiv.org/abs/2609.28169)), with its status and the Lean
declarations that formalize it. Names are shown without the prefix `Schubert.RS.`; paths
are relative to the repository root. Statements are referred to by their LaTeX labels.

| Label | Result | Status |
| --- | --- | --- |
| `thm:intro-family` | Theorem 1.1 | formalized |
| `cor:intro-filtrations` | Corollary 1.2 | formalized |
| `cor:intro-lascoux` | Corollary 1.3 | formalized |
| `thm:intro-quiver-polytope` | Theorem 1.4 | formalized |
| `cor:intro-quiver-density` | Corollary 1.5 | formalized |
| `lem:duality` | Lemma | formalized |
| `prop:window` | Proposition | formalized |
| `lem:hall-determinant` | Lemma | formalized |
| `lem:hall-flags` | Lemma | formalized |
| `def:paired-target` | Definition | formalized |
| `prop:paired-reduction` | Proposition | formalized |
| `lem:two-source-count` | Lemma | formalized |
| `def:quiver-triple` | Definition | formalized |
| `thm:quiver-coefficient` | Theorem | formalized |
| `prop:quiver-two-source` | Proposition | formalized |

## Standard results proved here

The paper cites three standard results for Theorems 1.4 and 5.3. Each is stated as a Lean
proposition in `Schubert/RS/Statements/` and proved here by a library of its own. Some
intermediate theorems take one of these results as an explicit hypothesis (found by scanning
theorem types); `Schubert/RS/Main/Unconditional.lean` applies the proofs to them.

### `QuiverSaturation`

- Statement: Saturation of quiver multiplicities: for an acyclic quiver, a dimension vector and a dominant weight lam, if the multiplicity at N lam is positive for some N >= 1, it is positive at lam.
- Source: H. Derksen, J. Weyman, Semi-invariants of quivers and saturation for Littlewood-Richardson coefficients, J. Amer. Math. Soc. 13 (2000); in the form for multiplicities in the coordinate ring: V. Baldoni, M. Vergne, M. Walter, arXiv:1901.07194, Section 8.
- File: [Schubert/RS/Statements/QuiverSaturation.lean](../Schubert/RS/Statements/QuiverSaturation.lean)
- Proof: `quiverSaturation_holds` ([Schubert/RS/Quiver/Saturation.lean](../Schubert/RS/Quiver/Saturation.lean))
- Library: `Schubert/QuiverInvariants/`; main theorem `QuiverInvariants.FQuiver.exists_semiInvariant_of_nsmul` ([Schubert/QuiverInvariants/Saturation.lean](../Schubert/QuiverInvariants/Saturation.lean))
- Further results: `QuiverInvariants.FQuiver.exists_generalQuot_euler_add_extDim_nonpos` ([Schubert/QuiverInvariants/Schofield.lean](../Schubert/QuiverInvariants/Schofield.lean)), `QuiverInvariants.FQuiver.isGreatest_genericExt` ([Schubert/QuiverInvariants/Schofield.lean](../Schubert/QuiverInvariants/Schofield.lean)), `QuiverInvariants.FQuiver.exists_extDim_eq_zero` ([Schubert/QuiverInvariants/Schofield.lean](../Schubert/QuiverInvariants/Schofield.lean)), `QuiverInvariants.FQuiver.IsSemiInvariant.sum_mul_nonneg_of_generalQuot` ([Schubert/QuiverInvariants/King.lean](../Schubert/QuiverInvariants/King.lean)), `QuiverInvariants.FQuiver.exists_semiInvariant_iff` ([Schubert/QuiverInvariants/Saturation.lean](../Schubert/QuiverInvariants/Saturation.lean)), `Quiver.ForwardQuiver.multiplicity_flag` ([Schubert/RS/Quiver/Flag.lean](../Schubert/RS/Quiver/Flag.lean)), `Quiver.ForwardQuiver.multiplicity_const_pos_iff` ([Schubert/RS/Quiver/SemiInvariant.lean](../Schubert/RS/Quiver/SemiInvariant.lean)), `quiverSaturation_of_semiInvariant` ([Schubert/RS/Quiver/Saturation.lean](../Schubert/RS/Quiver/Saturation.lean))
- Intermediate theorems that take it as a hypothesis: `Algorithms.quiverPositivity_decision`, `Algorithms.quiverPositivity_decision_of_saturation`, `Quiver.ForwardQuiver.multiplicity_pos_of_nsmul`, `Quiver.Flat.quiverCoefficient_pos_iff_nonempty`, `Quiver.Flat.quiverCoefficient_pos_iff_ratFeasible`
- The same theorems with the proof applied: `Algorithms.quiverPositivity_decision_polyTime` ([Schubert/RS/Main/Unconditional.lean](../Schubert/RS/Main/Unconditional.lean)), `Quiver.ForwardQuiver.multiplicity_pos_of_nsmul_pos` ([Schubert/RS/Main/Unconditional.lean](../Schubert/RS/Main/Unconditional.lean)), `Quiver.Flat.quiverCoefficient_pos_iff_realPoint` ([Schubert/RS/Main/Unconditional.lean](../Schubert/RS/Main/Unconditional.lean)), `Quiver.Flat.quiverCoefficient_pos_iff_ratPoint` ([Schubert/RS/Main/Unconditional.lean](../Schubert/RS/Main/Unconditional.lean))

### `PolyTimeRationalFeasibility`

- Statement: Some polynomial-time function on bitstrings accepts exactly the encodings of the finite systems A x <= b with integer coefficients that have a rational solution.
- Source: L. G. Khachiyan, A polynomial algorithm in linear programming, Dokl. Akad. Nauk SSSR 244 (1979); E. Tardos, A strongly polynomial algorithm to solve combinatorial linear programs, Oper. Res. 34 (1986).
- File: [Schubert/RS/Statements/PolyTimeRationalFeasibility.lean](../Schubert/RS/Statements/PolyTimeRationalFeasibility.lean)
- Proof: `polyTimeRationalFeasibility_holds` ([Schubert/RS/Complexity/RationalFeasibility.lean](../Schubert/RS/Complexity/RationalFeasibility.lean))
- Library: `Schubert/LinearProgramming/`; main theorem `LinearProgramming.exists_mem_FP_feasible` ([Schubert/LinearProgramming/Feasibility.lean](../Schubert/LinearProgramming/Feasibility.lean))
- Further results: `LinearProgramming.decideFeasible_iff` ([Schubert/LinearProgramming/Chubanov/Decide.lean](../Schubert/LinearProgramming/Chubanov/Decide.lean)), `LinearProgramming.chubanov_iff` ([Schubert/LinearProgramming/Chubanov/Algorithm.lean](../Schubert/LinearProgramming/Chubanov/Algorithm.lean))
- Intermediate theorems that take it as a hypothesis: `Algorithms.quiverPositivity_decision_of_iff`, `Algorithms.quiverPositivity_decision`
- The same theorems with the proof applied: `Algorithms.quiverPositivity_decision_of_criterion` ([Schubert/RS/Main/Unconditional.lean](../Schubert/RS/Main/Unconditional.lean)), `Algorithms.quiverPositivity_decision_of_saturation` ([Schubert/RS/Main/Unconditional.lean](../Schubert/RS/Main/Unconditional.lean))

### `GLCharacterMultiplicity`

- Statement: For a polynomial representation of a product of general linear groups with character chi, the dimension of Hom(tensor of the irreducible V^lambda, representation) is the coefficient of the corresponding product of Schur polynomials in the Schur expansion of chi.
- Source: Complete reducibility, characters of irreducible polynomial representations, and Schur's lemma: W. Fulton, J. Harris, Representation Theory, Lectures 6 and 15; R. Stanley, Enumerative Combinatorics 2, Appendix 2, Theorem A2.4.
- File: [Schubert/RS/Statements/GLCharacterMultiplicity.lean](../Schubert/RS/Statements/GLCharacterMultiplicity.lean)
- Proof: `glCharacterMultiplicity_holds` ([Schubert/RS/GL/CharacterMultiplicity.lean](../Schubert/RS/GL/CharacterMultiplicity.lean))
- Library: `Schubert/GLRep/`; main theorem `GLRep.IsPolynomialLeviRep.exists_leviCharacter_eq_sum` ([Schubert/GLRep/Levi/Multiplicity.lean](../Schubert/GLRep/Levi/Multiplicity.lean))
- Further results: `GLRep.alternant_mul_glCharacter_of_isGlHighestWeightVector` ([Schubert/GLRep/Weyl/WeylCharacter.lean](../Schubert/GLRep/Weyl/WeylCharacter.lean)), `GLRep.IsPolynomialRep.isSemisimpleRepresentation` ([Schubert/GLRep/HighestWeight/CompleteReducibility.lean](../Schubert/GLRep/HighestWeight/CompleteReducibility.lean)), `GLRep.isIrreducible_irrep` ([Schubert/GLRep/HighestWeight/WeylModule.lean](../Schubert/GLRep/HighestWeight/WeylModule.lean)), `GLRep.character_irrep` ([Schubert/GLRep/HighestWeight/WeylModule.lean](../Schubert/GLRep/HighestWeight/WeylModule.lean)), `GLRep.IsPolynomialRep.exists_nonempty_equiv_irrep` ([Schubert/GLRep/HighestWeight/WeylModule.lean](../Schubert/GLRep/HighestWeight/WeylModule.lean)), `GLRep.IsPolynomialRep.nonempty_equiv_of_character_eq` ([Schubert/GLRep/HighestWeight/Classification.lean](../Schubert/GLRep/HighestWeight/Classification.lean)), `GLRep.finrank_intertwiningMap_irrep_self` ([Schubert/GLRep/HighestWeight/WeylModule.lean](../Schubert/GLRep/HighestWeight/WeylModule.lean)), `GLRep.finrank_intertwiningMap_irrep_of_ne` ([Schubert/GLRep/HighestWeight/WeylModule.lean](../Schubert/GLRep/HighestWeight/WeylModule.lean)), `GLRep.IsPolynomialRep.character_eq_diagramSchurPoly` ([Schubert/GLRep/Weyl/GroupCharacter.lean](../Schubert/GLRep/Weyl/GroupCharacter.lean)), `GLRep.IsPolynomialRep.exists_character_eq_sum` ([Schubert/GLRep/Multiplicity/GL.lean](../Schubert/GLRep/Multiplicity/GL.lean)), `GLRep.IsRationalRep.isSemisimpleRepresentation` ([Schubert/GLRep/Rational/GL.lean](../Schubert/GLRep/Rational/GL.lean)), `GLRep.IsRationalRep.exists_nonempty_equiv_ratIrrep` ([Schubert/GLRep/Rational/GL.lean](../Schubert/GLRep/Rational/GL.lean)), `GLRep.IsRationalRep.exists_ratCharacter_eq_sum` ([Schubert/GLRep/Rational/GL.lean](../Schubert/GLRep/Rational/GL.lean)), `GLRep.IsRationalLeviRep.exists_ratLeviCharacter_eq_sum` ([Schubert/GLRep/Rational/Levi.lean](../Schubert/GLRep/Rational/Levi.lean))
- Intermediate theorems that take it as a hypothesis: `Quiver.ForwardQuiver.finrank_intertwiningMap_coordRep_eq_multiplicity_of`, `Quiver.ForwardQuiver.finrank_intertwiningMap_coordRep_eq_multiplicity_of_gl`, `Quiver.atomCoefficient_eq_finrank_hom`, `Quiver.Flat.quiverTheorem_counts`
- The same theorems with the proof applied: `Quiver.ForwardQuiver.finrank_ratLeviIrrep_coordRep_eq_multiplicity` ([Schubert/RS/Main/Unconditional.lean](../Schubert/RS/Main/Unconditional.lean)), `Quiver.atomCoefficient_eq_finrank_quiverHom` ([Schubert/RS/Main/Unconditional.lean](../Schubert/RS/Main/Unconditional.lean)), `Quiver.Flat.quiverTheorem_identity` ([Schubert/RS/Main/Unconditional.lean](../Schubert/RS/Main/Unconditional.lean))

## Statements

### `thm:intro-family` (Theorem 1.1)

Status: **formalized**

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

The parameters are `P : Parameters` with delta = `P.K` and 4(p+q-1) variables = `P.rank`; the compositions of (eq:intro-family-arrays) are `a P`, `b P`, `c P`, and [A_c]f is `atomCoefficient f c`. Both expressions of (eq:intro-family-value) are `atomCoefficient_eq_paper` (in Q) and `atomCoefficient_eq_narayana` (in Z), with the Narayana number `narayana`; the negativity criterion is `atomCoefficient_neg_iff`. The remark after the theorem ((p,q) = (3,5) and (4,4) give -105 and -350 in 28 variables for every delta >= 8) is `atomCoefficient_threeFive` and `atomCoefficient_fourFour`; that the first negative cases within the family occur in 28 variables is `isLeast_rank_of_negative`. No hypothesis: the Joseph-Polo presentation, the Demazure character formula and the PBW theorem are proved in this development. The meaning of `atomCoefficient`: every polynomial is the Z-combination of the atoms with coefficients `atomCoefficient f u` (`atomCoefficient_spec`), and this expansion is unique (`atomCoefficient_eq_of_expansion`). As in the paper, the family is a Hall triple (`isHallTriple_family`, with the 2-Hall partition `familyHallPartition`) and Proposition prop:paired-reduction gives its coefficient (`atomCoefficient_eq_paired`).

### `cor:intro-filtrations` (Corollary 1.2)

Status: **formalized**

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

Formalized for the sheaf-theoretic modules over C. The Schubert varieties X_w (the scheme-theoretic images of the B-orbit maps), the unions X_S and the Schubert boundaries are closed subschemes of the flag scheme Fl_n (`schubertVariety`, `schubertUnion`, `schubertBoundary`); L(eta) is the line bundle GL_n x^B C_eta (`lineBundle`), and H^0(X, L(eta)) is the module of global sections of its pullback to X (`sections`), with B acting by left translation (`sectionsRep`) and restriction of sections along X' in X (`sectionsRestrict`). P(nu) = H^0(X_sigma, L(eta)) (`FlagVarieties.dualJoseph`), Q(nu) is the kernel of the restriction from P(nu) to the sections over the Schubert boundary (`geometricMinimalRelativeSchubert`), and the module of the corollary is P(-a) (x) P(-b) (`geometricFamilyTensor`, of character kappa_a kappa_b: `ch_geometricFamilyTensor`). 'Admits a relative Schubert filtration' is `HasGeometricRelativeSchubertFiltration` (layers isomorphic to the geometric Q(nu)); 'Schubert filtration in Polo's sense' is `HasGeometricSchubertFiltration` (layers isomorphic to H^0(X_S, L(eta)) over a nonempty union X_S, S a Bruhat order ideal, eta antidominant); the SL_n forms ask for the layers over the Borel subgroup of SL_n. The SL_n forms and type A_27 at (p,q) = (3,5) are included. The identification of the sheaf-theoretic modules with the algebraic model is proved: H^0(X, L(eta)) is the module of B-semi-invariants of weight eta in the coordinate ring of the preimage of X in GL_n (`sectionsEquivSemiInvariants`, over every commutative ring), which for X = X_S is the ring model of the section module (`geometricSectionEquiv`, using `preimageIdeal_schubertUnion_eq_orbitIdeal_complex`: the ideal of the preimage of X_S is that of the union of the double cosets BwB, w in S); P(nu) and Q(nu) are the ring-model modules (`dualJosephEquiv`, `geometricMinimalRelativeSchubertEquiv`); and for eta = -lambda the section module is the B-module (demazureUnionModule m S).dual of `BModules.BModule` (`sectionBModuleIso`), the module underlying `schubertSectionModule` of the algebraic model. The equality Gamma(X_w, O) = C used by the section bases is proved (`globalSectionsConstant_complex`). The proof is the paper's: a filtration would make kappa_a kappa_b a nonnegative integral combination of atoms, contradicting Theorem 1.1. The Polo case is proved through the characters of the Polo layers (sums of atoms) rather than by refining with van der Kallen's Proposition 2.3.11. The module-level endpoints of release 2.0.0 are listed separately as the algebraic model: B-modules are finite-dimensional modules for the strictly upper triangular matrices and the diagonal torus with integral weight spaces (`BModules.BModule`), the section module over X_S is the twisted dual of the sum of the Demazure modules D_w, w in S, in the flag-minor model (`schubertSectionModule`), P(nu) and Q(nu) are defined from it (`dualJoseph`, `minRelSchubert`), and the flag-minor span is proved irreducible and identified with V(lambda) (`HighestWeight`).

### `cor:intro-lascoux` (Corollary 1.3)

Status: **formalized**

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

Lascoux polynomials are defined, as in Lascoux's original definition, by the K-theoretic isobaric divided difference operators pi_i^(beta) f = pi_i((1 + beta x_{i+1}) f); Lascoux atoms are defined by the operators pi_i^(beta) - 1 (Monical; Monical, Pechenik and Searles, Remark 4.24), in the same convention. `not_lascouxAtomPositive` is the statement with coefficients in Z_{>=0}[beta]; `no_lascouxExpansion_nonnegAtZero` is the stronger form with coefficients in Z[beta] that are nonnegative at beta = 0.

### `thm:intro-quiver-polytope` (Theorem 1.4)

Status: **formalized**. Uses the standard results `GLCharacterMultiplicity`, `PolyTimeRationalFeasibility`, `QuiverSaturation` (proved here)

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

The triple is given as lists a, b, c of natural numbers, read as weak compositions of length n = c.length (`listComp`): shorter lists are padded with 0, and entries of a or b beyond c.length are dropped, on both sides of every statement (`IsQuiverTripleList` requires the three lengths to be equal); the number of variables n is part of the input. P(a,b,c) is the explicit system of integer linear inequalities `quiverPolytope a b c` (dimension M = 2n^3 + 2n^4, coefficients in {-1,0,1}), with real points `points ℝ` and integer points `intPoints`. The displayed identity [A_c](kappa_a kappa_b) = dim Hom_{L_I}(tensor V_p^{lambda^(p)}, R_Q) = #(P(a,b,c) ∩ Z^M), with the Hom space finite-dimensional and the integer points finite: `quiverTheorem_identity`, which is `quiverTheorem_counts` applied to `glCharacterMultiplicity_holds` (the outer equality alone is `quiverPolytope_card`); boundedness: `quiverPolytope_bounded`. Positivity: [A_c](kappa_a kappa_b) > 0 iff P(a,b,c) is nonempty (`quiverCoefficient_pos_iff_realPoint`, real points; `quiverCoefficient_pos_iff_ratPoint`, rational points), which are `quiverCoefficient_pos_iff_nonempty` and `quiverCoefficient_pos_iff_ratFeasible` applied to `quiverSaturation_holds` (library `Schubert/QuiverInvariants`). The direction "positive implies nonempty" needs no saturation (`nonempty_of_quiverCoefficient_pos`), and P(a,b,c) is nonempty iff some dilation N(a,b,c), N >= 1, has a positive coefficient (`quiverPolytope_nonempty_iff_exists_nsmul_pos`, `quiverPolytope_ratFeasible_iff_exists_nsmul_pos`, with `atomCoefficient_nsmul_eq_card`). Complexity: recognition of quiver triples (`quiverTriple_recognition`) and construction of P(a,b,c) (`quiverPolytope_construction`, for every triple; description size `quiverPolytope_size`) in polynomial time, which is complexitylib's `Complexity.FP` on the binary encoding `encodeTriple` (its length is linear in the binary size of (a,b,c)); the polynomial-time decision of positivity (`quiverPositivity_decision_polyTime`), which is `quiverPositivity_decision` applied to `quiverSaturation_holds` and `polyTimeRationalFeasibility_holds` (library `Schubert/LinearProgramming`; the intermediate steps are `quiverPositivity_decision_of_saturation` and, with the criterion itself as the hypothesis, `quiverPositivity_decision_of_criterion`). Sanity checks that the complexity classes are non-trivial: `exists_not_mem_FP`, `exists_mem_P_not_mem_DTIME`.

### `cor:intro-quiver-density` (Corollary 1.5)

Status: **formalized**

- `Quiver.Density.card_positiveQuiverTriples_isTheta` ([Schubert/RS/Quiver/Density/Count.lean](../Schubert/RS/Quiver/Density/Count.lean))
- `Quiver.Density.positiveQuiverTriples_proportion` ([Schubert/RS/Quiver/Density/Count.lean](../Schubert/RS/Quiver/Density/Count.lean))
- `Quiver.Density.positiveQuiverTriples` ([Schubert/RS/Quiver/Density/Count.lean](../Schubert/RS/Quiver/Density/Count.lean))

`positiveQuiverTriples n H` is the set Q_n^+(H) of quiver triples in {0,...,H}^n with positive atom coefficient; `card_positiveQuiverTriples_isTheta` is #Q_n^+(H) = Theta(H^(3n-1)) for n >= 4, and `positiveQuiverTriples_proportion` the proportion bounded away from zero among the triples with |a| + |b| = |c|. The proof uses Proposition prop:quiver-two-source and none of the standard results stated in `Schubert/RS/Statements/`.

### `lem:duality`

Status: **formalized**

- `atomCoefficient_eq_rectangleCoefficient` ([Schubert/RS/AtomCoefficients.lean](../Schubert/RS/AtomCoefficients.lean))
- `rectangleCoefficient` ([Schubert/RS/RectangleCoefficient.lean](../Schubert/RS/RectangleCoefficient.lean))
- `keyAtom_orthogonality` ([Schubert/RS/GlobalDuality.lean](../Schubert/RS/GlobalDuality.lean))
- `Representation.compositionFlagJosephPolo` ([Schubert/RS/JosephPolo/GeneralTheorem.lean](../Schubert/RS/JosephPolo/GeneralTheorem.lean))
- `Representation.compositionFlagDemazureCharacter` ([Schubert/RS/JosephPolo/GeneralTheorem.lean](../Schubert/RS/JosephPolo/GeneralTheorem.lean))
- `Representation.orderedPBWBasis_exists` ([Schubert/RS/PBW/Theorem.lean](../Schubert/RS/PBW/Theorem.lean))
- `atomCoefficient_eq_rectangleCoefficient'` ([Schubert/RS/AtomCoefficientSpec.lean](../Schubert/RS/AtomCoefficientSpec.lean))

`rectangleCoefficient N c f` is [x^{N 1}] f kappa_{N 1 - c} Delta_n(x). The Lean statement takes the Joseph-Polo presentation, the Demazure character formula and the PBW basis as hypotheses; all three are proved in this development (`compositionFlagJosephPolo`, `compositionFlagDemazureCharacter`, `orderedPBWBasis_exists`) and are discharged wherever the lemma is used. The Fu-Lascoux duality (eq:fl-pairing) is proved as `keyAtom_orthogonality`. `atomCoefficient_eq_rectangleCoefficient'` is the lemma with the three theorems already applied, without hypotheses.

### `prop:window`

Status: **formalized**

- `Window.window_rational_extraction` ([Schubert/RS/Window/General.lean](../Schubert/RS/Window/General.lean))
- `Window.window_product_indep` ([Schubert/RS/Window/General.lean](../Schubert/RS/Window/General.lean))
- `Window.Hypotheses` ([Schubert/RS/Window/Basic.lean](../Schubert/RS/Window/Basic.lean))
- `Window.WindowInequality` ([Schubert/RS/Window/Basic.lean](../Schubert/RS/Window/Basic.lean))
- `Window.prefixHeight` ([Schubert/RS/Window/Basic.lean](../Schubert/RS/Window/Basic.lean))
- `Window.cmp` ([Schubert/RS/Window/Basic.lean](../Schubert/RS/Window/Basic.lean))
- `Window.hypotheses_iff_of_le` ([Schubert/RS/Window/Basic.lean](../Schubert/RS/Window/Basic.lean))

The rational extraction formula (eq:rational-extraction) is stated in the simple-root coordinates of the positive-root cone: x_i/x_j is the monomial of `rootDegree i j` and x^{c-a-b} that of `heightDegree a b c`. Independence of N (the remark before the proposition): `hypotheses_iff_of_le`, `window_product_indep`.

### `lem:hall-determinant`

Status: **formalized**

- `Hall.hall_determinant` ([Schubert/RS/Hall/Determinant.lean](../Schubert/RS/Hall/Determinant.lean))
- `Hall.hallProduct` ([Schubert/RS/Hall/Determinant.lean](../Schubert/RS/Hall/Determinant.lean))
- `Hall.hallMatrix` ([Schubert/RS/Hall/Determinant.lean](../Schubert/RS/Hall/Determinant.lean))
- `Hall.completeH` ([Schubert/RS/Hall/Determinant.lean](../Schubert/RS/Hall/Determinant.lean))
- `Hall.hallSum` ([Schubert/RS/Hall/Determinant.lean](../Schubert/RS/Hall/Determinant.lean))
- `Hall.IsHallAdmissible` ([Schubert/RS/Hall/Admissible.lean](../Schubert/RS/Hall/Admissible.lean))
- `HallLattice.hall_determinant` ([Schubert/RS/HallDeterminant.lean](../Schubert/RS/HallDeterminant.lean))
- `hall_source_extraction` ([Schubert/RS/HallSourceExtraction.lean](../Schubert/RS/HallSourceExtraction.lean))

`hall_determinant` states both equalities for weakly increasing heights l_1 <= ... <= l_m (the bound l_j <= d is not needed, and the rows R_i may be empty), with the t_j in any commutative ring and positions 0-based. Each geometric series (1 - x_i t_j)^(-1) is truncated in a degree B >= d (`hallProduct`), which does not change the coefficient of x_1...x_d. The case d = 0 is included. The flagged-column identity used in the proof (eq:flagged-column), for nonempty rows, is `HallLattice.hall_determinant`, proved by the paper's path involution; `hall_source_extraction` is its extraction form.

### `lem:hall-flags`

Status: **formalized**

- `Hall.hall_flags` ([Schubert/RS/Hall/Admissible.lean](../Schubert/RS/Hall/Admissible.lean))
- `Hall.hallFlag` ([Schubert/RS/Hall/Admissible.lean](../Schubert/RS/Hall/Admissible.lean))
- `Hall.firstAbove` ([Schubert/RS/Hall/Admissible.lean](../Schubert/RS/Hall/Admissible.lean))
- `Hall.isHallAdmissible_iff_flags` ([Schubert/RS/Hall/Admissible.lean](../Schubert/RS/Hall/Admissible.lean))

For weakly increasing heights. A subset {j_1 < ... < j_d} is a strictly increasing J : Fin d -> Fin m with j_k = J (k - 1) + 1; the canonical flags (eq:canonical-flags) `hallFlag` keep the paper's 1-based values, an empty minimum being m + 1 (`firstAbove`).

### `def:paired-target`

Status: **formalized**

- `Hall.HallPartition` ([Schubert/RS/Hall/Partition.lean](../Schubert/RS/Hall/Partition.lean))
- `Hall.IsHallTriple` ([Schubert/RS/Hall/Partition.lean](../Schubert/RS/Hall/Partition.lean))
- `Hall.isHallTriple_iff` ([Schubert/RS/Hall/Partition.lean](../Schubert/RS/Hall/Partition.lean))
- `Hall.HallPartition.changeN` ([Schubert/RS/Hall/Partition.lean](../Schubert/RS/Hall/Partition.lean))
- `Family.familyHallPartition` ([Schubert/RS/Family/HallPartition.lean](../Schubert/RS/Family/HallPartition.lean))
- `Family.isHallTriple_family` ([Schubert/RS/Family/HallPartition.lean](../Schubert/RS/Family/HallPartition.lean))

An r-Hall partition is a `Finpartition` of the positions with r distinguished blocks indexed by Fin r, every other block of size at most two, and conditions (i)-(iii); the degree equality |a| + |b| = |c|, the bound N >= max c and condition (iii) form the field `hypotheses` (the hypotheses of prop:window). Independence of N (the remark after the definition): `HallPartition.changeN`, `isHallTriple_iff`. The counterexample family has a 2-Hall partition (`familyHallPartition`), so the definition is not vacuous.

### `prop:paired-reduction`

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

For every r-Hall partition, with arbitrary interleavings of the blocks and arbitrary height profiles. The coefficient [t_1...t_m] is taken in the Laurent polynomials in t_1, ..., t_m (`tVar j` is t_j). The notation before the proposition: the positions q_j (`HallPartition.q`), the pairs E (`pairs`), the heights l_{s,j} (`height`), the flags f_{s,k} (`flag`), the Hall polynomials P_s of (eq:hall-polynomial) (`blockPolynomial`), and m = sum_s |B_s| (`m_eq_sum_card`). The Lean proof of Theorem 1.1 uses its own two-block instance, `double_source_extraction`. `paired_reduction_of_isHallTriple` is the statement for a Hall triple (some Hall partition). For the counterexample family it gives `atomCoefficient_eq_paired`.

### `lem:two-source-count`

Status: **formalized**

- `Family.two_source_count` ([Schubert/RS/Family/TwoSourceCount.lean](../Schubert/RS/Family/TwoSourceCount.lean))

For every perfect matching E between {1,...,m} and {m+1,...,2m}, given by a permutation of Fin m. The variables are relabelled: the paper's t_1, ..., t_m sit at the slots `slotRight i` (0-based position 2m-1-i) and t_{m+1}, ..., t_{2m} at the slots `slotLeft i` (position i). The coefficient of t_1...t_{2m} does not change under a permutation of the variables, so the statement is the same.

### `def:quiver-triple`

Status: **formalized**

- `Quiver.IsQuiverTriple` ([Schubert/RS/Quiver/Triple/Basic.lean](../Schubert/RS/Quiver/Triple/Basic.lean))
- `Quiver.IsQuiverPartition` ([Schubert/RS/Quiver/Triple/Basic.lean](../Schubert/RS/Quiver/Triple/Basic.lean))
- `Quiver.isQuiverPartition_iff_of_le` ([Schubert/RS/Quiver/Triple/Basic.lean](../Schubert/RS/Quiver/Triple/Basic.lean))
- `Quiver.isQuiverTriple_iff_canonical` ([Schubert/RS/Quiver/Triple/Canonical.lean](../Schubert/RS/Quiver/Triple/Canonical.lean))
- `Quiver.IsQuiverPartition.eq_canonical` ([Schubert/RS/Quiver/Triple/Canonical.lean](../Schubert/RS/Quiver/Triple/Canonical.lean))
- `Quiver.instDecidableIsQuiverTriple` ([Schubert/RS/Quiver/Triple/Canonical.lean](../Schubert/RS/Quiver/Triple/Canonical.lean))
- `Algorithms.IsQuiverTripleList` ([Schubert/RS/Complexity/Encoding.lean](../Schubert/RS/Complexity/Encoding.lean))

Interval partitions are Mathlib compositions of n; `IsQuiverTriple` uses N = max c, and the conditions do not depend on N (`isQuiverPartition_iff_of_le`, the remark after the definition). The partition is unique, the canonical one (`IsQuiverPartition.eq_canonical`, the paper's recognition argument), so being a quiver triple is decidable.

### `thm:quiver-coefficient`

Status: **formalized**. Uses the standard result `GLCharacterMultiplicity` (proved here)

- `Quiver.atomCoefficient_eq_finrank_quiverHom` ([Schubert/RS/Main/Unconditional.lean](../Schubert/RS/Main/Unconditional.lean))
- `Quiver.atomCoefficient_eq_finrank_hom` ([Schubert/RS/Quiver/HomSpace.lean](../Schubert/RS/Quiver/HomSpace.lean))
- `Quiver.finiteDimensional_quiverHom` ([Schubert/RS/Quiver/HomSpace.lean](../Schubert/RS/Quiver/HomSpace.lean))
- `Quiver.atomCoefficient_eq_multiplicity` ([Schubert/RS/Quiver/Extraction.lean](../Schubert/RS/Quiver/Extraction.lean))
- `Quiver.atomCoefficient_nonneg` ([Schubert/RS/Quiver/Polytope/Positivity.lean](../Schubert/RS/Quiver/Polytope/Positivity.lean))
- `Quiver.quiverOf` ([Schubert/RS/Quiver/OfTriple.lean](../Schubert/RS/Quiver/OfTriple.lean))
- `Quiver.leviWeight` ([Schubert/RS/Quiver/OfTriple.lean](../Schubert/RS/Quiver/OfTriple.lean))
- `Quiver.ForwardQuiver.multiplicity` ([Schubert/RS/Quiver/Multiplicity.lean](../Schubert/RS/Quiver/Multiplicity.lean))
- `GL.ratLeviIrrep` ([Schubert/RS/GL/Basic.lean](../Schubert/RS/GL/Basic.lean))

`atomCoefficient_eq_finrank_quiverHom` is (eq:quiver-multiplicity): for a quiver partition I of (a,b,c) and N >= max c, [A_c](kappa_a kappa_b) = dim Hom_{L_I}(tensor_p V_p^{lambda^(p)}, R_Q), with L_I = prod_p GL(V_p) acting on the coordinate ring R_Q of the representation space of `quiverOf a b c N I` and V_p^{lambda^(p)} the irreducible rational representations `ratLeviIrrep` (flag-minor models). It is `atomCoefficient_eq_finrank_hom` applied to the proof `glCharacterMultiplicity_holds` of `GLCharacterMultiplicity` (library `Schubert/GLRep`); the Hom space is finite-dimensional (`finiteDimensional_quiverHom`). At the level of characters: the coefficient is the multiplicity of the product of the Schur polynomials s_{lambda^(p)} in the graded character of R_Q (`atomCoefficient_eq_multiplicity`). Nonnegativity: `atomCoefficient_nonneg`.

### `prop:quiver-two-source`

Status: **formalized**

- `Quiver.twoSource_isQuiverPartition` ([Schubert/RS/Quiver/TwoSource.lean](../Schubert/RS/Quiver/TwoSource.lean))
- `Quiver.twoSource_eq_weylProjector` ([Schubert/RS/Quiver/TwoSource.lean](../Schubert/RS/Quiver/TwoSource.lean))
- `Quiver.twoSource_eq_kostka` ([Schubert/RS/Quiver/TwoSource.lean](../Schubert/RS/Quiver/TwoSource.lean))
- `Quiver.twoSource_pos_iff` ([Schubert/RS/Quiver/TwoSource.lean](../Schubert/RS/Quiver/TwoSource.lean))
- `Algorithms.twoSource_coefficient_computable` ([Schubert/RS/Complexity/TwoSourceAlgorithm.lean](../Schubert/RS/Complexity/TwoSourceAlgorithm.lean))
- `Algorithms.encodeTripleUnary` ([Schubert/RS/Complexity/UnaryEncoding.lean](../Schubert/RS/Complexity/UnaryEncoding.lean))
- `Algorithms.length_encodeTripleUnary_ofFn` ([Schubert/RS/Complexity/UnaryEncoding.lean](../Schubert/RS/Complexity/UnaryEncoding.lean))
- `Algorithms.encodeTripleUnary_injective` ([Schubert/RS/Complexity/UnaryEncoding.lean](../Schubert/RS/Complexity/UnaryEncoding.lean))
- `Algorithms.twoSource_eq_count` ([Schubert/RS/Complexity/TwoSourceCoefficient.lean](../Schubert/RS/Complexity/TwoSourceCoefficient.lean))

`twoSource_isQuiverPartition`: (a,b,c) is a quiver triple for the interval partition {1,2},{3},...,{n}. `twoSource_eq_weylProjector`: (eq:quiver-two-source), with the right-hand side written as the Weyl projector of (eq:quiver-weyl-projector) at u = (nu_1, nu_2), applied to the product of the h_(r_j)(x_1,x_2); this is the coefficient of s_(nu2,nu1), and `twoSource_eq_kostka` identifies it with the number of semistandard tableaux of shape (nu2,nu1) and content (r_1,...,r_m). `twoSource_pos_iff`: (eq:quiver-star-support). The last sentence of the proposition, that the coefficient in (eq:quiver-two-source) can be computed by a deterministic algorithm whose running time is polynomial in n+|a|+|b|+|c|: `twoSource_coefficient_computable`. Polynomial time is complexitylib's `Complexity.FP`; the input is the unary encoding `encodeTripleUnary` of (a,b,c), which is injective (`encodeTripleUnary_injective`) and has length 4(|a|+|b|+|c|)+6n+8 (`length_encodeTripleUnary_ofFn`), so polynomial in its length means polynomial in n+|a|+|b|+|c|; the output is the encoding of the integer coefficient, for every triple satisfying the hypotheses of the proposition. The algorithm is the dynamic program `twoSourceCount` on the r_j with binary values (`twoSource_eq_count`). Lean also allows m = 0, where the paper requires m >= 1.

## Displayed identities

### `eq:intro-bru-refinement`

Status: **formalized**

- `SchubertUnions.key_eq_sum_atom` ([Schubert/RS/SchubertUnions/BruhatRefinement.lean](../Schubert/RS/SchubertUnions/BruhatRefinement.lean))

kappa_{sigma lambda} = sum over u in W^lambda, u <= sigma of A_{u lambda}.

### `eq:intro-geometric-characters`

Status: **formalized**

- `FlagVarieties.ch_dualJoseph_negWeight` ([Schubert/FlagVarieties/Modules/Geometric.lean](../Schubert/FlagVarieties/Modules/Geometric.lean))
- `Geometric.ch_geometricMinimalRelativeSchubert_negWeight` ([Schubert/RS/Geometric/SchemeRelative.lean](../Schubert/RS/Geometric/SchemeRelative.lean))
- `Geometric.geometricMinimalRelativeSchubert_weightSpace_ne_bot` ([Schubert/RS/Geometric/SchemeRelative.lean](../Schubert/RS/Geometric/SchemeRelative.lean))

Algebraic model:

- `Filtrations.dualJoseph_hasCharacter` ([Schubert/RS/Filtrations/SectionModules.lean](../Schubert/RS/Filtrations/SectionModules.lean))
- `Filtrations.minRelSchubert_hasCharacter` ([Schubert/RS/Filtrations/RelativeSchubertCharacters.lean](../Schubert/RS/Filtrations/RelativeSchubertCharacters.lean))

ch P(-u) = kappa_u and ch Q(-u) = A_u for the sheaf-theoretic modules over C: P(nu) = H^0(X_sigma, L(eta)) (`FlagVarieties.dualJoseph`) and Q(nu) the kernel of the restriction to the Schubert boundary (`geometricMinimalRelativeSchubert`); the weight nu occurs in Q(nu). They are computed through the identification with the ring model (`dualJosephEquiv`, `geometricMinimalRelativeSchubertEquiv`, from `sectionsEquivSemiInvariants`). The same identities for the module-level P and Q of release 2.0.0 are listed separately as the algebraic model.

### `eq:intro-duality`

Status: **formalized**

- `atomCoefficient_eq_rectangleCoefficient` ([Schubert/RS/AtomCoefficients.lean](../Schubert/RS/AtomCoefficients.lean))

Same identity as lem:duality.
