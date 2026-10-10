import RSCounterexample.Paper.Main
import RSCounterexample.GLRep.Audit
import RSCounterexample.QuiverInvariants.Audit

/-!
# Audit of the main results

Prints the signatures of the main declarations, with their hypotheses, and their
transitive axiom dependencies. The expected axioms are only `propext`,
`Classical.choice` and `Quot.sound`.
-/

#check @Schubert.RS.Family.atomCoefficient_eq
#check @Schubert.RS.Family.atomCoefficient_factorization
#check @Schubert.RS.Family.atomCoefficient_neg_iff
#check @Schubert.RS.Family.existsUnique_atomExpansion
#check @Schubert.RS.Family.not_atomPositive
#check @Schubert.RS.Family.rank28_atomCoefficient
#check @Schubert.RS.Family.rank28_not_atomPositive
#check @Schubert.RS.Family.reiner_shimozono_false
#check @Schubert.RS.Family.atomCoefficient_eq_narayana
#check @Schubert.RS.Family.atomCoefficient_eq_paper
#check @Schubert.RS.Family.atomCoefficient_threeFive
#check @Schubert.RS.Family.atomCoefficient_fourFour
#check @Schubert.RS.Family.isLeast_rank_of_negative
#check @Schubert.RS.Family.narayana
#check @Schubert.RS.Family.Parameters
#check @Schubert.RS.Family.a
#check @Schubert.RS.Family.b
#check @Schubert.RS.Family.c
#check @Schubert.RS.atomCoefficient_spec
#check @Schubert.RS.atomCoefficient_eq_of_expansion
#check @Schubert.RS.Family.isHallTriple_family
#check @Schubert.RS.Family.atomCoefficient_eq_paired
#check @Schubert.RS.Geometric.not_hasGeometricRelativeSchubertFiltration
#check @Schubert.RS.Geometric.not_hasGeometricSchubertFiltration
#check @Schubert.RS.Geometric.not_hasGeometricSLRelativeSchubertFiltration
#check @Schubert.RS.Geometric.not_hasGeometricSLSchubertFiltration
#check @Schubert.RS.Geometric.typeA27_geometricFiltration_failure
#check @Schubert.RS.Geometric.geometricFamilyTensor
#check @Schubert.RS.Geometric.ch_geometricFamilyTensor
#check @FlagVarieties.dualJoseph
#check @Schubert.RS.Geometric.geometricMinimalRelativeSchubert
#check @Schubert.RS.Geometric.geometricBoundaryRestrict
#check @Schubert.RS.Geometric.IsGeometricSchubertLayer
#check @Schubert.RS.Geometric.IsGeometricMinimalRelativeSchubertLayer
#check @Schubert.RS.Geometric.HasGeometricRelativeSchubertFiltration
#check @Schubert.RS.Geometric.HasGeometricSchubertFiltration
#check @Schubert.RS.Geometric.HasGeometricSLRelativeSchubertFiltration
#check @Schubert.RS.Geometric.HasGeometricSLSchubertFiltration
#check @FlagVarieties.schubertVariety
#check @FlagVarieties.schubertUnion
#check @FlagVarieties.schubertBoundary
#check @FlagVarieties.lineBundle
#check @FlagVarieties.sections
#check @FlagVarieties.sectionsRep
#check @FlagVarieties.sectionsEquivSemiInvariants
#check @FlagVarieties.sectionsRestrict
#check @FlagVarieties.sectionsRestrictHom_eq_sectionsRestrict
#check @FlagVarieties.preimageIdeal_schubertUnion_eq_orbitIdeal_complex
#check @FlagVarieties.globalSectionsConstant_complex
#check @FlagVarieties.geometricSectionEquiv
#check @FlagVarieties.dualJosephEquiv
#check @Schubert.RS.Geometric.geometricMinimalRelativeSchubertEquiv
#check @Schubert.RS.Geometric.isGeometricSchubertLayer_iff
#check @Schubert.RS.Geometric.isGeometricMinimalRelativeSchubertLayer_iff
#check @FlagVarieties.sectionBModuleIso
#check @Schubert.RS.Family.not_hasRelativeSchubertFiltration
#check @Schubert.RS.Family.not_hasSchubertFiltration
#check @Schubert.RS.Family.not_hasSLRelativeSchubertFiltration
#check @Schubert.RS.Family.not_hasSLSchubertFiltration
#check @Schubert.RS.Family.rank_sub_one
#check @Schubert.RS.Family.typeA27_filtration_failure
#check @Schubert.RS.Family.factors_hasExcellentFiltration
#check @Schubert.RS.Family.familyTensor
#check @Schubert.RS.Family.familyTensor_hasCharacter
#check @Schubert.RS.Filtrations.HasRelativeSchubertFiltration
#check @Schubert.RS.Filtrations.HasSchubertFiltration
#check @Schubert.RS.Filtrations.HasExcellentFiltration
#check @Schubert.RS.Filtrations.HasSLRelativeSchubertFiltration
#check @Schubert.RS.Filtrations.HasSLSchubertFiltration
#check @Schubert.RS.Filtrations.schubertSectionModule
#check @Schubert.RS.Filtrations.dualJoseph
#check @Schubert.RS.Filtrations.minRelSchubert
#check @Schubert.RS.HighestWeight.flagOrbitSpan_irreducible
#check @Schubert.RS.Family.not_lascouxAtomPositive
#check @Schubert.RS.Family.no_lascouxExpansion_nonnegAtZero
#check @Schubert.RS.Family.rank28_not_lascouxAtomPositive
#check @Schubert.RS.Family.lascoux_product_positivity_false
#check @Schubert.RS.betaIsobaric
#check @Schubert.RS.betaAtomOperator
#check @Schubert.RS.lascoux
#check @Schubert.RS.lascouxAtom
#check @Schubert.RS.betaZero_lascoux
#check @Schubert.RS.betaZero_lascouxAtom
#check @Schubert.RS.LascouxAtomPositive
#check @Schubert.RS.Quiver.Flat.quiverPolytope
#check @Schubert.RS.Quiver.Flat.quiverTheorem_identity
#check @Schubert.RS.Quiver.Flat.quiverTheorem_counts
#check @Schubert.RS.Quiver.Flat.quiverPolytope_card
#check @Schubert.RS.Quiver.Flat.finiteDimensional_canonicalHom
#check @Schubert.RS.Quiver.Flat.quiverPolytope_bounded
#check @Schubert.RS.Quiver.Flat.quiverCoefficient_pos_iff_realPoint
#check @Schubert.RS.Quiver.Flat.quiverCoefficient_pos_iff_ratPoint
#check @Schubert.RS.Quiver.Flat.quiverCoefficient_pos_iff_nonempty
#check @Schubert.RS.Quiver.Flat.quiverCoefficient_pos_iff_ratFeasible
#check @Schubert.RS.Quiver.Flat.nonempty_of_quiverCoefficient_pos
#check @Schubert.RS.Quiver.Flat.quiverPolytope_nonempty_iff_exists_nsmul_pos
#check @Schubert.RS.Quiver.Flat.quiverPolytope_ratFeasible_iff_exists_nsmul_pos
#check @Schubert.RS.Quiver.Flat.atomCoefficient_nsmul_eq_card
#check @Schubert.RS.quiverSaturation_holds
#check @Schubert.RS.Quiver.atomCoefficient_eq_multiplicity
#check @Schubert.RS.Algorithms.quiverTriple_recognition
#check @Schubert.RS.Algorithms.quiverPolytope_construction
#check @Schubert.RS.Algorithms.quiverPolytope_size
#check @Schubert.RS.Algorithms.quiverPositivity_decision_polyTime
#check @Schubert.RS.Algorithms.quiverPositivity_decision
#check @Schubert.RS.Algorithms.quiverPositivity_decision_of_saturation
#check @Schubert.RS.Algorithms.quiverPositivity_decision_of_criterion
#check @Schubert.RS.Algorithms.quiverPositivity_decision_of_iff
#check @Schubert.RS.Algorithms.encodeTriple
#check @Schubert.RS.Algorithms.IsQuiverTripleList
#check @Schubert.RS.Algorithms.binarySize_le_length
#check @Schubert.RS.Algorithms.length_le_binarySize
#check @Schubert.RS.Algorithms.exists_not_mem_FP
#check @Schubert.RS.Algorithms.exists_mem_P_not_mem_DTIME
#check @Schubert.RS.Quiver.Density.card_positiveQuiverTriples_isTheta
#check @Schubert.RS.Quiver.Density.positiveQuiverTriples_proportion
#check @Schubert.RS.Quiver.Density.positiveQuiverTriples
#check @Schubert.RS.atomCoefficient_eq_rectangleCoefficient
#check @Schubert.RS.rectangleCoefficient
#check @Schubert.RS.keyAtom_orthogonality
#check @Schubert.RS.Representation.compositionFlagJosephPolo
#check @Schubert.RS.Representation.compositionFlagDemazureCharacter
#check @Schubert.RS.Representation.orderedPBWBasis_exists
#check @Schubert.RS.atomCoefficient_eq_rectangleCoefficient'
#check @Schubert.RS.Window.window_rational_extraction
#check @Schubert.RS.Window.window_product_indep
#check @Schubert.RS.Window.Hypotheses
#check @Schubert.RS.Window.WindowInequality
#check @Schubert.RS.Window.prefixHeight
#check @Schubert.RS.Window.cmp
#check @Schubert.RS.Window.hypotheses_iff_of_le
#check @Schubert.RS.Hall.hall_determinant
#check @Schubert.RS.Hall.hallProduct
#check @Schubert.RS.Hall.hallMatrix
#check @Schubert.RS.Hall.completeH
#check @Schubert.RS.Hall.hallSum
#check @Schubert.RS.Hall.IsHallAdmissible
#check @Schubert.RS.HallLattice.hall_determinant
#check @Schubert.RS.hall_source_extraction
#check @Schubert.RS.Hall.hall_flags
#check @Schubert.RS.Hall.hallFlag
#check @Schubert.RS.Hall.firstAbove
#check @Schubert.RS.Hall.isHallAdmissible_iff_flags
#check @Schubert.RS.Hall.HallPartition
#check @Schubert.RS.Hall.IsHallTriple
#check @Schubert.RS.Hall.isHallTriple_iff
#check @Schubert.RS.Hall.HallPartition.changeN
#check @Schubert.RS.Family.familyHallPartition
#check @Schubert.RS.Hall.paired_reduction
#check @Schubert.RS.Hall.tVar
#check @Schubert.RS.Hall.HallPartition.q
#check @Schubert.RS.Hall.HallPartition.pairs
#check @Schubert.RS.Hall.HallPartition.height
#check @Schubert.RS.Hall.HallPartition.flag
#check @Schubert.RS.Hall.HallPartition.blockPolynomial
#check @Schubert.RS.Hall.HallPartition.m_eq_sum_card
#check @Schubert.RS.double_source_extraction
#check @Schubert.RS.Hall.paired_reduction_of_isHallTriple
#check @Schubert.RS.Family.two_source_count
#check @Schubert.RS.Quiver.IsQuiverTriple
#check @Schubert.RS.Quiver.IsQuiverPartition
#check @Schubert.RS.Quiver.isQuiverPartition_iff_of_le
#check @Schubert.RS.Quiver.isQuiverTriple_iff_canonical
#check @Schubert.RS.Quiver.IsQuiverPartition.eq_canonical
#check @Schubert.RS.Quiver.instDecidableIsQuiverTriple
#check @Schubert.RS.Quiver.atomCoefficient_eq_finrank_quiverHom
#check @Schubert.RS.Quiver.atomCoefficient_eq_finrank_hom
#check @Schubert.RS.Quiver.finiteDimensional_quiverHom
#check @Schubert.RS.Quiver.atomCoefficient_nonneg
#check @Schubert.RS.Quiver.quiverOf
#check @Schubert.RS.Quiver.leviWeight
#check @Schubert.RS.Quiver.ForwardQuiver.multiplicity
#check @Schubert.RS.GL.ratLeviIrrep
#check @Schubert.RS.Quiver.twoSource_isQuiverPartition
#check @Schubert.RS.Quiver.twoSource_eq_weylProjector
#check @Schubert.RS.Quiver.twoSource_eq_kostka
#check @Schubert.RS.Quiver.twoSource_pos_iff
#check @Schubert.RS.Algorithms.twoSource_coefficient_computable
#check @Schubert.RS.Algorithms.encodeTripleUnary
#check @Schubert.RS.Algorithms.length_encodeTripleUnary_ofFn
#check @Schubert.RS.Algorithms.encodeTripleUnary_injective
#check @Schubert.RS.Algorithms.twoSource_eq_count
#check @Schubert.RS.SchubertUnions.key_eq_sum_atom
#check @FlagVarieties.ch_dualJoseph_negWeight
#check @Schubert.RS.Geometric.ch_geometricMinimalRelativeSchubert_negWeight
#check @Schubert.RS.Geometric.geometricMinimalRelativeSchubert_weightSpace_ne_bot
#check @Schubert.RS.Filtrations.dualJoseph_hasCharacter
#check @Schubert.RS.Filtrations.minRelSchubert_hasCharacter
#check @Schubert.RS.Quiver.ForwardQuiver.multiplicity_pos_of_nsmul_pos
#check @QuiverInvariants.FQuiver.exists_semiInvariant_of_nsmul
#check @QuiverInvariants.FQuiver.exists_generalQuot_euler_add_extDim_nonpos
#check @QuiverInvariants.FQuiver.isGreatest_genericExt
#check @QuiverInvariants.FQuiver.exists_extDim_eq_zero
#check @QuiverInvariants.FQuiver.IsSemiInvariant.sum_mul_nonneg_of_generalQuot
#check @QuiverInvariants.FQuiver.exists_semiInvariant_iff
#check @Schubert.RS.Quiver.ForwardQuiver.multiplicity_flag
#check @Schubert.RS.Quiver.ForwardQuiver.multiplicity_const_pos_iff
#check @Schubert.RS.quiverSaturation_of_semiInvariant
#check @Schubert.RS.polyTimeRationalFeasibility_holds
#check @LinearProgramming.exists_mem_FP_feasible
#check @LinearProgramming.decideFeasible_iff
#check @LinearProgramming.chubanov_iff
#check @Schubert.RS.glCharacterMultiplicity_holds
#check @Schubert.RS.Quiver.ForwardQuiver.finrank_ratLeviIrrep_coordRep_eq_multiplicity
#check @GLRep.IsPolynomialLeviRep.exists_leviCharacter_eq_sum
#check @GLRep.alternant_mul_glCharacter_of_isGlHighestWeightVector
#check @GLRep.IsPolynomialRep.isSemisimpleRepresentation
#check @GLRep.isIrreducible_irrep
#check @GLRep.character_irrep
#check @GLRep.IsPolynomialRep.exists_nonempty_equiv_irrep
#check @GLRep.IsPolynomialRep.nonempty_equiv_of_character_eq
#check @GLRep.finrank_intertwiningMap_irrep_self
#check @GLRep.finrank_intertwiningMap_irrep_of_ne
#check @GLRep.IsPolynomialRep.character_eq_diagramSchurPoly
#check @GLRep.IsPolynomialRep.exists_character_eq_sum
#check @GLRep.IsRationalRep.isSemisimpleRepresentation
#check @GLRep.IsRationalRep.exists_nonempty_equiv_ratIrrep
#check @GLRep.IsRationalRep.exists_ratCharacter_eq_sum
#check @GLRep.IsRationalLeviRep.exists_ratLeviCharacter_eq_sum
#check @Schubert.RS.Algorithms.exists_not_mem_P
#check @Schubert.RS.Algorithms.FP_countable
#check @Schubert.RS.key
#check @Schubert.RS.atom
#check @Schubert.RS.atomCoefficient
#check @Schubert.RS.GLCharacterMultiplicity
#check @Schubert.RS.QuiverSaturation
#check @Schubert.RS.PolyTimeRationalFeasibility
#check @LinearProgramming.encodeSystem
#check @FlagVarieties.FlagScheme
#check @FlagVarieties.FlagScheme.isProper_toSpec
#check @FlagVarieties.isColimitOrbitMap
#check @FlagVarieties.exists_mulRight_eq
#check @FlagVarieties.isIntegral_schubertVariety
#check @FlagVarieties.schubertVariety_globalSections_const
#check @FlagVarieties.PointModel.schubertVariety_le_iff
#check @FlagVarieties.oppositeSchubertVariety
#check @FlagVarieties.richardsonVariety
#check @FlagVarieties.Richardson.richardsonVariety_ne_top_iff
#check @FlagVarieties.isInvertible_lineBundle
#check @FlagVarieties.sectionsMul
#check @FlagVarieties.sectionsComodule
#check @FlagVarieties.contract_sectionsComodule
#check @GLRep.rationalBorelRepEquivComodule
#check @GLRep.indBorelFrobeniusEquiv
#check @GLRep.IsRationalBorelRep.toBModule
#check @FlagVarieties.PointModel.sectionsRestrict_surjective
#check @FlagVarieties.PointModel.schubertSectionsBasis
#check @FlagVarieties.PointModel.geometricSectionRingEquiv
#check @FlagVarieties.PointModel.geometricSectionRingEquiv_symm_of_mul_of
#check @FlagVarieties.PointModel.minorSpanEquivSections
#check @FlagVarieties.borelWeil_ratIrrep
#check @Demazure.FlagModule.flagDemazure
#check @Demazure.FlagModule.compositionFlagJosephPolo
#check @Demazure.SchubertUnions.flagDemazure_hasTorusCharacter
#check @Demazure.SchubertUnions.key_eq_sum_atom
#check @FlagVarieties.nonempty_sectionDemazureEquiv_ratIrrep
#check @FlagVarieties.PointModel.orbitIdeal_lowerSet_eq_fultonIdeal
#check @FlagVarieties.PointModel.isRadical_map_fultonIdeal
#check @FlagVarieties.PointModel.map_kazhdanLusztigSubst_fultonIdeal
#check @FlagVarieties.PointModel.isRadical_map_kazhdanLusztigSubst_fultonIdeal
#check @FlagVarieties.PointModel.cellRingEquiv
#check @FlagVarieties.Dimension.topologicalKrullDim_schubertVariety
#check @FlagVarieties.Bruhat.permCoxeterSystem
#check @FlagVarieties.Bruhat.bruhatLE_iff_strongBruhatLE
#check @FlagVarieties.Plucker.plucker
#check @FlagVarieties.Plucker.pluckerSegre
#check @FlagVarieties.Plucker.isClosedImmersion_pluckerSegre
#check @FlagVarieties.Plucker.pluckerSectionBasis_apply
#check @FlagVarieties.PointModel.pluckerVector_proportional_iff
#check @FlagVarieties.rankOneInduction
#check @FlagVarieties.rankOneInductionSectionsEquiv
#check @FlagVarieties.simpleSchubertSectionsEquiv
#check @FlagVarieties.ch_rankOneInduction_charCoaction
#check @Schubert.FinPermutation
#check @Schubert.FinPermutation.strongBruhatLE_iff_northwestRankNat
#check @Schubert.FinPermutation.strongBruhatLE_iff_reduced_adjacent_subword

#print axioms Schubert.RS.Family.atomCoefficient_eq
#print axioms Schubert.RS.Family.atomCoefficient_factorization
#print axioms Schubert.RS.Family.atomCoefficient_neg_iff
#print axioms Schubert.RS.Family.existsUnique_atomExpansion
#print axioms Schubert.RS.Family.not_atomPositive
#print axioms Schubert.RS.Family.rank28_atomCoefficient
#print axioms Schubert.RS.Family.rank28_not_atomPositive
#print axioms Schubert.RS.Family.reiner_shimozono_false
#print axioms Schubert.RS.Family.atomCoefficient_eq_narayana
#print axioms Schubert.RS.Family.atomCoefficient_eq_paper
#print axioms Schubert.RS.Family.atomCoefficient_threeFive
#print axioms Schubert.RS.Family.atomCoefficient_fourFour
#print axioms Schubert.RS.Family.isLeast_rank_of_negative
#print axioms Schubert.RS.Family.narayana
#print axioms Schubert.RS.Family.Parameters
#print axioms Schubert.RS.Family.a
#print axioms Schubert.RS.Family.b
#print axioms Schubert.RS.Family.c
#print axioms Schubert.RS.atomCoefficient_spec
#print axioms Schubert.RS.atomCoefficient_eq_of_expansion
#print axioms Schubert.RS.Family.isHallTriple_family
#print axioms Schubert.RS.Family.atomCoefficient_eq_paired
#print axioms Schubert.RS.Geometric.not_hasGeometricRelativeSchubertFiltration
#print axioms Schubert.RS.Geometric.not_hasGeometricSchubertFiltration
#print axioms Schubert.RS.Geometric.not_hasGeometricSLRelativeSchubertFiltration
#print axioms Schubert.RS.Geometric.not_hasGeometricSLSchubertFiltration
#print axioms Schubert.RS.Geometric.typeA27_geometricFiltration_failure
#print axioms Schubert.RS.Geometric.geometricFamilyTensor
#print axioms Schubert.RS.Geometric.ch_geometricFamilyTensor
#print axioms FlagVarieties.dualJoseph
#print axioms Schubert.RS.Geometric.geometricMinimalRelativeSchubert
#print axioms Schubert.RS.Geometric.geometricBoundaryRestrict
#print axioms Schubert.RS.Geometric.IsGeometricSchubertLayer
#print axioms Schubert.RS.Geometric.IsGeometricMinimalRelativeSchubertLayer
#print axioms Schubert.RS.Geometric.HasGeometricRelativeSchubertFiltration
#print axioms Schubert.RS.Geometric.HasGeometricSchubertFiltration
#print axioms Schubert.RS.Geometric.HasGeometricSLRelativeSchubertFiltration
#print axioms Schubert.RS.Geometric.HasGeometricSLSchubertFiltration
#print axioms FlagVarieties.schubertVariety
#print axioms FlagVarieties.schubertUnion
#print axioms FlagVarieties.schubertBoundary
#print axioms FlagVarieties.lineBundle
#print axioms FlagVarieties.sections
#print axioms FlagVarieties.sectionsRep
#print axioms FlagVarieties.sectionsEquivSemiInvariants
#print axioms FlagVarieties.sectionsRestrict
#print axioms FlagVarieties.sectionsRestrictHom_eq_sectionsRestrict
#print axioms FlagVarieties.preimageIdeal_schubertUnion_eq_orbitIdeal_complex
#print axioms FlagVarieties.globalSectionsConstant_complex
#print axioms FlagVarieties.geometricSectionEquiv
#print axioms FlagVarieties.dualJosephEquiv
#print axioms Schubert.RS.Geometric.geometricMinimalRelativeSchubertEquiv
#print axioms Schubert.RS.Geometric.isGeometricSchubertLayer_iff
#print axioms Schubert.RS.Geometric.isGeometricMinimalRelativeSchubertLayer_iff
#print axioms FlagVarieties.sectionBModuleIso
#print axioms Schubert.RS.Family.not_hasRelativeSchubertFiltration
#print axioms Schubert.RS.Family.not_hasSchubertFiltration
#print axioms Schubert.RS.Family.not_hasSLRelativeSchubertFiltration
#print axioms Schubert.RS.Family.not_hasSLSchubertFiltration
#print axioms Schubert.RS.Family.rank_sub_one
#print axioms Schubert.RS.Family.typeA27_filtration_failure
#print axioms Schubert.RS.Family.factors_hasExcellentFiltration
#print axioms Schubert.RS.Family.familyTensor
#print axioms Schubert.RS.Family.familyTensor_hasCharacter
#print axioms Schubert.RS.Filtrations.HasRelativeSchubertFiltration
#print axioms Schubert.RS.Filtrations.HasSchubertFiltration
#print axioms Schubert.RS.Filtrations.HasExcellentFiltration
#print axioms Schubert.RS.Filtrations.HasSLRelativeSchubertFiltration
#print axioms Schubert.RS.Filtrations.HasSLSchubertFiltration
#print axioms Schubert.RS.Filtrations.schubertSectionModule
#print axioms Schubert.RS.Filtrations.dualJoseph
#print axioms Schubert.RS.Filtrations.minRelSchubert
#print axioms Schubert.RS.HighestWeight.flagOrbitSpan_irreducible
#print axioms Schubert.RS.Family.not_lascouxAtomPositive
#print axioms Schubert.RS.Family.no_lascouxExpansion_nonnegAtZero
#print axioms Schubert.RS.Family.rank28_not_lascouxAtomPositive
#print axioms Schubert.RS.Family.lascoux_product_positivity_false
#print axioms Schubert.RS.betaIsobaric
#print axioms Schubert.RS.betaAtomOperator
#print axioms Schubert.RS.lascoux
#print axioms Schubert.RS.lascouxAtom
#print axioms Schubert.RS.betaZero_lascoux
#print axioms Schubert.RS.betaZero_lascouxAtom
#print axioms Schubert.RS.LascouxAtomPositive
#print axioms Schubert.RS.Quiver.Flat.quiverPolytope
#print axioms Schubert.RS.Quiver.Flat.quiverTheorem_identity
#print axioms Schubert.RS.Quiver.Flat.quiverTheorem_counts
#print axioms Schubert.RS.Quiver.Flat.quiverPolytope_card
#print axioms Schubert.RS.Quiver.Flat.finiteDimensional_canonicalHom
#print axioms Schubert.RS.Quiver.Flat.quiverPolytope_bounded
#print axioms Schubert.RS.Quiver.Flat.quiverCoefficient_pos_iff_realPoint
#print axioms Schubert.RS.Quiver.Flat.quiverCoefficient_pos_iff_ratPoint
#print axioms Schubert.RS.Quiver.Flat.quiverCoefficient_pos_iff_nonempty
#print axioms Schubert.RS.Quiver.Flat.quiverCoefficient_pos_iff_ratFeasible
#print axioms Schubert.RS.Quiver.Flat.nonempty_of_quiverCoefficient_pos
#print axioms Schubert.RS.Quiver.Flat.quiverPolytope_nonempty_iff_exists_nsmul_pos
#print axioms Schubert.RS.Quiver.Flat.quiverPolytope_ratFeasible_iff_exists_nsmul_pos
#print axioms Schubert.RS.Quiver.Flat.atomCoefficient_nsmul_eq_card
#print axioms Schubert.RS.quiverSaturation_holds
#print axioms Schubert.RS.Quiver.atomCoefficient_eq_multiplicity
#print axioms Schubert.RS.Algorithms.quiverTriple_recognition
#print axioms Schubert.RS.Algorithms.quiverPolytope_construction
#print axioms Schubert.RS.Algorithms.quiverPolytope_size
#print axioms Schubert.RS.Algorithms.quiverPositivity_decision_polyTime
#print axioms Schubert.RS.Algorithms.quiverPositivity_decision
#print axioms Schubert.RS.Algorithms.quiverPositivity_decision_of_saturation
#print axioms Schubert.RS.Algorithms.quiverPositivity_decision_of_criterion
#print axioms Schubert.RS.Algorithms.quiverPositivity_decision_of_iff
#print axioms Schubert.RS.Algorithms.encodeTriple
#print axioms Schubert.RS.Algorithms.IsQuiverTripleList
#print axioms Schubert.RS.Algorithms.binarySize_le_length
#print axioms Schubert.RS.Algorithms.length_le_binarySize
#print axioms Schubert.RS.Algorithms.exists_not_mem_FP
#print axioms Schubert.RS.Algorithms.exists_mem_P_not_mem_DTIME
#print axioms Schubert.RS.Quiver.Density.card_positiveQuiverTriples_isTheta
#print axioms Schubert.RS.Quiver.Density.positiveQuiverTriples_proportion
#print axioms Schubert.RS.Quiver.Density.positiveQuiverTriples
#print axioms Schubert.RS.atomCoefficient_eq_rectangleCoefficient
#print axioms Schubert.RS.rectangleCoefficient
#print axioms Schubert.RS.keyAtom_orthogonality
#print axioms Schubert.RS.Representation.compositionFlagJosephPolo
#print axioms Schubert.RS.Representation.compositionFlagDemazureCharacter
#print axioms Schubert.RS.Representation.orderedPBWBasis_exists
#print axioms Schubert.RS.atomCoefficient_eq_rectangleCoefficient'
#print axioms Schubert.RS.Window.window_rational_extraction
#print axioms Schubert.RS.Window.window_product_indep
#print axioms Schubert.RS.Window.Hypotheses
#print axioms Schubert.RS.Window.WindowInequality
#print axioms Schubert.RS.Window.prefixHeight
#print axioms Schubert.RS.Window.cmp
#print axioms Schubert.RS.Window.hypotheses_iff_of_le
#print axioms Schubert.RS.Hall.hall_determinant
#print axioms Schubert.RS.Hall.hallProduct
#print axioms Schubert.RS.Hall.hallMatrix
#print axioms Schubert.RS.Hall.completeH
#print axioms Schubert.RS.Hall.hallSum
#print axioms Schubert.RS.Hall.IsHallAdmissible
#print axioms Schubert.RS.HallLattice.hall_determinant
#print axioms Schubert.RS.hall_source_extraction
#print axioms Schubert.RS.Hall.hall_flags
#print axioms Schubert.RS.Hall.hallFlag
#print axioms Schubert.RS.Hall.firstAbove
#print axioms Schubert.RS.Hall.isHallAdmissible_iff_flags
#print axioms Schubert.RS.Hall.HallPartition
#print axioms Schubert.RS.Hall.IsHallTriple
#print axioms Schubert.RS.Hall.isHallTriple_iff
#print axioms Schubert.RS.Hall.HallPartition.changeN
#print axioms Schubert.RS.Family.familyHallPartition
#print axioms Schubert.RS.Hall.paired_reduction
#print axioms Schubert.RS.Hall.tVar
#print axioms Schubert.RS.Hall.HallPartition.q
#print axioms Schubert.RS.Hall.HallPartition.pairs
#print axioms Schubert.RS.Hall.HallPartition.height
#print axioms Schubert.RS.Hall.HallPartition.flag
#print axioms Schubert.RS.Hall.HallPartition.blockPolynomial
#print axioms Schubert.RS.Hall.HallPartition.m_eq_sum_card
#print axioms Schubert.RS.double_source_extraction
#print axioms Schubert.RS.Hall.paired_reduction_of_isHallTriple
#print axioms Schubert.RS.Family.two_source_count
#print axioms Schubert.RS.Quiver.IsQuiverTriple
#print axioms Schubert.RS.Quiver.IsQuiverPartition
#print axioms Schubert.RS.Quiver.isQuiverPartition_iff_of_le
#print axioms Schubert.RS.Quiver.isQuiverTriple_iff_canonical
#print axioms Schubert.RS.Quiver.IsQuiverPartition.eq_canonical
#print axioms Schubert.RS.Quiver.instDecidableIsQuiverTriple
#print axioms Schubert.RS.Quiver.atomCoefficient_eq_finrank_quiverHom
#print axioms Schubert.RS.Quiver.atomCoefficient_eq_finrank_hom
#print axioms Schubert.RS.Quiver.finiteDimensional_quiverHom
#print axioms Schubert.RS.Quiver.atomCoefficient_nonneg
#print axioms Schubert.RS.Quiver.quiverOf
#print axioms Schubert.RS.Quiver.leviWeight
#print axioms Schubert.RS.Quiver.ForwardQuiver.multiplicity
#print axioms Schubert.RS.GL.ratLeviIrrep
#print axioms Schubert.RS.Quiver.twoSource_isQuiverPartition
#print axioms Schubert.RS.Quiver.twoSource_eq_weylProjector
#print axioms Schubert.RS.Quiver.twoSource_eq_kostka
#print axioms Schubert.RS.Quiver.twoSource_pos_iff
#print axioms Schubert.RS.Algorithms.twoSource_coefficient_computable
#print axioms Schubert.RS.Algorithms.encodeTripleUnary
#print axioms Schubert.RS.Algorithms.length_encodeTripleUnary_ofFn
#print axioms Schubert.RS.Algorithms.encodeTripleUnary_injective
#print axioms Schubert.RS.Algorithms.twoSource_eq_count
#print axioms Schubert.RS.SchubertUnions.key_eq_sum_atom
#print axioms FlagVarieties.ch_dualJoseph_negWeight
#print axioms Schubert.RS.Geometric.ch_geometricMinimalRelativeSchubert_negWeight
#print axioms Schubert.RS.Geometric.geometricMinimalRelativeSchubert_weightSpace_ne_bot
#print axioms Schubert.RS.Filtrations.dualJoseph_hasCharacter
#print axioms Schubert.RS.Filtrations.minRelSchubert_hasCharacter
#print axioms Schubert.RS.Quiver.ForwardQuiver.multiplicity_pos_of_nsmul_pos
#print axioms QuiverInvariants.FQuiver.exists_semiInvariant_of_nsmul
#print axioms QuiverInvariants.FQuiver.exists_generalQuot_euler_add_extDim_nonpos
#print axioms QuiverInvariants.FQuiver.isGreatest_genericExt
#print axioms QuiverInvariants.FQuiver.exists_extDim_eq_zero
#print axioms QuiverInvariants.FQuiver.IsSemiInvariant.sum_mul_nonneg_of_generalQuot
#print axioms QuiverInvariants.FQuiver.exists_semiInvariant_iff
#print axioms Schubert.RS.Quiver.ForwardQuiver.multiplicity_flag
#print axioms Schubert.RS.Quiver.ForwardQuiver.multiplicity_const_pos_iff
#print axioms Schubert.RS.quiverSaturation_of_semiInvariant
#print axioms Schubert.RS.polyTimeRationalFeasibility_holds
#print axioms LinearProgramming.exists_mem_FP_feasible
#print axioms LinearProgramming.decideFeasible_iff
#print axioms LinearProgramming.chubanov_iff
#print axioms Schubert.RS.glCharacterMultiplicity_holds
#print axioms Schubert.RS.Quiver.ForwardQuiver.finrank_ratLeviIrrep_coordRep_eq_multiplicity
#print axioms GLRep.IsPolynomialLeviRep.exists_leviCharacter_eq_sum
#print axioms GLRep.alternant_mul_glCharacter_of_isGlHighestWeightVector
#print axioms GLRep.IsPolynomialRep.isSemisimpleRepresentation
#print axioms GLRep.isIrreducible_irrep
#print axioms GLRep.character_irrep
#print axioms GLRep.IsPolynomialRep.exists_nonempty_equiv_irrep
#print axioms GLRep.IsPolynomialRep.nonempty_equiv_of_character_eq
#print axioms GLRep.finrank_intertwiningMap_irrep_self
#print axioms GLRep.finrank_intertwiningMap_irrep_of_ne
#print axioms GLRep.IsPolynomialRep.character_eq_diagramSchurPoly
#print axioms GLRep.IsPolynomialRep.exists_character_eq_sum
#print axioms GLRep.IsRationalRep.isSemisimpleRepresentation
#print axioms GLRep.IsRationalRep.exists_nonempty_equiv_ratIrrep
#print axioms GLRep.IsRationalRep.exists_ratCharacter_eq_sum
#print axioms GLRep.IsRationalLeviRep.exists_ratLeviCharacter_eq_sum
#print axioms Schubert.RS.Algorithms.exists_not_mem_P
#print axioms Schubert.RS.Algorithms.FP_countable
#print axioms Schubert.RS.key
#print axioms Schubert.RS.atom
#print axioms Schubert.RS.atomCoefficient
#print axioms Schubert.RS.GLCharacterMultiplicity
#print axioms Schubert.RS.QuiverSaturation
#print axioms Schubert.RS.PolyTimeRationalFeasibility
#print axioms LinearProgramming.encodeSystem
#print axioms FlagVarieties.FlagScheme
#print axioms FlagVarieties.FlagScheme.isProper_toSpec
#print axioms FlagVarieties.isColimitOrbitMap
#print axioms FlagVarieties.exists_mulRight_eq
#print axioms FlagVarieties.isIntegral_schubertVariety
#print axioms FlagVarieties.schubertVariety_globalSections_const
#print axioms FlagVarieties.PointModel.schubertVariety_le_iff
#print axioms FlagVarieties.oppositeSchubertVariety
#print axioms FlagVarieties.richardsonVariety
#print axioms FlagVarieties.Richardson.richardsonVariety_ne_top_iff
#print axioms FlagVarieties.isInvertible_lineBundle
#print axioms FlagVarieties.sectionsMul
#print axioms FlagVarieties.sectionsComodule
#print axioms FlagVarieties.contract_sectionsComodule
#print axioms GLRep.rationalBorelRepEquivComodule
#print axioms GLRep.indBorelFrobeniusEquiv
#print axioms GLRep.IsRationalBorelRep.toBModule
#print axioms FlagVarieties.PointModel.sectionsRestrict_surjective
#print axioms FlagVarieties.PointModel.schubertSectionsBasis
#print axioms FlagVarieties.PointModel.geometricSectionRingEquiv
#print axioms FlagVarieties.PointModel.geometricSectionRingEquiv_symm_of_mul_of
#print axioms FlagVarieties.PointModel.minorSpanEquivSections
#print axioms FlagVarieties.borelWeil_ratIrrep
#print axioms Demazure.FlagModule.flagDemazure
#print axioms Demazure.FlagModule.compositionFlagJosephPolo
#print axioms Demazure.SchubertUnions.flagDemazure_hasTorusCharacter
#print axioms Demazure.SchubertUnions.key_eq_sum_atom
#print axioms FlagVarieties.nonempty_sectionDemazureEquiv_ratIrrep
#print axioms FlagVarieties.PointModel.orbitIdeal_lowerSet_eq_fultonIdeal
#print axioms FlagVarieties.PointModel.isRadical_map_fultonIdeal
#print axioms FlagVarieties.PointModel.map_kazhdanLusztigSubst_fultonIdeal
#print axioms FlagVarieties.PointModel.isRadical_map_kazhdanLusztigSubst_fultonIdeal
#print axioms FlagVarieties.PointModel.cellRingEquiv
#print axioms FlagVarieties.Dimension.topologicalKrullDim_schubertVariety
#print axioms FlagVarieties.Bruhat.permCoxeterSystem
#print axioms FlagVarieties.Bruhat.bruhatLE_iff_strongBruhatLE
#print axioms FlagVarieties.Plucker.plucker
#print axioms FlagVarieties.Plucker.pluckerSegre
#print axioms FlagVarieties.Plucker.isClosedImmersion_pluckerSegre
#print axioms FlagVarieties.Plucker.pluckerSectionBasis_apply
#print axioms FlagVarieties.PointModel.pluckerVector_proportional_iff
#print axioms FlagVarieties.rankOneInduction
#print axioms FlagVarieties.rankOneInductionSectionsEquiv
#print axioms FlagVarieties.simpleSchubertSectionsEquiv
#print axioms FlagVarieties.ch_rankOneInduction_charCoaction
#print axioms Schubert.FinPermutation
#print axioms Schubert.FinPermutation.strongBruhatLE_iff_northwestRankNat
#print axioms Schubert.FinPermutation.strongBruhatLE_iff_reduced_adjacent_subword
