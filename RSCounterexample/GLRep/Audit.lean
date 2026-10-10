import RSCounterexample.GLRep.Main

/-!
# Audit of the library

Prints the main results of the library indexed in `RSCounterexample/GLRep/Main.lean`, with the axioms
they depend on. Each `#print axioms` below should report only `propext`, `Classical.choice` and
`Quot.sound`.
-/

-- Polynomial representations, weights and characters
#check @GLRep.hasCoeffsIn_iff_toMatrix
#check @GLRep.isZariskiDense_glCoord
#check @GLRep.HasCoeffsIn.isInternal_torusWeightSpace
#check @GLRep.trace_diagGL_eq_eval_character
#check @GLRep.eq_character_of_forall_trace_eq
#check @GLRep.IsPolynomialRep.character_isSymmetric
#check @GLRep.leviCharacter_extTensor
#print axioms GLRep.hasCoeffsIn_iff_toMatrix
#print axioms GLRep.isZariskiDense_glCoord
#print axioms GLRep.HasCoeffsIn.isInternal_torusWeightSpace
#print axioms GLRep.eq_character_of_forall_trace_eq
#print axioms GLRep.IsPolynomialRep.character_isSymmetric
#print axioms GLRep.leviCharacter_extTensor

-- The Lie algebra
#check @GLRep.IsPolynomialRep.lie
#check @GLRep.IsPolynomialRep.adjoin_range_eq
#check @GLRep.IsPolynomialRep.subrepOrderIso
#check @GLRep.IsPolynomialRep.intertwiningEquivLieHom
#print axioms GLRep.IsPolynomialRep.lie
#print axioms GLRep.IsPolynomialRep.adjoin_range_eq
#print axioms GLRep.IsPolynomialRep.intertwiningEquivLieHom

-- The Weyl character formula
#check @GLRep.freudenthal
#check @GLRep.alternant_mul_glCharacter_of_isGlHighestWeightVector
#check @GLRep.IsPolynomialRep.character_eq_diagramSchurPoly
#print axioms GLRep.freudenthal
#print axioms GLRep.alternant_mul_glCharacter_of_isGlHighestWeightVector
#print axioms GLRep.IsPolynomialRep.character_eq_diagramSchurPoly

-- Highest weights, irreducibles and complete reducibility
#check @GLRep.IsPolynomialRep.exists_highestWeight
#check @GLRep.IsPolynomialRep.nonempty_equiv_of_character_eq
#check @GLRep.isIrreducible_irrep
#check @GLRep.character_irrep
#check @GLRep.IsPolynomialRep.exists_nonempty_equiv_irrep
#check @GLRep.irrep_eq_of_nonempty_equiv
#check @GLRep.finrank_intertwiningMap_irrep_self
#check @GLRep.IsIntegralGLModule.complementedLattice
#check @GLRep.IsPolynomialRep.isSemisimpleRepresentation
#print axioms GLRep.IsPolynomialRep.exists_highestWeight
#print axioms GLRep.IsPolynomialRep.nonempty_equiv_of_character_eq
#print axioms GLRep.isIrreducible_irrep
#print axioms GLRep.character_irrep
#print axioms GLRep.IsPolynomialRep.exists_nonempty_equiv_irrep
#print axioms GLRep.irrep_eq_of_nonempty_equiv
#print axioms GLRep.finrank_intertwiningMap_irrep_self
#print axioms GLRep.IsIntegralGLModule.complementedLattice
#print axioms GLRep.IsPolynomialRep.isSemisimpleRepresentation

-- Multiplicities
#check @GLRep.IsPolynomialRep.exists_character_eq_sum
#check @GLRep.leviCharacter_leviIrrep
#check @GLRep.IsPolynomialLeviRep.exists_leviCharacter_eq_sum
#print axioms GLRep.IsPolynomialRep.exists_character_eq_sum
#print axioms GLRep.leviCharacter_leviIrrep
#print axioms GLRep.IsPolynomialLeviRep.exists_leviCharacter_eq_sum

-- Rational representations
#check @GLRep.nonempty_equiv_scaledRep_irrep
#check @GLRep.IsRationalTorusRep.eq_laurentCharacter_of_forall
#check @GLRep.IsRationalRep.isSemisimpleRepresentation
#check @GLRep.IsRationalRep.exists_nonempty_equiv_ratIrrep
#check @GLRep.eq_of_nonempty_equiv_ratIrrep
#check @GLRep.ratCharacter_ratIrrep
#check @GLRep.IsRationalRep.exists_ratCharacter_eq_sum
#check @GLRep.ratLeviCharacter_ratLeviIrrep
#check @GLRep.IsRationalLeviRep.exists_ratLeviCharacter_eq_sum
#print axioms GLRep.nonempty_equiv_scaledRep_irrep
#print axioms GLRep.IsRationalTorusRep.eq_laurentCharacter_of_forall
#print axioms GLRep.IsRationalRep.isSemisimpleRepresentation
#print axioms GLRep.IsRationalRep.exists_nonempty_equiv_ratIrrep
#print axioms GLRep.eq_of_nonempty_equiv_ratIrrep
#print axioms GLRep.ratCharacter_ratIrrep
#print axioms GLRep.IsRationalRep.exists_ratCharacter_eq_sum
#print axioms GLRep.ratLeviCharacter_ratLeviIrrep
#print axioms GLRep.IsRationalLeviRep.exists_ratLeviCharacter_eq_sum
