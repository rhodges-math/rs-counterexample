import Schubert.RS.Family.Main

open Schubert.RS
open Schubert.RS.Family
open Schubert.RS.Representation
open Schubert.RS.PBW

#check @orderedPBWBasis_exists
#check @orderedRootMonomial_linearIndependent
#check @atomCoefficient_eq
#check @atomCoefficient_factorization
#check @atomCoefficient_neg_iff
#check @existsUnique_atomExpansion
#check @not_atomPositive
#check @rank28_atomCoefficient
#check @rank28_not_atomPositive
#check @reiner_shimozono_false

#print axioms orderedRootMonomial_span_eq_top
#print axioms differentialWord_principal
#print axioms centerPolynomial_word
#print axioms partialWord_constant
#print axioms orderedRootMonomial_linearIndependent
#print axioms orderedPBWBasis_exists
#print axioms compositionFlagJosephPolo
#print axioms compositionFlagDemazureCharacter
#print axioms atomCoefficient_eq
#print axioms atomCoefficient_factorization
#print axioms atomCoefficient_neg_iff
#print axioms existsUnique_atomExpansion
#print axioms not_atomPositive
#print axioms rank28_atomCoefficient
#print axioms rank28_not_atomPositive
#print axioms reiner_shimozono_false

-- The order type is inhabited at every rank, including the empty root systems.
example : HasOrderedPBWBasis 0 := orderedPBWBasis_exists 0
example : HasOrderedPBWBasis 1 := orderedPBWBasis_exists 1
example : HasOrderedPBWBasis 28 := orderedPBWBasis_exists 28

#print HasOrderedPBWBasis
#print orderedRootMonomial
#print Enveloping
#print orderedRootBasis
#print orderedPBWBasis_exists
#print atomCoefficient_eq
#print Parameters
#print Counterexample.a
#print Counterexample.b
#print Counterexample.c
