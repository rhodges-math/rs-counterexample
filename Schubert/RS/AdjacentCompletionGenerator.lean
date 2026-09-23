import Schubert.RS.PolynomialRootCompletion
import Schubert.RS.Representation.ParabolicRadical
import Schubert.RS.Sl2EndpointGeneration

namespace Schubert.RS.Representation
noncomputable section
open FinPermutation
attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000

theorem compositionFlag_adjacent_raising_stable {n : ℕ} (u : Composition n)
    (i : AdjacentPosition n) (p : MatrixPolynomial n) (hp : p∈compositionFlag u) :
    matrixUnitDerivation i.left i.right p∈compositionFlag u :=
  upperCyclic_root_stable _ ⟨(i.left,i.right),i.left_lt_right⟩ hp

theorem compositionFlagGenerator_polynomial_weight {n : ℕ} (u : Composition n)
    (t : DiagonalTorus n) :
    polynomialTorus n t (compositionFlagGenerator u).val=
      integerWeightScalar (fun j => (u j:ℤ)) t • (compositionFlagGenerator u).val :=
  congrArg Subtype.val (compositionFlagGenerator_weight u t)

theorem compositionFlagGenerator_raising_zero {n : ℕ} (u : Composition n)
    (i : AdjacentPosition n) (hu : u i.right<u i.left) :
    matrixUnitDerivation i.left i.right (compositionFlagGenerator u).val=0 := by
  apply extremalFlag_lowering_zero _ _ i.right i.left
  simpa only [composition_extremalWeight] using hu

variable {n : ℕ} (u : Composition n) (i : AdjacentPosition n)
  (B : PolynomialRootStringBasis i.left i.right (compositionFlag (swapComposition u i)))

def PolynomialRootStringBasis.adjacentHighest : B.completedModule i.left_ne_right :=
  B.completionBoundary i.left_ne_right (compositionFlagGenerator (swapComposition u i))

def PolynomialRootStringBasis.adjacentEndpoint : B.completedModule i.left_ne_right :=
  primitiveStringVector (sl2LoweringElement (polynomialSl2Triple i.left i.right i.left_ne_right))
    (B.adjacentHighest u i) (u i.right-u i.left)

theorem PolynomialRootStringBasis.adjacentHighest_ne_zero : B.adjacentHighest u i≠0 := by
  intro hh
  apply compositionFlagGenerator_ne_zero (swapComposition u i)
  apply B.completionBoundary_injective i.left_ne_right
    (compositionFlag_adjacent_raising_stable (swapComposition u i) i)
  rw [map_zero]
  exact hh

theorem PolynomialRootStringBasis.adjacentHighest_e (hu : u i.left<u i.right) :
    ⁅sl2RaisingElement (polynomialSl2Triple i.left i.right i.left_ne_right),B.adjacentHighest u i⁆=0 := by
  rw [PolynomialRootStringBasis.adjacentHighest,← (B.isCompletion i.left_ne_right
    (compositionFlag_adjacent_raising_stable (swapComposition u i) i)).map_e]
  have he : matrixUnitOnSubmodule i.left i.right (compositionFlag (swapComposition u i))
      (compositionFlag_adjacent_raising_stable (swapComposition u i) i)
      (compositionFlagGenerator (swapComposition u i))=0 := by
    apply Subtype.ext
    exact compositionFlagGenerator_raising_zero (swapComposition u i) i
      (by simpa only [swapComposition_left,swapComposition_right] using hu)
  rw [he,map_zero]

theorem PolynomialRootStringBasis.adjacentHighest_h (hu : u i.left<u i.right) :
    ⁅sl2CartanElement (polynomialSl2Triple i.left i.right i.left_ne_right),B.adjacentHighest u i⁆=
      ((u i.right-u i.left:ℕ):ℂ) • B.adjacentHighest u i := by
  have hh : B.cartan i.left_ne_right (compositionFlagGenerator (swapComposition u i))=
      ((u i.right-u i.left:ℕ):ℂ) • compositionFlagGenerator (swapComposition u i) := by
    apply Subtype.ext
    rw [B.cartan_val]
    rw [polynomialRootCartan_weight _ _ _ _ (compositionFlagGenerator_polynomial_weight (swapComposition u i))]
    simp only [swapComposition_left,swapComposition_right,Int.cast_sub,Int.cast_natCast,
      Nat.cast_sub hu.le,Submodule.coe_smul]
  rw [PolynomialRootStringBasis.adjacentHighest,← (B.isCompletion i.left_ne_right
    (compositionFlag_adjacent_raising_stable (swapComposition u i) i)).map_h,hh,map_smul]

theorem PolynomialRootStringBasis.adjacentEndpoint_h (hu : u i.left<u i.right) :
    ⁅sl2CartanElement (polynomialSl2Triple i.left i.right i.left_ne_right),B.adjacentEndpoint u i⁆=
      -((u i.right-u i.left:ℕ):ℂ) • B.adjacentEndpoint u i :=
  highestVector_endpoint_h (sl2SubalgebraTriple (polynomialSl2Triple i.left i.right i.left_ne_right))
    (B.adjacentHighest_h u i hu) (B.adjacentHighest_e u i hu)

theorem PolynomialRootStringBasis.adjacentEndpoint_f (hu : u i.left<u i.right) :
    ⁅sl2LoweringElement (polynomialSl2Triple i.left i.right i.left_ne_right),B.adjacentEndpoint u i⁆=0 :=
  highestVector_endpoint_f (sl2SubalgebraTriple (polynomialSl2Triple i.left i.right i.left_ne_right))
    (B.adjacentHighest_h u i hu) (B.adjacentHighest_e u i hu)

end
end Schubert.RS.Representation
