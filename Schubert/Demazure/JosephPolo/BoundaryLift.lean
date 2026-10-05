import Schubert.Demazure.JosephPolo.AdjacentCartan
import Schubert.Demazure.JosephPolo.PresentationAction
import Schubert.Demazure.JosephPolo.FinitePresentation

/-!
# Lifting the boundary into the presentation

When `swapComposition u i` has the Joseph–Polo presentation, its flag module is the presentation
quotient (`compositionPresentationEquiv`), and the boundary of the adjacent completion maps into the
presentation of `u` compatibly with raising and the Cartan operator. This gives a map from the
adjacent completion to the presentation (`adjacentCompletionToPresentation`).
-/

open Schubert

namespace Demazure.FlagModule
noncomputable section
open FinPermutation
attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 600000

/-- The isomorphism from the presentation quotient of `v` onto its flag module, given the
Joseph–Polo presentation of `v`. -/
def compositionPresentationEquiv {n : ℕ} (v : Composition n)
    (hJP : CompositionFlagJosephPolo v) :
    PresentationQuotient v ≃ₗ[Enveloping n] compositionFlag v :=
  LinearEquiv.ofBijective (compositionPresentationMap v)
    ⟨(compositionFlagJosephPolo_iff_injective v).mp hJP, compositionPresentationMap_surjective v⟩

/-- The map from the flag module of `swapComposition u i` to the presentation quotient of `u`,
through the presentation of `swapComposition u i`. -/
def adjacentPresentationBoundary {n : ℕ} (u : Composition n) (i : AdjacentPosition n)
    (hu : u i.left ≤ u i.right) (hJP : CompositionFlagJosephPolo (swapComposition u i)) :
    compositionFlag (swapComposition u i) →ₗ[Enveloping n] PresentationQuotient u :=
  (adjacentPresentationMap u i hu).comp
    (compositionPresentationEquiv (swapComposition u i) hJP).symm.toLinearMap

theorem adjacentPresentationBoundary_map {n : ℕ} (u : Composition n) (i : AdjacentPosition n)
    (hu : u i.left ≤ u i.right) (hJP : CompositionFlagJosephPolo (swapComposition u i))
    (x : PresentationQuotient (swapComposition u i)) :
    adjacentPresentationBoundary u i hu hJP (compositionPresentationMap (swapComposition u i) x) =
      adjacentPresentationMap u i hu x := by
  change adjacentPresentationMap u i hu
    ((compositionPresentationEquiv (swapComposition u i) hJP).symm
      ((compositionPresentationEquiv (swapComposition u i) hJP) x)) = _
  rw [LinearEquiv.symm_apply_apply]

variable {n : ℕ} (u : Composition n) (i : AdjacentPosition n)
  (hu : u i.left ≤ u i.right) (hJP : CompositionFlagJosephPolo (swapComposition u i))
  (B : PolynomialRootStringBasis i.left i.right (compositionFlag (swapComposition u i)))

theorem adjacentPresentationBoundary_raising (p : compositionFlag (swapComposition u i)) :
    letI := presentationSl2LieRingModule u i hu
    adjacentPresentationBoundary u i hu hJP
      (matrixUnitOnSubmodule i.left i.right (compositionFlag (swapComposition u i))
        (compositionFlag_adjacent_raising_stable (swapComposition u i) i) p) =
      ⁅sl2RaisingElement (polynomialSl2Triple i.left i.right i.left_ne_right),
        adjacentPresentationBoundary u i hu hJP p⁆ := by
  have he : matrixUnitOnSubmodule i.left i.right (compositionFlag (swapComposition u i))
      (compositionFlag_adjacent_raising_stable (swapComposition u i) i) p =
      rootOperator (adjacentPositiveRoot i) • p := by
    apply Subtype.ext
    change matrixUnitDerivation i.left i.right p.val =
      polynomialEnveloping n (rootOperator (adjacentPositiveRoot i)) p.val
    rw [polynomialEnveloping_root]
    rfl
  rw [he]
  rw [map_smul, presentationSl2_raising u i hu]
  rfl

theorem adjacentPresentationBoundary_cartan (p : compositionFlag (swapComposition u i)) :
    letI := presentationSl2LieRingModule u i hu
    adjacentPresentationBoundary u i hu hJP (B.cartan i.left_ne_right p) =
      ⁅sl2CartanElement (polynomialSl2Triple i.left i.right i.left_ne_right),
        adjacentPresentationBoundary u i hu hJP p⁆ := by
  obtain ⟨q,rfl⟩ := compositionPresentationMap_surjective (swapComposition u i) p
  have hh : B.cartan i.left_ne_right (compositionPresentationMap (swapComposition u i) q) =
      compositionPresentationMap (swapComposition u i)
          (presentationCartan (swapComposition u i) i q) := by
    apply Subtype.ext
    rw [B.cartan_val, compositionPresentationMap_cartan]
  rw [hh, adjacentPresentationBoundary_map, adjacentPresentationBoundary_map,
    presentationSl2_cartan u i hu, adjacentPresentationMap_cartan]

/-- The rank-one Lie-module map from the completion to the presentation,
using the Joseph-Polo property for the smaller composition. -/
def adjacentCompletionToPresentation :
    letI := presentationSl2LieRingModule u i hu
    letI := presentationSl2LieModule u i hu
    B.completedModule i.left_ne_right →ₗ⁅ℂ,
      (polynomialSl2Triple i.left i.right i.left_ne_right).toLieSubalgebra ℂ⁆ PresentationQuotient
          u :=
  letI := presentationSl2LieRingModule u i hu
  letI := presentationSl2LieModule u i hu
  letI := presentation_finite u
  (B.isCompletion i.left_ne_right
    (compositionFlag_adjacent_raising_stable (swapComposition u i) i)).lift
    ((adjacentPresentationBoundary u i hu hJP).restrictScalars ℂ)
    (adjacentPresentationBoundary_raising u i hu hJP)
    (adjacentPresentationBoundary_cartan u i hu hJP B)

theorem adjacentCompletionToPresentation_boundary (p : compositionFlag (swapComposition u i)) :
    letI := presentationSl2LieRingModule u i hu
    letI := presentationSl2LieModule u i hu
    adjacentCompletionToPresentation u i hu hJP B (B.completionBoundary i.left_ne_right p) =
      adjacentPresentationBoundary u i hu hJP p := by
  let := presentationSl2LieRingModule u i hu
  let := presentationSl2LieModule u i hu
  let := presentation_finite u
  exact IsRankOneCompletion.lift_boundary _ _ _ _ p

end
end Demazure.FlagModule
