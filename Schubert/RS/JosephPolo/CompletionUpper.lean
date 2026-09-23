import Schubert.RS.JosephPolo.BoundaryLift
import Schubert.RS.JosephPolo.PresentationRadical
import Schubert.RS.Representation.PolynomialCompletionEvaluation

namespace Schubert.RS.Representation
noncomputable section
open FinPermutation TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 200000

theorem radicalPolynomialAction_as_smul {n : ℕ} (v : Composition n) (i : AdjacentPosition n)
    (r : radicalEndLie i) (p : compositionFlag v) :
    radicalPolynomialAction i (compositionFlag v) (compositionFlag_radical_stable i v)
      (r ⊗ₜ[ℂ] p) = UniversalEnvelopingAlgebra.ι ℂ (radicalUpper i r) • p := by
  apply Subtype.ext
  rw [radicalPolynomialAction_tmul_val]
  change r.val p.val = polynomialEnveloping n (UniversalEnvelopingAlgebra.ι ℂ (radicalUpper i r)) p.val
  rw [polynomialEnveloping, UniversalEnvelopingAlgebra.lift_ι_apply, radicalUpper_polynomial]

theorem upper_decomposition_from_radical {n : ℕ} (i : AdjacentPosition n) (A : upperNilpotent n) :
    A=upperSimpleCoefficient i A • rootVector (adjacentPositiveRoot i)+
      radicalUpper i (upperRadicalPart i A) := by
  apply polynomialUpperLie_injective n
  rw [map_add, map_smul, radicalUpper_polynomial]
  exact polynomialUpperLie_decomposition i A

theorem presentationUpper_decomposition {n : ℕ} (u : Composition n) (i : AdjacentPosition n)
    (A : upperNilpotent n) (x : PresentationQuotient u) :
    UniversalEnvelopingAlgebra.ι ℂ A • x = upperSimpleCoefficient i A • presentationRaising u i x+
      UniversalEnvelopingAlgebra.ι ℂ (radicalUpper i (upperRadicalPart i A)) • x := by
  have h := congrArg (presentationUpperLie u) (upper_decomposition_from_radical i A)
  rw [map_add, map_smul, presentationUpperLie_raising] at h
  exact LinearMap.congr_fun h x

variable {n : ℕ} (u : Composition n) (i : AdjacentPosition n)
  (hu : u i.left ≤ u i.right) (hJP : CompositionFlagJosephPolo (swapComposition u i))
  (B : PolynomialRootStringBasis i.left i.right (compositionFlag (swapComposition u i)))

theorem adjacentCompletionToPresentation_radical
    (r : radicalEndLie i) (x : B.completedModule i.left_ne_right) :
    letI := presentationSl2LieRingModule u i hu
    letI := presentationSl2LieModule u i hu
    adjacentCompletionToPresentation u i hu hJP B
      (B.completedRadicalAction (compositionFlag_adjacent_raising_stable (swapComposition u i) i)
        (compositionFlag_radical_stable i (swapComposition u i)) (r ⊗ₜ[ℂ] x)) =
      UniversalEnvelopingAlgebra.ι ℂ (radicalUpper i r) •
        adjacentCompletionToPresentation u i hu hJP B x := by
  letI := presentationSl2LieRingModule u i hu
  letI := presentationSl2LieModule u i hu
  letI := presentation_finite u
  let G := adjacentCompletionToPresentation u i hu hJP B
  let A := presentationRadicalAction u i hu
  have hb (s : radicalEndLie i) (p : compositionFlag (swapComposition u i)) :
      G (B.completionBoundary i.left_ne_right
        (radicalPolynomialAction i (compositionFlag (swapComposition u i))
          (compositionFlag_radical_stable i (swapComposition u i)) (s ⊗ₜ[ℂ] p))) =
        A (s ⊗ₜ[ℂ] G (B.completionBoundary i.left_ne_right p)) := by
    change adjacentCompletionToPresentation u i hu hJP B _=presentationRadicalAction u i hu _
    rw [adjacentCompletionToPresentation_boundary, adjacentCompletionToPresentation_boundary,
      presentationRadicalAction_tmul, radicalPolynomialAction_as_smul, map_smul]
  have hc := (B.isCompletion i.left_ne_right
    (compositionFlag_adjacent_raising_stable (swapComposition u i) i)).extendAction_natural_apply
    (radicalPolynomialAction i (compositionFlag (swapComposition u i))
      (compositionFlag_radical_stable i (swapComposition u i)))
    (polynomialRadicalSource_e (compositionFlag_adjacent_raising_stable (swapComposition u i) i)
      (compositionFlag_radical_stable i (swapComposition u i)))
    (B.radicalSource_h (compositionFlag_radical_stable i (swapComposition u i)))
    A G hb r x
  exact hc.trans (presentationRadicalAction_tmul u i hu r (G x))

theorem adjacentCompletionToPresentation_upper
    (A : upperNilpotent n) (x : B.completedModule i.left_ne_right) :
    letI := presentationSl2LieRingModule u i hu
    letI := presentationSl2LieModule u i hu
    adjacentCompletionToPresentation u i hu hJP B
      (B.completedUpperLie (compositionFlag_adjacent_raising_stable (swapComposition u i) i)
        (compositionFlag_radical_stable i (swapComposition u i)) A x) =
      UniversalEnvelopingAlgebra.ι ℂ A • adjacentCompletionToPresentation u i hu hJP B x := by
  let sourceRing : LieRingModule
      ((polynomialSl2Triple i.left i.right i.left_ne_right).toLieSubalgebra ℂ)
      (B.completedModule i.left_ne_right) := inferInstance
  letI := presentationSl2LieRingModule u i hu
  letI := presentationSl2LieModule u i hu
  letI := sourceRing
  let G := adjacentCompletionToPresentation u i hu hJP B
  have he := G.map_lie (sl2RaisingElement (polynomialSl2Triple i.left i.right i.left_ne_right)) x
  rw [presentationSl2_raising u i hu] at he
  have hr := adjacentCompletionToPresentation_radical u i hu hJP B (upperRadicalPart i A) x
  change G _=UniversalEnvelopingAlgebra.ι ℂ A • G x
  calc
    _ = G (upperSimpleCoefficient i A •
        ⁅sl2RaisingElement (polynomialSl2Triple i.left i.right i.left_ne_right),x⁆+
          B.completedRadicalAction (compositionFlag_adjacent_raising_stable (swapComposition u i) i)
            (compositionFlag_radical_stable i (swapComposition u i)) (upperRadicalPart i A ⊗ₜ[ℂ] x)) := rfl
    _ = upperSimpleCoefficient i A • G
        ⁅sl2RaisingElement (polynomialSl2Triple i.left i.right i.left_ne_right),x⁆+
          G (B.completedRadicalAction (compositionFlag_adjacent_raising_stable (swapComposition u i) i)
            (compositionFlag_radical_stable i (swapComposition u i)) (upperRadicalPart i A ⊗ₜ[ℂ] x)) :=
      (G.toLinearMap.map_add _ _).trans (congrArg₂ (·+·) (G.toLinearMap.map_smul _ _) rfl)
    _ = upperSimpleCoefficient i A • presentationRaising u i (G x)+
        UniversalEnvelopingAlgebra.ι ℂ (radicalUpper i (upperRadicalPart i A)) • G x :=
      congrArg₂ (·+·) (congrArg (upperSimpleCoefficient i A • ·) he) hr
    _ = UniversalEnvelopingAlgebra.ι ℂ A • G x := (presentationUpper_decomposition u i A (G x)).symm

theorem adjacentCompletionToPresentation_enveloping
    (a : Enveloping n) (x : B.completedModule i.left_ne_right) :
    letI := presentationSl2LieRingModule u i hu
    letI := presentationSl2LieModule u i hu
    adjacentCompletionToPresentation u i hu hJP B
      (B.completedUpperEnveloping (compositionFlag_adjacent_raising_stable (swapComposition u i) i)
        (compositionFlag_radical_stable i (swapComposition u i)) a x) =
      a • adjacentCompletionToPresentation u i hu hJP B x := by
  letI := presentationSl2LieRingModule u i hu
  letI := presentationSl2LieModule u i hu
  apply enveloping_intertwines
    (B.completedUpperEnveloping (compositionFlag_adjacent_raising_stable (swapComposition u i) i)
      (compositionFlag_radical_stable i (swapComposition u i)))
    (Algebra.lsmul ℂ ℂ (PresentationQuotient u))
    (adjacentCompletionToPresentation u i hu hJP B).toLinearMap
  intro A y
  rw [B.completedUpperEnveloping_ι]
  exact adjacentCompletionToPresentation_upper u i hu hJP B A y

end
end Schubert.RS.Representation
