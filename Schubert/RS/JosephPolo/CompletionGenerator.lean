import Schubert.RS.JosephPolo.BoundaryLift
import Schubert.RS.Sl2EndpointGeneration

namespace Schubert.RS.Representation
noncomputable section
open FinPermutation
attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 400000

theorem sl2Triple_reverse {L : Type*} [LieRing L] {h e f : L} (t : IsSl2Triple h e f) :
    IsSl2Triple (-h) f e where
  h_ne_zero := neg_ne_zero.mpr t.h_ne_zero
  lie_e_f := by rw [← lie_skew, t.lie_e_f]
  lie_h_e_nsmul := by rw [neg_lie, t.lie_h_f_nsmul, neg_neg]
  lie_h_f_nsmul := by rw [neg_lie, t.lie_h_e_nsmul]

theorem lowestVector_mem_of_top {L X : Type*} [LieRing L] [LieAlgebra ℂ L]
    [AddCommGroup X] [Module ℂ X] [LieRingModule L X] [LieModule ℂ L X]
    {h e f : L} (t : IsSl2Triple h e f) {z : X} {d : ℕ}
    (hh : ⁅h,z⁆=-(d:ℂ) • z) (hf : ⁅f,z⁆=0)
    (Y : Submodule ℂ X) (hY : ∀ x, x∈Y → ⁅f,x⁆∈Y)
    (htop : primitiveStringVector e z d∈Y) : z∈Y := by
  apply highestVector_mem_of_endpoint (sl2Triple_reverse t) (d := d) _ hf Y hY htop
  rw [neg_lie, hh, neg_smul, neg_neg]

variable {n : ℕ} (u : Composition n) (i : AdjacentPosition n)
  (hu : u i.left ≤ u i.right)

theorem presentation_raisingString (k : ℕ) :
    letI := presentationSl2LieRingModule u i hu
    letI := presentationSl2LieModule u i hu
    primitiveStringVector (sl2RaisingElement (polynomialSl2Triple i.left i.right i.left_ne_right))
      (presentationGenerator u) k = rootOperator (adjacentPositiveRoot i)^k • presentationGenerator u := by
  letI := presentationSl2LieRingModule u i hu
  letI := presentationSl2LieModule u i hu
  induction k with
  | zero => simp
  | succ k ih =>
    rw [primitiveStringVector_succ, presentationSl2_raising u i hu, ih, pow_succ', mul_smul]
    rfl

variable (hJP : CompositionFlagJosephPolo (swapComposition u i))
  (B : PolynomialRootStringBasis i.left i.right (compositionFlag (swapComposition u i)))

theorem adjacentCompletionToPresentation_generator_mem :
    letI := presentationSl2LieRingModule u i hu
    letI := presentationSl2LieModule u i hu
    presentationGenerator u ∈ (adjacentCompletionToPresentation u i hu hJP B).toLinearMap.range := by
  letI := presentationSl2LieRingModule u i hu
  letI := presentationSl2LieModule u i hu
  let t := polynomialSl2Triple i.left i.right i.left_ne_right
  let G := adjacentCompletionToPresentation u i hu hJP B
  apply lowestVector_mem_of_top (sl2SubalgebraTriple t) (d := u i.right-u i.left)
  · rw [presentationSl2_cartan u i hu, presentationCartan_generator, adjacentWeight_gap u i hu]
  · rw [presentationSl2_lowering u i hu, presentationLowering_generator]
  · intro x hx
    obtain ⟨y,rfl⟩ := hx
    exact ⟨⁅sl2LoweringElement t,y⁆,G.map_lie _ _⟩
  · rw [presentation_raisingString u i hu]
    refine ⟨B.adjacentHighest u i,?_⟩
    change G (B.completionBoundary i.left_ne_right (compositionFlagGenerator (swapComposition u i))) = _
    rw [adjacentCompletionToPresentation_boundary]
    rw [← compositionPresentationMap_generator (swapComposition u i), adjacentPresentationBoundary_map,
      adjacentPresentationMap_generator]
    rfl

end
end Schubert.RS.Representation
