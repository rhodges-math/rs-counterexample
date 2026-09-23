import Schubert.RS.Representation.PolynomialCompletionRadical
import Schubert.RS.Representation.ParabolicUpperRepresentation
import Schubert.RS.Representation.EnvelopingIntertwining

namespace Schubert.RS.Representation
noncomputable section
open FinPermutation TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000

variable {n : ℕ} {i : AdjacentPosition n} {S : Submodule ℂ (MatrixPolynomial n)}
  (B : PolynomialRootStringBasis i.left i.right S)
  (hE : ∀ p∈S, matrixUnitDerivation i.left i.right p∈S)
  (hR : ∀ r : RadicalRoot i, ∀ p∈S, matrixUnitDerivation r.val.val.1 r.val.val.2 p∈S)

include hE hR in
theorem positiveRoot_stable_of_simple_radical (r : PositiveRoot n) (p : MatrixPolynomial n)
    (hp : p∈S) : matrixUnitDerivation r.val.1 r.val.2 p∈S := by
  by_cases hr : r=adjacentPositiveRoot i
  · subst r
    exact hE p hp
  · exact hR ⟨r,fun hh => hr (Subtype.ext hh)⟩ p hp

def PolynomialRootStringBasis.completedUpperLie :
    upperNilpotent n →ₗ⁅ℂ⁆ Module.End ℂ (B.completedModule i.left_ne_right) :=
  letI := B.completedRadicalLieRingModule hE hR
  letI := B.completedRadicalLieModule hE hR
  letI := B.completedRadical_isLieTower hE hR
  parabolicUpperLie i (B.completedModule i.left_ne_right)

theorem PolynomialRootStringBasis.completedUpperLie_apply (A : upperNilpotent n)
    (x : B.completedModule i.left_ne_right) :
    B.completedUpperLie hE hR A x = upperSimpleCoefficient i A •
      ⁅sl2RaisingElement (polynomialSl2Triple i.left i.right i.left_ne_right),x⁆ +
      B.completedRadicalAction hE hR (upperRadicalPart i A ⊗ₜ[ℂ] x) := rfl

def PolynomialRootStringBasis.completedUpperEnveloping :
    Enveloping n →ₐ[ℂ] Module.End ℂ (B.completedModule i.left_ne_right) :=
  UniversalEnvelopingAlgebra.lift ℂ (B.completedUpperLie hE hR)

theorem PolynomialRootStringBasis.completedUpperEnveloping_ι (A : upperNilpotent n) :
    B.completedUpperEnveloping hE hR (UniversalEnvelopingAlgebra.ι ℂ A) =
      B.completedUpperLie hE hR A :=
  UniversalEnvelopingAlgebra.lift_ι_apply ℂ _ A

@[instance_reducible] def PolynomialRootStringBasis.completedUpperModule :
    Module (Enveloping n) (B.completedModule i.left_ne_right) :=
  Module.compHom _ (B.completedUpperEnveloping hE hR).toRingHom

theorem PolynomialRootStringBasis.completionBoundary_upper (A : upperNilpotent n) (p : S) :
    B.completionBoundary i.left_ne_right
      (polynomialSubmoduleEnveloping S (positiveRoot_stable_of_simple_radical hE hR)
        (UniversalEnvelopingAlgebra.ι ℂ A) p) =
      B.completedUpperLie hE hR A (B.completionBoundary i.left_ne_right p) := by
  have hp : polynomialSubmoduleEnveloping S (positiveRoot_stable_of_simple_radical hE hR)
      (UniversalEnvelopingAlgebra.ι ℂ A) p =
      upperSimpleCoefficient i A • matrixUnitOnSubmodule i.left i.right S hE p +
        radicalPolynomialAction i S hR (upperRadicalPart i A ⊗ₜ[ℂ] p) := by
    apply Subtype.ext
    change polynomialEnveloping n (UniversalEnvelopingAlgebra.ι ℂ A) p.val = _
    rw [polynomialEnveloping,UniversalEnvelopingAlgebra.lift_ι_apply,
      polynomialUpperLie_decomposition i A]
    rfl
  calc
    _ = B.completionBoundary i.left_ne_right
        (upperSimpleCoefficient i A • matrixUnitOnSubmodule i.left i.right S hE p +
          radicalPolynomialAction i S hR (upperRadicalPart i A ⊗ₜ[ℂ] p)) :=
      congrArg (B.completionBoundary i.left_ne_right) hp
    _ = upperSimpleCoefficient i A • B.completionBoundary i.left_ne_right
          (matrixUnitOnSubmodule i.left i.right S hE p) +
        B.completionBoundary i.left_ne_right
          (radicalPolynomialAction i S hR (upperRadicalPart i A ⊗ₜ[ℂ] p)) := by
      rw [map_add,map_smul]
    _ = upperSimpleCoefficient i A •
          ⁅sl2RaisingElement (polynomialSl2Triple i.left i.right i.left_ne_right),
            B.completionBoundary i.left_ne_right p⁆ +
        B.completedRadicalAction hE hR
          (upperRadicalPart i A ⊗ₜ[ℂ] B.completionBoundary i.left_ne_right p) :=
      congrArg₂ (· + ·)
        (congrArg (upperSimpleCoefficient i A • ·) ((B.isCompletion i.left_ne_right hE).map_e p))
        (B.completedRadicalAction_boundary hE hR (upperRadicalPart i A) p).symm
    _ = _ := (B.completedUpperLie_apply hE hR A (B.completionBoundary i.left_ne_right p)).symm

/-- The constructed completion boundary intertwines the entire actual
upper enveloping action. -/
theorem PolynomialRootStringBasis.completionBoundary_enveloping (a : Enveloping n) (p : S) :
    B.completionBoundary i.left_ne_right
      (polynomialSubmoduleEnveloping S (positiveRoot_stable_of_simple_radical hE hR) a p) =
      B.completedUpperEnveloping hE hR a (B.completionBoundary i.left_ne_right p) :=
  enveloping_intertwines _ _ _ (fun A p => by
    rw [B.completedUpperEnveloping_ι]
    exact B.completionBoundary_upper hE hR A p) a p

def PolynomialRootStringBasis.completionBoundaryU :
    letI := polynomialSubmoduleEnvelopingModule S (positiveRoot_stable_of_simple_radical hE hR)
    letI := B.completedUpperModule hE hR
    S →ₗ[Enveloping n] B.completedModule i.left_ne_right :=
  letI := polynomialSubmoduleEnvelopingModule S (positiveRoot_stable_of_simple_radical hE hR)
  letI := B.completedUpperModule hE hR
  { toFun := B.completionBoundary i.left_ne_right
    map_add' := (B.completionBoundary i.left_ne_right).map_add
    map_smul' := B.completionBoundary_enveloping hE hR }

end
end Schubert.RS.Representation
