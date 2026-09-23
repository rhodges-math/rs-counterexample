import Schubert.RS.Representation.PolynomialCompletionUpper
import Schubert.RS.Representation.RankOneActionNaturality

namespace Schubert.RS.Representation
noncomputable section
open FinPermutation TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000

variable {n : ℕ} {i : AdjacentPosition n} {S T : Submodule ℂ (MatrixPolynomial n)}
  (B : PolynomialRootStringBasis i.left i.right S)
  (hE : ∀ p∈S, matrixUnitDerivation i.left i.right p∈S)
  (hR : ∀ r : RadicalRoot i, ∀ p∈S, matrixUnitDerivation r.val.val.1 r.val.val.2 p∈S)
  (hTE : ∀ p∈T, matrixUnitDerivation i.left i.right p∈T)
  (hTF : ∀ p∈T, matrixUnitDerivation i.right i.left p∈T)
  (hTR : ∀ r : RadicalRoot i, ∀ p∈T, matrixUnitDerivation r.val.val.1 r.val.val.2 p∈T)

theorem PolynomialRootStringBasis.completedUpperTower :
    letI := B.completedUpperModule hE hR
    IsScalarTower ℂ (Enveloping n) (B.completedModule i.left_ne_right) := by
  letI := B.completedUpperModule hE hR
  exact ⟨fun c a x => by
    change B.completedUpperEnveloping hE hR (c • a) x = c • B.completedUpperEnveloping hE hR a x
    rw [map_smul]
    rfl⟩

def polynomialRootRadicalLinear :
    (radicalEndLie i ⊗[ℂ] polynomialRootModule i.left i.right i.left_ne_right T hTE hTF)
      →ₗ[ℂ] polynomialRootModule i.left i.right i.left_ne_right T hTE hTF :=
  letI : LieRingModule (radicalEndLie i)
      (polynomialRootModule i.left i.right i.left_ne_right T hTE hTF) :=
    inferInstanceAs (LieRingModule (radicalEndLie i) (radicalPolynomialSubmodule i T hTR))
  letI : LieModule ℂ (radicalEndLie i)
      (polynomialRootModule i.left i.right i.left_ne_right T hTE hTF) :=
    inferInstanceAs (LieModule ℂ (radicalEndLie i) (radicalPolynomialSubmodule i T hTR))
  (LieModule.toModuleHom ℂ (radicalEndLie i)
    (polynomialRootModule i.left i.right i.left_ne_right T hTE hTF)).toLinearMap

theorem polynomialRootRadicalLinear_val (r : radicalEndLie i)
    (p : polynomialRootModule i.left i.right i.left_ne_right T hTE hTF) :
    (polynomialRootRadicalLinear hTE hTF hTR (r ⊗ₜ[ℂ] p) : MatrixPolynomial n) = r.val p.val := rfl

/-- The actual radical action on a root-stable polynomial target is
equivariant for the full chosen sl2. -/
def polynomialRootRadicalAction :
    (radicalEndLie i ⊗[ℂ] polynomialRootModule i.left i.right i.left_ne_right T hTE hTF)
      →ₗ⁅ℂ,(polynomialSl2Triple i.left i.right i.left_ne_right).toLieSubalgebra ℂ⁆
        polynomialRootModule i.left i.right i.left_ne_right T hTE hTF where
  toLinearMap := polynomialRootRadicalLinear hTE hTF hTR
  map_lie' := by
    intro a z
    change polynomialRootRadicalLinear hTE hTF hTR ⁅a,z⁆ =
      ⁅a,polynomialRootRadicalLinear hTE hTF hTR z⁆
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul r p =>
        rw [TensorProduct.LieModule.lie_tmul_right,map_add]
        apply Subtype.ext
        change (a.val (r.val p.val)-r.val (a.val p.val)) + r.val (a.val p.val) = a.val (r.val p.val)
        exact sub_add_cancel _ _
    | add z w hz hw => simp only [lie_add,map_add,hz,hw]

variable [Module.Finite ℂ T] (hST : S≤T)

def polynomialRootInclusion : S →ₗ[ℂ] polynomialRootModule i.left i.right i.left_ne_right T hTE hTF where
  toFun p := ⟨p.val,hST p.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance polynomialRootModule_finite :
    Module.Finite ℂ (polynomialRootModule i.left i.right i.left_ne_right T hTE hTF) :=
  inferInstanceAs (Module.Finite ℂ T)

def PolynomialRootStringBasis.completionEvaluation :
    B.completedModule i.left_ne_right →ₗ⁅ℂ,
      (polynomialSl2Triple i.left i.right i.left_ne_right).toLieSubalgebra ℂ⁆
        polynomialRootModule i.left i.right i.left_ne_right T hTE hTF := by
  exact (B.isCompletion i.left_ne_right hE).lift (polynomialRootInclusion hTE hTF hST)
    (fun p => by apply Subtype.ext; rfl)
    (fun p => by apply Subtype.ext; exact B.cartan_val i.left_ne_right p)

theorem PolynomialRootStringBasis.completionEvaluation_boundary (p : S) :
    B.completionEvaluation hE hTE hTF hST (B.completionBoundary i.left_ne_right p) =
      polynomialRootInclusion hTE hTF hST p := by
  unfold PolynomialRootStringBasis.completionEvaluation
  exact (B.isCompletion i.left_ne_right hE).lift_boundary _ _ _ p

theorem PolynomialRootStringBasis.completionEvaluation_radical
    (r : radicalEndLie i) (x : B.completedModule i.left_ne_right) :
    B.completionEvaluation hE hTE hTF hST (B.completedRadicalAction hE hR (r ⊗ₜ[ℂ] x)) =
      polynomialRootRadicalAction hTE hTF hTR
        (r ⊗ₜ[ℂ] B.completionEvaluation hE hTE hTF hST x) := by
  apply (B.isCompletion i.left_ne_right hE).extendAction_natural_apply
    (radicalPolynomialAction i S hR) (polynomialRadicalSource_e hE hR) (B.radicalSource_h hR)
    (polynomialRootRadicalAction hTE hTF hTR) (B.completionEvaluation hE hTE hTF hST)
  intro r p
  calc
    _ = polynomialRootInclusion hTE hTF hST
        (radicalPolynomialAction i S hR (r ⊗ₜ[ℂ] p)) :=
      B.completionEvaluation_boundary hE hTE hTF hST _
    _ = polynomialRootRadicalAction hTE hTF hTR
        (r ⊗ₜ[ℂ] polynomialRootInclusion hTE hTF hST p) := by
      apply Subtype.ext
      exact (radicalPolynomialAction_tmul_val i S hR r p).trans
        (polynomialRootRadicalLinear_val hTE hTF hTR r (polynomialRootInclusion hTE hTF hST p)).symm
    _ = _ := congrArg (fun y => polynomialRootRadicalAction hTE hTF hTR (r ⊗ₜ[ℂ] y))
      (B.completionEvaluation_boundary hE hTE hTF hST p).symm

def PolynomialRootStringBasis.completionEvaluationPolynomial :
    B.completedModule i.left_ne_right →ₗ[ℂ] MatrixPolynomial n :=
  (polynomialRootModule i.left i.right i.left_ne_right T hTE hTF).toSubmodule.subtype.comp
    (B.completionEvaluation hE hTE hTF hST).toLinearMap

include hTR in
theorem PolynomialRootStringBasis.completionEvaluation_upper_val
    (A : upperNilpotent n) (x : B.completedModule i.left_ne_right) :
    (B.completionEvaluation hE hTE hTF hST (B.completedUpperLie hE hR A x) : MatrixPolynomial n) =
      polynomialUpperLie n A (B.completionEvaluation hE hTE hTF hST x).val := by
  let f := B.completionEvaluationPolynomial hE hTE hTF hST
  have he : f ⁅sl2RaisingElement (polynomialSl2Triple i.left i.right i.left_ne_right),x⁆ =
      matrixUnitDerivation i.left i.right (f x) :=
    congrArg Subtype.val ((B.completionEvaluation hE hTE hTF hST).map_lie
      (sl2RaisingElement (polynomialSl2Triple i.left i.right i.left_ne_right)) x)
  have hr : f (B.completedRadicalAction hE hR (upperRadicalPart i A ⊗ₜ[ℂ] x)) =
      (upperRadicalPart i A).val (f x) :=
    congrArg Subtype.val (B.completionEvaluation_radical hE hR hTE hTF hTR hST (upperRadicalPart i A) x)
  change f (B.completedUpperLie hE hR A x) = polynomialUpperLie n A (f x)
  calc
    _ = f (upperSimpleCoefficient i A •
          ⁅sl2RaisingElement (polynomialSl2Triple i.left i.right i.left_ne_right),x⁆ +
        B.completedRadicalAction hE hR (upperRadicalPart i A ⊗ₜ[ℂ] x)) :=
      congrArg f (B.completedUpperLie_apply hE hR A x)
    _ = upperSimpleCoefficient i A •
          f ⁅sl2RaisingElement (polynomialSl2Triple i.left i.right i.left_ne_right),x⁆ +
        f (B.completedRadicalAction hE hR (upperRadicalPart i A ⊗ₜ[ℂ] x)) :=
      (f.map_add _ _).trans (congrArg₂ (· + ·) (f.map_smul _ _) rfl)
    _ = upperSimpleCoefficient i A • matrixUnitDerivation i.left i.right (f x) +
        (upperRadicalPart i A).val (f x) :=
      congrArg₂ (· + ·) (congrArg (upperSimpleCoefficient i A • ·) he) hr
    _ = _ := (congrArg (fun D : Module.End ℂ (MatrixPolynomial n) => D (f x))
      (polynomialUpperLie_decomposition i A)).symm

include hTR in
/-- Evaluation into any finite actual polynomial target containing the
source respects the entire upper enveloping action. -/
theorem PolynomialRootStringBasis.completionEvaluation_enveloping_val
    (a : Enveloping n) (x : B.completedModule i.left_ne_right) :
    (B.completionEvaluation hE hTE hTF hST (B.completedUpperEnveloping hE hR a x) : MatrixPolynomial n) =
      polynomialEnveloping n a (B.completionEvaluation hE hTE hTF hST x).val := by
  apply enveloping_intertwines _ _ (B.completionEvaluationPolynomial hE hTE hTF hST) _ a x
  intro A x
  let f := B.completionEvaluationPolynomial hE hTE hTF hST
  calc
    _ = f (B.completedUpperLie hE hR A x) :=
      congrArg (fun D : Module.End ℂ (B.completedModule i.left_ne_right) => f (D x))
        (B.completedUpperEnveloping_ι hE hR A)
    _ = polynomialUpperLie n A (f x) :=
      B.completionEvaluation_upper_val hE hR hTE hTF hTR hST A x
    _ = _ := (congrArg (fun D : Module.End ℂ (MatrixPolynomial n) => D (f x))
      (UniversalEnvelopingAlgebra.lift_ι_apply ℂ (polynomialUpperLie n) A)).symm

def PolynomialRootStringBasis.completionEvaluationU :
    letI := B.completedUpperModule hE hR
    letI := polynomialSubmoduleEnvelopingModule T (positiveRoot_stable_of_simple_radical hTE hTR)
    B.completedModule i.left_ne_right →ₗ[Enveloping n] T :=
  letI := B.completedUpperModule hE hR
  letI := polynomialSubmoduleEnvelopingModule T (positiveRoot_stable_of_simple_radical hTE hTR)
  { toFun := fun x => ⟨(B.completionEvaluation hE hTE hTF hST x).val,
      (B.completionEvaluation hE hTE hTF hST x).property⟩
    map_add' := fun x y => Subtype.ext ((B.completionEvaluationPolynomial hE hTE hTF hST).map_add x y)
    map_smul' := fun a x => Subtype.ext (B.completionEvaluation_enveloping_val hE hR hTE hTF hTR hST a x) }

end
end Schubert.RS.Representation
