import Schubert.RS.Representation.ParabolicRadicalSpan

namespace Schubert.RS.Representation
noncomputable section
open FinPermutation
attribute [local instance 100] LieRing.ofAssociativeRing

/-- The actual adjacent parabolic radical, realized faithfully as a finite
Lie subalgebra of polynomial operators generated linearly by its roots. -/
def radicalEndLie {n : ℕ} (i : AdjacentPosition n) :
    LieSubalgebra ℂ (Module.End ℂ (MatrixPolynomial n)) where
  toSubmodule := radicalEndSpan i
  lie_mem' := radicalEndSpan_lie_mem i

instance radicalEndLie_finite {n : ℕ} (i : AdjacentPosition n) :
    Module.Finite ℂ (radicalEndLie i) :=
  Module.Finite.span_of_finite ℂ (Set.finite_range _)

def radicalEndRoot {n : ℕ} (i : AdjacentPosition n) (r : RadicalRoot i) : radicalEndLie i :=
  ⟨(matrixUnitDerivation r.val.val.1 r.val.val.2).toLinearMap,radicalEndSpan_root_mem i r⟩

theorem radicalEndRoot_apply {n : ℕ} (i : AdjacentPosition n) (r : RadicalRoot i)
    (p : MatrixPolynomial n) :
    (radicalEndRoot i r).val p = matrixUnitDerivation r.val.val.1 r.val.val.2 p := rfl

/-- Stability under the actual generated sl₂ subalgebra, including lowering. -/
def radicalLeviSubmodule {n : ℕ} (i : AdjacentPosition n) :
    LieSubmodule ℂ ((polynomialSl2Triple i.left i.right i.left_ne_right).toLieSubalgebra ℂ)
      (Module.End ℂ (MatrixPolynomial n)) where
  toSubmodule := radicalEndSpan i
  lie_mem := by
    intro z A hA
    change ⁅z.val,A⁆ ∈ radicalEndSpan i
    obtain ⟨u,v,w,hz⟩ := (IsSl2Triple.mem_toLieSubalgebra_iff (R := ℂ)
      (t := polynomialSl2Triple i.left i.right i.left_ne_right)).mp z.property
    rw [hz,polynomial_root_e_f,add_lie,add_lie,smul_lie,smul_lie,smul_lie]
    exact (radicalEndSpan i).add_mem
      ((radicalEndSpan i).add_mem
        ((radicalEndSpan i).smul_mem u (radicalEndSpan_raising i hA))
        ((radicalEndSpan i).smul_mem v (radicalEndSpan_lowering i hA)))
      ((radicalEndSpan i).smul_mem w (radicalEndSpan_cartan i hA))

instance radicalEndLie_leviLieRingModule {n : ℕ} (i : AdjacentPosition n) :
    LieRingModule ((polynomialSl2Triple i.left i.right i.left_ne_right).toLieSubalgebra ℂ)
      (radicalEndLie i) :=
  inferInstanceAs (LieRingModule
    ((polynomialSl2Triple i.left i.right i.left_ne_right).toLieSubalgebra ℂ) (radicalLeviSubmodule i))

instance radicalEndLie_leviLieModule {n : ℕ} (i : AdjacentPosition n) :
    LieModule ℂ ((polynomialSl2Triple i.left i.right i.left_ne_right).toLieSubalgebra ℂ)
      (radicalEndLie i) :=
  inferInstanceAs (LieModule ℂ
    ((polynomialSl2Triple i.left i.right i.left_ne_right).toLieSubalgebra ℂ) (radicalLeviSubmodule i))

theorem radicalEndLie_levi_action_val {n : ℕ} (i : AdjacentPosition n)
    (z : (polynomialSl2Triple i.left i.right i.left_ne_right).toLieSubalgebra ℂ)
    (r : radicalEndLie i) : (⁅z,r⁆ : radicalEndLie i).val = ⁅z.val,r.val⁆ := rfl

/-- Adjoint stability is an actual derivation action on the radical bracket. -/
theorem radicalEndLie_levi_derivation {n : ℕ} (i : AdjacentPosition n)
    (z : (polynomialSl2Triple i.left i.right i.left_ne_right).toLieSubalgebra ℂ)
    (r s : radicalEndLie i) : ⁅z,⁅r,s⁆⁆ = ⁅⁅z,r⁆,s⁆ + ⁅r,⁅z,s⁆⁆ := by
  apply Subtype.ext
  exact leibniz_lie z.val r.val s.val

theorem radicalEndSpan_preserves {n : ℕ} (i : AdjacentPosition n)
    (S : Submodule ℂ (MatrixPolynomial n))
    (hS : ∀ r : RadicalRoot i, ∀ p∈S, matrixUnitDerivation r.val.val.1 r.val.val.2 p∈S)
    {A : Module.End ℂ (MatrixPolynomial n)} (hA : A∈radicalEndSpan i)
    {p : MatrixPolynomial n} (hp : p∈S) : A p∈S := by
  induction hA using Submodule.span_induction with
  | mem A hA => obtain ⟨r,rfl⟩ := hA; exact hS r p hp
  | zero => simpa only [LinearMap.zero_apply] using S.zero_mem
  | add A B hA hB ihA ihB => simpa only [LinearMap.add_apply] using S.add_mem ihA ihB
  | smul c A hA ihA => simpa only [LinearMap.smul_apply] using S.smul_mem c ihA

/-- Restriction of the actual radical polynomial action to a stable subspace. -/
def radicalPolynomialSubmodule {n : ℕ} (i : AdjacentPosition n)
    (S : Submodule ℂ (MatrixPolynomial n))
    (hS : ∀ r : RadicalRoot i, ∀ p∈S, matrixUnitDerivation r.val.val.1 r.val.val.2 p∈S) :
    LieSubmodule ℂ (radicalEndLie i) (MatrixPolynomial n) where
  toSubmodule := S
  lie_mem := by
    intro r p hp
    exact radicalEndSpan_preserves i S hS r.property hp

@[instance_reducible] def radicalPolynomialLieRingModule {n : ℕ} (i : AdjacentPosition n)
    (S : Submodule ℂ (MatrixPolynomial n))
    (hS : ∀ r : RadicalRoot i, ∀ p∈S, matrixUnitDerivation r.val.val.1 r.val.val.2 p∈S) :
    LieRingModule (radicalEndLie i) S :=
  inferInstanceAs (LieRingModule (radicalEndLie i) (radicalPolynomialSubmodule i S hS))

theorem radicalPolynomialLieModule {n : ℕ} (i : AdjacentPosition n)
    (S : Submodule ℂ (MatrixPolynomial n))
    (hS : ∀ r : RadicalRoot i, ∀ p∈S, matrixUnitDerivation r.val.val.1 r.val.val.2 p∈S) :
    @LieModule ℂ (radicalEndLie i) S _ _ _ _ _ (radicalPolynomialLieRingModule i S hS) :=
  inferInstanceAs (LieModule ℂ (radicalEndLie i) (radicalPolynomialSubmodule i S hS))

theorem compositionFlag_radical_stable {n : ℕ} (i : AdjacentPosition n) (u : Composition n)
    (r : RadicalRoot i) (p : MatrixPolynomial n) (hp : p∈compositionFlag u) :
    matrixUnitDerivation r.val.val.1 r.val.val.2 p∈compositionFlag u :=
  upperCyclic_root_stable _ r.val hp

end
end Schubert.RS.Representation
