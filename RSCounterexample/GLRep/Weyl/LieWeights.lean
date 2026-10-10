import RSCounterexample.GLRep.Weyl.CharacterFormula
import TauCeti.Algebra.Lie.GeneralLinear.Existence
import TauCeti.LinearAlgebra.Eigenspace.JointEigenvector.Basic
import Mathlib.LinearAlgebra.Trace

/-!
# Integral weights of `gl_n`-modules and their characters

Let `M` be a module over `gl_n(K) = Matrix (Fin n) (Fin n) K`, `K` a field of characteristic zero.
For an integral weight `μ : Fin n → ℤ`, the **weight space** `GLRep.glWeightSpace K M μ` consists of
the vectors on which every diagonal matrix unit `E_ii` acts by `μ_i`. The matrix unit `E_ab` maps
the weight space of `μ` into that of `μ + ε_a − ε_b` (`GLRep.lie_mem_glWeightSpace`).

`M` is **integral** (`GLRep.IsIntegralGLModule`) when it is finite-dimensional and spanned by its
integral weight spaces. Its **character** (`GLRep.glCharacter M`) is the Laurent polynomial
`∑_μ dim M_μ · x^μ`.

## Main definitions

* `GLRep.glWeightSpace`, `GLRep.IsIntegralGLModule`, `GLRep.glCharacter`.
* `GLRep.weightShift`: `E_ab` as a linear map `M_μ → M_ν`, for `ν = μ + ε_a − ε_b`.

## Main results

* `GLRep.iSupIndep_glWeightSpace`: the weight spaces are independent.
* `GLRep.coeff_glCharacter`.
-/

namespace GLRep

open Module LieModule

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K : Type*} [Field K] {n : ℕ}
variable {M : Type*} [AddCommGroup M] [Module K M] [LieRingModule (Matrix (Fin n) (Fin n) K) M]
  [LieModule K (Matrix (Fin n) (Fin n) K) M]

/-- The matrix unit `E_ab`. -/
abbrev matUnit (a b : Fin n) : Matrix (Fin n) (Fin n) K := Matrix.single a b 1

variable (K M) in
/-- The **weight space** of an integral weight `μ`: the vectors on which each diagonal matrix
unit `E_ii` acts by `μ_i`. -/
def glWeightSpace (μ : Fin n → ℤ) : Submodule K M :=
  ⨅ i, Module.End.eigenspace (toEnd K (Matrix (Fin n) (Fin n) K) M (matUnit i i)) (μ i : K)

theorem mem_glWeightSpace {μ : Fin n → ℤ} {m : M} :
    m ∈ glWeightSpace K M μ ↔
      ∀ i, ⁅(matUnit i i : Matrix (Fin n) (Fin n) K), m⁆ = (μ i : K) • m := by
  simp [glWeightSpace]

/-- The root `ε_a − ε_b`. -/
def root (a b : Fin n) : Fin n → ℤ := Pi.single a 1 - Pi.single b 1

/-- **`E_ab` shifts weights by `ε_a − ε_b`.** -/
theorem lie_mem_glWeightSpace {μ : Fin n → ℤ} {m : M} (hm : m ∈ glWeightSpace K M μ) (a b : Fin n) :
    ⁅(matUnit a b : Matrix (Fin n) (Fin n) K), m⁆ ∈ glWeightSpace K M (μ + root a b) := by
  rw [mem_glWeightSpace] at hm ⊢
  intro i
  rw [TauCeti.lie_single_self_lie_single_eq_smul (mu := fun j => (μ j : K)) hm a b i]
  congr 1
  simp [root, Pi.single_apply]

variable [CharZero K]

variable (K M) in
/-- **The weight spaces are independent**, in characteristic zero. -/
theorem iSupIndep_glWeightSpace : iSupIndep (glWeightSpace K M (n := n)) :=
  (iSupIndep_iInf_eigenspace
    (fun i => toEnd K (Matrix (Fin n) (Fin n) K) M (matUnit i i))).comp fun μ ν h => by
      funext i
      exact Int.cast_injective (congrFun h i)

variable (K M) in
/-- A finite-dimensional module has finitely many nonzero weight spaces. -/
theorem finite_glWeightSpace_ne_bot [FiniteDimensional K M] :
    {μ : Fin n → ℤ | glWeightSpace K M μ ≠ ⊥}.Finite :=
  WellFoundedGT.finite_ne_bot_of_iSupIndep (iSupIndep_glWeightSpace K M)

variable (n K M) in
/-- `M` is an **integral** `gl_n`-module: finite-dimensional and spanned by its integral weight
spaces. -/
structure IsIntegralGLModule : Prop where
  finiteDimensional : FiniteDimensional K M
  iSup_eq_top : ⨆ μ : Fin n → ℤ, glWeightSpace K M μ = ⊤

theorem IsIntegralGLModule.isInternal (hM : IsIntegralGLModule K n M) :
    DirectSum.IsInternal (glWeightSpace K M (n := n)) :=
  (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr
    ⟨iSupIndep_glWeightSpace K M, hM.iSup_eq_top⟩

/-! ### Laurent polynomials from finitely supported functions -/

/-- The Laurent polynomial with coefficients `f`, for `f` of finite support (it is `0`
otherwise). -/
def LaurentPoly.ofFun (f : (Fin n → ℤ) → K) : LaurentPoly K n :=
  open Classical in
  if h : (Function.support f).Finite then AddMonoidAlgebra.ofCoeff (Finsupp.ofSupportFinite f h)
  else 0

omit [CharZero K] in
theorem LaurentPoly.coeff_ofFun {f : (Fin n → ℤ) → K} (hf : (Function.support f).Finite)
    (μ : Fin n → ℤ) : (LaurentPoly.ofFun f).coeff μ = f μ := by
  simp only [LaurentPoly.ofFun, hf, ↓reduceDIte]
  rfl

variable (K M) in
/-- The **character** `∑_μ dim M_μ · x^μ` of a `gl_n`-module. -/
def glCharacter : LaurentPoly K n :=
  LaurentPoly.ofFun fun μ => (finrank K (glWeightSpace K M μ) : K)

theorem finite_support_finrank_glWeightSpace [FiniteDimensional K M] :
    (Function.support fun μ : Fin n → ℤ => (finrank K (glWeightSpace K M μ) : K)).Finite := by
  refine (finite_glWeightSpace_ne_bot K M).subset fun μ hμ => ?_
  simp only [Function.mem_support, ne_eq, Nat.cast_eq_zero] at hμ
  intro hbot
  apply hμ
  rw [hbot, finrank_bot]

theorem coeff_glCharacter [FiniteDimensional K M] (μ : Fin n → ℤ) :
    (glCharacter K M).coeff μ = (finrank K (glWeightSpace K M μ) : K) :=
  LaurentPoly.coeff_ofFun finite_support_finrank_glWeightSpace μ

end

end GLRep
