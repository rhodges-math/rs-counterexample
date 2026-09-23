import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.LinearAlgebra.Multilinear.Basis
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! Exact coefficient extraction for independent source variables. -/

namespace Schubert.RS

noncomputable section
variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

def laurentCoeffLinear {α : Type*} (a : α) : AddMonoidAlgebra R α →ₗ[R] R :=
  (Finsupp.lapply a).comp (AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap

@[simp] theorem laurentCoeffLinear_apply {α : Type*} (a : α) (f : AddMonoidAlgebra R α) :
    laurentCoeffLinear a f = f.coeff a := rfl

/-- Place a one-variable Laurent polynomial in the specified source variable. -/
def sourceRow (i : ι) : AddMonoidAlgebra R ℤ →ₗ[R] AddMonoidAlgebra R (ι → ℤ) :=
  AddMonoidAlgebra.mapDomainLinearMap R R (fun k : ℤ => (Pi.single i k : ι → ℤ))

@[simp] theorem sourceRow_single (i : ι) (k : ℤ) (r : R) :
    sourceRow i (AddMonoidAlgebra.single k r) =
      AddMonoidAlgebra.single (Pi.single i k) r :=
  AddMonoidAlgebra.mapDomainLinearMap_single _ _ _

/-- Extracting a coefficient in independent source variables factors by row.
The coefficient ring is arbitrary, so it may itself be the slot-polynomial ring. -/
theorem coefficient_source_rows (p : ι → AddMonoidAlgebra R ℤ) (w : ι → ℤ) :
    (∏ i, sourceRow i (p i)).coeff w = ∏ i, (p i).coeff (w i) := by
  classical
  let b : Module.Basis ℤ R (AddMonoidAlgebra R ℤ) :=
    Finsupp.basisSingleOne.map (AddMonoidAlgebra.coeffLinearEquiv R).symm
  have hb (k : ℤ) : b k = AddMonoidAlgebra.single k 1 := by
    simp [b, Module.Basis.map_apply, Finsupp.coe_basisSingleOne]
  let f : MultilinearMap R (fun _ : ι => AddMonoidAlgebra R ℤ) R :=
    (laurentCoeffLinear w).compMultilinearMap
      ((MultilinearMap.mkPiAlgebra R ι (AddMonoidAlgebra R (ι → ℤ))).compLinearMap sourceRow)
  let g : MultilinearMap R (fun _ : ι => AddMonoidAlgebra R ℤ) R :=
    (MultilinearMap.mkPiAlgebra R ι R).compLinearMap (fun i => laurentCoeffLinear (w i))
  have hfg : f = g := by
    apply Module.Basis.ext_multilinear (fun _ => b)
    intro k
    simp only [f, g, LinearMap.compMultilinearMap_apply, MultilinearMap.compLinearMap_apply,
      MultilinearMap.mkPiAlgebra_apply, hb, laurentCoeffLinear_apply, sourceRow_single,
      AddMonoidAlgebra.prod_single, Finset.prod_const_one]
    have hk : (∑ i, Pi.single i (k i) : ι → ℤ) = k := by ext i; simp
    rw [hk]
    simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    rw [Fintype.prod_boole]
    simp only [← funext_iff]
  exact congrArg (fun h => h p) hfg

/-- A determinant whose rows use independent source variables admits rowwise
coefficient extraction. This is the determinant step of source extraction. -/
theorem coefficient_det_source_rows
    (p : ι → ι → AddMonoidAlgebra R ℤ) (w : ι → ℤ) :
    (Matrix.det (fun i j => sourceRow i (p i j))).coeff w =
      Matrix.det (fun i j => (p i j).coeff (w i)) := by
  rw [← Matrix.det_transpose (fun i j => sourceRow i (p i j)),
    ← Matrix.det_transpose (fun i j => (p i j).coeff (w i))]
  simp only [Matrix.det_apply, Matrix.transpose_apply, Units.smul_def]
  change laurentCoeffLinear w (∑ σ : Equiv.Perm ι,
    (σ.sign : ℤ) • ∏ i, sourceRow i (p i (σ i))) = _
  simp only [map_sum, map_zsmul, laurentCoeffLinear_apply, coefficient_source_rows]
  rfl

theorem sourceRow_mul (i : ι) (p q : AddMonoidAlgebra R ℤ) :
    sourceRow i (p * q) = sourceRow i p * sourceRow i q := by
  let e : ℤ →+ (ι → ℤ) :=
    { toFun := fun k => Pi.single i k
      map_zero' := by simp
      map_add' := by intros; simp [Pi.single_add] }
  exact AddMonoidAlgebra.mapDomain_mul e p q

set_option backward.isDefEq.respectTransparency false in
/-- Multiplying by a source alternant replaces each row by shifted
coefficients. No terms of the alternant have been dropped. -/
theorem coefficient_source_alternant (d : ℕ)
    (p : Fin d → AddMonoidAlgebra R ℤ) (w : Fin d → ℤ) :
    (Matrix.det (fun i j : Fin d =>
       sourceRow i (AddMonoidAlgebra.single ((j.val : ℤ) - i.val) (1 : R))) *
       ∏ i, sourceRow i (p i)).coeff w =
      Matrix.det (fun i j : Fin d => (p i).coeff (w i + i.val - j.val)) := by
  have h := coefficient_det_source_rows
    (fun i j : Fin d => AddMonoidAlgebra.single ((j.val : ℤ) - i.val) (1 : R) * p i) w
  have hm : (fun i j : Fin d => sourceRow i
      (AddMonoidAlgebra.single ((j.val : ℤ) - i.val) (1 : R) * p i)) =
      Matrix.of (fun i j : Fin d => sourceRow i (p i) *
        sourceRow i (AddMonoidAlgebra.single ((j.val : ℤ) - i.val) (1 : R))) := by
    funext i j
    rw [sourceRow_mul]
    exact mul_comm _ _
  rw [hm, Matrix.det_mul_column] at h
  rw [mul_comm (∏ i, sourceRow i (p i))] at h
  refine h.trans (congrArg Matrix.det ?_)
  funext i j
  rw [AddMonoidAlgebra.coeff_single_mul_apply, one_mul]
  congr 1
  ring

end
end Schubert.RS
