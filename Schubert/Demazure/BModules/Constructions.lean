import Schubert.Demazure.BModules.Characters
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Duals, tensor products and twists of `B`-modules

* `M.dual`: the contragredient module on `Module.Dual ℂ M`, with `(X · φ) = -φ ∘ X` and
  `(t · φ) = φ ∘ t⁻¹`. Its weights are the negatives of the weights of `M`.
* `M.tensor N`: the tensor product, with `X ↦ X ⊗ 1 + 1 ⊗ X` and `t ↦ t ⊗ t`. Its character is
  the product of the characters.
* `M.twist k`: the tensor product with the one-dimensional module of weight `k · (1, …, 1)`,
  i.e. with the `k`-th power of the determinant. Its weights are shifted by `k · (1, …, 1)`.
-/

open Schubert

namespace Demazure.BModules

open FlagModule TensorProduct

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : ℕ}

/-! ### Preliminaries -/

theorem integerWeightScalar_inv (μ : Weight n) (t : DiagonalTorus n) :
    integerWeightScalar μ t⁻¹ = integerWeightScalar (-μ) t := by
  simp [integerWeightScalar, zpow_neg]

theorem torusLie_inv_torusLie (t : DiagonalTorus n) (X : upperNilpotent n) :
    torusLie t⁻¹ (torusLie t X) = X := by
  apply Subtype.ext
  ext i j
  change rootScalar t⁻¹ i j * (rootScalar t i j * X.val i j) = X.val i j
  rw [← mul_assoc, ← rootScalar_mul, inv_mul_cancel, rootScalar_one, one_mul]

/-- A basis of weight vectors makes a representation weight-diagonal. -/
theorem isWeightDiagonal_of_basis {E : Type*} [AddCommGroup E] [Module ℂ E]
    (ρ : DiagonalTorus n →* Module.End ℂ E) {ι : Type*} (b : Module.Basis ι ℂ E)
    (wt : ι → Weight n) (hb : ∀ t i, ρ t (b i) = integerWeightScalar (wt i) t • b i) :
    IsWeightDiagonal ρ := by
  refine eq_top_iff.mpr ?_
  rw [← b.span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact (le_iSup (torusWeightSpace ρ) (wt i)) (fun t => hb t i)

namespace BModule

/-! ### Duals -/

section Dual

variable (M : BModule n)

/-- The contragredient torus action `t · φ = φ ∘ t⁻¹`. -/
def dualTorus : DiagonalTorus n →* Module.End ℂ (Module.Dual ℂ M) where
  toFun t := (M.torus t⁻¹).dualMap
  map_one' := by
    apply LinearMap.ext; intro φ; apply LinearMap.ext; intro v
    simp
  map_mul' s t := by
    apply LinearMap.ext; intro φ; apply LinearMap.ext; intro v
    simp only [LinearMap.dualMap_apply, Module.End.mul_apply, mul_inv, map_mul]
    rw [← Module.End.mul_apply, ← map_mul, mul_comm, map_mul, Module.End.mul_apply]

@[simp] theorem dualTorus_apply (t : DiagonalTorus n) (φ : Module.Dual ℂ M) (v : M) :
    M.dualTorus t φ v = φ (M.torus t⁻¹ v) := rfl

/-- The contragredient action of `𝔫⁺`, `X · φ = -φ ∘ X`. -/
def dualNil : upperNilpotent n →ₗ⁅ℂ⁆ Module.End ℂ (Module.Dual ℂ M) where
  toFun X := -(M.nil X).dualMap
  map_add' X Y := by
    apply LinearMap.ext; intro φ; apply LinearMap.ext; intro v
    simp; ring
  map_smul' c X := by
    apply LinearMap.ext; intro φ; apply LinearMap.ext; intro v
    simp
  map_lie' {X Y} := by
    apply LinearMap.ext; intro φ; apply LinearMap.ext; intro v
    simp [LieHom.map_lie, Ring.lie_def, Module.End.mul_apply]

@[simp] theorem dualNil_apply (X : upperNilpotent n) (φ : Module.Dual ℂ M) (v : M) :
    M.dualNil X φ v = -φ (M.nil X v) := rfl

theorem dualTorus_dualBasis {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ M)
    (wt : ι → Weight n) (hb : ∀ t i, M.torus t (b i) = integerWeightScalar (wt i) t • b i)
    (t : DiagonalTorus n) (i : ι) :
    M.dualTorus t (b.dualBasis i) = integerWeightScalar (-wt i) t • b.dualBasis i := by
  apply b.ext
  intro j
  rw [dualTorus_apply, hb, map_smul, LinearMap.smul_apply, integerWeightScalar_inv]
  by_cases h : i = j
  · subst h; rfl
  · simp [Ne.symm h]

/-- The dual `B`-module. -/
def dual : BModule n where
  carrier := Module.Dual ℂ M
  nil := M.dualNil
  torus := M.dualTorus
  torus_nil t X φ := by
    apply LinearMap.ext; intro v
    have h := M.torus_nil t⁻¹ (torusLie t X) v
    rw [torusLie_inv_torusLie] at h
    simp only [dualTorus_apply, dualNil_apply, h]
  weightDiagonal := by
    classical
    obtain ⟨ι, _, b, wt, hb⟩ := M.exists_weightBasis
    exact isWeightDiagonal_of_basis _ b.dualBasis (fun i => -wt i) (M.dualTorus_dualBasis b wt hb)

/-- The weight multiplicities of the dual are those of `M` at the negated weights. -/
theorem finrank_dual_weightSpace (μ : Weight n) :
    Module.finrank ℂ (M.dual.weightSpace μ) = Module.finrank ℂ (M.weightSpace (-μ)) := by
  classical
  obtain ⟨ι, _, b, wt, hb⟩ := M.exists_weightBasis
  change Module.finrank ℂ (torusWeightSpace M.dualTorus μ) = _
  rw [torusWeightSpace_finrank_of_eigenbasis M.dualTorus b.dualBasis (fun i => -wt i)
      (M.dualTorus_dualBasis b wt hb) μ,
    weightSpace, torusWeightSpace_finrank_of_eigenbasis M.torus b wt hb (-μ)]
  exact Fintype.card_congr (Equiv.subtypeEquivRight fun i => neg_eq_iff_eq_neg)

/-- If `M` has character `p` in the convention `Σ (dim M_μ) x^μ`, then the dual of `M` has
character `p` in the convention `Σ (dim M_μ) x^{-μ}` of `HasCharacter`. -/
theorem hasCharacter_dual_of_hasTorusCharacter {p : Polynomial n}
    (h : HasTorusCharacter M.torus p) : M.dual.HasCharacter (toLaurent p) := by
  intro μ
  rw [finrank_dual_weightSpace]
  exact h (-μ)

end Dual

/-! ### Tensor products -/

section Tensor

variable (M N : BModule n)

/-- The diagonal torus action on `M ⊗ N`. -/
def tensorTorus : DiagonalTorus n →* Module.End ℂ (M ⊗[ℂ] N) where
  toFun t := TensorProduct.map (M.torus t) (N.torus t)
  map_one' := by
    rw [map_one, map_one]
    exact TensorProduct.map_one
  map_mul' s t := by
    rw [map_mul, map_mul]
    exact TensorProduct.map_mul _ _ _ _

@[simp] theorem tensorTorus_tmul (t : DiagonalTorus n) (x : M) (y : N) :
    M.tensorTorus N t (x ⊗ₜ y) = M.torus t x ⊗ₜ N.torus t y := rfl

/-- The action `X ↦ X ⊗ 1 + 1 ⊗ X` of `𝔫⁺` on `M ⊗ N`. -/
def tensorNil : upperNilpotent n →ₗ⁅ℂ⁆ Module.End ℂ (M ⊗[ℂ] N) where
  toFun X := (M.nil X).rTensor N + (N.nil X).lTensor M
  map_add' X Y := by
    apply TensorProduct.ext'; intro x y
    simp; abel
  map_smul' c X := by
    apply TensorProduct.ext'; intro x y
    simp [TensorProduct.smul_tmul', smul_add]
  map_lie' {X Y} := by
    apply TensorProduct.ext'; intro x y
    simp [LieHom.map_lie, Ring.lie_def, Module.End.mul_apply]
    abel

@[simp] theorem tensorNil_tmul (X : upperNilpotent n) (x : M) (y : N) :
    M.tensorNil N X (x ⊗ₜ y) = M.nil X x ⊗ₜ y + x ⊗ₜ N.nil X y := rfl

theorem tensorTorus_basis {ι κ : Type*} (b : Module.Basis ι ℂ M) (wt : ι → Weight n)
    (hb : ∀ t i, M.torus t (b i) = integerWeightScalar (wt i) t • b i)
    (c : Module.Basis κ ℂ N) (wt' : κ → Weight n)
    (hc : ∀ t j, N.torus t (c j) = integerWeightScalar (wt' j) t • c j)
    (t : DiagonalTorus n) (x : ι × κ) :
    M.tensorTorus N t (b.tensorProduct c x) =
      integerWeightScalar (wt x.1 + wt' x.2) t • b.tensorProduct c x := by
  rw [Module.Basis.tensorProduct_apply, tensorTorus_tmul, hb, hc, integerWeightScalar_add,
    TensorProduct.smul_tmul_smul]

/-- The tensor product of two `B`-modules. -/
def tensor : BModule n where
  carrier := M ⊗[ℂ] N
  nil := M.tensorNil N
  torus := M.tensorTorus N
  torus_nil t X v := by
    have h : (M.tensorTorus N t).comp (M.tensorNil N X) =
        (M.tensorNil N (torusLie t X)).comp (M.tensorTorus N t) := by
      apply TensorProduct.ext'; intro x y
      simp [M.torus_nil, N.torus_nil]
    exact LinearMap.congr_fun h v
  weightDiagonal := by
    obtain ⟨ι, _, b, wt, hb⟩ := M.exists_weightBasis
    obtain ⟨κ, _, c, wt', hc⟩ := N.exists_weightBasis
    exact isWeightDiagonal_of_basis _ (b.tensorProduct c) (fun x => wt x.1 + wt' x.2)
      (M.tensorTorus_basis N b wt hb c wt' hc)

variable {M N}

/-- Characters are multiplicative on tensor products. -/
theorem HasCharacter.tensor {f g : Laurent n} (hM : M.HasCharacter f) (hN : N.HasCharacter g) :
    (M.tensor N).HasCharacter (f * g) := by
  obtain ⟨ι, _, b, wt, hb⟩ := M.exists_weightBasis
  obtain ⟨κ, _, c, wt', hc⟩ := N.exists_weightBasis
  rw [hM.unique (M.hasCharacter_of_basis b wt hb), hN.unique (N.hasCharacter_of_basis c wt' hc),
    ← labelledLaurent_prod]
  exact (M.tensor N).hasCharacter_of_basis (b.tensorProduct c) (fun x => wt x.1 + wt' x.2)
    (M.tensorTorus_basis N b wt hb c wt' hc)

end Tensor

/-! ### Twists by powers of the determinant -/

section Twist

variable (M : BModule n)

/-- The weight `k · (1, …, 1)`. -/
def constWeight (k : ℤ) : Weight n := fun _ => k

/-- The torus action twisted by the character `t ↦ (t₁ ⋯ tₙ)^k`. -/
def twistTorus (k : ℤ) : DiagonalTorus n →* Module.End ℂ M where
  toFun t := integerWeightScalar (constWeight k) t • M.torus t
  map_one' := by
    apply LinearMap.ext; intro v
    simp [integerWeightScalar]
  map_mul' s t := by
    apply LinearMap.ext; intro v
    simp only [integerWeightScalar_mul, map_mul, LinearMap.smul_apply, Module.End.mul_apply,
      map_smul, smul_smul]
    ring_nf

@[simp] theorem twistTorus_apply (k : ℤ) (t : DiagonalTorus n) (v : M) :
    M.twistTorus k t v = integerWeightScalar (constWeight k) t • M.torus t v := rfl

theorem torusWeightSpace_twistTorus (k : ℤ) (μ : Weight n) :
    torusWeightSpace (M.twistTorus k) μ = M.weightSpace (μ - constWeight k) := by
  ext v
  have hsplit : ∀ t, integerWeightScalar μ t =
      integerWeightScalar (constWeight k) t * integerWeightScalar (μ - constWeight k) t := by
    intro t
    rw [← integerWeightScalar_add, add_sub_cancel]
  constructor
  · intro hv t
    have h := hv t
    rw [twistTorus_apply, hsplit, mul_smul] at h
    exact smul_right_injective M (integerWeightScalar_ne_zero _ t) h
  · intro hv t
    rw [twistTorus_apply, hv t, hsplit, mul_smul]

/-- The twist of `M` by the `k`-th power of the determinant. -/
def twist (k : ℤ) : BModule n where
  carrier := M
  nil := M.nil
  torus := M.twistTorus k
  torus_nil t X v := by
    simp only [twistTorus_apply, map_smul, M.torus_nil]
  weightDiagonal := by
    refine eq_top_iff.mpr ?_
    rw [← M.weightDiagonal]
    refine iSup_le fun ν => ?_
    have : torusWeightSpace M.torus ν =
        torusWeightSpace (M.twistTorus k) (ν + constWeight k) := by
      rw [torusWeightSpace_twistTorus, add_sub_cancel_right]
      rfl
    rw [this]
    exact le_iSup (torusWeightSpace (M.twistTorus k)) _

theorem finrank_twist_weightSpace (k : ℤ) (μ : Weight n) :
    Module.finrank ℂ ((M.twist k).weightSpace μ) =
      Module.finrank ℂ (M.weightSpace (μ - constWeight k)) := by
  change Module.finrank ℂ (torusWeightSpace (M.twistTorus k) μ) = _
  rw [torusWeightSpace_twistTorus]

variable {M}

/-- Twisting by `det^k` multiplies the character by `x^{-k·(1,…,1)}`. -/
theorem HasCharacter.twist {f : Laurent n} (hM : M.HasCharacter f) (k : ℤ) :
    (M.twist k).HasCharacter (AddMonoidAlgebra.single (-constWeight k) 1 * f) := by
  intro μ
  rw [finrank_twist_weightSpace, hM]
  have h : -μ = -constWeight k + -(μ - constWeight k) := by abel
  rw [h, laurent_coefficient_shift]

end Twist

end BModule

end

end Demazure.BModules
