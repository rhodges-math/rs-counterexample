import Schubert.FlagVarieties.Schubert.GlobalSections
import Schubert.FlagVarieties.Normality.OrbitIdealComparison

/-!
# `Γ(X_w, 𝒪) = K` for Schubert varieties

The statement `Γ(X_w, 𝒪) = K` in ring form (`FlagVarieties.PointModel.GlobalSectionsConstant K w`,
and `FlagVarieties.PointModel.Complex.GlobalSectionsConstant w` over `ℂ`) holds over every field of
characteristic `0` (`FlagVarieties.globalSectionsConstant_of_charZero`,
`FlagVarieties.globalSectionsConstant_complex`).

A function `t` on `GLₙ` that is invariant under right translation by `B(K)` at the `K`-points of
`⋃_{v ≤ w} B v̇ B` is invariant on the scheme `π⁻¹(X_w)`: for every `b ∈ B(K)`, evaluating its
defect `ρ(t) - t ⊗ 1 ∈ 𝒪(π⁻¹X_w) ⊗ 𝒪(B)` at `b` gives the class of `t(· b) - t`, which vanishes
(`FlagVarieties.tensor_eq_zero_of_forall_borelPoint`: `B(K)` is dense in `B`). Then
`FlagVarieties.exists_sub_algebraMap_mem_schubertOrbitIdeal` applies.
-/

noncomputable section

namespace FlagVarieties

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

universe u

variable {K : Type u} [Field K] {n : ℕ}

/-- Evaluation of the second factor at `b ∈ B(K)`: `V ⊗ 𝒪(B) → V`. -/
def evalBorelPoint (V : Type*) [AddCommGroup V] [Module K V] (b : Matrix (Fin n) (Fin n) K)
    (hb : IsUnit b.det) (hup : b.BlockTriangular id) : V ⊗[K] BorelCoord K n →ₗ[K] V :=
  (TensorProduct.rid K V).toLinearMap ∘ₗ
    LinearMap.lTensor V (borelPointOfMatrix K b hb hup).toLinearMap

theorem evalBorelPoint_tmul {V : Type*} [AddCommGroup V] [Module K V]
    (b : Matrix (Fin n) (Fin n) K) (hb : IsUnit b.det) (hup : b.BlockTriangular id) (v : V)
    (β : BorelCoord K n) :
    evalBorelPoint V b hb hup (v ⊗ₜ β) = borelPointOfMatrix K b hb hup β • v := by
  simp [evalBorelPoint]

/-- **`V ⊗ 𝒪(B)` embeds into the `V`-valued functions on `B(K)`** (`K` infinite). -/
theorem tensor_eq_zero_of_forall_borelPoint [Infinite K] {V : Type*} [AddCommGroup V] [Module K V]
    (x : V ⊗[K] BorelCoord K n)
    (hx : ∀ (b : Matrix (Fin n) (Fin n) K) (hb : IsUnit b.det) (hup : b.BlockTriangular id),
      evalBorelPoint V b hb hup x = 0) :
    x = 0 := by
  classical
  let 𝒞 := Module.Free.chooseBasis K V
  let e := TensorProduct.equivFinsuppOfBasisLeft (N := BorelCoord K n) 𝒞
  have hsum : x = (e x).sum fun i β => 𝒞 i ⊗ₜ β := by
    rw [← TensorProduct.equivFinsuppOfBasisLeft_symm_apply, LinearEquiv.symm_apply_apply]
  suffices he : e x = 0 by rw [hsum, he, Finsupp.sum_zero_index]
  ext i
  rw [Finsupp.zero_apply]
  apply borelCoord_eq_zero_of_forall
  intro b hb hup
  set p := borelPointOfMatrix K b hb hup
  have h := hx b hb hup
  rw [hsum, map_finsuppSum] at h
  simp only [evalBorelPoint_tmul] at h
  have h2 : Finsupp.linearCombination K 𝒞 ((e x).mapRange p (map_zero p)) = 0 := by
    rw [Finsupp.linearCombination_apply,
      Finsupp.sum_mapRange_index (fun i => by rw [zero_smul])]
    exact h
  have h3 := congrArg (fun v => 𝒞.repr v i) h2
  simpa [Module.Basis.repr_linearCombination, Finsupp.mapRange_apply] using h3

variable (K n)

/-- Right translation by `b ∈ B(K)`: `f ↦ f(· b)`. -/
def rightTransl (b : Matrix (Fin n) (Fin n) K) (hb : IsUnit b.det) (hup : b.BlockTriangular id) :
    GLCoord K n →ₐ[K] GLCoord K n :=
  (Algebra.TensorProduct.lift (AlgHom.id K (GLCoord K n))
    ((Algebra.ofId K (GLCoord K n)).comp (borelPointOfMatrix K b hb hup))
    fun _ _ => Commute.all _ _).comp (rightCoaction K n)

variable {K n}

/-- Evaluating the coaction at `b ∈ B(K)` is right translation by `b`. -/
theorem evalBorelPoint_rightCoactionMod (J : Ideal (GLCoord K n)) (b : Matrix (Fin n) (Fin n) K)
    (hb : IsUnit b.det) (hup : b.BlockTriangular id) (f : GLCoord K n) :
    evalBorelPoint _ b hb hup (rightCoactionMod K n J f) =
      Ideal.Quotient.mk J (rightTransl K n b hb hup f) := by
  rw [rightCoactionMod, rightTransl, AlgHom.comp_apply, AlgHom.comp_apply]
  generalize rightCoaction K n f = y
  induction y using TensorProduct.inductionOn with
  | tmul x β =>
    simp only [Algebra.TensorProduct.map_tmul, evalBorelPoint_tmul,
      Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply, AlgHom.id_apply,
      Ideal.Quotient.mkₐ_eq_mk, map_mul]
    rw [mul_comm, Algebra.ofId_apply, Ideal.Quotient.mk_algebraMap, ← Algebra.smul_def]
  | add x y hx hy =>
    rw [map_add, LinearMap.map_add, hx, hy, map_add, map_add]

/-- The `K`-point of `GLₙ` of an upper triangular matrix with invertible determinant. -/
def borelGL (b : Matrix (Fin n) (Fin n) K) (hb : IsUnit b.det) : GL (Fin n) K :=
  ((Matrix.isUnit_iff_isUnit_det b).mpr hb).unit

theorem glEval_rightTransl (g : GL (Fin n) K) (b : Matrix (Fin n) (Fin n) K) (hb : IsUnit b.det)
    (hup : b.BlockTriangular id) (t : GLCoord K n) :
    GLRep.glEval g (rightTransl K n b hb hup t) =
      GLRep.glEval (g * borelGL b hb) t := by
  have e : (GLRep.glEval g).comp (rightTransl K n b hb hup) =
      GLRep.glEval (g * borelGL b hb) := by
    apply genericMatrix_algHom_ext
    ext i j
    have hc := congrFun (congrFun (map_rightCoaction_genericMatrix K n) i) j
    simp only [Matrix.map_apply, Matrix.mul_apply] at hc
    rw [Matrix.map_apply, Matrix.map_apply, AlgHom.comp_apply, rightTransl, AlgHom.comp_apply, hc,
      PointModel.glEval_genericMatrix, Units.val_mul, Matrix.mul_apply, map_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hbk := congrFun (congrFun (borelMatrix_map_borelPointOfMatrix K b hb hup) k) j
    rw [Matrix.map_apply] at hbk
    simp only [Algebra.TensorProduct.lift_tmul, map_mul, Algebra.TensorProduct.includeLeft_apply,
      Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      mul_one, AlgHom.comp_apply, AlgHom.id_apply, hbk, Algebra.ofId_apply,
      AlgHom.commutes, PointModel.glEval_genericMatrix, Algebra.algebraMap_self,
      RingHom.id_apply]
    rfl
  exact congrArg (fun φ : GLCoord K n →ₐ[K] K => φ t) e

/-- **Pointwise `B(K)`-invariance on `⋃_{v ≤ w} B v̇ B` is `B`-invariance on `π⁻¹(X_w)`**
(characteristic `0`). -/
theorem semiInvariantDefect_eq_zero_of_isSemiInvOn [CharZero K] (w : Equiv.Perm (Fin n))
    (t : GLCoord K n)
    (ht : PointModel.IsSemiInvOn
      (PointModel.orbitSet K (PointModel.lowerSet w)) 0 t) :
    semiInvariantDefect K n (schubertOrbitIdeal K n w) 0 t = 0 := by
  have : Infinite K := Infinite.of_injective (Nat.cast : ℕ → K) Nat.cast_injective
  apply tensor_eq_zero_of_forall_borelPoint
  intro b hb hup
  rw [semiInvariantDefect_apply, LinearMap.map_sub, evalBorelPoint_rightCoactionMod,
    borelCharacterUnit_zero, inv_one, Units.val_one, evalBorelPoint_tmul, map_one, one_smul,
    ← map_sub, Ideal.Quotient.eq_zero_iff_mem,
    PointModel.schubertOrbitIdeal_eq_orbitIdeal_lowerSet, PointModel.mem_orbitIdeal]
  intro g hg
  have hB : PointModel.IsBorel (borelGL b hb) := by
    unfold PointModel.IsBorel
    rw [borelGL, IsUnit.unit_spec]
    exact hup
  rw [map_sub, glEval_rightTransl, ht g hg _ hB]
  simp [PointModel.borelCharValue]

/-- **`Γ(X_w, 𝒪) = K`** (`PointModel.GlobalSectionsConstant K w`), over every field of
characteristic `0`. -/
theorem globalSectionsConstant_of_charZero (K : Type u) [Field K] [CharZero K] (n : ℕ) :
    ∀ w : Equiv.Perm (Fin n), PointModel.GlobalSectionsConstant K w := by
  intro w t ht
  rw [← PointModel.schubertOrbitIdeal_eq_orbitIdeal_lowerSet]
  exact exists_sub_algebraMap_mem_schubertOrbitIdeal K n w t
      (semiInvariantDefect_eq_zero_of_isSemiInvOn w t ht)

/-- **`Γ(X_w, 𝒪) = ℂ`** (`FlagVarieties.PointModel.Complex.GlobalSectionsConstant`). -/
theorem globalSectionsConstant_complex (n : ℕ) :
    ∀ w : Equiv.Perm (Fin n), PointModel.Complex.GlobalSectionsConstant w :=
  globalSectionsConstant_of_charZero ℂ n

end FlagVarieties
