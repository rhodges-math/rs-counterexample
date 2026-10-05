import Schubert.GLRep.Borel.BorelRational
import Schubert.GLRep.Borel.BorelLieDual
import TauCeti.Algebra.Coalgebra.Comodule.Dual
import TauCeti.Algebra.HopfAlgebra.Basic

/-!
# Duals of comodules over `𝒪(B)`

The antipode of `𝒪(B)` corresponds to inversion on points: `b(S c) = b⁻¹(c)`
(`GLRep.borelPoint_antipode`). Hence the dual of a finite-dimensional `𝒪(B)`-comodule (Tau Ceti's
`Comodule.dual`) has as point action the dual representation `b ↦ (ρ(b⁻¹))ᵗ`
(`GLRep.borelComoduleRep_dual`), and over an infinite field the comodule of the dual of a rational
representation of `B(K)` is the dual comodule (`GLRep.IsRationalBorelRep.comodule_dual`).
-/

namespace GLRep

open Module TauCeti TauCeti.GeneralLinear TensorProduct

noncomputable section

variable {K : Type*} [Field K] {n : ℕ}

/-- **The antipode is inversion on points**: `b(S c) = b⁻¹(c)`. -/
theorem borelPoint_antipode (b : borel K n) (c : borelHopf K n) :
    borelPoint b (HopfAlgebra.antipode K c) = borelPoint b⁻¹ c := by
  have h : (borelPoint b).comp ((UpperTriangular.coordinateMap K n).hom.toAlgHom.comp
      (HopfAlgebra.antipodeAlgHom K (glHopf K n))) =
      (borelPoint b⁻¹).comp (UpperTriangular.coordinateMap K n).hom.toAlgHom :=
    coordinateHopfAlgebra_algHom_ext K n fun i j => by
      rw [← genericMatrix_apply, AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.comp_apply,
        HopfAlgebra.antipodeAlgHom_apply]
      change borelPoint b (toBorelHopf K n (HopfAlgebra.antipode K (genericMatrix K n i j))) =
        borelPoint b⁻¹ (toBorelHopf K n (genericMatrix K n i j))
      rw [borelPoint_toBorelHopf, glPoint_antipode, borelPoint_genericMatrix]
      rfl
  obtain ⟨x, rfl⟩ := toBorelHopf_surjective (K := K) (n := n) c
  have e : HopfAlgebra.antipode K (toBorelHopf K n x) =
      toBorelHopf K n (HopfAlgebra.antipode K x) :=
    (BialgHomClass.map_antipode (UpperTriangular.coordinateMap K n).hom x).symm
  rw [e]
  exact DFunLike.congr_fun h x

section Dual

variable {M : Type*} [AddCommGroup M] [Module K M] [FiniteDimensional K M]
variable [TauCeti.Comodule K (borelHopf K n) M]

omit [FiniteDimensional K M] [TauCeti.Comodule K (borelHopf K n) M] in
theorem rid_lTensor_apply_dual (x : borelHopf K n →ₐ[K] K)
    (t : Module.Dual K M ⊗[K] borelHopf K n) (m : M) :
    TensorProduct.rid K (Module.Dual K M) (x.toLinearMap.lTensor _ t) m =
      x (dualTensorHom K M (borelHopf K n) t m) := by
  induction t with
  | tmul φ c => simp [mul_comm]
  | add s t hs ht => rw [map_add, map_add, LinearMap.add_apply, hs, ht, map_add,
      LinearMap.add_apply, map_add]

omit [FiniteDimensional K M] in
theorem borelPoint_matrixCoefficient (x : borelHopf K n →ₐ[K] K) (φ : Module.Dual K M) (m : M) :
    x (Comodule.matrixCoefficient (R := K) (C := borelHopf K n) φ m) =
      φ (contract x (TauCeti.Comodule.coact (R := K) (C := borelHopf K n) (M := M)) m) := by
  rw [Comodule.matrixCoefficient_def]
  change x (TensorProduct.lid K _ (TensorProduct.map φ LinearMap.id
    (TauCeti.Comodule.coact (R := K) (C := borelHopf K n) (M := M) m))) =
      φ (TensorProduct.rid K M (x.toLinearMap.lTensor M
        (TauCeti.Comodule.coact (R := K) (C := borelHopf K n) (M := M) m)))
  induction (TauCeti.Comodule.coact (R := K) (C := borelHopf K n) (M := M) m) with
  | tmul m' c => simp [mul_comm]
  | add s t hs ht => rw [map_add, map_add, map_add, hs, ht, map_add, map_add, map_add]

/-- **The point action of the dual comodule is the dual representation.** -/
theorem borelComoduleRep_dual :
    (letI := Comodule.dual (R := K) (H := borelHopf K n) (M := M)
     borelComoduleRep K n (Module.Dual K M)) = (borelComoduleRep K n M).dual := by
  let _ := Comodule.dual (R := K) (H := borelHopf K n) (M := M)
  refine MonoidHom.ext fun b => LinearMap.ext fun φ => LinearMap.ext fun m => ?_
  rw [borelComoduleRep_apply, Representation.dual_apply, Module.Dual.transpose_apply,
    LinearMap.comp_apply, borelComoduleRep_apply, ← borelPoint_matrixCoefficient,
    ← borelPoint_antipode, ← Comodule.dualTensorHom_dualCoact_apply, ← rid_lTensor_apply_dual]
  rfl

end Dual

variable [Infinite K]
variable {W : Type*} [AddCommGroup W] [Module K W] {ρ : Representation K (borel K n) W}

/-- **The comodule of the dual representation is the dual comodule.** -/
theorem IsRationalBorelRep.comodule_dual (hρ : IsRationalBorelRep ρ) :
    hρ.dual.comodule =
      (letI := hρ.comodule
       letI := hρ.finiteDimensional
       Comodule.dual (R := K) (H := borelHopf K n) (M := W)) := by
  let _ := hρ.comodule
  have _ := hρ.finiteDimensional
  refine borelComodule_ext fun b => ?_
  rw [hρ.dual.contract_comodule]
  have h := DFunLike.congr_fun (borelComoduleRep_dual (K := K) (n := n) (M := W)) b
  rw [hρ.borelComoduleRep_comodule] at h
  exact h.symm

end

end GLRep
