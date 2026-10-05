import Schubert.GLRep.Borel.Comodule
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.UpperTriangular.Basic
import TauCeti.Algebra.Coalgebra.Comodule.Corestrict
import TauCeti.Algebra.Coalgebra.Subcomodule.Induced

/-!
# Comodules over `𝒪(B)`

Tau Ceti's coordinate Hopf algebra of the upper-triangular subgroup scheme,
`𝒪(B) = 𝒪(GL_n)/(x_ij : i > j)` (`TauCeti.GeneralLinear.UpperTriangular.coordinateHopfAlgebra`,
here `GLRep.borelHopf`), and its points `b ∈ B(K)` (`GLRep.borelPoint`):

* over an infinite field the points separate `𝒪(B)` (`GLRep.borelHopf_ext`): a regular function on
  `GL_n` vanishing on `B(K)` lies in the ideal of the coordinates below the diagonal
  (`GLRep.mem_borelIdeal_of_forall`);
* the restriction to `B` of a rational representation of `GL_n(K)` is a comodule over `𝒪(B)`
  whose point action is `ρ|_B` (`GLRep.borelComodule`, `GLRep.contract_borelComodule`);
* a subspace stable under `B(K)` is a subcomodule, whose induced point action is the restricted
  action (`GLRep.borelSubcomodule`, `GLRep.contract_borelSubcomodule`); this applies to the
  Demazure modules `D_S ⊆ V(λ)`.

-/

namespace GLRep

open Module TauCeti TauCeti.GeneralLinear TensorProduct WithConv

noncomputable section

variable {K : Type*} [Field K] {n : ℕ}

/-! ### The coordinate Hopf algebra of `B` and its points -/

/-- The coordinate Hopf algebra `𝒪(B)` (Tau Ceti's upper-triangular coordinate Hopf algebra), over
a commutative ring. -/
abbrev borelHopf (K : Type*) [CommRing K] (n : ℕ) : CommHopfAlgCat K :=
  UpperTriangular.coordinateHopfAlgebra K n

variable (K n) in
/-- The ideal of the coordinates below the diagonal in `𝒪(GL_n)`. -/
abbrev borelIdeal : Ideal (glHopf K n) := (UpperTriangular.definingHopfIdeal K n).toIdeal

theorem glPoint_mem_ker (b : borel K n) :
    borelIdeal K n ≤ RingHom.ker (glPoint (b : GL (Fin n) K)).toRingHom :=
  UpperTriangular.definingHopfIdeal_toIdeal_le_ker K n (glPoint (b : GL (Fin n) K))
    fun i j hji => by rw [glPoint_X]; exact b.2 hji

/-- The point `b ∈ B(K)` as an algebra map `𝒪(B) → K`. -/
def borelPoint (b : borel K n) : borelHopf K n →ₐ[K] K :=
  Ideal.Quotient.liftₐ (borelIdeal K n) (glPoint (b : GL (Fin n) K))
    fun _ hh => glPoint_mem_ker b hh

theorem borelPoint_mk (b : borel K n) (h : glHopf K n) :
    borelPoint b (Ideal.Quotient.mk (borelIdeal K n) h) = glPoint (b : GL (Fin n) K) h :=
  rfl

/-! ### Point separation -/

section Separation

open MvPolynomial

variable [Infinite K]

/-- Setting the coordinates below the diagonal to zero. -/
def upperPartPoly : MvPolynomial (Fin n × Fin n) K →ₐ[K] MvPolynomial (Fin n × Fin n) K :=
  aeval fun ij => if ij.2 < ij.1 then 0 else X ij

variable (K n) in
/-- The ideal of the polynomial coordinates below the diagonal. -/
def belowIdeal : Ideal (MvPolynomial (Fin n × Fin n) K) :=
  Ideal.span (Set.range fun ij : {ij : Fin n × Fin n // ij.2 < ij.1} => X ij.1)

omit [Infinite K] in
theorem eval_upperPartPoly (x : Fin n × Fin n → K) (p : MvPolynomial (Fin n × Fin n) K) :
    eval x (upperPartPoly p) = eval (fun ij => if ij.2 < ij.1 then 0 else x ij) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [upperPartPoly]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]
  | mul_X p ij hp =>
    rw [map_mul, map_mul, hp, map_mul, eval_X, upperPartPoly, aeval_X]
    split_ifs <;> simp

omit [Infinite K] in
theorem sub_upperPartPoly_mem (p : MvPolynomial (Fin n × Fin n) K) :
    p - upperPartPoly p ∈ belowIdeal K n := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [upperPartPoly]
  | add p q hp hq =>
    rw [map_add, add_sub_add_comm]
    exact add_mem hp hq
  | mul_X p ij hp =>
    have hX : X ij - upperPartPoly (X ij) ∈ belowIdeal K n := by
      rw [upperPartPoly, aeval_X]
      split_ifs with h
      · rw [sub_zero]
        exact Ideal.subset_span ⟨⟨ij, h⟩, rfl⟩
      · rw [sub_self]
        exact zero_mem _
    have : p * X ij - upperPartPoly (p * X ij) =
        (p - upperPartPoly p) * X ij + upperPartPoly p * (X ij - upperPartPoly (X ij)) := by
      rw [map_mul]
      ring
    rw [this]
    exact add_mem (Ideal.mul_mem_right _ _ hp) (Ideal.mul_mem_left _ _ hX)

/-- A polynomial vanishing on the invertible upper-triangular matrices lies in the ideal of the
coordinates below the diagonal. -/
theorem mem_belowIdeal_of_forall {p : MvPolynomial (Fin n × Fin n) K}
    (hp : ∀ g : GL (Fin n) K, g ∈ borel K n →
      eval (fun ij => (g : Matrix (Fin n) (Fin n) K) ij.1 ij.2) p = 0) :
    p ∈ belowIdeal K n := by
  have hD : (∏ i : Fin n, X (i, i) : MvPolynomial (Fin n × Fin n) K) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => X_ne_zero _
  have hzero : upperPartPoly p * ∏ i : Fin n, X (i, i) = 0 := by
    refine MvPolynomial.funext fun x => ?_
    rw [map_mul, map_zero, map_prod]
    simp only [eval_X]
    by_cases hx : ∀ i, x (i, i) ≠ 0
    · let M : Matrix (Fin n) (Fin n) K := Matrix.of fun i j => if j < i then 0 else x (i, j)
      have hM : M.IsUpperTriangular := fun i j hij => by
        simp only [M, Matrix.of_apply]
        exact ite_eq_left_iff.mpr fun h => absurd hij h
      have hdet : M.det ≠ 0 := by
        rw [Matrix.det_of_isUpperTriangular hM]
        exact Finset.prod_ne_zero_iff.mpr fun i _ => by simpa [M] using hx i
      let g : GL (Fin n) K := Matrix.GeneralLinearGroup.mkOfDetNeZero M hdet
      have hg := hp g hM
      have hfun : (fun ij : Fin n × Fin n => if ij.2 < ij.1 then (0 : K) else x ij) =
          fun ij => (g : Matrix (Fin n) (Fin n) K) ij.1 ij.2 := rfl
      have heval : eval x (upperPartPoly p) =
          eval (fun ij => (g : Matrix (Fin n) (Fin n) K) ij.1 ij.2) p := by
        rw [eval_upperPartPoly, hfun]
      rw [heval, hg, zero_mul]
    · obtain ⟨i, hi⟩ := not_forall.mp hx
      rw [ne_eq, not_not] at hi
      rw [Finset.prod_eq_zero (Finset.mem_univ i) hi, mul_zero]
  have hu : upperPartPoly p = 0 := (mul_eq_zero.mp hzero).resolve_right hD
  have := sub_upperPartPoly_mem p
  rwa [hu, sub_zero] at this

/-- **A regular function on `GL_n` vanishing on `B(K)` lies in the ideal of the coordinates below
the diagonal.** -/
theorem mem_borelIdeal_of_forall {h : glHopf K n}
    (hh : ∀ b : borel K n, glPoint (b : GL (Fin n) K) h = 0) : h ∈ borelIdeal K n := by
  let e := coordinateHopfAlgebraAlgEquiv K n
  set f : GLCoord K n := e.symm h with hf
  obtain ⟨m, a, hz⟩ := IsLocalization.Away.surj (genericDet K n) f
  have ha : a ∈ belowIdeal K n := mem_belowIdeal_of_forall fun g hg => by
    have := congrArg (glEval g) hz
    have h0 : glEval g f = 0 := hh ⟨g, hg⟩
    rw [map_mul, h0, zero_mul, glEval_algebraMap] at this
    rw [← coe_aeval_eq_eval]
    exact this.symm
  have hfa : f = algebraMap (MvPolynomial (Fin n × Fin n) K) (GLCoord K n) a *
      glDetInv K n ^ m := by
    rw [← hz, mul_assoc, ← mul_pow, algebraMap_genericDet_mul_glDetInv, one_pow, mul_one]
  have hJ : ∀ p ∈ belowIdeal K n,
      e (algebraMap (MvPolynomial (Fin n × Fin n) K) (GLCoord K n) p) ∈ borelIdeal K n := by
    intro p hp
    have hle : belowIdeal K n ≤ (borelIdeal K n).comap
        ((e : GLCoord K n →ₐ[K] glHopf K n).toRingHom.comp
          (algebraMap (MvPolynomial (Fin n × Fin n) K) (GLCoord K n))) := by
      rw [belowIdeal, Ideal.span_le]
      rintro _ ⟨⟨ij, hij⟩, rfl⟩
      rw [SetLike.mem_coe, Ideal.mem_comap]
      show _ ∈ (UpperTriangular.definingHopfIdeal K n).toIdeal
      rw [UpperTriangular.definingHopfIdeal_toIdeal]
      exact Ideal.subset_span ⟨ij.1, ij.2, hij, rfl⟩
    exact hle hp
  have : h = e f := (e.apply_symm_apply h).symm
  rw [this, hfa, map_mul]
  exact Ideal.mul_mem_right _ _ (hJ a ha)

/-- **The points of `B(K)` separate `𝒪(B)`** (`K` infinite). -/
theorem borelHopf_ext {x y : borelHopf K n} (h : ∀ b : borel K n, borelPoint b x = borelPoint b y) :
    x = y := by
  rw [← sub_eq_zero]
  obtain ⟨g, hg⟩ := Ideal.Quotient.mk_surjective (I := borelIdeal K n) (x - y)
  change Ideal.Quotient.mk (borelIdeal K n) g = x - y at hg
  rw [← hg, Ideal.Quotient.eq_zero_iff_mem]
  refine mem_borelIdeal_of_forall fun b => ?_
  have := h b
  rw [← sub_eq_zero, ← map_sub, ← hg] at this
  exact this

end Separation

/-! ### Contractions with points -/

section Contract

variable {C : Type*} [CommRing C] [Algebra K C]
variable {M N : Type*} [AddCommMonoid M] [Module K M] [AddCommMonoid N] [Module K N]

theorem rid_lTensor_rTensor (x : C →ₐ[K] K) (f : M →ₗ[K] N) (t : M ⊗[K] C) :
    TensorProduct.rid K N (x.toLinearMap.lTensor N (f.rTensor C t)) =
      f (TensorProduct.rid K M (x.toLinearMap.lTensor M t)) := by
  induction t with
  | tmul m c => simp
  | add s t hs ht => simp only [map_add, hs, ht]

theorem rid_lTensor_lTensor {D : Type*} [CommRing D] [Algebra K D] (x : D →ₐ[K] K)
    (f : C →ₗ[K] D) (t : M ⊗[K] C) :
    TensorProduct.rid K M (x.toLinearMap.lTensor M (f.lTensor M t)) =
      TensorProduct.rid K M ((x.toLinearMap ∘ₗ f).lTensor M t) := by
  rw [LinearMap.lTensor_comp, LinearMap.comp_apply]

/-- **Point separation in `M ⊗ C`** for a family of points separating `C` and finite-dimensional
`M`. -/
theorem tensor_ext_of_points {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {ι : Type*} (pts : ι → C →ₐ[K] K)
    (hsep : ∀ x y : C, (∀ i, pts i x = pts i y) → x = y) {t t' : V ⊗[K] C}
    (h : ∀ i, TensorProduct.rid K V ((pts i).toLinearMap.lTensor V t) =
      TensorProduct.rid K V ((pts i).toLinearMap.lTensor V t')) : t = t' := by
  classical
  let b := Module.finBasis K V
  apply (TensorProduct.equivFinsuppOfBasisLeft b).injective
  ext j
  refine hsep _ _ fun i => ?_
  have key : ∀ s : V ⊗[K] C, pts i (TensorProduct.equivFinsuppOfBasisLeft b s j) =
      b.coord j (TensorProduct.rid K V ((pts i).toLinearMap.lTensor V s)) := by
    intro s
    rw [TensorProduct.equivFinsuppOfBasisLeft_apply]
    induction s with
    | tmul m c => simp [mul_comm]
    | add s s' hs hs' => simp only [map_add, hs, hs']
  rw [key, key, h i]

end Contract

/-! ### Rational representations of `GL_n` as `𝒪(B)`-comodules -/

section Comodules

variable {W : Type*} [AddCommGroup W] [Module K W] {ρ : Representation K (GL (Fin n) K) W}

variable (K n) in
/-- The restriction `𝒪(GL_n) → 𝒪(B)` as a coalgebra map. -/
abbrev toBorelHopf : glHopf K n →ₗc[K] borelHopf K n :=
  (UpperTriangular.coordinateMap K n).hom.toCoalgHom

theorem borelPoint_toBorelHopf (b : borel K n) (h : glHopf K n) :
    borelPoint b (toBorelHopf K n h) = glPoint (b : GL (Fin n) K) h := by
  change borelPoint b ((UpperTriangular.coordinateMap K n).hom h) = _
  rw [UpperTriangular.coordinateMap_apply]
  rfl

variable [Infinite K]

/-- **The restriction to `B` of a rational representation of `GL_n(K)`, as a comodule over
`𝒪(B)`**: the corestriction of `GLRep.rationalComodule`. -/
@[instance_reducible]
def borelComodule (hρ : IsRationalRep ρ) : TauCeti.Comodule K (borelHopf K n) W :=
  letI := rationalComodule hρ
  TauCeti.Comodule.Corestrict (R := K) (C := glHopf K n) (D := borelHopf K n) (M := W)
    (toBorelHopf K n)

/-- **The point action of `borelComodule` is `ρ|_B`.** -/
theorem contract_borelComodule (hρ : IsRationalRep ρ) (b : borel K n) :
    contract (borelPoint b) (borelComodule hρ).coact = ρ b := by
  rw [← contract_rationalComodule hρ (b : GL (Fin n) K)]
  refine LinearMap.ext fun w => ?_
  let _ := rationalComodule hρ
  change TensorProduct.rid K W ((borelPoint b).toLinearMap.lTensor W
      (TensorProduct.map LinearMap.id (toBorelHopf K n).toLinearMap
        (TauCeti.Comodule.coact (R := K) (C := glHopf K n) (M := W) w))) = _
  rw [← LinearMap.lTensor_def, rid_lTensor_lTensor]
  congr 2

/-- **A subspace stable under `B(K)` is a subcomodule.** -/
def borelSubcomodule {M : Type*} [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    [TauCeti.Comodule K (borelHopf K n) M] (U : Submodule K M)
    (hU : ∀ b : borel K n, ∀ u ∈ U,
      contract (borelPoint b)
        (TauCeti.Comodule.coact (R := K) (C := borelHopf K n) (M := M)) u ∈ U) :
    Subcomodule K (borelHopf K n) M :=
  Subcomodule.ofSubmodule U fun m hm => by
    have hex := _root_.rTensor_exact (borelHopf K n) (LinearMap.exact_subtype_mkQ U)
      U.mkQ_surjective
    refine (hex _).mp (tensor_ext_of_points borelPoint (fun x y h => borelHopf_ext h)
      fun b => ?_)
    rw [rid_lTensor_rTensor, map_zero, map_zero, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    exact hU b m hm

omit [Infinite K] in
/-- The point action on a subcomodule is the restriction of the ambient point action. -/
theorem coe_contract_subcomodule {M : Type*} [AddCommGroup M] [Module K M]
    [TauCeti.Comodule K (borelHopf K n) M] (N : Subcomodule K (borelHopf K n) M)
    (x : borelHopf K n →ₐ[K] K) (u : N) :
    ((contract x (TauCeti.Comodule.coact (R := K) (C := borelHopf K n) (M := N)) u : N) : M) =
      contract x (TauCeti.Comodule.coact (R := K) (C := borelHopf K n) (M := M)) u := by
  change SMulMemClass.subtype N (TensorProduct.rid K N (x.toLinearMap.lTensor N
      (TauCeti.Comodule.coact (R := K) (C := borelHopf K n) (M := N) u))) = _
  rw [← rid_lTensor_rTensor, Subcomodule.subtype_rTensor_coact]
  rfl

/-- **The point action on `borelSubcomodule U` is the restriction to `U`.** -/
theorem contract_borelSubcomodule {M : Type*} [AddCommGroup M] [Module K M]
    [FiniteDimensional K M] [TauCeti.Comodule K (borelHopf K n) M] (U : Submodule K M)
    (hU : ∀ b : borel K n, ∀ u ∈ U,
      contract (borelPoint b)
        (TauCeti.Comodule.coact (R := K) (C := borelHopf K n) (M := M)) u ∈ U)
    (b : borel K n) (u : borelSubcomodule U hU) :
    ((contract (borelPoint b) (TauCeti.Comodule.coact (R := K) (C := borelHopf K n)
      (M := borelSubcomodule U hU)) u : borelSubcomodule U hU) : M) =
      contract (borelPoint b) (TauCeti.Comodule.coact (R := K) (C := borelHopf K n) (M := M)) u :=
  coe_contract_subcomodule _ _ u

/-- **A `B`-stable subspace of a rational representation of `GL_n(K)` is a subcomodule of its
`𝒪(B)`-comodule** (for example the Demazure modules `D_S ⊆ V(λ)`). -/
def borelSubcomoduleOfStable (hρ : IsRationalRep ρ) (U : Submodule K W)
    (hU : ∀ b : borel K n, ∀ u ∈ U, ρ b u ∈ U) :
    letI := borelComodule hρ
    Subcomodule K (borelHopf K n) W :=
  letI := borelComodule hρ
  have := hρ.finiteDimensional
  borelSubcomodule U fun b u hu => by
    rw [contract_borelComodule hρ b]
    exact hU b u hu

/-- The point action on `borelSubcomoduleOfStable` is `ρ` restricted to `U`. -/
theorem contract_borelSubcomoduleOfStable (hρ : IsRationalRep ρ) (U : Submodule K W)
    (hU : ∀ b : borel K n, ∀ u ∈ U, ρ b u ∈ U) (b : borel K n)
    (u : (letI := borelComodule hρ; borelSubcomoduleOfStable hρ U hU)) :
    letI := borelComodule hρ
    ((contract (borelPoint b) (TauCeti.Comodule.coact (R := K) (C := borelHopf K n)
      (M := borelSubcomoduleOfStable hρ U hU)) u : borelSubcomoduleOfStable hρ U hU) : W) =
      ρ b u := by
  let _ := borelComodule hρ
  rw [coe_contract_subcomodule, contract_borelComodule]

end Comodules

end

end GLRep
