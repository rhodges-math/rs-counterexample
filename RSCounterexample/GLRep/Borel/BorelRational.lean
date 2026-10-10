import RSCounterexample.GLRep.Borel.BorelComodule

/-!
# Rational representations of `B` are comodules over `𝒪(B)`

Over an infinite field `K`, the points `b ∈ B(K)` of Tau Ceti's coordinate Hopf algebra
`𝒪(B) = GLRep.borelHopf K n` form a submonoid of the convolution monoid
(`GLRep.borelPointHom`), so every `𝒪(B)`-comodule is a representation of `B(K)`
(`GLRep.borelComoduleRep`: `b` acts by contracting the coaction with `b`). Conversely:

* the functions `b ↦ c(b)`, `c ∈ 𝒪(B)`, are exactly the regular functions on `B`
  (`GLRep.borelPoint_mem_borelFunctions`, `GLRep.exists_borelHopf_eq`);
* **a rational representation of `B(K)` is a comodule over `𝒪(B)`**
  (`GLRep.IsRationalBorelRep.comodule`), whose point action is `ρ`
  (`GLRep.IsRationalBorelRep.contract_comodule`);
* **the two constructions are inverse**: for a finite-dimensional `W`, rational representations
  of `B(K)` on `W` correspond to `𝒪(B)`-comodule structures on `W`
  (`GLRep.rationalBorelRepEquivComodule`).

-/

namespace GLRep

open Module TauCeti TauCeti.GeneralLinear TensorProduct WithConv

noncomputable section

variable {K : Type*} [Field K] {n : ℕ}

/-! ### The points of `B(K)` -/

theorem toBorelHopf_surjective : Function.Surjective (toBorelHopf K n) := fun c => by
  obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective c
  refine ⟨h, ?_⟩
  change (UpperTriangular.coordinateMap K n).hom h = _
  rw [UpperTriangular.coordinateMap_apply]
  rfl

/-- `R`-algebra maps out of `𝒪(B)` agreeing on the coordinates `b_ij` are equal. -/
theorem borelHopf_algHom_ext {A : Type*} [Semiring A] [Algebra K A] {φ ψ : borelHopf K n →ₐ[K] A}
    (h : ∀ i j, φ (toBorelHopf K n (genericMatrix K n i j)) =
      ψ (toBorelHopf K n (genericMatrix K n i j))) : φ = ψ := by
  have hc : φ.comp (UpperTriangular.coordinateMap K n).hom.toAlgHom =
      ψ.comp (UpperTriangular.coordinateMap K n).hom.toAlgHom :=
    coordinateHopfAlgebra_algHom_ext K n fun i j => by
      rw [← genericMatrix_apply]
      exact h i j
  refine AlgHom.ext fun c => ?_
  obtain ⟨x, rfl⟩ := toBorelHopf_surjective (K := K) (n := n) c
  exact DFunLike.congr_fun hc x

theorem borelPoint_genericMatrix (b : borel K n) (i j : Fin n) :
    borelPoint b (toBorelHopf K n (genericMatrix K n i j)) =
      ((b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j := by
  rw [borelPoint_toBorelHopf, genericMatrix_apply, glPoint_X]

theorem comul_toBorelHopf (h : glHopf K n) :
    Coalgebra.comul (R := K) (toBorelHopf K n h) =
      TensorProduct.map (toBorelHopf K n).toLinearMap (toBorelHopf K n).toLinearMap
        (Coalgebra.comul (R := K) h) :=
  (CoalgHomClass.map_comp_comul_apply (toBorelHopf K n) h).symm

theorem counit_toBorelHopf (h : glHopf K n) :
    Coalgebra.counit (R := K) (toBorelHopf K n h) = Coalgebra.counit (R := K) h :=
  CoalgHomClass.counit_comp_apply (toBorelHopf K n) h

theorem borelPoint_one :
    borelPoint (1 : borel K n) = (1 : WithConv (borelHopf K n →ₐ[K] K)).ofConv := by
  refine borelHopf_algHom_ext fun i j => ?_
  rw [borelPoint_genericMatrix, OneMemClass.coe_one, Units.val_one, Matrix.one_apply,
    AlgHom.convOne_def, ofConv_toConv, AlgHom.comp_apply, Bialgebra.counitAlgHom_apply,
    counit_toBorelHopf, genericMatrix_apply, coordinateHopfAlgebra_counit_X]
  split_ifs <;> simp

theorem borelPoint_mul (b b' : borel K n) :
    borelPoint (b * b') = (toConv (borelPoint b) * toConv (borelPoint b')).ofConv := by
  refine borelHopf_algHom_ext fun i j => ?_
  rw [borelPoint_genericMatrix, Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply,
    AlgHom.convMul_def, ofConv_toConv, AlgHom.comp_apply, AlgHom.comp_apply,
    Bialgebra.comulAlgHom_apply, comul_toBorelHopf, genericMatrix_apply,
    coordinateHopfAlgebra_comul_X, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul,
    Algebra.TensorProduct.lmul'_apply_tmul, ofConv_toConv, ofConv_toConv]
  change _ = borelPoint b (toBorelHopf K n (genericMatrix K n i k)) *
    borelPoint b' (toBorelHopf K n (genericMatrix K n k j))
  rw [borelPoint_genericMatrix, borelPoint_genericMatrix]

variable (K n) in
/-- The points of `B(K)` in the convolution monoid of points of `𝒪(B)`. -/
def borelPointHom : borel K n →* WithConv (borelHopf K n →ₐ[K] K) where
  toFun b := toConv (borelPoint b)
  map_one' := by rw [borelPoint_one, toConv_ofConv]
  map_mul' b b' := by rw [borelPoint_mul, toConv_ofConv]

/-! ### The representation of a comodule -/

section ComoduleRep

variable {M : Type*} [AddCommGroup M] [Module K M] [TauCeti.Comodule K (borelHopf K n) M]

theorem contract_eq_endOfPoint_borel (x : borelHopf K n →ₐ[K] K) :
    contract x (TauCeti.Comodule.coact (R := K) (C := borelHopf K n) (M := M)) =
      (TensorProduct.lid K M).toLinearMap ∘ₗ TauCeti.Comodule.endOfPoint M x ∘ₗ
        (TensorProduct.lid K M).symm.toLinearMap := by
  refine LinearMap.ext fun m => ?_
  simp only [contract, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    TensorProduct.lid_symm_apply, TauCeti.Comodule.endOfPoint_tmul, one_smul, lid_comm_eq_rid]

variable (K n M) in
/-- **The representation of `B(K)` on a comodule over `𝒪(B)`**: `b` acts by contracting the
coaction with the point `b`. -/
def borelComoduleRep : Representation K (borel K n) M where
  toFun b := contract (borelPoint b) (TauCeti.Comodule.coact (R := K) (C := borelHopf K n) (M := M))
  map_one' := by
    rw [contract_eq_endOfPoint_borel, borelPoint_one, TauCeti.Comodule.endOfPoint_convOne]
    ext m
    simp
  map_mul' b b' := by
    change contract (borelPoint (b * b')) _ = contract (borelPoint b) _ * contract (borelPoint b') _
    rw [contract_eq_endOfPoint_borel (borelPoint (b * b')), contract_eq_endOfPoint_borel
      (borelPoint b), contract_eq_endOfPoint_borel (borelPoint b'), borelPoint_mul,
      TauCeti.Comodule.endOfPoint_convMul, ofConv_toConv, ofConv_toConv, Module.End.mul_eq_comp]
    ext m
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply]

theorem borelComoduleRep_apply (b : borel K n) :
    borelComoduleRep K n M b =
      contract (borelPoint b) (TauCeti.Comodule.coact (R := K) (C := borelHopf K n) (M := M)) :=
  rfl

end ComoduleRep

/-! ### Regular functions on `B` -/

theorem glPoint_antipode (g : GL (Fin n) K) (i k : Fin n) :
    glPoint g (HopfAlgebra.antipode K (genericMatrix K n i k)) =
      ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i k := by
  have hmap : (localizedGenericMatrix K n).map (glEval g) = (g : Matrix (Fin n) (Fin n) K) := by
    ext a c
    rw [Matrix.map_apply, localizedGenericMatrix_apply, coordinateRingMap_apply]
    exact glEval_glX g a c
  have hinv : ((localizedGenericMatrix K n)⁻¹).map (glEval g) =
      ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    rw [Matrix.coe_units_inv]
    refine (Matrix.inv_eq_right_inv ?_).symm
    rw [← hmap, ← AlgHom.mapMatrix_apply, ← AlgHom.mapMatrix_apply, ← map_mul,
      Matrix.mul_nonsing_inv _ (isUnit_det_localizedGenericMatrix K n), map_one]
  rw [genericMatrix_apply, coordinateHopfAlgebra_antipode_X]
  exact congrFun (congrFun hinv i) k

/-- The coordinate `b_ij` of `𝒪(B)`. -/
def borelEntry (i j : Fin n) : borelHopf K n :=
  toBorelHopf K n (genericMatrix K n i j)

/-- The coordinate `(b⁻¹)_ii = b_ii⁻¹` of `𝒪(B)`. -/
def borelInverseEntry (i : Fin n) : borelHopf K n :=
  toBorelHopf K n (HopfAlgebra.antipode K (genericMatrix K n i i))

theorem borelPoint_borelEntry (b : borel K n) (i j : Fin n) :
    borelPoint b (borelEntry i j) = ((b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j :=
  borelPoint_genericMatrix b i j

theorem borelPoint_borelInverseEntry (b : borel K n) (i : Fin n) :
    borelPoint b (borelInverseEntry i) = (((borelDiag K n b i)⁻¹ : Kˣ) : K) := by
  rw [borelInverseEntry, borelPoint_toBorelHopf, glPoint_antipode]
  have h := borelDiag_apply_val (K := K) (n := n) b⁻¹ i
  rw [map_inv, Pi.inv_apply] at h
  exact h.symm

/-- **The regular functions on `B` are the functions `b ↦ c(b)`, `c ∈ 𝒪(B)`.** -/
theorem exists_borelHopf_eq {f : borel K n → K} (hf : f ∈ borelFunctions K n) :
    ∃ c : borelHopf K n, ∀ b, borelPoint b c = f b := by
  obtain ⟨P, hP⟩ := mem_coordFunctions.mp hf
  refine ⟨MvPolynomial.aeval (Sum.elim (fun p : Fin n × Fin n => borelEntry p.1 p.2)
      borelInverseEntry) P,
    fun b => ?_⟩
  rw [hP b, ← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  have hv :
      (fun s => borelPoint b (Sum.elim (fun p : Fin n × Fin n => borelEntry p.1 p.2)
      borelInverseEntry s)) =
      borelCoord K n b := by
    funext s
    rcases s with p | i
    · exact borelPoint_borelEntry b p.1 p.2
    · exact borelPoint_borelInverseEntry b i
  rw [hv]
  rfl

/-- The functions `b ↦ c(b)`, `c ∈ 𝒪(B)`, are regular on `B`. -/
theorem borelPoint_mem_borelFunctions (c : borelHopf K n) :
    (fun b : borel K n => borelPoint b c) ∈ borelFunctions K n := by
  obtain ⟨h, rfl⟩ := toBorelHopf_surjective (K := K) (n := n) c
  have key : ∀ x : GLCoord K n,
      (fun b : borel K n => glEval (b : GL (Fin n) K) x) ∈ borelFunctions K n := by
    intro x
    let φ : GLCoord K n →ₐ[K] (borel K n → K) :=
      AlgHom.pi fun b => glEval (b : GL (Fin n) K)
    have hle : Algebra.adjoin K (Set.range (fun p : Fin n × Fin n => glX p.1 p.2) ∪
        {glDetInv K n}) ≤ (borelFunctions K n).comap φ := by
      refine Algebra.adjoin_le ?_
      rintro _ (⟨p, rfl⟩ | hx)
      · rw [SetLike.mem_coe, Subalgebra.mem_comap]
        change (fun b : borel K n => glEval (b : GL (Fin n) K) (glX p.1 p.2)) ∈
          borelFunctions K n
        simp only [glEval_glX]
        exact entry_mem_borelFunctions p.1 p.2
      · rw [Set.mem_singleton_iff] at hx
        subst hx
        rw [SetLike.mem_coe, Subalgebra.mem_comap]
        change (fun b : borel K n => glEval (b : GL (Fin n) K) (glDetInv K n)) ∈
          borelFunctions K n
        have : (fun b : borel K n => glEval (b : GL (Fin n) K) (glDetInv K n)) =
            ∏ l, fun b : borel K n => (((borelDiag K n b l)⁻¹ : Kˣ) : K) := by
          funext b
          rw [glEval_glDetInv, det_borel, Finset.prod_apply, ← Finset.prod_inv_distrib,
            Units.coe_prod]
        rw [this]
        exact prod_mem fun l _ => diag_inv_mem_borelFunctions l
    rw [adjoin_glX_glDetInv] at hle
    exact hle (Algebra.mem_top (x := x))
  have e : (fun b : borel K n => borelPoint b (toBorelHopf K n h)) =
      fun b : borel K n =>
        glEval (b : GL (Fin n) K) ((coordinateHopfAlgebraAlgEquiv K n).symm h) := by
    funext b
    rw [borelPoint_toBorelHopf]
    rfl
  rw [e]
  exact key _

/-! ### Separation of `M ⊗ 𝒪(B)` and `𝒪(B) ⊗ 𝒪(B)` -/

section Separation

variable [Infinite K]

/-- **Point separation in `M ⊗ 𝒪(B)`**, for any `K`-module `M`. -/
theorem tensor_ext_borelPoint {M : Type*} [AddCommGroup M] [Module K M]
    {t t' : M ⊗[K] borelHopf K n}
    (h : ∀ b : borel K n, TensorProduct.rid K M ((borelPoint b).toLinearMap.lTensor M t) =
      TensorProduct.rid K M ((borelPoint b).toLinearMap.lTensor M t')) : t = t' := by
  classical
  let B := Basis.ofVectorSpace K M
  apply (TensorProduct.equivFinsuppOfBasisLeft B).injective
  ext j
  refine borelHopf_ext fun b => ?_
  have key : ∀ s : M ⊗[K] borelHopf K n,
      borelPoint b (TensorProduct.equivFinsuppOfBasisLeft B s j) =
        B.coord j (TensorProduct.rid K M ((borelPoint b).toLinearMap.lTensor M s)) := by
    intro s
    rw [TensorProduct.equivFinsuppOfBasisLeft_apply]
    induction s with
    | tmul m c => simp [mul_comm]
    | add s s' hs hs' => simp only [map_add, hs, hs']
  rw [key, key, h b]

omit [Infinite K] in
theorem borelPoint_rid_lTensor (b b' : borel K n) (t : borelHopf K n ⊗[K] borelHopf K n) :
    borelPoint b (TensorProduct.rid K (borelHopf K n) ((borelPoint b').toLinearMap.lTensor _ t)) =
      Algebra.TensorProduct.lmul' K
        (Algebra.TensorProduct.map (borelPoint b) (borelPoint b') t) := by
  induction t with
  | tmul x y => simp [mul_comm]
  | add s s' hs hs' => simp only [map_add, hs, hs']

/-- `𝒪(B) ⊗ 𝒪(B)` is separated by the pairs of points of `B(K)`. -/
theorem tensor_ext_borelPoint₂ {t t' : borelHopf K n ⊗[K] borelHopf K n}
    (h : ∀ b b' : borel K n,
      Algebra.TensorProduct.lmul' K (Algebra.TensorProduct.map (borelPoint b) (borelPoint b') t) =
        Algebra.TensorProduct.lmul' K
          (Algebra.TensorProduct.map (borelPoint b) (borelPoint b') t')) : t = t' :=
  tensor_ext_borelPoint fun b' => borelHopf_ext fun b => by
    rw [borelPoint_rid_lTensor, borelPoint_rid_lTensor, h b b']

end Separation

/-! ### Rational representations of `B` as comodules -/

variable [Infinite K]
variable {W : Type*} [AddCommGroup W] [Module K W] {ρ : Representation K (borel K n) W}

namespace IsRationalBorelRep

variable (hρ : IsRationalBorelRep ρ)

/-- A basis of the (finite-dimensional) space of a rational representation. -/
def comoduleBasis : Basis (Fin (finrank K W)) K W :=
  letI := hρ.finiteDimensional
  Module.finBasis K W

/-- The matrix coefficients of `ρ` in the basis `comoduleBasis`, as elements of `𝒪(B)`. -/
def hopfCoeff (i j : Fin (finrank K W)) : borelHopf K n :=
  (exists_borelHopf_eq (hρ.coeff_mem (hρ.comoduleBasis.coord i) (hρ.comoduleBasis j))).choose

omit [Infinite K] in
theorem borelPoint_hopfCoeff (b : borel K n) (i j : Fin (finrank K W)) :
    borelPoint b (hρ.hopfCoeff i j) =
      LinearMap.toMatrix hρ.comoduleBasis hρ.comoduleBasis (ρ b) i j := by
  rw [LinearMap.toMatrix_apply]
  exact (exists_borelHopf_eq (hρ.coeff_mem (hρ.comoduleBasis.coord i)
    (hρ.comoduleBasis j))).choose_spec b

theorem comul_hopfCoeff (i j : Fin (finrank K W)) :
    Coalgebra.comul (R := K) (hρ.hopfCoeff i j) =
      ∑ k, hρ.hopfCoeff i k ⊗ₜ[K] hρ.hopfCoeff k j := by
  refine tensor_ext_borelPoint₂ fun b b' => ?_
  have h1 : Algebra.TensorProduct.lmul' K (Algebra.TensorProduct.map (borelPoint b)
      (borelPoint b') (Coalgebra.comul (R := K) (hρ.hopfCoeff i j))) =
      borelPoint (b * b') (hρ.hopfCoeff i j) := by
    rw [borelPoint_mul, AlgHom.convMul_def, ofConv_toConv, ofConv_toConv]
    rfl
  rw [h1, map_sum, map_sum, borelPoint_hopfCoeff, map_mul, LinearMap.toMatrix_mul,
    Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lmul'_apply_tmul,
    borelPoint_hopfCoeff, borelPoint_hopfCoeff]

omit [Infinite K] in
theorem counit_hopfCoeff (i j : Fin (finrank K W)) :
    Coalgebra.counit (R := K) (hρ.hopfCoeff i j) = if i = j then 1 else 0 := by
  have h1 : Coalgebra.counit (R := K) (hρ.hopfCoeff i j) =
      borelPoint 1 (hρ.hopfCoeff i j) := by
    rw [borelPoint_one]
    rfl
  rw [h1, borelPoint_hopfCoeff, map_one, LinearMap.toMatrix_one, Matrix.one_apply]

/-- **A rational representation of `B(K)` as a comodule over `𝒪(B)`.** -/
@[instance_reducible]
def comodule : TauCeti.Comodule K (borelHopf K n) W :=
  basisComodule hρ.comoduleBasis (Matrix.of hρ.hopfCoeff) hρ.comul_hopfCoeff hρ.counit_hopfCoeff

/-- **The point action of the comodule of `ρ` is `ρ`.** -/
theorem contract_comodule (b : borel K n) :
    contract (borelPoint b) hρ.comodule.coact = ρ b := by
  apply (LinearMap.toMatrix hρ.comoduleBasis hρ.comoduleBasis).injective
  change LinearMap.toMatrix _ _ (contract (borelPoint b)
    (basisCoact hρ.comoduleBasis (Matrix.of hρ.hopfCoeff))) = _
  rw [toMatrix_contract]
  ext i j
  rw [Matrix.map_apply, Matrix.of_apply, borelPoint_hopfCoeff]

theorem borelComoduleRep_comodule :
    (letI := hρ.comodule; borelComoduleRep K n W) = ρ :=
  MonoidHom.ext fun b => hρ.contract_comodule b

end IsRationalBorelRep

omit [Infinite K] in
/-- **The representation of a finite-dimensional comodule over `𝒪(B)` is rational.** -/
theorem isRationalBorelRep_borelComoduleRep {M : Type*} [AddCommGroup M] [Module K M]
    [FiniteDimensional K M] [TauCeti.Comodule K (borelHopf K n) M] :
    IsRationalBorelRep (borelComoduleRep K n M) where
  finiteDimensional := inferInstance
  coeff_mem f w := by
    have key : ∀ t : M ⊗[K] borelHopf K n, (fun b : borel K n =>
        f (TensorProduct.rid K M ((borelPoint b).toLinearMap.lTensor M t))) ∈
          borelFunctions K n := by
      intro t
      induction t with
      | tmul m c =>
        have : (fun b : borel K n =>
            f (TensorProduct.rid K M ((borelPoint b).toLinearMap.lTensor M (m ⊗ₜ[K] c)))) =
            (fun b : borel K n => borelPoint b c) * fun _ => f m := by
          funext b
          simp
        rw [this]
        exact mul_mem (borelPoint_mem_borelFunctions c) (algebraMap_mem _ (f m))
      | add s t hs ht =>
        have : (fun b : borel K n =>
            f (TensorProduct.rid K M ((borelPoint b).toLinearMap.lTensor M (s + t)))) =
            (fun b : borel K n =>
              f (TensorProduct.rid K M ((borelPoint b).toLinearMap.lTensor M s))) +
              fun b => f (TensorProduct.rid K M ((borelPoint b).toLinearMap.lTensor M t)) := by
          funext b
          simp only [map_add, Pi.add_apply]
        rw [this]
        exact add_mem hs ht
    exact key _

/-- **Over an infinite field a comodule structure over `𝒪(B)` is determined by its points.** -/
theorem borelComodule_ext {M : Type*} [AddCommGroup M] [Module K M]
    {c₁ c₂ : TauCeti.Comodule K (borelHopf K n) M}
    (h : ∀ b : borel K n, contract (borelPoint b) c₁.coact = contract (borelPoint b) c₂.coact) :
    c₁ = c₂ :=
  TauCeti.Comodule.ext (LinearMap.ext fun m =>
    tensor_ext_borelPoint fun b => LinearMap.congr_fun (h b) m)

variable (K n W) in
/-- **Rational representations of `B(K)` are the comodules over `𝒪(B)`**: on a
finite-dimensional space `W`, `ρ ↦ ρ.comodule` and `c ↦ borelComoduleRep` are inverse bijections
(`K` infinite). -/
def rationalBorelRepEquivComodule [FiniteDimensional K W] :
    {ρ : Representation K (borel K n) W // IsRationalBorelRep ρ} ≃
      TauCeti.Comodule K (borelHopf K n) W where
  toFun ρ := ρ.2.comodule
  invFun c := letI := c; ⟨borelComoduleRep K n W, isRationalBorelRep_borelComoduleRep⟩
  left_inv ρ := Subtype.ext ρ.2.borelComoduleRep_comodule
  right_inv c := borelComodule_ext fun b => by
    let _ := c
    exact IsRationalBorelRep.contract_comodule isRationalBorelRep_borelComoduleRep b

end

end GLRep
