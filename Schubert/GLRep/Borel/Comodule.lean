import Schubert.GLRep.Borel.Frobenius
import Schubert.GLRep.Lie.Extension
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Coordinate.HopfAlgebra
import TauCeti.Algebra.Coalgebra.Comodule.Basic
import TauCeti.Algebra.Coalgebra.Comodule.PointsAction

/-!
# Rational representations as comodules over `𝒪(GL_n)`

A rational representation `ρ` of `GL_n(K)` (`K` infinite) is a right comodule over Tau Ceti's
coordinate Hopf algebra `𝒪(GL_n) = K[x_ij][det⁻¹]` (`TauCeti.GeneralLinear.coordinateHopfAlgebra`)
whose point action recovers `ρ` (`GLRep.rationalComodule`, `GLRep.contract_rationalComodule`):
contracting the coaction of `w` with the point `g ∈ GL_n(K)` gives `ρ(g) w`.

* A matrix `Y` over a bialgebra with `Δ Y = Y ⊗ Y` (entrywise `Δ(Y_ij) = Σ_k Y_ik ⊗ Y_kj`) and
  `ε(Y) = 1` defines a comodule on any module with a basis (`GLRep.basisComodule`), and contracting
  with an algebra map `x` gives the endomorphism with matrix `x(Y)` (`GLRep.toMatrix_contract`).
* For a polynomial representation the polynomial matrix coefficients evaluated at the generic
  matrix form such a matrix, by the multiplicativity of GLRep's extension of `ρ` to matrices over
  commutative algebras (`GLRep.IsPolynomialRep.extend_mul`).
* A rational representation is a polynomial one twisted by a power of `det⁻¹`, which is
  group-like (`GLRep.comul_genericDetInv`).

Conversely a comodule is a representation by contracting with points (`GLRep.comoduleRep`, via
Tau Ceti's `TauCeti.Comodule.endOfPoint`), the round trip is the identity
(`GLRep.comoduleRep_rationalComodule`), comodule morphisms are intertwining maps
(`GLRep.Comodule.Hom.toIntertwiningMap`) and, over an infinite field, conversely
(`GLRep.homOfIntertwining`, `GLRep.rationalHom`; point separation `GLRep.tensor_ext_glPoint`).

This is the comodule form of GLRep's rational representations, the interface for
base change and for later work in positive characteristic.
-/

namespace GLRep

open Module TauCeti TauCeti.GeneralLinear TensorProduct WithConv

noncomputable section

/-! ### Contraction with a point -/

section Contract

variable {R : Type*} [CommSemiring R] {S : Type*} [Semiring S] [Algebra R S]
variable {M : Type*} [AddCommMonoid M] [Module R M]

/-- Contracting a coaction with an algebra map `x : S → R` (a point). -/
def contract (x : S →ₐ[R] R) (coact : M →ₗ[R] M ⊗[R] S) : M →ₗ[R] M :=
  (TensorProduct.rid R M).toLinearMap ∘ₗ x.toLinearMap.lTensor M ∘ₗ coact

end Contract

/-! ### Comodules from multiplicative matrices -/

section BasisComodule

variable {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Bialgebra R S]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Type*} [AddCommGroup M] [Module R M]
variable (b : Basis ι R M) (Y : Matrix ι ι S)

/-- The candidate coaction `b_j ↦ Σ_i b_i ⊗ Y_ij` of a matrix on a module with a basis. -/
def basisCoact : M →ₗ[R] M ⊗[R] S :=
  b.constr R fun j => ∑ i, b i ⊗ₜ[R] Y i j

omit [DecidableEq ι] in
theorem basisCoact_basis (j : ι) : basisCoact b Y (b j) = ∑ i, b i ⊗ₜ[R] Y i j := by
  rw [basisCoact, Basis.constr_basis]

/-- **A multiplicative matrix makes a module with a basis a comodule.** -/
@[instance_reducible]
def basisComodule (hcomul : ∀ i j, Coalgebra.comul (R := R) (Y i j) = ∑ k, Y i k ⊗ₜ[R] Y k j)
    (hcounit : ∀ i j, Coalgebra.counit (R := R) (Y i j) = if i = j then 1 else 0) :
    TauCeti.Comodule R S M where
  coact := basisCoact b Y
  coassoc := by
    apply b.ext
    intro j
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [basisCoact_basis]
    simp only [map_sum, LinearMap.rTensor_tmul, basisCoact_basis, TensorProduct.sum_tmul,
      LinearEquiv.coe_coe, TensorProduct.assoc_tmul, LinearMap.lTensor_tmul, hcomul,
      TensorProduct.tmul_sum]
    rw [Finset.sum_comm]
  lTensor_counit_comp_coact := by
    apply b.ext
    intro j
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [basisCoact_basis]
    simp only [map_sum, LinearMap.lTensor_tmul, hcounit]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      simp [hij]
    · simp


omit [DecidableEq ι] in
theorem contract_basisCoact_basis (x : S →ₐ[R] R) (j : ι) :
    contract x (basisCoact b Y) (b j) = ∑ i, x (Y i j) • b i := by
  simp only [contract, LinearMap.coe_comp, Function.comp_apply, basisCoact_basis, map_sum,
    LinearMap.lTensor_tmul, AlgHom.toLinearMap_apply, LinearEquiv.coe_coe,
    TensorProduct.rid_tmul]

/-- Contracting with a point `x` gives the endomorphism with matrix `x(Y)`. -/
theorem toMatrix_contract (x : S →ₐ[R] R) :
    LinearMap.toMatrix b b (contract x (basisCoact b Y)) = Y.map x := by
  ext i j
  rw [LinearMap.toMatrix_apply, contract_basisCoact_basis, map_sum, Finsupp.finsetSum_apply,
    Matrix.map_apply]
  simp [b.repr_self, Finsupp.single_apply]

end BasisComodule

/-! ### The coordinate Hopf algebra of `GL_n` -/

variable {K : Type*} [Field K] {n : ℕ}

/-- The coordinate Hopf algebra `𝒪(GL_n)` (Tau Ceti's bundled `coordinateHopfAlgebra`), over a
commutative ring. -/
abbrev glHopf (K : Type*) [CommRing K] (n : ℕ) : CommHopfAlgCat K := coordinateHopfAlgebra K n

/-- The point `g ∈ GL_n(K)` as an algebra map `𝒪(GL_n) → K`. -/
def glPoint (g : GL (Fin n) K) : glHopf K n →ₐ[K] K :=
  (glEval g).comp (coordinateHopfAlgebraAlgEquiv K n).symm.toAlgHom

theorem glPoint_genericMatrix (g : GL (Fin n) K) :
    (genericMatrix K n).map (glPoint g) = (g : Matrix (Fin n) (Fin n) K) := by
  ext i j
  rw [Matrix.map_apply, genericMatrix_apply]
  change glEval g ((coordinateHopfAlgebraAlgEquiv K n).symm
    (coordinateHopfAlgebraAlgEquiv K n (coordinateRingMap K n (MvPolynomial.X (i, j))))) = _
  rw [AlgEquiv.symm_apply_apply, coordinateRingMap_apply]
  exact (glEval_algebraMap g _).trans (MvPolynomial.aeval_X _ _)

/-- The determinant of the generic matrix. -/
def genericDetHopf : glHopf K n := (genericMatrix K n).det

/-- `det⁻¹ ∈ 𝒪(GL_n)`. -/
def genericDetInv : glHopf K n := ↑(isUnit_det_genericMatrix K n).unit⁻¹

theorem genericDetHopf_mul_genericDetInv : (genericDetHopf : glHopf K n) * genericDetInv = 1 :=
  (isUnit_det_genericMatrix K n).mul_val_inv

theorem comul_genericDetHopf :
    Bialgebra.comulAlgHom K (glHopf K n) genericDetHopf =
      genericDetHopf ⊗ₜ[K] (genericDetHopf : glHopf K n) := by
  rw [genericDetHopf, AlgHom.map_det, AlgHom.mapMatrix_apply, map_comul_genericMatrix,
      Matrix.det_mul,
    ← AlgHom.mapMatrix_apply, ← AlgHom.map_det, ← AlgHom.mapMatrix_apply, ← AlgHom.map_det,
    Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
    one_mul]

/-- **`det⁻¹` is group-like.** -/
theorem comul_genericDetInv :
    Bialgebra.comulAlgHom K (glHopf K n) genericDetInv =
      genericDetInv ⊗ₜ[K] (genericDetInv : glHopf K n) := by
  refine left_inv_eq_right_inv (a := genericDetHopf ⊗ₜ[K] (genericDetHopf : glHopf K n)) ?_ ?_
  · rw [← comul_genericDetHopf, ← map_mul, mul_comm, genericDetHopf_mul_genericDetInv, map_one]
  · rw [Algebra.TensorProduct.tmul_mul_tmul, genericDetHopf_mul_genericDetInv,
      Algebra.TensorProduct.one_def]

theorem counit_genericDetInv :
    Bialgebra.counitAlgHom K (glHopf K n) genericDetInv = 1 := by
  have h1 : Bialgebra.counitAlgHom K (glHopf K n) genericDetHopf = 1 := by
    rw [genericDetHopf, AlgHom.map_det, AlgHom.mapMatrix_apply, map_counit_genericMatrix,
      Matrix.det_one]
  have h2 := congrArg (Bialgebra.counitAlgHom K (glHopf K n))
    (genericDetHopf_mul_genericDetInv (n := n))
  rwa [map_mul, h1, one_mul, map_one] at h2

theorem glPoint_genericDetInv (g : GL (Fin n) K) :
    glPoint g genericDetInv = (((Matrix.GeneralLinearGroup.det g)⁻¹ : Kˣ) : K) := by
  have h1 : glPoint g genericDetHopf = (g : Matrix (Fin n) (Fin n) K).det := by
    rw [genericDetHopf, AlgHom.map_det, AlgHom.mapMatrix_apply, glPoint_genericMatrix]
  have h2 := congrArg (glPoint g) (genericDetHopf_mul_genericDetInv (n := n))
  rw [map_mul, h1, map_one] at h2
  rw [Units.val_inv_eq_inv_val, Matrix.GeneralLinearGroup.val_det_apply]
  exact (eq_inv_of_mul_eq_one_right h2)

/-! ### Polynomial and rational representations -/

variable [Infinite K]
variable {W : Type*} [AddCommGroup W] [Module K W] {ρ : Representation K (GL (Fin n) K) W}

namespace IsPolynomialRep

variable (h : IsPolynomialRep ρ)

/-- The matrix coefficients of a polynomial representation, in `𝒪(GL_n)`. -/
def coeffMatrix : Matrix (Idx (K := K) W) (Idx (K := K) W) (glHopf K n) :=
  h.extend (glHopf K n) (genericMatrix K n)

theorem comul_coeffMatrix (i j : Idx (K := K) W) :
    Coalgebra.comul (R := K) (h.coeffMatrix i j) =
      ∑ k, h.coeffMatrix i k ⊗ₜ[K] h.coeffMatrix k j := by
  have e := h.extend_map (Bialgebra.comulAlgHom K (glHopf K n)) (genericMatrix K n)
  rw [map_comul_genericMatrix, h.extend_mul, h.extend_map, h.extend_map] at e
  have e' := congrFun (congrFun e i) j
  rw [Matrix.map_apply, Bialgebra.comulAlgHom_apply, Matrix.mul_apply] at e'
  change Coalgebra.comul (R := K) (h.extend (glHopf K n) (genericMatrix K n) i j) = _
  rw [← e']
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.map_apply, Matrix.map_apply, Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
    mul_one]
  rfl

omit [Infinite K] in
theorem counit_coeffMatrix (i j : Idx (K := K) W) :
    Coalgebra.counit (R := K) (h.coeffMatrix i j) = if i = j then 1 else 0 := by
  have e := h.extend_map (Bialgebra.counitAlgHom K (glHopf K n)) (genericMatrix K n)
  rw [map_counit_genericMatrix, h.extend_one] at e
  have e' := congrFun (congrFun e i) j
  rw [Matrix.map_apply, Bialgebra.counitAlgHom_apply, Matrix.one_apply] at e'
  exact e'.symm

omit [Infinite K] in
theorem glPoint_coeffMatrix (g : GL (Fin n) K) :
    h.coeffMatrix.map (glPoint g) = LinearMap.toMatrix h.basis h.basis (ρ g) := by
  rw [coeffMatrix, ← h.extend_map, glPoint_genericMatrix, h.extend_glCoord]

end IsPolynomialRep

/-- The matrix coefficients of a rational representation in `𝒪(GL_n)`:
`det⁻ᵏ` times those of the polynomial representation `ρ ⊗ det^k`. -/
def ratCoeffMatrix (hρ : IsRationalRep ρ) :
    Matrix (IsPolynomialRep.Idx (K := K) W) (IsPolynomialRep.Idx (K := K) W) (glHopf K n) :=
  fun i j => genericDetInv ^ hρ.choose * hρ.choose_spec.coeffMatrix i j

theorem comul_ratCoeffMatrix (hρ : IsRationalRep ρ) (i j : IsPolynomialRep.Idx (K := K) W) :
    Coalgebra.comul (R := K) (ratCoeffMatrix hρ i j) =
      ∑ k, ratCoeffMatrix hρ i k ⊗ₜ[K] ratCoeffMatrix hρ k j := by
  have hc : ∀ x : glHopf K n,
      Coalgebra.comul (R := K) x = Bialgebra.comulAlgHom K (glHopf K n) x := fun _ => rfl
  rw [ratCoeffMatrix, hc, map_mul, map_pow, comul_genericDetInv, ← hc,
    hρ.choose_spec.comul_coeffMatrix, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.tmul_mul_tmul]
  rfl

omit [Infinite K] in
theorem counit_ratCoeffMatrix (hρ : IsRationalRep ρ) (i j : IsPolynomialRep.Idx (K := K) W) :
    Coalgebra.counit (R := K) (ratCoeffMatrix hρ i j) = if i = j then 1 else 0 := by
  have hc : ∀ x : glHopf K n,
      Coalgebra.counit (R := K) x = Bialgebra.counitAlgHom K (glHopf K n) x := fun _ => rfl
  rw [ratCoeffMatrix, hc, map_mul, map_pow, counit_genericDetInv, one_pow, one_mul, ← hc,
    hρ.choose_spec.counit_coeffMatrix]

/-- **A rational representation of `GL_n(K)` as a comodule over `𝒪(GL_n)`.** -/
@[instance_reducible]
def rationalComodule (hρ : IsRationalRep ρ) : TauCeti.Comodule K (glHopf K n) W :=
  basisComodule hρ.choose_spec.basis (ratCoeffMatrix hρ) (comul_ratCoeffMatrix hρ)
    (counit_ratCoeffMatrix hρ)

theorem rationalComodule_coact (hρ : IsRationalRep ρ) :
    (rationalComodule hρ).coact = basisCoact hρ.choose_spec.basis (ratCoeffMatrix hρ) :=
  rfl

/-- **The point action of the comodule is `ρ`**: contracting the coaction with the point `g`
gives `ρ(g)`. -/
theorem contract_rationalComodule (hρ : IsRationalRep ρ) (g : GL (Fin n) K) :
    contract (glPoint g) (rationalComodule hρ).coact = ρ g := by
  set h := hρ.choose_spec
  rw [rationalComodule_coact]
  apply (LinearMap.toMatrix h.basis h.basis).injective
  rw [toMatrix_contract]
  ext i j
  rw [Matrix.map_apply, ratCoeffMatrix, map_mul, map_pow, glPoint_genericDetInv]
  have e := congrFun (congrFun (h.glPoint_coeffMatrix g) i) j
  rw [Matrix.map_apply] at e
  rw [e, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply, scaledRep_apply, map_smul,
    Finsupp.smul_apply, smul_eq_mul, detPow_apply, ← mul_assoc, ← Units.val_pow_eq_pow_val,
    ← Matrix.GeneralLinearGroup.val_det_apply, ← Units.val_pow_eq_pow_val, ← Units.val_mul,
    ← mul_pow, inv_mul_cancel, one_pow, Units.val_one, one_mul]


/-! ### The representation of a comodule -/

section ComoduleRep

variable {K : Type*} [Field K] {n : ℕ}

theorem glPoint_X (g : GL (Fin n) K) (i j : Fin n) :
    glPoint g (coordinateHopfAlgebraAlgEquiv K n (coordinateRingMap K n (MvPolynomial.X (i, j)))) =
      (g : Matrix (Fin n) (Fin n) K) i j := by
  have := congrFun (congrFun (glPoint_genericMatrix g) i) j
  rwa [Matrix.map_apply, genericMatrix_apply] at this

theorem glPoint_one :
    glPoint (1 : GL (Fin n) K) = (1 : WithConv (glHopf K n →ₐ[K] K)).ofConv := by
  apply coordinateHopfAlgebra_algHom_ext K n
  intro i j
  rw [glPoint_X, Units.val_one, Matrix.one_apply, AlgHom.convOne_def, ofConv_toConv,
    AlgHom.comp_apply, Bialgebra.counitAlgHom_apply, coordinateHopfAlgebra_counit_X]
  split_ifs <;> simp

theorem glPoint_mul (g h : GL (Fin n) K) :
    glPoint (g * h) = (toConv (glPoint g) * toConv (glPoint h)).ofConv := by
  apply coordinateHopfAlgebra_algHom_ext K n
  intro i j
  rw [glPoint_X, Units.val_mul, Matrix.mul_apply, AlgHom.convMul_def, ofConv_toConv,
    AlgHom.comp_apply, AlgHom.comp_apply, Bialgebra.comulAlgHom_apply,
    coordinateHopfAlgebra_comul_X, map_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lmul'_apply_tmul, ofConv_toConv,
    ofConv_toConv, glPoint_X, glPoint_X]

variable (K n) in
/-- The points of `GL_n(K)` in the convolution monoid of points of `𝒪(GL_n)`. -/
def glPointHom : GL (Fin n) K →* WithConv (glHopf K n →ₐ[K] K) where
  toFun g := toConv (glPoint g)
  map_one' := by rw [glPoint_one, toConv_ofConv]
  map_mul' g h := by rw [glPoint_mul, toConv_ofConv]

variable {M : Type*} [AddCommGroup M] [Module K M] [TauCeti.Comodule K (glHopf K n) M]

omit [TauCeti.Comodule K (glHopf K n) M] in
theorem lid_comm_eq_rid (t : M ⊗[K] K) :
    TensorProduct.lid K M (TensorProduct.comm K M K t) = TensorProduct.rid K M t := by
  induction t with
  | tmul m c => simp
  | add s t hs ht => rw [map_add, map_add, hs, ht, map_add]

theorem contract_eq_endOfPoint (x : glHopf K n →ₐ[K] K) :
    contract x (TauCeti.Comodule.coact (R := K) (C := glHopf K n) (M := M)) =
      (TensorProduct.lid K M).toLinearMap ∘ₗ TauCeti.Comodule.endOfPoint M x ∘ₗ
        (TensorProduct.lid K M).symm.toLinearMap := by
  refine LinearMap.ext fun m => ?_
  simp only [contract, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    TensorProduct.lid_symm_apply, TauCeti.Comodule.endOfPoint_tmul, one_smul, lid_comm_eq_rid]

variable (K n M) in
/-- **The representation of `GL_n(K)` on a comodule over `𝒪(GL_n)`**: `g` acts by contracting
the coaction with the point `g`. -/
def comoduleRep : Representation K (GL (Fin n) K) M where
  toFun g := contract (glPoint g) (TauCeti.Comodule.coact (R := K) (C := glHopf K n) (M := M))
  map_one' := by
    rw [contract_eq_endOfPoint, glPoint_one, TauCeti.Comodule.endOfPoint_convOne]
    ext m
    simp
  map_mul' g h := by
    change contract (glPoint (g * h)) _ = contract (glPoint g) _ * contract (glPoint h) _
    rw [contract_eq_endOfPoint (glPoint (g * h)), contract_eq_endOfPoint (glPoint g),
      contract_eq_endOfPoint (glPoint h), glPoint_mul, TauCeti.Comodule.endOfPoint_convMul,
      ofConv_toConv, ofConv_toConv, Module.End.mul_eq_comp]
    ext m
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply]

theorem comoduleRep_apply (g : GL (Fin n) K) :
    comoduleRep K n M g =
      contract (glPoint g) (TauCeti.Comodule.coact (R := K) (C := glHopf K n) (M := M)) :=
  rfl

end ComoduleRep

section RoundTrip

variable {K : Type*} [Field K] [Infinite K] {n : ℕ}
variable {W : Type*} [AddCommGroup W] [Module K W] {ρ : Representation K (GL (Fin n) K) W}

/-- **The representation of the comodule of a rational representation `ρ` is `ρ`.** -/
theorem comoduleRep_rationalComodule (hρ : IsRationalRep ρ) :
    letI := rationalComodule hρ
    comoduleRep K n W = ρ := by
  exact MonoidHom.ext fun g => contract_rationalComodule hρ g

end RoundTrip

/-! ### Morphisms -/

section Morphisms

variable {K : Type*} [Field K] {n : ℕ}
variable {M : Type*} [AddCommGroup M] [Module K M] [TauCeti.Comodule K (glHopf K n) M]
variable {N : Type*} [AddCommGroup N] [Module K N] [TauCeti.Comodule K (glHopf K n) N]

omit [TauCeti.Comodule K (glHopf K n) M] [TauCeti.Comodule K (glHopf K n) N] in
theorem rid_lTensor_map (x : glHopf K n →ₐ[K] K) (f : M →ₗ[K] N) (t : M ⊗[K] glHopf K n) :
    TensorProduct.rid K N (x.toLinearMap.lTensor N (TensorProduct.map f LinearMap.id t)) =
      f (TensorProduct.rid K M (x.toLinearMap.lTensor M t)) := by
  induction t with
  | tmul m c => simp
  | add s t hs ht => rw [map_add, map_add, map_add, hs, ht, map_add, map_add, map_add]

/-- A comodule morphism intertwines the representations. -/
def Comodule.Hom.toIntertwiningMap (f : TauCeti.Comodule.Hom K (glHopf K n) M N) :
    (comoduleRep K n M).IntertwiningMap (comoduleRep K n N) where
  toLinearMap := f.toLinearMap
  isIntertwining' g := LinearMap.ext fun m => by
    simp only [LinearMap.coe_comp, Function.comp_apply, comoduleRep_apply, contract,
      LinearEquiv.coe_coe]
    rw [← rid_lTensor_map, TauCeti.Comodule.Hom.map_coact_apply]
    rfl

omit [TauCeti.Comodule K (glHopf K n) M] in
/-- The coefficient of `b_i` of the contraction is the point applied to the `i`-th coordinate. -/
theorem glPoint_equivFinsuppOfBasisLeft {ι : Type*} [DecidableEq ι] (b : Basis ι K M)
    (x : glHopf K n →ₐ[K] K) (t : M ⊗[K] glHopf K n) (i : ι) :
    x (TensorProduct.equivFinsuppOfBasisLeft b t i) =
      b.coord i (TensorProduct.rid K M (x.toLinearMap.lTensor M t)) := by
  rw [TensorProduct.equivFinsuppOfBasisLeft_apply]
  induction t with
  | tmul m c => simp [mul_comm]
  | add s t hs ht => simp only [map_add, hs, ht]

variable [Infinite K]

/-- Functions in `𝒪(GL_n)` are determined by their values at the points of `GL_n(K)`. -/
theorem glHopf_ext {a c : glHopf K n} (h : ∀ g : GL (Fin n) K, glPoint g a = glPoint g c) :
    a = c :=
  (coordinateHopfAlgebraAlgEquiv K n).symm.injective (glCoord_ext h)

omit [TauCeti.Comodule K (glHopf K n) M] in
/-- **Point separation in `M ⊗ 𝒪(GL_n)`.** -/
theorem tensor_ext_glPoint [FiniteDimensional K M] {t t' : M ⊗[K] glHopf K n}
    (h : ∀ g : GL (Fin n) K, TensorProduct.rid K M ((glPoint g).toLinearMap.lTensor M t) =
      TensorProduct.rid K M ((glPoint g).toLinearMap.lTensor M t')) : t = t' := by
  classical
  let b := Module.finBasis K M
  apply (TensorProduct.equivFinsuppOfBasisLeft b).injective
  ext i
  refine glHopf_ext fun g => ?_
  rw [glPoint_equivFinsuppOfBasisLeft, glPoint_equivFinsuppOfBasisLeft, h g]

/-- **A linear map intertwining the representations of two comodules is a comodule morphism**
(over an infinite field, for a finite-dimensional target). -/
def homOfIntertwining [FiniteDimensional K N]
    (f : (comoduleRep K n M).IntertwiningMap (comoduleRep K n N)) :
    TauCeti.Comodule.Hom K (glHopf K n) M N where
  toLinearMap := f.toLinearMap
  map_coact := LinearMap.ext fun m => tensor_ext_glPoint fun g => by
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [rid_lTensor_map]
    have := LinearMap.congr_fun (f.isIntertwining' g) m
    simp only [LinearMap.coe_comp, Function.comp_apply, comoduleRep_apply, contract,
      LinearEquiv.coe_coe] at this
    exact this

end Morphisms

section RationalMorphisms

variable {K : Type*} [Field K] [Infinite K] {n : ℕ}
variable {W : Type*} [AddCommGroup W] [Module K W] {ρ : Representation K (GL (Fin n) K) W}
variable {V : Type*} [AddCommGroup V] [Module K V] {σ : Representation K (GL (Fin n) K) V}

/-- **Intertwining maps of rational representations are comodule morphisms.** -/
def rationalHom (hρ : IsRationalRep ρ) (hσ : IsRationalRep σ) (φ : ρ.IntertwiningMap σ) :
    letI := rationalComodule hρ
    letI := rationalComodule hσ
    TauCeti.Comodule.Hom K (glHopf K n) W V :=
  letI := rationalComodule hρ
  letI := rationalComodule hσ
  have := hσ.finiteDimensional
  homOfIntertwining
    { toLinearMap := φ.toLinearMap
      isIntertwining' := by
        rw [comoduleRep_rationalComodule hρ, comoduleRep_rationalComodule hσ]
        exact φ.isIntertwining' }

theorem coe_rationalHom (hρ : IsRationalRep ρ) (hσ : IsRationalRep σ) (φ : ρ.IntertwiningMap σ) :
    ⇑(rationalHom hρ hσ φ) = ⇑φ :=
  rfl

end RationalMorphisms

end

end GLRep
