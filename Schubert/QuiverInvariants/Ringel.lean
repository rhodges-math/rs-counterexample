import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.Rank
import Schubert.QuiverInvariants.Basic

/-!
# The Ringel map

For representations `V` on `ι` and `W` on `κ` of a forward quiver, the **Ringel map** is
`d_{V,W} : ⊕_p Hom(K^{ι p}, K^{κ p}) → ⊕_{e : p → q} Hom(K^{ι p}, K^{κ q})`,
`ψ ↦ (W_e ψ_p − ψ_q V_e)_e`. Its kernel is the space of homomorphisms `V → W`, and its cokernel
is `Ext¹(V, W)` for the path algebra (Ringel 1976). We never use that identification: here
`homDim V W` and `extDim V W` are *defined* as the dimensions of the kernel and the cokernel, and
the Euler identity `homDim − extDim = ⟨dim V, dim W⟩` is rank–nullity.

## Main definitions

* `QuiverInvariants.vertexCoord`: the coordinates of `VertexHom R ι κ`.
* `QuiverInvariants.vertexConj`: conjugation of vertex data by two families of isomorphisms.
* `QuiverInvariants.FQuiver.ringel V W`: the Ringel map, an `R`-linear map.
* `QuiverInvariants.FQuiver.ringelMatrix V W`: its matrix in the coordinates.
* `QuiverInvariants.FQuiver.homDim`, `extDim`, `ringelRank`: the dimensions of the kernel, the
  cokernel and the image of the Ringel map.

## Main results

* `QuiverInvariants.FQuiver.homDim_sub_extDim`: `homDim V W − extDim V W = ⟨dim ι, dim κ⟩`.
* `QuiverInvariants.FQuiver.ringelMatrix_map`: the Ringel matrix commutes with ring
  homomorphisms; with `FQuiver.univRep` this makes its minors polynomials in `(V, W)`.
* `QuiverInvariants.FQuiver.homDim_transport`, `extDim_transport`: invariance under changes of
  coordinates, hence under the group action and reindexing.
* `QuiverInvariants.FQuiver.extDim_le_extDim_blockRep`,
  `QuiverInvariants.FQuiver.extDim_blockRep_eq_of_forall`: for a block upper-triangular `W` with
  quotient `C`, the induced map on cokernels is onto, and it is an isomorphism as soon as every
  arrow datum with values in the first block lies in the image of the Ringel map.
* `QuiverInvariants.FQuiver.isSubrep_ker`, `isSubrep_range`: kernels and images of
  homomorphisms are subrepresentations.
-/

open Matrix

namespace QuiverInvariants

noncomputable section

/-! ### Coordinates and conjugation of vertex data -/

section Vertex

variable (R : Type*) [CommRing R] {s : ℕ} (ι κ : Fin s → Type)

/-- The coordinates of vertex data, as a linear isomorphism: `⟨p, (i, j)⟩` is the entry `(j, i)`
of the matrix at `p`. -/
def vertexCoord : VertexHom R ι κ ≃ₗ[R] (VertexEntry ι κ → R) where
  toFun ψ x := ψ x.1 x.2.2 x.2.1
  invFun c p j i := c ⟨p, (i, j)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem vertexCoord_apply (ψ : VertexHom R ι κ) (x : VertexEntry ι κ) :
    vertexCoord R ι κ ψ x = ψ x.1 x.2.2 x.2.1 :=
  rfl

@[simp] theorem vertexCoord_symm_apply (c : VertexEntry ι κ → R) (p : Fin s) (j : κ p)
    (i : ι p) : (vertexCoord R ι κ).symm c p j i = c ⟨p, (i, j)⟩ :=
  rfl

variable {R ι κ} [∀ p, Fintype (ι p)] [∀ p, DecidableEq (ι p)] [∀ p, Fintype (κ p)]
  [∀ p, DecidableEq (κ p)] {ι' κ' : Fin s → Type} [∀ p, Fintype (ι' p)]
  [∀ p, DecidableEq (ι' p)] [∀ p, Fintype (κ' p)] [∀ p, DecidableEq (κ' p)]

/-- **Conjugation of vertex data** by two families of isomorphisms:
`ψ_p ↦ P'_p ψ_p P_p⁻¹`. -/
def vertexConj (P : VertexIso R ι ι') (P' : VertexIso R κ κ') :
    VertexHom R ι κ ≃ₗ[R] VertexHom R ι' κ' where
  toFun ψ p := P'.hom p * ψ p * P.inv p
  invFun ψ p := P'.inv p * ψ p * P.hom p
  map_add' ψ φ := funext fun p => by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c ψ := funext fun p => by simp [Matrix.mul_smul, Matrix.smul_mul]
  left_inv ψ := funext fun p => by
    simp only [← Matrix.mul_assoc, P'.inv_mul_hom, Matrix.one_mul]
    rw [Matrix.mul_assoc, P.inv_mul_hom, Matrix.mul_one]
  right_inv ψ := funext fun p => by
    simp only [← Matrix.mul_assoc, P'.hom_mul_inv, Matrix.one_mul]
    rw [Matrix.mul_assoc, P.hom_mul_inv, Matrix.mul_one]

@[simp] theorem vertexConj_apply (P : VertexIso R ι ι') (P' : VertexIso R κ κ')
    (ψ : VertexHom R ι κ) (p : Fin s) : vertexConj P P' ψ p = P'.hom p * ψ p * P.inv p :=
  rfl

@[simp] theorem vertexConj_symm_apply (P : VertexIso R ι ι') (P' : VertexIso R κ κ')
    (ψ : VertexHom R ι' κ') (p : Fin s) :
    (vertexConj P P').symm ψ p = P'.inv p * ψ p * P.hom p :=
  rfl

end Vertex

namespace FQuiver

variable (Q : FQuiver)

/-! ### The Ringel map -/

section Ringel

variable {R : Type*} [CommRing R] {ι κ : Fin Q.s → Type} [∀ p, Fintype (ι p)]
  [∀ p, Fintype (κ p)]

/-- **The Ringel map** `d_{V,W} : ψ ↦ (W_e ψ_p − ψ_q V_e)_{e : p → q}`. Its kernel consists of the
homomorphisms `V → W`. -/
def ringel (V : Q.Rep R ι) (W : Q.Rep R κ) : VertexHom R ι κ →ₗ[R] Q.ArrowHom R ι κ where
  toFun ψ e := W e * ψ (Q.src e) - ψ (Q.tgt e) * V e
  map_add' ψ φ := funext fun e => by
    simp only [Pi.add_apply, Matrix.mul_add, Matrix.add_mul]
    abel
  map_smul' c ψ := funext fun e => by
    simp only [Pi.smul_apply, Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply, smul_sub]

@[simp] theorem ringel_apply (V : Q.Rep R ι) (W : Q.Rep R κ) (ψ : VertexHom R ι κ)
    (e : Q.Arrow) : Q.ringel V W ψ e = W e * ψ (Q.src e) - ψ (Q.tgt e) * V e :=
  rfl

theorem mem_ker_ringel {V : Q.Rep R ι} {W : Q.Rep R κ} {φ : VertexHom R ι κ} :
    φ ∈ LinearMap.ker (Q.ringel V W) ↔ ∀ e, W e * φ (Q.src e) = φ (Q.tgt e) * V e := by
  rw [LinearMap.mem_ker, funext_iff]
  simp only [ringel_apply, Pi.zero_apply, sub_eq_zero]

/-- The Ringel map is additive in the pair `(V, W)`. -/
theorem ringel_add (V V' : Q.Rep R ι) (W W' : Q.Rep R κ) :
    Q.ringel (V + V') (W + W') = Q.ringel V W + Q.ringel V' W' := by
  refine LinearMap.ext fun ψ => funext fun e => ?_
  simp only [ringel_apply, LinearMap.add_apply, Pi.add_apply, Matrix.mul_add, Matrix.add_mul]
  abel

theorem ringel_smul (c : R) (V : Q.Rep R ι) (W : Q.Rep R κ) :
    Q.ringel (c • V) (c • W) = c • Q.ringel V W := by
  refine LinearMap.ext fun ψ => funext fun e => ?_
  simp only [ringel_apply, LinearMap.smul_apply, Pi.smul_apply, Matrix.smul_mul,
    Matrix.mul_smul, smul_sub]

@[simp] theorem ringel_zero_zero : Q.ringel (0 : Q.Rep R ι) (0 : Q.Rep R κ) = 0 :=
  LinearMap.ext fun ψ => funext fun e => by simp

theorem ringel_add_left (V V' : Q.Rep R ι) (W : Q.Rep R κ) :
    Q.ringel (V + V') W = Q.ringel V W + Q.ringel V' 0 := by
  simpa using Q.ringel_add V V' W 0

theorem ringel_add_right (V : Q.Rep R ι) (W W' : Q.Rep R κ) :
    Q.ringel V (W + W') = Q.ringel V W + Q.ringel 0 W' := by
  simpa using Q.ringel_add V 0 W W'

@[simp] theorem ringel_zero_left_apply (W : Q.Rep R κ) (ψ : VertexHom R ι κ) (e : Q.Arrow) :
    Q.ringel 0 W ψ e = W e * ψ (Q.src e) := by
  simp

@[simp] theorem ringel_zero_right_apply (V : Q.Rep R ι) (ψ : VertexHom R ι κ) (e : Q.Arrow) :
    Q.ringel V 0 ψ e = -(ψ (Q.tgt e) * V e) := by
  simp

/-! ### The Ringel matrix -/

variable [∀ p, DecidableEq (ι p)] [∀ p, DecidableEq (κ p)]

/-- **The Ringel matrix**: the matrix of `ringel V W` in the coordinates `vertexCoord` and
`arrowCoord`. -/
def ringelMatrix (V : Q.Rep R ι) (W : Q.Rep R κ) :
    Matrix (Q.ArrowEntry ι κ) (VertexEntry ι κ) R :=
  LinearMap.toMatrix' ((Q.arrowCoord R ι κ).toLinearMap ∘ₗ Q.ringel V W ∘ₗ
    (vertexCoord R ι κ).symm.toLinearMap)

/-- The Ringel matrix as a linear map is the Ringel map in coordinates. -/
theorem toLin'_ringelMatrix (V : Q.Rep R ι) (W : Q.Rep R κ) :
    Matrix.toLin' (Q.ringelMatrix V W) = (Q.arrowCoord R ι κ).toLinearMap ∘ₗ Q.ringel V W ∘ₗ
      (vertexCoord R ι κ).symm.toLinearMap :=
  Matrix.toLin'_toMatrix' _

theorem ringelMatrix_apply (V : Q.Rep R ι) (W : Q.Rep R κ) (x : Q.ArrowEntry ι κ)
    (y : VertexEntry ι κ) :
    Q.ringelMatrix V W x y = Q.ringel V W ((vertexCoord R ι κ).symm (Pi.single y 1))
      x.1 x.2.2 x.2.1 := by
  rw [ringelMatrix, LinearMap.toMatrix'_apply]
  congr 1

/-- **The Ringel matrix commutes with ring homomorphisms.** -/
theorem ringelMatrix_map {S : Type*} [CommRing S] (f : R →+* S) (V : Q.Rep R ι)
    (W : Q.Rep R κ) :
    (Q.ringelMatrix V W).map f = Q.ringelMatrix (Q.mapArrowHom f V) (Q.mapArrowHom f W) := by
  ext x y
  rw [Matrix.map_apply, ringelMatrix_apply, ringelMatrix_apply]
  have hψ : (vertexCoord S ι κ).symm (Pi.single y 1) =
      fun p => ((vertexCoord R ι κ).symm (Pi.single y 1) p).map f := by
    funext p
    ext j i
    simp only [vertexCoord_symm_apply, Matrix.map_apply, Pi.single_apply]
    split_ifs <;> simp
  rw [hψ]
  simp only [ringel_apply, mapArrowHom_apply, Matrix.sub_apply, Matrix.mul_apply,
    Matrix.map_apply, map_sub, map_sum, map_mul]

end Ringel

/-! ### Dimensions of the kernel, image and cokernel -/

section Dimensions

variable {K : Type*} [Field K] {ι κ : Fin Q.s → Type} [∀ p, Fintype (ι p)]
  [∀ p, Fintype (κ p)]

/-- `hom(V, W)`: the dimension of the space of homomorphisms `V → W`, the kernel of the Ringel
map. -/
def homDim (V : Q.Rep K ι) (W : Q.Rep K κ) : ℕ :=
  Module.finrank K (LinearMap.ker (Q.ringel V W))

/-- `ext(V, W)`: the dimension of the cokernel of the Ringel map. -/
def extDim (V : Q.Rep K ι) (W : Q.Rep K κ) : ℕ :=
  Module.finrank K (Q.ArrowHom K ι κ ⧸ LinearMap.range (Q.ringel V W))

/-- The rank of the Ringel map. -/
def ringelRank (V : Q.Rep K ι) (W : Q.Rep K κ) : ℕ :=
  Module.finrank K (LinearMap.range (Q.ringel V W))

theorem finrank_vertexHom :
    Module.finrank K (VertexHom K ι κ) = ∑ p, Fintype.card (κ p) * Fintype.card (ι p) := by
  rw [Module.finrank_pi_fintype]
  simp [Module.finrank_matrix]

theorem finrank_arrowHom :
    Module.finrank K (Q.ArrowHom K ι κ) =
      ∑ e : Q.Arrow, Fintype.card (κ (Q.tgt e)) * Fintype.card (ι (Q.src e)) := by
  rw [Module.finrank_pi_fintype]
  simp [Module.finrank_matrix]

/-- Rank–nullity for the Ringel map. -/
theorem homDim_add_ringelRank (V : Q.Rep K ι) (W : Q.Rep K κ) :
    Q.homDim V W + Q.ringelRank V W = ∑ p, Fintype.card (κ p) * Fintype.card (ι p) := by
  rw [← Q.finrank_vertexHom (K := K) (ι := ι) (κ := κ), homDim, ringelRank, add_comm,
    LinearMap.finrank_range_add_finrank_ker]

theorem extDim_add_ringelRank (V : Q.Rep K ι) (W : Q.Rep K κ) :
    Q.extDim V W + Q.ringelRank V W =
      ∑ e : Q.Arrow, Fintype.card (κ (Q.tgt e)) * Fintype.card (ι (Q.src e)) := by
  rw [← Q.finrank_arrowHom (K := K) (ι := ι) (κ := κ), extDim, ringelRank,
    Submodule.finrank_quotient_add_finrank]

/-- **The Euler identity** `hom(V, W) − ext(V, W) = ⟨dim V, dim W⟩`. -/
theorem homDim_sub_extDim (V : Q.Rep K ι) (W : Q.Rep K κ) :
    (Q.homDim V W : ℤ) - Q.extDim V W =
      Q.euler (fun p => (Fintype.card (ι p) : ℤ)) fun p => (Fintype.card (κ p) : ℤ) := by
  have h₁ := Q.homDim_add_ringelRank V W
  have h₂ := Q.extDim_add_ringelRank V W
  have h₁' : (Q.homDim V W : ℤ) = ∑ p, (Fintype.card (κ p) : ℤ) * Fintype.card (ι p) -
      Q.ringelRank V W := by
    rw [eq_sub_iff_add_eq]
    exact_mod_cast h₁
  have h₂' : (Q.extDim V W : ℤ) = ∑ e : Q.Arrow,
      (Fintype.card (κ (Q.tgt e)) : ℤ) * Fintype.card (ι (Q.src e)) - Q.ringelRank V W := by
    rw [eq_sub_iff_add_eq]
    exact_mod_cast h₂
  rw [h₁', h₂', euler]
  simp only [mul_comm]
  ring

theorem extDim_eq_homDim_sub_euler (V : Q.Rep K ι) (W : Q.Rep K κ) :
    (Q.extDim V W : ℤ) = Q.homDim V W -
      Q.euler (fun p => (Fintype.card (ι p) : ℤ)) fun p => (Fintype.card (κ p) : ℤ) := by
  rw [← Q.homDim_sub_extDim V W]
  ring

/-- For pairs on the same vertex families, `hom` and `ext` change together. -/
theorem extDim_le_extDim_iff (V V' : Q.Rep K ι) (W W' : Q.Rep K κ) :
    Q.extDim V W ≤ Q.extDim V' W' ↔ Q.homDim V W ≤ Q.homDim V' W' := by
  have h := Q.extDim_eq_homDim_sub_euler V W
  have h' := Q.extDim_eq_homDim_sub_euler V' W'
  omega

/-- For pairs on the same vertex families, a smaller `hom` means a larger rank. -/
theorem homDim_le_homDim_iff (V V' : Q.Rep K ι) (W W' : Q.Rep K κ) :
    Q.homDim V W ≤ Q.homDim V' W' ↔ Q.ringelRank V' W' ≤ Q.ringelRank V W := by
  have h := Q.homDim_add_ringelRank V W
  have h' := Q.homDim_add_ringelRank V' W'
  omega

variable [∀ p, DecidableEq (ι p)] [∀ p, DecidableEq (κ p)]

/-- The rank of the Ringel matrix is the rank of the Ringel map. -/
theorem rank_ringelMatrix (V : Q.Rep K ι) (W : Q.Rep K κ) :
    (Q.ringelMatrix V W).rank = Q.ringelRank V W := by
  rw [Matrix.rank, ← Matrix.toLin'_apply', toLin'_ringelMatrix, ringelRank,
    LinearMap.range_comp, LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)]
  exact LinearEquiv.finrank_map_eq _ _

/-! ### Invariance under changes of coordinates -/

variable {ι' κ' : Fin Q.s → Type} [∀ p, Fintype (ι' p)] [∀ p, DecidableEq (ι' p)]
  [∀ p, Fintype (κ' p)] [∀ p, DecidableEq (κ' p)]

/-- **Conjugation of the Ringel map.** Changing coordinates on both sides conjugates the Ringel
map by the corresponding conjugations of vertex and arrow data. -/
theorem ringel_transport {R : Type*} [CommRing R] {ι κ ι' κ' : Fin Q.s → Type}
    [∀ p, Fintype (ι p)] [∀ p, DecidableEq (ι p)] [∀ p, Fintype (κ p)] [∀ p, DecidableEq (κ p)]
    [∀ p, Fintype (ι' p)] [∀ p, DecidableEq (ι' p)] [∀ p, Fintype (κ' p)]
    [∀ p, DecidableEq (κ' p)] (P : VertexIso R ι ι') (P' : VertexIso R κ κ') (V : Q.Rep R ι)
    (W : Q.Rep R κ) :
    Q.ringel (Q.transport P V) (Q.transport P' W) =
      (Q.arrowConj P P').toLinearMap ∘ₗ Q.ringel V W ∘ₗ (vertexConj P P').symm.toLinearMap := by
  refine LinearMap.ext fun ψ => funext fun e => ?_
  have h₁ : ∀ p (M : Matrix (κ' p) (ι' (Q.src e)) R), P'.hom p * (P'.inv p * M) = M :=
    fun p M => by rw [← Matrix.mul_assoc, P'.hom_mul_inv, Matrix.one_mul]
  simp only [ringel_apply, transport_apply, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply, vertexConj_symm_apply, arrowConj_apply, Matrix.mul_sub,
    Matrix.sub_mul, Matrix.mul_assoc, P.hom_mul_inv, Matrix.mul_one, h₁]

theorem ringelRank_transport (P : VertexIso K ι ι') (P' : VertexIso K κ κ') (V : Q.Rep K ι)
    (W : Q.Rep K κ) :
    Q.ringelRank (Q.transport P V) (Q.transport P' W) = Q.ringelRank V W := by
  rw [ringelRank, ringel_transport, LinearMap.range_comp,
    LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)]
  exact LinearEquiv.finrank_map_eq _ _

theorem homDim_transport (P : VertexIso K ι ι') (P' : VertexIso K κ κ') (V : Q.Rep K ι)
    (W : Q.Rep K κ) :
    Q.homDim (Q.transport P V) (Q.transport P' W) = Q.homDim V W := by
  have h := Q.homDim_add_ringelRank V W
  have h' := Q.homDim_add_ringelRank (Q.transport P V) (Q.transport P' W)
  rw [ringelRank_transport] at h'
  have hs : ∑ p, Fintype.card (κ' p) * Fintype.card (ι' p) =
      ∑ p, Fintype.card (κ p) * Fintype.card (ι p) := by
    simp only [P.card_eq, P'.card_eq]
  omega

theorem extDim_transport (P : VertexIso K ι ι') (P' : VertexIso K κ κ') (V : Q.Rep K ι)
    (W : Q.Rep K κ) :
    Q.extDim (Q.transport P V) (Q.transport P' W) = Q.extDim V W := by
  have h := Q.extDim_add_ringelRank V W
  have h' := Q.extDim_add_ringelRank (Q.transport P V) (Q.transport P' W)
  rw [ringelRank_transport] at h'
  have hs : ∑ e : Q.Arrow, Fintype.card (κ' (Q.tgt e)) * Fintype.card (ι' (Q.src e)) =
      ∑ e : Q.Arrow, Fintype.card (κ (Q.tgt e)) * Fintype.card (ι (Q.src e)) := by
    simp only [P.card_eq, P'.card_eq]
  omega

theorem homDim_act (g : GLFamily K ι) (h : GLFamily K κ) (V : Q.Rep K ι) (W : Q.Rep K κ) :
    Q.homDim (Q.act g V) (Q.act h W) = Q.homDim V W :=
  Q.homDim_transport (VertexIso.ofGL g) (VertexIso.ofGL h) V W

theorem extDim_act (g : GLFamily K ι) (h : GLFamily K κ) (V : Q.Rep K ι) (W : Q.Rep K κ) :
    Q.extDim (Q.act g V) (Q.act h W) = Q.extDim V W :=
  Q.extDim_transport (VertexIso.ofGL g) (VertexIso.ofGL h) V W

end Dimensions

/-! ### Kernels and images of homomorphisms -/

section KerRange

variable {K : Type*} [Field K] {ι κ : Fin Q.s → Type} [∀ p, Fintype (ι p)]
  [∀ p, Fintype (κ p)]

/-- The kernel of a homomorphism is a subrepresentation of its source. -/
theorem isSubrep_ker {V : Q.Rep K ι} {W : Q.Rep K κ} {φ : VertexHom K ι κ}
    (hφ : φ ∈ LinearMap.ker (Q.ringel V W)) :
    Q.IsSubrep V fun p => LinearMap.ker (φ p).mulVecLin := by
  intro e v hv
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv ⊢
  rw [Matrix.mulVec_mulVec, ← (Q.mem_ker_ringel.mp hφ e), ← Matrix.mulVec_mulVec, hv,
    Matrix.mulVec_zero]

/-- The image of a homomorphism is a subrepresentation of its target. -/
theorem isSubrep_range {V : Q.Rep K ι} {W : Q.Rep K κ} {φ : VertexHom K ι κ}
    (hφ : φ ∈ LinearMap.ker (Q.ringel V W)) :
    Q.IsSubrep W fun p => LinearMap.range (φ p).mulVecLin := by
  intro e w hw
  obtain ⟨v, rfl⟩ := hw
  refine ⟨V e *ᵥ v, ?_⟩
  rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec,
    ← (Q.mem_ker_ringel.mp hφ e), Matrix.mulVec_mulVec]

end KerRange

/-! ### Block exactness -/

section Block

variable {K : Type*} [Field K] {ι κ₁ κ₂ : Fin Q.s → Type}

/-- The second-block rows of arrow data with values in `κ₁ ⊕ κ₂`. -/
def arrowInr : Q.ArrowHom K ι (fun p => κ₁ p ⊕ κ₂ p) →ₗ[K] Q.ArrowHom K ι κ₂ where
  toFun X e := (X e).submatrix Sum.inr id
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Arrow data with values in the first block `κ₁` of `κ₁ ⊕ κ₂`. -/
def arrowInl : Q.ArrowHom K ι κ₁ →ₗ[K] Q.ArrowHom K ι (fun p => κ₁ p ⊕ κ₂ p) where
  toFun ξ e := Matrix.fromRows (ξ e) 0
  map_add' ξ ξ' := funext fun e => by
    ext (j | j) i <;> simp
  map_smul' c ξ := funext fun e => by
    ext (j | j) i <;> simp

/-- The second-block rows of vertex data with values in `κ₁ ⊕ κ₂`. -/
def vertexInr : VertexHom K ι (fun p => κ₁ p ⊕ κ₂ p) →ₗ[K] VertexHom K ι κ₂ where
  toFun ψ p := (ψ p).submatrix Sum.inr id
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem vertexInr_apply (ψ : VertexHom K ι (fun p => κ₁ p ⊕ κ₂ p)) (p : Fin Q.s)
    (j : κ₂ p) (i : ι p) : Q.vertexInr ψ p j i = ψ p (Sum.inr j) i :=
  rfl

@[simp] theorem arrowInr_apply (X : Q.ArrowHom K ι (fun p => κ₁ p ⊕ κ₂ p)) (e : Q.Arrow)
    (j : κ₂ (Q.tgt e)) (i : ι (Q.src e)) : Q.arrowInr X e j i = X e (Sum.inr j) i :=
  rfl

@[simp] theorem arrowInl_apply_inl (ξ : Q.ArrowHom K ι κ₁) (e : Q.Arrow) (j : κ₁ (Q.tgt e))
    (i : ι (Q.src e)) :
    (Q.arrowInl (κ₂ := κ₂) ξ) e (Sum.inl j) i = ξ e j i :=
  rfl

@[simp] theorem arrowInl_apply_inr (ξ : Q.ArrowHom K ι κ₁) (e : Q.Arrow) (j : κ₂ (Q.tgt e))
    (i : ι (Q.src e)) : (Q.arrowInl (κ₂ := κ₂) ξ) e (Sum.inr j) i = 0 :=
  rfl

theorem arrowInr_surjective : Function.Surjective (Q.arrowInr (K := K) (ι := ι) (κ₁ := κ₁)
    (κ₂ := κ₂)) := fun X =>
  ⟨fun e => Matrix.fromRows 0 (X e), rfl⟩

theorem vertexInr_surjective : Function.Surjective (vertexInr (K := K) (ι := ι) (κ₁ := κ₁)
    (κ₂ := κ₂)) := fun ψ =>
  ⟨fun p => Matrix.fromRows 0 (ψ p), rfl⟩

/-- Arrow data with vanishing second-block rows come from the first block. -/
theorem exists_arrowInl_of_arrowInr_eq_zero {X : Q.ArrowHom K ι (fun p => κ₁ p ⊕ κ₂ p)}
    (hX : Q.arrowInr X = 0) : ∃ ξ, Q.arrowInl ξ = X := by
  refine ⟨fun e => (X e).submatrix Sum.inl id, funext fun e => ?_⟩
  ext (j | j) i
  · rfl
  · have := congrFun (congrFun (congrFun hX e) j) i
    simp only [arrowInr_apply, Pi.zero_apply, Matrix.zero_apply] at this
    rw [arrowInl_apply_inr, this]

variable [∀ p, Fintype (ι p)] [∀ p, Fintype (κ₁ p)] [∀ p, Fintype (κ₂ p)]

/-- The second-block rows of the Ringel map of a block upper-triangular representation are the
Ringel map of its quotient. -/
theorem arrowInr_ringel_blockRep (V : Q.Rep K ι) (A : Q.Rep K κ₁) (y : Q.ArrowHom K κ₂ κ₁)
    (C : Q.Rep K κ₂) (ψ : VertexHom K ι (fun p => κ₁ p ⊕ κ₂ p)) :
    Q.arrowInr (Q.ringel V (Q.blockRep A y C) ψ) = Q.ringel V C (Q.vertexInr ψ) := by
  funext e
  ext j i
  simp [arrowInr_apply, vertexInr_apply, Matrix.mul_apply, Fintype.sum_sum_type,
    Matrix.sub_apply]

/-- **Block exactness, surjectivity.** For `W = [[A, y], [0, C]]`, the projection to the
quotient `C` induces a surjection `coker d_{V,W} → coker d_{V,C}`; in particular
`ext(V, C) ≤ ext(V, W)`. -/
theorem extDim_le_extDim_blockRep (V : Q.Rep K ι) (A : Q.Rep K κ₁) (y : Q.ArrowHom K κ₂ κ₁)
    (C : Q.Rep K κ₂) : Q.extDim V C ≤ Q.extDim V (Q.blockRep A y C) := by
  set g := (LinearMap.range (Q.ringel V C)).mkQ ∘ₗ Q.arrowInr (κ₁ := κ₁)
  have hg : Function.Surjective g :=
    (Submodule.mkQ_surjective _).comp (Q.arrowInr_surjective)
  have hle : LinearMap.range (Q.ringel V (Q.blockRep A y C)) ≤ LinearMap.ker g := by
    rintro _ ⟨ψ, rfl⟩
    simp only [g, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, arrowInr_ringel_blockRep]
    exact LinearMap.mem_range_self _ _
  have h₁ := LinearMap.finrank_range_add_finrank_ker g
  rw [LinearMap.range_eq_top.mpr hg, finrank_top] at h₁
  have h₂ := Submodule.finrank_mono hle
  have h₃ := (LinearMap.range (Q.ringel V (Q.blockRep A y C))).finrank_quotient_add_finrank
  unfold extDim
  omega

/-- **Block exactness, injectivity.** For `W = [[A, y], [0, C]]`, if every arrow datum with
values in the first block lies in the image of `d_{V,W}`, then
`coker d_{V,W} → coker d_{V,C}` is an isomorphism, so `ext(V, W) = ext(V, C)`. -/
theorem extDim_blockRep_eq_of_forall (V : Q.Rep K ι) (A : Q.Rep K κ₁)
    (y : Q.ArrowHom K κ₂ κ₁) (C : Q.Rep K κ₂)
    (h : ∀ ξ : Q.ArrowHom K ι κ₁,
      Q.arrowInl (κ₂ := κ₂) ξ ∈ LinearMap.range (Q.ringel V (Q.blockRep A y C))) :
    Q.extDim V (Q.blockRep A y C) = Q.extDim V C := by
  set g := (LinearMap.range (Q.ringel V C)).mkQ ∘ₗ Q.arrowInr (κ₁ := κ₁)
  have hg : Function.Surjective g :=
    (Submodule.mkQ_surjective _).comp (Q.arrowInr_surjective)
  have heq : LinearMap.ker g = LinearMap.range (Q.ringel V (Q.blockRep A y C)) := by
    apply le_antisymm
    · intro X hX
      simp only [g, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero] at hX
      obtain ⟨ψ₂, hψ₂⟩ := hX
      obtain ⟨ψ, rfl⟩ := Q.vertexInr_surjective (K := K) (κ₁ := κ₁) ψ₂
      have hbot : Q.arrowInr (X - Q.ringel V (Q.blockRep A y C) ψ) = 0 := by
        rw [map_sub, arrowInr_ringel_blockRep, hψ₂, sub_self]
      obtain ⟨ξ, hξ⟩ := Q.exists_arrowInl_of_arrowInr_eq_zero hbot
      have hX : X = Q.arrowInl ξ + Q.ringel V (Q.blockRep A y C) ψ := by
        rw [hξ, sub_add_cancel]
      rw [hX]
      exact add_mem (h ξ) (LinearMap.mem_range_self _ _)
    · rintro _ ⟨ψ, rfl⟩
      simp only [g, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero, arrowInr_ringel_blockRep]
      exact LinearMap.mem_range_self _ _
  have h₁ := LinearMap.finrank_range_add_finrank_ker g
  rw [LinearMap.range_eq_top.mpr hg, finrank_top, heq] at h₁
  have h₃ := (LinearMap.range (Q.ringel V (Q.blockRep A y C))).finrank_quotient_add_finrank
  unfold extDim
  omega

end Block

end FQuiver

end

end QuiverInvariants
