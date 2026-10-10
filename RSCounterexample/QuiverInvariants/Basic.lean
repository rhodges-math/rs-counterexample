import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Projection
import RSCounterexample.QuiverInvariants.Generic

/-!
# Representations of forward quivers

A *forward quiver* is a finite quiver whose vertices `0, …, s − 1` are listed in a topological
order, so that every arrow `p → q` has `p < q`. Parallel arrows are allowed. Every quiver without
oriented cycles is of this form.

Representations live on *typed vertex families* `ι : Fin s → Type`: the vertex `p` carries the
coordinate space `R^{ι p}`, and an arrow `e : p → q` carries a matrix with rows indexed by `ι q`
and columns indexed by `ι p`. Index types, rather than dimension vectors, make block
decompositions `R^{ι₁ p ⊕ ι₂ p}` available without arithmetic on dimensions.

## Main definitions

* `QuiverInvariants.FQuiver`: forward quivers; `FQuiver.Arrow`, `FQuiver.src`, `FQuiver.tgt`.
* `QuiverInvariants.VertexHom R ι κ`, `FQuiver.ArrowHom R ι κ`: the spaces
  `⊕_p Hom(R^{ι p}, R^{κ p})` and `⊕_{e : p → q} Hom(R^{ι p}, R^{κ q})`. The representations on
  `ι` are `FQuiver.Rep R ι = ArrowHom R ι ι`.
* `FQuiver.Entry`, `FQuiver.coord`: the coordinates of a representation, and
  `FQuiver.univRep`, the representation whose entries are the coordinate variables.
* `QuiverInvariants.GLFamily R ι`, `FQuiver.act`: the group `∏_p GL(R^{ι p})` and its action
  `(g · V)_e = g_q V_e g_p⁻¹` for `e : p → q`.
* `QuiverInvariants.chi`, `FQuiver.IsSemiInvariant`: the character `χ_σ(g) = ∏_p det(g_p)^{σ_p}`
  and the semi-invariants of weight `σ`, the polynomials with `f(g · V) = χ_σ(g)⁻¹ f(V)`.
* `FQuiver.euler`: the Euler form `⟨α, β⟩ = ∑_p α_p β_p − ∑_{e : p → q} α_p β_q`.
* `QuiverInvariants.VertexIso R ι κ`, `FQuiver.transport`: families of invertible matrices and
  the change of coordinates they induce on representations. Both the group action
  (`FQuiver.act_eq_transport`) and reindexing (`VertexIso.ofEquiv`) are special cases.
* `FQuiver.blockRep A y C`: the block upper-triangular representation `[[A, y], [0, C]]` on
  `ι₁ ⊕ ι₂`, with subrepresentation `A` and quotient `C`.
* `FQuiver.IsSubrep`, `FQuiver.HasSubrepOfDim`, `FQuiver.HasQuotientOfDim`: subrepresentations,
  given by subspaces of the vertex spaces, and the dimensions of subrepresentations and quotients.
* `FQuiver.GeneralSub K ι γ`, `FQuiver.GeneralQuot K ι β`: a general representation on `ι` has a
  subrepresentation of dimension `γ` (a quotient of dimension `β`), in the sense that the
  representations which have one form a Zariski-dense set. Schofield's relations `γ ↪ α` and
  `α ↠ β` ask for this of every representation; the density form is the one used here.

## Main results

* `FQuiver.act_one`, `FQuiver.act_mul`: `act` is an action.
* `FQuiver.IsSubrep.exists_transport_eq_blockRep`: a representation with a subrepresentation is
  conjugate to a block upper-triangular one.
* `FQuiver.generalSub_iff_of_vertexIso`, `FQuiver.generalQuot_iff_of_vertexIso`: the relations
  depend only on the vertex families up to isomorphism.
-/

open Matrix MvPolynomial

namespace QuiverInvariants

noncomputable section

/-! ### Forward quivers -/

/-- A **forward quiver**: a quiver without oriented cycles whose vertices `0, …, s − 1` are listed
in a topological order. `arrows p q` is the number of arrows `p → q`; parallel arrows are allowed
and are distinct. -/
structure FQuiver where
  /-- The number of vertices. -/
  s : ℕ
  /-- The number of arrows `p → q`. -/
  arrows : Fin s → Fin s → ℕ
  /-- Every arrow points forward. -/
  forward : ∀ p q, arrows p q ≠ 0 → p < q

namespace FQuiver

variable (Q : FQuiver)

/-- The arrows of `Q`: an arrow is a pair of vertices `(p, q)` together with an index among the
parallel arrows `p → q`. -/
abbrev Arrow : Type := Σ pq : Fin Q.s × Fin Q.s, Fin (Q.arrows pq.1 pq.2)

/-- The source of an arrow. -/
def src (e : Q.Arrow) : Fin Q.s := e.1.1

/-- The target of an arrow. -/
def tgt (e : Q.Arrow) : Fin Q.s := e.1.2

theorem src_lt_tgt (e : Q.Arrow) : Q.src e < Q.tgt e :=
  Q.forward _ _ fun h => Fin.elim0 (h ▸ e.2)

theorem src_ne_tgt (e : Q.Arrow) : Q.src e ≠ Q.tgt e :=
  (Q.src_lt_tgt e).ne

end FQuiver

/-! ### Linear maps between coordinate spaces are polynomial -/

/-- A linear map between coordinate spaces is a polynomial map. -/
theorem isPolynomialMap_linearMap {K : Type*} [CommRing K] {σ τ : Type*} [Fintype τ]
    (L : (τ → K) →ₗ[K] (σ → K)) : IsPolynomialMap L := by
  classical
  intro s
  refine ⟨∑ t, MvPolynomial.C (L (fun t' => if t = t' then 1 else 0) s) * MvPolynomial.X t,
    fun x => ?_⟩
  rw [L.pi_apply_eq_sum_univ x]
  simp [mul_comm]

/-! ### Vertex families -/

section VertexFamily

variable (R : Type*) {s : ℕ} (ι κ : Fin s → Type)

/-- The space `⊕_p Hom(R^{ι p}, R^{κ p})`, one matrix per vertex. -/
abbrev VertexHom : Type _ := (p : Fin s) → Matrix (κ p) (ι p) R

/-- The coordinates of `VertexHom R ι κ`: `⟨p, (i, j)⟩` is the entry `(j, i)` of the matrix at
`p`. -/
abbrev VertexEntry : Type := Σ p : Fin s, ι p × κ p

/-- The dimension vector of a vertex family. -/
def dimVec [∀ p, Fintype (ι p)] : Fin s → ℕ := fun p => Fintype.card (ι p)

@[simp] theorem dimVec_apply [∀ p, Fintype (ι p)] (p : Fin s) :
    dimVec ι p = Fintype.card (ι p) :=
  rfl

/-- The standard vertex family `p ↦ Fin (n p)` of a dimension vector. -/
abbrev finFam (n : Fin s → ℕ) : Fin s → Type := fun p => Fin (n p)

@[simp] theorem dimVec_finFam (n : Fin s → ℕ) : dimVec (finFam n) = n :=
  funext fun p => Fintype.card_fin (n p)

variable [∀ p, Fintype (ι p)] [∀ p, DecidableEq (ι p)]

/-- The group `∏_p GL(R^{ι p})`. -/
abbrev GLFamily [CommRing R] : Type _ := (p : Fin s) → GL (ι p) R

variable {R ι}

/-- The character `χ_σ(g) = ∏_p det(g_p)^{σ_p}` of `GLFamily R ι`. -/
def chi [CommRing R] (σ : Fin s → ℤ) (g : GLFamily R ι) : Rˣ :=
  ∏ p, Matrix.GeneralLinearGroup.det (g p) ^ σ p

@[simp] theorem chi_one [CommRing R] (σ : Fin s → ℤ) : chi σ (1 : GLFamily R ι) = 1 := by
  simp [chi]

theorem chi_mul [CommRing R] (σ : Fin s → ℤ) (g h : GLFamily R ι) :
    chi σ (g * h) = chi σ g * chi σ h := by
  simp only [chi, Pi.mul_apply, map_mul, mul_zpow, Finset.prod_mul_distrib]

theorem chi_add [CommRing R] (σ τ : Fin s → ℤ) (g : GLFamily R ι) :
    chi (σ + τ) g = chi σ g * chi τ g := by
  simp only [chi, Pi.add_apply, zpow_add, Finset.prod_mul_distrib]

theorem chi_nsmul [CommRing R] (N : ℕ) (σ : Fin s → ℤ) (g : GLFamily R ι) :
    chi (N • σ) g = chi σ g ^ N := by
  simp only [chi, Pi.smul_apply, nsmul_eq_mul, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [← zpow_natCast, ← zpow_mul, mul_comm]

end VertexFamily

/-! ### Families of isomorphisms between vertex spaces -/

section VertexIso

variable (R : Type*) [CommRing R] {s : ℕ}

/-- A family of isomorphisms `R^{ι p} ≅ R^{κ p}`, one for each vertex, given by matrices and their
inverses. -/
structure VertexIso (ι κ : Fin s → Type) [∀ p, Fintype (ι p)] [∀ p, DecidableEq (ι p)]
    [∀ p, Fintype (κ p)] [∀ p, DecidableEq (κ p)] where
  /-- The matrix of the isomorphism at each vertex. -/
  hom : (p : Fin s) → Matrix (κ p) (ι p) R
  /-- The matrix of the inverse isomorphism at each vertex. -/
  inv : (p : Fin s) → Matrix (ι p) (κ p) R
  hom_mul_inv : ∀ p, hom p * inv p = 1
  inv_mul_hom : ∀ p, inv p * hom p = 1

namespace VertexIso

variable {R} {ι κ μ : Fin s → Type} [∀ p, Fintype (ι p)] [∀ p, DecidableEq (ι p)]
  [∀ p, Fintype (κ p)] [∀ p, DecidableEq (κ p)] [∀ p, Fintype (μ p)] [∀ p, DecidableEq (μ p)]

variable (R ι) in
/-- The identity family. -/
def refl : VertexIso R ι ι where
  hom _ := 1
  inv _ := 1
  hom_mul_inv _ := Matrix.one_mul 1
  inv_mul_hom _ := Matrix.one_mul 1

/-- The inverse family. -/
def symm (P : VertexIso R ι κ) : VertexIso R κ ι where
  hom := P.inv
  inv := P.hom
  hom_mul_inv := P.inv_mul_hom
  inv_mul_hom := P.hom_mul_inv

/-- The composite family: first `P`, then `P'`. -/
def trans (P : VertexIso R ι κ) (P' : VertexIso R κ μ) : VertexIso R ι μ where
  hom p := P'.hom p * P.hom p
  inv p := P.inv p * P'.inv p
  hom_mul_inv p := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (P.hom p), P.hom_mul_inv, Matrix.one_mul,
      P'.hom_mul_inv]
  inv_mul_hom p := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (P'.inv p), P'.inv_mul_hom, Matrix.one_mul,
      P.inv_mul_hom]

@[simp] theorem symm_hom (P : VertexIso R ι κ) (p : Fin s) : P.symm.hom p = P.inv p := rfl

@[simp] theorem symm_inv (P : VertexIso R ι κ) (p : Fin s) : P.symm.inv p = P.hom p := rfl

@[simp] theorem trans_hom (P : VertexIso R ι κ) (P' : VertexIso R κ μ) (p : Fin s) :
    (P.trans P').hom p = P'.hom p * P.hom p := rfl

@[simp] theorem trans_inv (P : VertexIso R ι κ) (P' : VertexIso R κ μ) (p : Fin s) :
    (P.trans P').inv p = P.inv p * P'.inv p := rfl

@[simp] theorem refl_hom (p : Fin s) : (refl R ι).hom p = 1 := rfl

@[simp] theorem refl_inv (p : Fin s) : (refl R ι).inv p = 1 := rfl

/-- An element of `GLFamily R ι` as a family of isomorphisms. -/
def ofGL (g : GLFamily R ι) : VertexIso R ι ι where
  hom p := (g p : Matrix (ι p) (ι p) R)
  inv p := ((g p)⁻¹ : GL (ι p) R)
  hom_mul_inv p := (g p).mul_inv
  inv_mul_hom p := (g p).inv_mul

/-- A family of automorphisms as an element of `GLFamily R ι`. -/
def toGL (P : VertexIso R ι ι) : GLFamily R ι :=
  fun p => ⟨P.hom p, P.inv p, P.hom_mul_inv p, P.inv_mul_hom p⟩

@[simp] theorem ofGL_hom (g : GLFamily R ι) (p : Fin s) :
    (ofGL g).hom p = (g p : Matrix (ι p) (ι p) R) := rfl

@[simp] theorem ofGL_inv (g : GLFamily R ι) (p : Fin s) :
    (ofGL g).inv p = ((g p)⁻¹ : GL (ι p) R) := rfl

@[simp] theorem ofGL_toGL (P : VertexIso R ι ι) : ofGL P.toGL = P := rfl

@[simp] theorem toGL_ofGL (g : GLFamily R ι) : (ofGL g).toGL = g := rfl

/-- The family of permutation matrices of a family of bijections `ι p ≃ κ p`: reindexing. -/
def ofEquiv (σ : ∀ p, ι p ≃ κ p) : VertexIso R ι κ where
  hom p := (1 : Matrix (ι p) (ι p) R).submatrix (σ p).symm id
  inv p := (1 : Matrix (ι p) (ι p) R).submatrix id (σ p).symm
  hom_mul_inv p := by
    ext k k'
    simp [Matrix.mul_apply, Matrix.one_apply, eq_comm]
  inv_mul_hom p := by
    ext i i'
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, id, Matrix.one_apply]
    rw [(σ p).symm.sum_comp
      (fun k => (if i = k then (1 : R) else 0) * if k = i' then 1 else 0)]
    simp

theorem ofEquiv_hom_apply (σ : ∀ p, ι p ≃ κ p) (p : Fin s) (k : κ p) (i : ι p) :
    (ofEquiv (R := R) σ).hom p k i = if (σ p).symm k = i then 1 else 0 := by
  simp [ofEquiv, Matrix.one_apply]

theorem ofEquiv_inv_apply (σ : ∀ p, ι p ≃ κ p) (p : Fin s) (i : ι p) (k : κ p) :
    (ofEquiv (R := R) σ).inv p i k = if i = (σ p).symm k then 1 else 0 := by
  simp [ofEquiv, Matrix.one_apply]

/-- The matrices of a family `P` and of its inverse are inverse as linear maps. -/
theorem toLin'_inv_comp_hom (P : VertexIso R ι κ) (p : Fin s) :
    (Matrix.toLin' (P.inv p)).comp (Matrix.toLin' (P.hom p)) = LinearMap.id := by
  rw [← Matrix.toLin'_mul, P.inv_mul_hom, Matrix.toLin'_one]

theorem toLin'_hom_comp_inv (P : VertexIso R ι κ) (p : Fin s) :
    (Matrix.toLin' (P.hom p)).comp (Matrix.toLin' (P.inv p)) = LinearMap.id := by
  rw [← Matrix.toLin'_mul, P.hom_mul_inv, Matrix.toLin'_one]

/-- The linear isomorphism `R^{ι p} ≃ R^{κ p}` at a vertex. -/
def linearEquiv (P : VertexIso R ι κ) (p : Fin s) : (ι p → R) ≃ₗ[R] (κ p → R) :=
  LinearEquiv.ofLinearMap (Matrix.toLin' (P.hom p)) (Matrix.toLin' (P.inv p))
    (P.toLin'_hom_comp_inv p) (P.toLin'_inv_comp_hom p)

@[simp] theorem linearEquiv_apply (P : VertexIso R ι κ) (p : Fin s) (v : ι p → R) :
    P.linearEquiv p v = P.hom p *ᵥ v := rfl

@[simp] theorem linearEquiv_symm_apply (P : VertexIso R ι κ) (p : Fin s) (v : κ p → R) :
    (P.linearEquiv p).symm v = P.inv p *ᵥ v := rfl

/-- The block-diagonal family on `ι₁ ⊕ ι₂` made of two families. -/
def sum {ι₁ ι₂ κ₁ κ₂ : Fin s → Type} [∀ p, Fintype (ι₁ p)] [∀ p, DecidableEq (ι₁ p)]
    [∀ p, Fintype (ι₂ p)] [∀ p, DecidableEq (ι₂ p)] [∀ p, Fintype (κ₁ p)]
    [∀ p, DecidableEq (κ₁ p)] [∀ p, Fintype (κ₂ p)] [∀ p, DecidableEq (κ₂ p)]
    (P₁ : VertexIso R ι₁ κ₁) (P₂ : VertexIso R ι₂ κ₂) :
    VertexIso R (fun p => ι₁ p ⊕ ι₂ p) (fun p => κ₁ p ⊕ κ₂ p) where
  hom p := Matrix.fromBlocks (P₁.hom p) 0 0 (P₂.hom p)
  inv p := Matrix.fromBlocks (P₁.inv p) 0 0 (P₂.inv p)
  hom_mul_inv p := by
    rw [Matrix.fromBlocks_multiply]
    simp [P₁.hom_mul_inv, P₂.hom_mul_inv, Matrix.fromBlocks_one]
  inv_mul_hom p := by
    rw [Matrix.fromBlocks_multiply]
    simp [P₁.inv_mul_hom, P₂.inv_mul_hom, Matrix.fromBlocks_one]

section Field

variable {K : Type*} [Field K]

/-- Isomorphic vertex families have the same dimension vector. -/
theorem card_eq (P : VertexIso K ι κ) (p : Fin s) :
    Fintype.card (ι p) = Fintype.card (κ p) := by
  simpa using (P.linearEquiv p).finrank_eq

theorem dimVec_eq (P : VertexIso K ι κ) : dimVec ι = dimVec κ :=
  funext P.card_eq

/-- The family of isomorphisms that expresses coordinates in the bases `b p`: its inverse at
`p` is the matrix whose columns are the vectors of `b p`. -/
def ofBasis (b : ∀ p, Module.Basis (κ p) K (ι p → K)) : VertexIso K ι κ where
  hom p := (b p).toMatrix (Pi.basisFun K (ι p))
  inv p := (Pi.basisFun K (ι p)).toMatrix (b p)
  hom_mul_inv _ := Module.Basis.toMatrix_mul_toMatrix_flip _ _
  inv_mul_hom _ := Module.Basis.toMatrix_mul_toMatrix_flip _ _

theorem ofBasis_inv_apply (b : ∀ p, Module.Basis (κ p) K (ι p → K)) (p : Fin s) (i : ι p)
    (k : κ p) : (ofBasis b).inv p i k = b p k i := by
  simp [ofBasis, Module.Basis.toMatrix_apply]

theorem ofBasis_hom_mulVec (b : ∀ p, Module.Basis (κ p) K (ι p → K)) (p : Fin s)
    (v : ι p → K) : (ofBasis b).hom p *ᵥ v = (b p).repr v := by
  have h : ((Pi.basisFun K (ι p)).repr v : ι p → K) = v := funext fun i => by simp
  conv_lhs => rw [← h]
  exact Module.Basis.toMatrix_mulVec_repr _ _ v

end Field

end VertexIso

end VertexIso

namespace FQuiver

variable (Q : FQuiver)

/-! ### Arrow data and representations -/

section Arrows

variable (R : Type*) (ι κ : Fin Q.s → Type)

/-- The space `⊕_{e : p → q} Hom(R^{ι p}, R^{κ q})`, one matrix per arrow. -/
abbrev ArrowHom : Type _ := (e : Q.Arrow) → Matrix (κ (Q.tgt e)) (ι (Q.src e)) R

/-- The **representations** of `Q` on the vertex family `ι`: one matrix
`V_e : R^{ι p} → R^{ι q}` for each arrow `e : p → q`. -/
abbrev Rep : Type _ := Q.ArrowHom R ι ι

/-- The coordinates of `ArrowHom R ι κ`: `⟨e, (i, j)⟩` is the entry `(j, i)` of the matrix at
`e`, with `i` indexing the source space and `j` the target space. -/
abbrev ArrowEntry : Type := Σ e : Q.Arrow, ι (Q.src e) × κ (Q.tgt e)

/-- The coordinates of a representation on `ι`. -/
abbrev Entry : Type := Q.ArrowEntry ι ι

variable [CommRing R]

/-- The coordinates of arrow data, as a linear isomorphism. -/
def arrowCoord : Q.ArrowHom R ι κ ≃ₗ[R] (Q.ArrowEntry ι κ → R) where
  toFun X x := X x.1 x.2.2 x.2.1
  invFun c e j i := c ⟨e, (i, j)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem arrowCoord_apply (X : Q.ArrowHom R ι κ) (x : Q.ArrowEntry ι κ) :
    Q.arrowCoord R ι κ X x = X x.1 x.2.2 x.2.1 :=
  rfl

@[simp] theorem arrowCoord_symm_apply (c : Q.ArrowEntry ι κ → R) (e : Q.Arrow)
    (j : κ (Q.tgt e)) (i : ι (Q.src e)) : (Q.arrowCoord R ι κ).symm c e j i = c ⟨e, (i, j)⟩ :=
  rfl

variable {R ι κ}

/-- The coordinates of a representation: `coord V ⟨e, (i, j)⟩` is the entry `(j, i)` of
`V_e`. -/
def coord (V : Q.Rep R ι) : Q.Entry ι → R :=
  Q.arrowCoord R ι ι V

@[simp] theorem coord_apply (V : Q.Rep R ι) (x : Q.Entry ι) : Q.coord V x = V x.1 x.2.2 x.2.1 :=
  rfl

theorem coord_injective : Function.Injective (Q.coord : Q.Rep R ι → Q.Entry ι → R) :=
  (Q.arrowCoord R ι ι).injective

theorem coord_surjective : Function.Surjective (Q.coord : Q.Rep R ι → Q.Entry ι → R) :=
  (Q.arrowCoord R ι ι).surjective

@[simp] theorem coord_add (V W : Q.Rep R ι) : Q.coord (V + W) = Q.coord V + Q.coord W :=
  rfl

@[simp] theorem coord_smul (c : R) (V : Q.Rep R ι) : Q.coord (c • V) = c • Q.coord V :=
  rfl

@[simp] theorem coord_zero : Q.coord (0 : Q.Rep R ι) = 0 :=
  rfl

/-- The representation with given coordinates. -/
def ofCoord (x : Q.Entry ι → R) : Q.Rep R ι :=
  (Q.arrowCoord R ι ι).symm x

@[simp] theorem coord_ofCoord (x : Q.Entry ι → R) : Q.coord (Q.ofCoord x) = x :=
  rfl

@[simp] theorem ofCoord_coord (V : Q.Rep R ι) : Q.ofCoord (Q.coord V) = V :=
  rfl

/-- Changing the coefficient ring of arrow data along a ring homomorphism. -/
def mapArrowHom {S : Type*} [CommRing S] (f : R →+* S) (X : Q.ArrowHom R ι κ) :
    Q.ArrowHom S ι κ :=
  fun e => (X e).map f

@[simp] theorem mapArrowHom_apply {S : Type*} [CommRing S] (f : R →+* S)
    (X : Q.ArrowHom R ι κ) (e : Q.Arrow) : Q.mapArrowHom f X e = (X e).map f :=
  rfl

theorem arrowCoord_mapArrowHom {S : Type*} [CommRing S] (f : R →+* S) (X : Q.ArrowHom R ι κ) :
    Q.arrowCoord S ι κ (Q.mapArrowHom f X) = f ∘ Q.arrowCoord R ι κ X :=
  rfl

theorem coord_mapArrowHom {S : Type*} [CommRing S] (f : R →+* S) (V : Q.Rep R ι) :
    Q.coord (Q.mapArrowHom f V) = f ∘ Q.coord V :=
  rfl

variable (R ι κ)

/-- The **universal arrow data**: its entries are the coordinate variables, in the polynomial
ring over the coordinates. -/
def univArrowHom : Q.ArrowHom (MvPolynomial (Q.ArrowEntry ι κ) R) ι κ :=
  fun e j i => X ⟨e, (i, j)⟩

/-- The **universal representation** on `ι`: its entries are the coordinate variables. -/
abbrev univRep : Q.Rep (MvPolynomial (Q.Entry ι) R) ι :=
  Q.univArrowHom R ι ι

variable {R ι κ}

/-- Evaluating the universal arrow data at a point gives the arrow data with those
coordinates. -/
@[simp] theorem mapArrowHom_eval_univArrowHom (x : Q.ArrowEntry ι κ → R) :
    Q.mapArrowHom (eval x) (Q.univArrowHom R ι κ) = (Q.arrowCoord R ι κ).symm x := by
  funext e
  ext j i
  simp [univArrowHom]

@[simp] theorem mapArrowHom_eval_coord_univRep (V : Q.Rep R ι) :
    Q.mapArrowHom (eval (Q.coord V)) (Q.univRep R ι) = V :=
  Q.mapArrowHom_eval_univArrowHom (Q.coord V)

end Arrows

/-! ### The group action and semi-invariants -/

section Action

variable {R : Type*} [CommRing R] {ι κ : Fin Q.s → Type}
  [∀ p, Fintype (ι p)] [∀ p, DecidableEq (ι p)] [∀ p, Fintype (κ p)] [∀ p, DecidableEq (κ p)]

/-- **Conjugation of arrow data** by two families of isomorphisms:
`X_e ↦ P'_q X_e P_p⁻¹` for `e : p → q`. -/
def arrowConj {ι' κ' : Fin Q.s → Type} [∀ p, Fintype (ι' p)] [∀ p, DecidableEq (ι' p)]
    [∀ p, Fintype (κ' p)] [∀ p, DecidableEq (κ' p)] (P : VertexIso R ι ι')
    (P' : VertexIso R κ κ') : Q.ArrowHom R ι κ ≃ₗ[R] Q.ArrowHom R ι' κ' where
  toFun X e := P'.hom (Q.tgt e) * X e * P.inv (Q.src e)
  invFun X e := P'.inv (Q.tgt e) * X e * P.hom (Q.src e)
  map_add' X Y := funext fun e => by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := funext fun e => by simp [Matrix.mul_smul, Matrix.smul_mul]
  left_inv X := funext fun e => by
    simp only [← Matrix.mul_assoc, P'.inv_mul_hom, Matrix.one_mul]
    rw [Matrix.mul_assoc, P.inv_mul_hom, Matrix.mul_one]
  right_inv X := funext fun e => by
    simp only [← Matrix.mul_assoc, P'.hom_mul_inv, Matrix.one_mul]
    rw [Matrix.mul_assoc, P.hom_mul_inv, Matrix.mul_one]

@[simp] theorem arrowConj_apply {ι' κ' : Fin Q.s → Type} [∀ p, Fintype (ι' p)]
    [∀ p, DecidableEq (ι' p)] [∀ p, Fintype (κ' p)] [∀ p, DecidableEq (κ' p)]
    (P : VertexIso R ι ι') (P' : VertexIso R κ κ') (X : Q.ArrowHom R ι κ) (e : Q.Arrow) :
    Q.arrowConj P P' X e = P'.hom (Q.tgt e) * X e * P.inv (Q.src e) :=
  rfl

@[simp] theorem arrowConj_symm_apply {ι' κ' : Fin Q.s → Type} [∀ p, Fintype (ι' p)]
    [∀ p, DecidableEq (ι' p)] [∀ p, Fintype (κ' p)] [∀ p, DecidableEq (κ' p)]
    (P : VertexIso R ι ι') (P' : VertexIso R κ κ') (X : Q.ArrowHom R ι' κ') (e : Q.Arrow) :
    (Q.arrowConj P P').symm X e = P'.inv (Q.tgt e) * X e * P.hom (Q.src e) :=
  rfl

/-- **Change of coordinates** of a representation along a family of isomorphisms:
`(P · V)_e = P_q V_e P_p⁻¹` for `e : p → q`. -/
def transport (P : VertexIso R ι κ) (V : Q.Rep R ι) : Q.Rep R κ :=
  Q.arrowConj P P V

@[simp] theorem transport_apply (P : VertexIso R ι κ) (V : Q.Rep R ι) (e : Q.Arrow) :
    Q.transport P V e = P.hom (Q.tgt e) * V e * P.inv (Q.src e) :=
  rfl

@[simp] theorem transport_refl (V : Q.Rep R ι) : Q.transport (VertexIso.refl R ι) V = V :=
  funext fun e => by simp

theorem transport_trans {μ : Fin Q.s → Type} [∀ p, Fintype (μ p)] [∀ p, DecidableEq (μ p)]
    (P : VertexIso R ι κ) (P' : VertexIso R κ μ) (V : Q.Rep R ι) :
    Q.transport (P.trans P') V = Q.transport P' (Q.transport P V) :=
  funext fun e => by simp [Matrix.mul_assoc]

@[simp] theorem transport_symm_transport (P : VertexIso R ι κ) (V : Q.Rep R ι) :
    Q.transport P.symm (Q.transport P V) = V :=
  (Q.arrowConj P P).symm_apply_apply V

@[simp] theorem transport_transport_symm (P : VertexIso R ι κ) (V : Q.Rep R κ) :
    Q.transport P (Q.transport P.symm V) = V :=
  (Q.arrowConj P P).apply_symm_apply V

theorem transport_add (P : VertexIso R ι κ) (V W : Q.Rep R ι) :
    Q.transport P (V + W) = Q.transport P V + Q.transport P W :=
  map_add (Q.arrowConj P P) V W

theorem transport_smul (P : VertexIso R ι κ) (c : R) (V : Q.Rep R ι) :
    Q.transport P (c • V) = c • Q.transport P V :=
  map_smul (Q.arrowConj P P) c V

theorem transport_injective (P : VertexIso R ι κ) : Function.Injective (Q.transport P) :=
  (Q.arrowConj P P).injective

theorem transport_surjective (P : VertexIso R ι κ) : Function.Surjective (Q.transport P) :=
  (Q.arrowConj P P).surjective

/-- **The action of `GLFamily R ι`** on representations: `(g · V)_e = g_q V_e g_p⁻¹` for
`e : p → q`. -/
def act (g : GLFamily R ι) (V : Q.Rep R ι) : Q.Rep R ι :=
  fun e => (g (Q.tgt e) : Matrix _ _ R) * V e * (((g (Q.src e))⁻¹ : GL _ R) : Matrix _ _ R)

theorem act_apply (g : GLFamily R ι) (V : Q.Rep R ι) (e : Q.Arrow) :
    Q.act g V e =
      (g (Q.tgt e) : Matrix _ _ R) * V e * (((g (Q.src e))⁻¹ : GL _ R) : Matrix _ _ R) :=
  rfl

theorem act_eq_transport (g : GLFamily R ι) (V : Q.Rep R ι) :
    Q.act g V = Q.transport (VertexIso.ofGL g) V :=
  rfl

theorem transport_eq_act (P : VertexIso R ι ι) (V : Q.Rep R ι) :
    Q.transport P V = Q.act P.toGL V :=
  rfl

@[simp] theorem act_one (V : Q.Rep R ι) : Q.act 1 V = V :=
  funext fun e => by simp [act_apply]

theorem act_mul (g h : GLFamily R ι) (V : Q.Rep R ι) :
    Q.act (g * h) V = Q.act g (Q.act h V) :=
  funext fun e => by simp [act_apply, Matrix.mul_assoc]

@[simp] theorem act_inv_act (g : GLFamily R ι) (V : Q.Rep R ι) : Q.act g⁻¹ (Q.act g V) = V := by
  rw [← act_mul, inv_mul_cancel, act_one]

@[simp] theorem act_act_inv (g : GLFamily R ι) (V : Q.Rep R ι) : Q.act g (Q.act g⁻¹ V) = V := by
  rw [← act_mul, mul_inv_cancel, act_one]

theorem act_add (g : GLFamily R ι) (V W : Q.Rep R ι) :
    Q.act g (V + W) = Q.act g V + Q.act g W :=
  Q.transport_add (VertexIso.ofGL g) V W

theorem act_smul (g : GLFamily R ι) (c : R) (V : Q.Rep R ι) :
    Q.act g (c • V) = c • Q.act g V :=
  Q.transport_smul (VertexIso.ofGL g) c V

@[simp] theorem act_zero (g : GLFamily R ι) : Q.act g (0 : Q.Rep R ι) = 0 :=
  funext fun e => by simp [act_apply]

/-- A polynomial `f` in the coordinates of representations on `ι` is a **semi-invariant of
weight `σ`** when `f(g · V) = χ_σ(g)⁻¹ f(V)` for all `g` and `V`. -/
def IsSemiInvariant (σ : Fin Q.s → ℤ) (f : MvPolynomial (Q.Entry ι) R) : Prop :=
  ∀ (g : GLFamily R ι) (V : Q.Rep R ι),
    eval (Q.coord (Q.act g V)) f = ((chi σ g)⁻¹ : Rˣ) * eval (Q.coord V) f

end Action

/-! ### The Euler form -/

section Euler

/-- The **Euler form** `⟨α, β⟩ = ∑_p α_p β_p − ∑_{e : p → q} α_p β_q`. -/
def euler {A : Type*} [CommRing A] (α β : Fin Q.s → A) : A :=
  ∑ p, α p * β p - ∑ e : Q.Arrow, α (Q.src e) * β (Q.tgt e)

theorem euler_add_left {A : Type*} [CommRing A] (α α' β : Fin Q.s → A) :
    Q.euler (α + α') β = Q.euler α β + Q.euler α' β := by
  simp only [euler, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  ring

theorem euler_add_right {A : Type*} [CommRing A] (α β β' : Fin Q.s → A) :
    Q.euler α (β + β') = Q.euler α β + Q.euler α β' := by
  simp only [euler, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  ring

theorem euler_smul_left {A : Type*} [CommRing A] (c : A) (α β : Fin Q.s → A) :
    Q.euler (c • α) β = c * Q.euler α β := by
  simp only [euler, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, mul_sub]

theorem euler_smul_right {A : Type*} [CommRing A] (c : A) (α β : Fin Q.s → A) :
    Q.euler α (c • β) = c * Q.euler α β := by
  simp only [euler, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c, ← Finset.mul_sum, mul_sub]

theorem euler_map {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (α β : Fin Q.s → A) :
    f (Q.euler α β) = Q.euler (f ∘ α) (f ∘ β) := by
  simp [euler]

theorem euler_natCast {A : Type*} [CommRing A] (α β : Fin Q.s → ℕ) :
    ((Q.euler (fun p => (α p : ℤ)) fun p => (β p : ℤ) : ℤ) : A) =
      Q.euler (fun p => (α p : A)) fun p => (β p : A) := by
  simp [euler]

end Euler

/-! ### Block upper-triangular representations -/

section Block

variable {R : Type*} [CommRing R] {ι₁ ι₂ : Fin Q.s → Type}

/-- The **block upper-triangular representation** `[[A, y], [0, C]]` on `ι₁ ⊕ ι₂`. The first
block is a subrepresentation isomorphic to `A`, with quotient isomorphic to `C`. -/
def blockRep (A : Q.Rep R ι₁) (y : Q.ArrowHom R ι₂ ι₁) (C : Q.Rep R ι₂) :
    Q.Rep R (fun p => ι₁ p ⊕ ι₂ p) :=
  fun e => Matrix.fromBlocks (A e) (y e) 0 (C e)

@[simp] theorem blockRep_apply (A : Q.Rep R ι₁) (y : Q.ArrowHom R ι₂ ι₁) (C : Q.Rep R ι₂)
    (e : Q.Arrow) : Q.blockRep A y C e = Matrix.fromBlocks (A e) (y e) 0 (C e) :=
  rfl

theorem blockRep_injective {A A' : Q.Rep R ι₁} {y y' : Q.ArrowHom R ι₂ ι₁} {C C' : Q.Rep R ι₂}
    (h : Q.blockRep A y C = Q.blockRep A' y' C') : A = A' ∧ y = y' ∧ C = C' := by
  refine ⟨funext fun e => ?_, funext fun e => ?_, funext fun e => ?_⟩ <;>
  · have := (Matrix.fromBlocks_inj.mp (congrFun h e))
    tauto

/-- A block upper-triangular representation is block upper-triangular in its own blocks. -/
theorem blockRep_inr_inl (A : Q.Rep R ι₁) (y : Q.ArrowHom R ι₂ ι₁) (C : Q.Rep R ι₂)
    (e : Q.Arrow) (j : ι₂ (Q.tgt e)) (i : ι₁ (Q.src e)) :
    Q.blockRep A y C e (Sum.inr j) (Sum.inl i) = 0 :=
  rfl

end Block

/-! ### Subrepresentations and quotients -/

section Subrep

variable {K : Type*} [Field K] {ι κ : Fin Q.s → Type}
  [∀ p, Fintype (ι p)] [∀ p, DecidableEq (ι p)] [∀ p, Fintype (κ p)] [∀ p, DecidableEq (κ p)]

/-- A family of subspaces `S p ⊆ K^{ι p}` is a **subrepresentation** of `V` when every `V_e`
maps `S (src e)` into `S (tgt e)`. -/
def IsSubrep (V : Q.Rep K ι) (S : (p : Fin Q.s) → Submodule K (ι p → K)) : Prop :=
  ∀ e, ∀ v ∈ S (Q.src e), V e *ᵥ v ∈ S (Q.tgt e)

/-- `V` has a **subrepresentation of dimension `γ`**. -/
def HasSubrepOfDim (V : Q.Rep K ι) (γ : Fin Q.s → ℕ) : Prop :=
  ∃ S, Q.IsSubrep V S ∧ ∀ p, Module.finrank K (S p) = γ p

/-- `V` has a **quotient representation of dimension `β`**: a subrepresentation of dimension
`dim ι − β`. -/
def HasQuotientOfDim (V : Q.Rep K ι) (β : Fin Q.s → ℕ) : Prop :=
  ∃ S, Q.IsSubrep V S ∧ ∀ p, Module.finrank K (S p) + β p = Fintype.card (ι p)

omit [∀ p, DecidableEq (ι p)] in
theorem isSubrep_bot (V : Q.Rep K ι) : Q.IsSubrep V fun _ => ⊥ := fun e v hv => by
  rw [Submodule.mem_bot] at hv ⊢
  rw [hv, Matrix.mulVec_zero]

omit [∀ p, DecidableEq (ι p)] in
theorem isSubrep_top (V : Q.Rep K ι) : Q.IsSubrep V fun _ => ⊤ := fun _ _ _ =>
  Submodule.mem_top

omit [∀ p, DecidableEq (ι p)] in
/-- Every representation is a quotient of itself. -/
theorem hasQuotientOfDim_self (V : Q.Rep K ι) : Q.HasQuotientOfDim V (dimVec ι) :=
  ⟨_, Q.isSubrep_bot V, fun p => by simp⟩

omit [∀ p, DecidableEq (ι p)] in
/-- Every representation has the zero quotient. -/
theorem hasQuotientOfDim_zero (V : Q.Rep K ι) : Q.HasQuotientOfDim V 0 :=
  ⟨_, Q.isSubrep_top V, fun p => by simp⟩

omit [∀ p, DecidableEq (ι p)] in
theorem hasSubrepOfDim_iff_hasQuotientOfDim (V : Q.Rep K ι) {γ β : Fin Q.s → ℕ}
    (h : ∀ p, γ p + β p = Fintype.card (ι p)) :
    Q.HasSubrepOfDim V γ ↔ Q.HasQuotientOfDim V β := by
  constructor
  · rintro ⟨S, hS, hdim⟩
    exact ⟨S, hS, fun p => by rw [hdim, h]⟩
  · rintro ⟨S, hS, hdim⟩
    exact ⟨S, hS, fun p => by have := h p; have := hdim p; omega⟩

/-- The image of a subrepresentation under a change of coordinates. -/
theorem IsSubrep.transport {V : Q.Rep K ι} {S : (p : Fin Q.s) → Submodule K (ι p → K)}
    (hS : Q.IsSubrep V S) (P : VertexIso K ι κ) :
    Q.IsSubrep (Q.transport P V) fun p => (S p).map (Matrix.toLin' (P.hom p)) := by
  intro e w hw
  obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hw
  refine Submodule.mem_map.mpr ⟨V e *ᵥ v, hS e v hv, ?_⟩
  simp only [Matrix.toLin'_apply, transport_apply, Matrix.mulVec_mulVec, Matrix.mul_assoc,
    P.inv_mul_hom, Matrix.mul_one]

theorem finrank_map_toLin'_hom (P : VertexIso K ι κ) (p : Fin Q.s)
    (S : Submodule K (ι p → K)) :
    Module.finrank K (S.map (Matrix.toLin' (P.hom p))) = Module.finrank K S :=
  LinearEquiv.finrank_map_eq (P.linearEquiv p) S

theorem HasSubrepOfDim.transport {V : Q.Rep K ι} {γ : Fin Q.s → ℕ} (h : Q.HasSubrepOfDim V γ)
    (P : VertexIso K ι κ) : Q.HasSubrepOfDim (Q.transport P V) γ := by
  obtain ⟨S, hS, hdim⟩ := h
  exact ⟨_, hS.transport Q P, fun p => by rw [Q.finrank_map_toLin'_hom P p, hdim]⟩

theorem HasQuotientOfDim.transport {V : Q.Rep K ι} {β : Fin Q.s → ℕ}
    (h : Q.HasQuotientOfDim V β) (P : VertexIso K ι κ) :
    Q.HasQuotientOfDim (Q.transport P V) β := by
  obtain ⟨S, hS, hdim⟩ := h
  exact ⟨_, hS.transport Q P, fun p => by
    rw [Q.finrank_map_toLin'_hom P p, hdim, P.card_eq]⟩

theorem hasSubrepOfDim_transport_iff (P : VertexIso K ι κ) (V : Q.Rep K ι)
    (γ : Fin Q.s → ℕ) : Q.HasSubrepOfDim (Q.transport P V) γ ↔ Q.HasSubrepOfDim V γ :=
  ⟨fun h => by
    have h' := h.transport Q P.symm
    rwa [transport_symm_transport] at h', fun h => h.transport Q P⟩

theorem hasQuotientOfDim_transport_iff (P : VertexIso K ι κ) (V : Q.Rep K ι)
    (β : Fin Q.s → ℕ) : Q.HasQuotientOfDim (Q.transport P V) β ↔ Q.HasQuotientOfDim V β :=
  ⟨fun h => by
    have h' := h.transport Q P.symm
    rwa [transport_symm_transport] at h', fun h => h.transport Q P⟩

theorem hasSubrepOfDim_act_iff (g : GLFamily K ι) (V : Q.Rep K ι) (γ : Fin Q.s → ℕ) :
    Q.HasSubrepOfDim (Q.act g V) γ ↔ Q.HasSubrepOfDim V γ :=
  Q.hasSubrepOfDim_transport_iff (VertexIso.ofGL g) V γ

theorem hasQuotientOfDim_act_iff (g : GLFamily K ι) (V : Q.Rep K ι) (β : Fin Q.s → ℕ) :
    Q.HasQuotientOfDim (Q.act g V) β ↔ Q.HasQuotientOfDim V β :=
  Q.hasQuotientOfDim_transport_iff (VertexIso.ofGL g) V β

/-! #### Subrepresentations of block representations -/

variable {ι₁ ι₂ : Fin Q.s → Type} [∀ p, Fintype (ι₁ p)] [∀ p, Fintype (ι₂ p)]

/-- On the second block, a block upper-triangular representation acts as its quotient `C`. -/
theorem mulVec_blockRep_comp_inr (A : Q.Rep K ι₁) (y : Q.ArrowHom K ι₂ ι₁) (C : Q.Rep K ι₂)
    (e : Q.Arrow) (v : (ι₁ (Q.src e) ⊕ ι₂ (Q.src e)) → K) :
    (Q.blockRep A y C e *ᵥ v) ∘ Sum.inr = C e *ᵥ (v ∘ Sum.inr) := by
  funext j
  simp [Matrix.fromBlocks_mulVec]

/-- The preimage of a subrepresentation of the quotient `C` is a subrepresentation of the block
representation. -/
theorem IsSubrep.comap_inr (A : Q.Rep K ι₁) (y : Q.ArrowHom K ι₂ ι₁) {C : Q.Rep K ι₂}
    {S : (p : Fin Q.s) → Submodule K (ι₂ p → K)} (hS : Q.IsSubrep C S) :
    Q.IsSubrep (Q.blockRep A y C)
      fun p => (S p).comap (LinearMap.funLeft K K (Sum.inr : ι₂ p → ι₁ p ⊕ ι₂ p)) := by
  intro e v hv
  change (Q.blockRep A y C e *ᵥ v) ∘ Sum.inr ∈ S (Q.tgt e)
  rw [mulVec_blockRep_comp_inr]
  exact hS e _ hv

theorem finrank_comap_funLeft_inr {α β : Type*} [Fintype α] [Fintype β]
    (S : Submodule K (β → K)) :
    Module.finrank K (S.comap (LinearMap.funLeft K K (Sum.inr : β → α ⊕ β))) =
      Fintype.card α + Module.finrank K S := by
  set f := LinearMap.funLeft K K (Sum.inr : β → α ⊕ β)
  have hf : Function.Surjective f := LinearMap.funLeft_surjective_of_injective _ _ _
    Sum.inr_injective
  have hg : Function.Surjective (S.mkQ ∘ₗ f) :=
    (Submodule.mkQ_surjective S).comp hf
  have h₁ := LinearMap.finrank_range_add_finrank_ker (S.mkQ ∘ₗ f)
  rw [LinearMap.range_eq_top.mpr hg, finrank_top, LinearMap.ker_comp, Submodule.ker_mkQ] at h₁
  have h₂ := S.finrank_quotient_add_finrank
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_sum] at h₁ h₂
  omega

/-- A block upper-triangular representation has its first block as a subrepresentation. -/
theorem hasSubrepOfDim_blockRep (A : Q.Rep K ι₁) (y : Q.ArrowHom K ι₂ ι₁) (C : Q.Rep K ι₂) :
    Q.HasSubrepOfDim (Q.blockRep A y C) (dimVec ι₁) :=
  ⟨_, (Q.isSubrep_bot C).comap_inr Q A y, fun p => by
    rw [finrank_comap_funLeft_inr, finrank_bot, add_zero, dimVec_apply]⟩

/-- **Quotients of the quotient.** A quotient of `C` is a quotient of the block representation
`[[A, y], [0, C]]`. -/
theorem HasQuotientOfDim.blockRep {C : Q.Rep K ι₂} {β : Fin Q.s → ℕ}
    (h : Q.HasQuotientOfDim C β) (A : Q.Rep K ι₁) (y : Q.ArrowHom K ι₂ ι₁) :
    Q.HasQuotientOfDim (Q.blockRep A y C) β := by
  obtain ⟨S, hS, hdim⟩ := h
  refine ⟨_, hS.comap_inr Q A y, fun p => ?_⟩
  rw [finrank_comap_funLeft_inr, Fintype.card_sum, add_assoc, hdim]

/-- A basis of `E` indexed by `α ⊕ β` whose first block is a basis of a given subspace `S`. -/
theorem exists_basis_sum_of_finrank {E : Type*} [AddCommGroup E] [Module K E]
    [FiniteDimensional K E] (S : Submodule K E) (α β : Type*) [Fintype α] [Fintype β]
    (h₁ : Fintype.card α = Module.finrank K S)
    (h₂ : Fintype.card α + Fintype.card β = Module.finrank K E) :
    ∃ b : Module.Basis (α ⊕ β) K E, (∀ i, b (Sum.inl i) ∈ S) ∧
      ∀ w ∈ S, ∀ j, b.repr w (Sum.inr j) = 0 := by
  obtain ⟨T, hT⟩ := S.exists_isCompl
  have hTdim : Module.finrank K T = Fintype.card β := by
    have := Submodule.finrank_add_eq_of_isCompl hT
    omega
  let bS : Module.Basis α K S :=
    (Module.finBasisOfFinrankEq K S h₁.symm).reindex (Fintype.equivFin α).symm
  let bT : Module.Basis β K T :=
    (Module.finBasisOfFinrankEq K T hTdim).reindex (Fintype.equivFin β).symm
  refine ⟨(bS.prod bT).map (Submodule.prodEquivOfIsCompl S T hT), fun i => ?_, fun w hw j => ?_⟩
  · simp [Module.Basis.map_apply, Module.Basis.prod_apply]
  · rw [Module.Basis.map_repr, LinearEquiv.trans_apply,
      show w = ((⟨w, hw⟩ : S) : E) from rfl, Submodule.prodEquivOfIsCompl_symm_apply_left,
      Module.Basis.prod_repr_inr, map_zero, Finsupp.zero_apply]

variable [∀ p, DecidableEq (ι₁ p)] [∀ p, DecidableEq (ι₂ p)]

/-- **Block normal form.** If `S` is a subrepresentation of `V`, then in a suitable basis of
each vertex space, adapted to `S`, the representation `V` becomes block upper-triangular. The
blocks are indexed by any vertex families `ι₁`, `ι₂` of the dimensions of `S` and of the
quotient. -/
theorem IsSubrep.exists_transport_eq_blockRep {V : Q.Rep K ι}
    {S : (p : Fin Q.s) → Submodule K (ι p → K)} (hS : Q.IsSubrep V S)
    (h₁ : ∀ p, Fintype.card (ι₁ p) = Module.finrank K (S p))
    (h₂ : ∀ p, Fintype.card (ι₁ p) + Fintype.card (ι₂ p) = Fintype.card (ι p)) :
    ∃ (P : VertexIso K ι fun p => ι₁ p ⊕ ι₂ p) (A : Q.Rep K ι₁) (y : Q.ArrowHom K ι₂ ι₁)
      (C : Q.Rep K ι₂), Q.transport P V = Q.blockRep A y C := by
  have hb : ∀ p, ∃ b : Module.Basis (ι₁ p ⊕ ι₂ p) K (ι p → K), (∀ i, b (Sum.inl i) ∈ S p) ∧
      ∀ w ∈ S p, ∀ j, b.repr w (Sum.inr j) = 0 := fun p =>
    exists_basis_sum_of_finrank (S p) _ _ (h₁ p)
      (by rw [Module.finrank_fintype_fun_eq_card]; exact h₂ p)
  choose b hbS hbrepr using hb
  set P := VertexIso.ofBasis b
  have hzero : ∀ e (j : ι₂ (Q.tgt e)) (i : ι₁ (Q.src e)),
      Q.transport P V e (Sum.inr j) (Sum.inl i) = 0 := by
    intro e j i
    have hcol : (fun k => (V e * P.inv (Q.src e)) k (Sum.inl i)) =
        V e *ᵥ b (Q.src e) (Sum.inl i) := by
      funext k
      simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, P, VertexIso.ofBasis_inv_apply]
    have : Q.transport P V e (Sum.inr j) (Sum.inl i) =
        (P.hom (Q.tgt e) *ᵥ (V e *ᵥ b (Q.src e) (Sum.inl i))) (Sum.inr j) := by
      rw [← hcol, transport_apply, Matrix.mul_assoc]
      simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    rw [this, VertexIso.ofBasis_hom_mulVec]
    exact hbrepr _ _ (hS e _ (hbS _ i)) j
  refine ⟨P, fun e => (Q.transport P V e).toBlocks₁₁, fun e => (Q.transport P V e).toBlocks₁₂,
    fun e => (Q.transport P V e).toBlocks₂₂, funext fun e => ?_⟩
  rw [blockRep_apply, ← Matrix.fromBlocks_toBlocks (Q.transport P V e)]
  congr 1
  ext j i
  exact hzero e j i

/-- **Block normal form inside the group orbit.** If `V` has a subrepresentation of dimension
`γ`, then for any identification `σ p : ι₁ p ⊕ ι₂ p ≃ ι p` with `|ι₁ p| = γ p`, some `g · V` is
the block upper-triangular representation reindexed along `σ`. -/
theorem HasSubrepOfDim.exists_act_eq {V : Q.Rep K ι} {γ : Fin Q.s → ℕ}
    (h : Q.HasSubrepOfDim V γ) (σ : ∀ p, ι₁ p ⊕ ι₂ p ≃ ι p)
    (hγ : ∀ p, Fintype.card (ι₁ p) = γ p) :
    ∃ (g : GLFamily K ι) (A : Q.Rep K ι₁) (y : Q.ArrowHom K ι₂ ι₁) (C : Q.Rep K ι₂),
      Q.act g V = Q.transport (VertexIso.ofEquiv σ) (Q.blockRep A y C) := by
  obtain ⟨S, hS, hdim⟩ := h
  obtain ⟨P, A, y, C, hP⟩ := hS.exists_transport_eq_blockRep Q (ι₁ := ι₁) (ι₂ := ι₂)
    (fun p => by rw [hγ, hdim])
    (fun p => by rw [← Fintype.card_sum, Fintype.card_congr (σ p)])
  refine ⟨(P.trans (VertexIso.ofEquiv σ)).toGL, A, y, C, ?_⟩
  rw [← transport_eq_act, transport_trans, hP]

end Subrep

/-! ### Changes of coordinates are linear in the coordinates -/

section Coordinates

variable {K : Type*} [Field K] {ι κ : Fin Q.s → Type}
  [∀ p, Fintype (ι p)] [∀ p, DecidableEq (ι p)] [∀ p, Fintype (κ p)] [∀ p, DecidableEq (κ p)]

/-- A change of coordinates, as a linear map between the coordinate spaces of
representations. -/
def coordTransport (P : VertexIso K ι κ) : (Q.Entry ι → K) →ₗ[K] (Q.Entry κ → K) :=
  ((Q.arrowCoord K ι ι).symm.trans ((Q.arrowConj P P).trans (Q.arrowCoord K κ κ))).toLinearMap

@[simp] theorem coordTransport_coord (P : VertexIso K ι κ) (V : Q.Rep K ι) :
    Q.coordTransport P (Q.coord V) = Q.coord (Q.transport P V) :=
  rfl

theorem isPolynomialMap_coordTransport (P : VertexIso K ι κ) :
    IsPolynomialMap (Q.coordTransport P) :=
  isPolynomialMap_linearMap _

end Coordinates

/-! ### General subrepresentations and quotients -/

section General

variable (K : Type*) [Field K] (ι : Fin Q.s → Type) [∀ p, Fintype (ι p)]

/-- **A general representation on `ι` has a subrepresentation of dimension `γ`**: the
representations that have one form a Zariski-dense set. This is the density form of Schofield's
relation `γ ↪ dim ι`. -/
def GeneralSub (γ : Fin Q.s → ℕ) : Prop :=
  ZariskiDense (Q.coord '' {V : Q.Rep K ι | Q.HasSubrepOfDim V γ})

/-- **A general representation on `ι` has a quotient of dimension `β`**: the representations that
have one form a Zariski-dense set. This is the density form of Schofield's relation
`dim ι ↠ β`. -/
def GeneralQuot (β : Fin Q.s → ℕ) : Prop :=
  ZariskiDense (Q.coord '' {V : Q.Rep K ι | Q.HasQuotientOfDim V β})

variable {K ι}

theorem generalSub_iff_generalQuot {γ β : Fin Q.s → ℕ}
    (h : ∀ p, γ p + β p = Fintype.card (ι p)) : Q.GeneralSub K ι γ ↔ Q.GeneralQuot K ι β := by
  unfold GeneralSub GeneralQuot
  simp only [Q.hasSubrepOfDim_iff_hasQuotientOfDim _ h]

variable [Infinite K]

/-- Every representation is a quotient of itself. -/
theorem generalQuot_dimVec : Q.GeneralQuot K ι (dimVec ι) :=
  zariskiDense_univ.mono fun x _ => ⟨Q.ofCoord x, Q.hasQuotientOfDim_self _, rfl⟩

/-- Every representation has the zero quotient. -/
theorem generalQuot_zero : Q.GeneralQuot K ι 0 :=
  zariskiDense_univ.mono fun x _ => ⟨Q.ofCoord x, Q.hasQuotientOfDim_zero _, rfl⟩

variable [∀ p, DecidableEq (ι p)] {κ : Fin Q.s → Type} [∀ p, Fintype (κ p)]
  [∀ p, DecidableEq (κ p)]

theorem GeneralSub.of_vertexIso {γ : Fin Q.s → ℕ} (h : Q.GeneralSub K ι γ)
    (P : VertexIso K ι κ) : Q.GeneralSub K κ γ := by
  have hrange : ZariskiDense (Set.range (Q.coordTransport P)) :=
    zariskiDense_univ.mono fun x _ =>
      ⟨Q.coord (Q.transport P.symm (Q.ofCoord x)), by simp⟩
  refine (ZariskiDense.image (Q.isPolynomialMap_coordTransport P) hrange h).mono ?_
  rintro _ ⟨_, ⟨V, hV, rfl⟩, rfl⟩
  exact ⟨_, hV.transport Q P, rfl⟩

theorem GeneralQuot.of_vertexIso {β : Fin Q.s → ℕ} (h : Q.GeneralQuot K ι β)
    (P : VertexIso K ι κ) : Q.GeneralQuot K κ β := by
  have hrange : ZariskiDense (Set.range (Q.coordTransport P)) :=
    zariskiDense_univ.mono fun x _ =>
      ⟨Q.coord (Q.transport P.symm (Q.ofCoord x)), by simp⟩
  refine (ZariskiDense.image (Q.isPolynomialMap_coordTransport P) hrange h).mono ?_
  rintro _ ⟨_, ⟨V, hV, rfl⟩, rfl⟩
  exact ⟨_, hV.transport Q P, rfl⟩

/-- The relation `γ ↪ dim ι` depends on `ι` only up to isomorphism. -/
theorem generalSub_iff_of_vertexIso {γ : Fin Q.s → ℕ} (P : VertexIso K ι κ) :
    Q.GeneralSub K ι γ ↔ Q.GeneralSub K κ γ :=
  ⟨fun h => h.of_vertexIso Q P, fun h => h.of_vertexIso Q P.symm⟩

/-- The relation `dim ι ↠ β` depends on `ι` only up to isomorphism. -/
theorem generalQuot_iff_of_vertexIso {β : Fin Q.s → ℕ} (P : VertexIso K ι κ) :
    Q.GeneralQuot K ι β ↔ Q.GeneralQuot K κ β :=
  ⟨fun h => h.of_vertexIso Q P, fun h => h.of_vertexIso Q P.symm⟩

end General

end FQuiver

end

end QuiverInvariants
