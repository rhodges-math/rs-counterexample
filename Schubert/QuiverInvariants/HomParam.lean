import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Schubert.QuiverInvariants.Ringel

/-!
# Generic homomorphisms and the unobstructedness lemma

Fix a forward quiver and vertex families `ι`, `κ` over an infinite field `K`. The pairs `(V, W)`
of representations on `ι` and on `κ` form the affine space with coordinates `Entry ι ⊕ Entry κ`.
The Ringel matrix of the *universal pair*, whose entries are the coordinate variables, is a
matrix of polynomials on this space. Its generic rank defines the generic values `genericHom`
and `genericExt`, the smallest values of `homDim` and `extDim`. A pair is *hom-generic* when its
Ringel map has the generic rank; this holds on a nonempty principal open set of pairs.

The main result is the **unobstructedness lemma**: at a hom-generic pair `(V, W)`,
every homomorphism `φ : V → W` extends along every first-order deformation, that is,
`φ · dV = (φ_q dV_e)_e` and `dW · φ = (dW_e φ_p)_e` lie in the image of the Ringel map for all
`dV`, `dW`. The proof deforms `V` along the line `V + t dV`: the rank of the Ringel map cannot
grow, and a determinant that is a polynomial in `t` shows that it would grow if
`φ · dV` were not in the image. Only the fact that a nonzero polynomial in one variable has
finitely many roots is used; there is no assumption on the characteristic.

Its consequence, the **quotient lemma**, is that at a hom-generic pair, dividing `W` by the
image of any homomorphism does not change `ext(V, −)`. We state it in coordinates adapted to the
image: `W = [[A, y], [0, C]]` with the image of `φ` equal to the first block.

Finally, the homomorphisms of the pairs in a nonempty principal open set are parametrized by a
matrix of polynomials, built from the adjugate of a maximal minor of the generic Ringel matrix
(`FQuiver.exists_homProjector`).

## Main definitions

* `FQuiver.pairCoord V W`, `FQuiver.pairFst x`, `FQuiver.pairSnd x`: coordinates of pairs.
* `FQuiver.genericRingelMatrix K ι κ`: the Ringel matrix of the universal pair.
* `FQuiver.genericRingelRank K ι κ`, `FQuiver.genericHom K ι κ`, `FQuiver.genericExt K ι κ`: the
  generic rank of the Ringel map and the generic values of `hom` and `ext`.
* `FQuiver.IsHomGeneric V W`: the Ringel map of `(V, W)` has the generic rank.
* `QuiverInvariants.kerProjector M f g`: for a matrix `M` and an `r × r` submatrix `A` (rows `f`,
  columns `g`), the matrix `det A · 1 − E_g · adj A · M_f`; when `A` is invertible and `M` has
  rank `r`, its image is the kernel of `M`.

## Main results

* `QuiverInvariants.exists_ne_zero_le_rank_add_smul`: the rank of `G₀ + t G₁` is at least the
  rank of `G₀` for some `t ≠ 0`.
* `QuiverInvariants.mem_range_of_forall_finrank_range_le`: the abstract unobstructedness lemma.
* `FQuiver.genericHom_le_homDim`, `FQuiver.genericExt_le_extDim`: the generic values are the
  minima; `FQuiver.exists_isHomGeneric`: they are attained.
* `FQuiver.eventually_isHomGeneric`: a generic pair is hom-generic.
* `FQuiver.IsHomGeneric.hom_mul_mem_range`, `FQuiver.IsHomGeneric.mul_hom_mem_range`:
  the unobstructedness lemma.
* `FQuiver.IsHomGeneric.extDim_blockRep_eq`, `FQuiver.IsHomGeneric.extDim_normalForm`:
  the quotient lemma.
* `FQuiver.exists_homProjector`: the polynomial parametrization of homomorphisms.
-/

open Matrix MvPolynomial Filter

namespace QuiverInvariants

noncomputable section

/-! ### Perturbing the rank of a matrix along a line -/

section Perturbation

variable {K : Type*} [Field K]

/-- The rank of the matrix of coordinates of a family of vectors is the dimension of their
span. -/
theorem rank_of_repr {N : Type*} [AddCommGroup N] [Module K N] {m l : Type*} [Fintype m]
    [Fintype l] (b : Module.Basis m K N) (w : l → N) :
    (Matrix.of fun i j => b.repr (w j) i).rank =
      Module.finrank K (Submodule.span K (Set.range w)) := by
  rw [Matrix.rank_eq_finrank_span_cols]
  have hcol : (Matrix.of fun i j => b.repr (w j) i).col = b.equivFun ∘ w := by
    funext j i
    rfl
  rw [hcol, Set.range_comp, ← LinearEquiv.coe_coe, Submodule.span_image]
  exact LinearEquiv.finrank_map_eq _ _

/-- **Lower semicontinuity of the rank along a line.** If `G₀` has rank at least `n`, then so has
`G₀ + t • G₁` for some `t ≠ 0` (indeed for all but finitely many `t`). -/
theorem exists_ne_zero_le_rank_add_smul [Infinite K] {m l : Type*} [Fintype m] [Fintype l]
    {G₀ : Matrix m l K} (G₁ : Matrix m l K) {n : ℕ} (h : n ≤ G₀.rank) :
    ∃ t : K, t ≠ 0 ∧ n ≤ (G₀ + t • G₁).rank := by
  classical
  obtain ⟨f, g, hfg⟩ := le_rank_iff_exists_det_submatrix_ne_zero.mp h
  set P : Polynomial K := ((G₀.map Polynomial.C +
    (Polynomial.X : Polynomial K) • G₁.map Polynomial.C).submatrix f g).det with hPdef
  have heval : ∀ t : K, P.eval t = ((G₀ + t • G₁).submatrix f g).det := by
    intro t
    rw [hPdef, ← Polynomial.coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i j
    simp [RingHom.mapMatrix_apply]
    ring
  have hP : P ≠ 0 := fun h0 => hfg (by simpa [heval] using congrArg (Polynomial.eval 0) h0)
  obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset (insert 0 P.roots.toFinset)
  rw [Finset.mem_insert, not_or, Multiset.mem_toFinset, Polynomial.mem_roots hP] at ht
  refine ⟨t, ht.1, le_rank_iff_exists_det_submatrix_ne_zero.mpr ⟨f, g, ?_⟩⟩
  rw [← heval]
  exact ht.2

/-- **Unobstructedness, abstract form.** Let `d₀, d₁ : M → N` be linear maps such that no member
`d₀ + t d₁` of the line through `d₀` in direction `d₁` has larger rank than `d₀`. Then `d₁` maps
the kernel of `d₀` into the image of `d₀`. -/
theorem mem_range_of_forall_finrank_range_le [Infinite K] {M N : Type*} [AddCommGroup M]
    [Module K M] [AddCommGroup N] [Module K N] [FiniteDimensional K N] (d₀ d₁ : M →ₗ[K] N)
    (h : ∀ t : K, Module.finrank K (LinearMap.range (d₀ + t • d₁)) ≤
      Module.finrank K (LinearMap.range d₀))
    {φ : M} (hφ : d₀ φ = 0) : d₁ φ ∈ LinearMap.range d₀ := by
  by_contra hnot
  set r := Module.finrank K (LinearMap.range d₀)
  let bR := Module.finBasis K (LinearMap.range d₀)
  have hbR : ∀ j, ∃ u, d₀ u = bR j := fun j => (bR j).2
  choose u hu using hbR
  let bN := Module.finBasis K N
  let w₀ : Fin (r + 1) → N := Fin.cons (d₁ φ) fun j => d₀ (u j)
  let w₁ : Fin (r + 1) → N := Fin.cons 0 fun j => d₁ (u j)
  let G : (Fin (r + 1) → N) → Matrix (Fin (Module.finrank K N)) (Fin (r + 1)) K :=
    fun w => Matrix.of fun i j => bN.repr (w j) i
  have hind : LinearIndependent K w₀ := by
    refine linearIndependent_finCons.mpr ⟨?_, fun hmem => hnot ?_⟩
    · have hcomp : (fun j => d₀ (u j)) = (LinearMap.range d₀).subtype ∘ bR :=
        funext fun j => hu j
      rw [hcomp]
      exact bR.linearIndependent.map' _ (Submodule.ker_subtype _)
    · refine (Submodule.span_le.mpr ?_) hmem
      rintro _ ⟨j, rfl⟩
      exact LinearMap.mem_range_self _ _
  have h₀ : r + 1 ≤ (G w₀).rank := by
    rw [rank_of_repr, finrank_span_eq_card hind, Fintype.card_fin]
  obtain ⟨t, ht0, ht⟩ := exists_ne_zero_le_rank_add_smul (G w₁) h₀
  have hG : G w₀ + t • G w₁ = G (w₀ + t • w₁) := by
    ext i j
    simp [G]
  rw [hG, rank_of_repr] at ht
  have hle : Submodule.span K (Set.range (w₀ + t • w₁)) ≤ LinearMap.range (d₀ + t • d₁) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    refine Fin.cases ?_ (fun k => ?_) j
    · refine ⟨t⁻¹ • φ, ?_⟩
      have h0 : (w₀ + t • w₁) 0 = d₁ φ := by simp [w₀, w₁]
      rw [h0, LinearMap.add_apply, LinearMap.smul_apply, map_smul, map_smul, hφ, smul_zero,
        zero_add, smul_smul, mul_inv_cancel₀ ht0, one_smul]
    · exact ⟨u k, by simp [w₀, w₁]⟩
  have h₁ := ht.trans (Submodule.finrank_mono hle)
  have h₂ := h t
  omega

end Perturbation

/-! ### Kernels parametrized by adjugates -/

section KerProjector

variable {R : Type*} [CommRing R] {m n : Type*} [Fintype n] [DecidableEq n] {r : ℕ}

/-- The matrix that places the coordinates `Fin r` at the columns `g`. -/
def colEmbed (g : Fin r → n) : Matrix n (Fin r) R :=
  Matrix.of fun y i => if g i = y then 1 else 0

theorem submatrix_mul_colEmbed (M : Matrix m n R) (f : Fin r → m) (g : Fin r → n) :
    M.submatrix f id * colEmbed g = M.submatrix f g := by
  ext a i
  simp [colEmbed, Matrix.mul_apply]

/-- **The kernel projector** of a matrix `M` relative to an `r × r` submatrix `A` (rows `f`,
columns `g`): `det A · 1 − E_g · adj A · M_f`. Its columns lie in the kernel of the rows `f`
of `M`, and it acts on that kernel as multiplication by `det A`. -/
def kerProjector (M : Matrix m n R) (f : Fin r → m) (g : Fin r → n) : Matrix n n R :=
  (M.submatrix f g).det • (1 : Matrix n n R) - colEmbed g * (M.submatrix f g).adjugate *
    M.submatrix f id

theorem submatrix_mul_kerProjector (M : Matrix m n R) (f : Fin r → m) (g : Fin r → n) :
    M.submatrix f id * kerProjector M f g = 0 := by
  rw [kerProjector, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc, submatrix_mul_colEmbed, Matrix.mul_adjugate, Matrix.smul_mul,
    Matrix.one_mul, sub_self]

theorem kerProjector_mulVec_of_mulVec_eq_zero (M : Matrix m n R) (f : Fin r → m)
    (g : Fin r → n) {c : n → R} (hc : M *ᵥ c = 0) :
    kerProjector M f g *ᵥ c = (M.submatrix f g).det • c := by
  have hR : M.submatrix f id *ᵥ c = 0 := by
    funext a
    exact congrFun hc (f a)
  rw [kerProjector, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    ← Matrix.mulVec_mulVec, hR, Matrix.mulVec_zero, sub_zero]

omit [Fintype n] in
theorem kerProjector_map {S : Type*} [CommRing S] (φ : R →+* S) (M : Matrix m n R)
    (f : Fin r → m) (g : Fin r → n) :
    (kerProjector M f g).map φ = kerProjector (M.map φ) f g := by
  have hA : (M.submatrix f g).adjugate.map φ = ((M.map φ).submatrix f g).adjugate := by
    have := RingHom.map_adjugate φ (M.submatrix f g)
    simpa [RingHom.mapMatrix_apply, Matrix.submatrix_map] using this
  have hD : φ (M.submatrix f g).det = ((M.map φ).submatrix f g).det := by
    rw [RingHom.map_det]
    rfl
  have hE : (colEmbed g : Matrix n (Fin r) R).map φ = colEmbed g := by
    ext y i
    simp only [colEmbed, Matrix.map_apply, Matrix.of_apply]
    split_ifs <;> simp
  rw [kerProjector, kerProjector, Matrix.map_sub φ (map_sub φ), Matrix.map_mul, Matrix.map_mul,
    hA, hE, ← hD, ← Matrix.submatrix_map]
  congr 1
  ext i j
  by_cases hij : i = j <;> simp [hij]

variable {K : Type*} [Field K]

omit [DecidableEq n] in
/-- Over a field, if `M` has rank `r` and the `r × r` submatrix with rows `f` and columns `g` is
invertible, then the rows `f` cut out the kernel of `M`. -/
theorem ker_submatrix_eq (M : Matrix m n K) (f : Fin r → m) (g : Fin r → n)
    (hdet : (M.submatrix f g).det ≠ 0) (hrank : M.rank = r) :
    LinearMap.ker (M.submatrix f id).mulVecLin = LinearMap.ker M.mulVecLin := by
  have hle : LinearMap.ker M.mulVecLin ≤ LinearMap.ker (M.submatrix f id).mulVecLin := by
    intro c hc
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hc ⊢
    funext a
    exact congrFun hc (f a)
  have hrankR : (M.submatrix f id).rank = r := by
    apply le_antisymm
    · simpa using (M.submatrix f id).rank_le_card_height
    · exact le_rank_iff_exists_det_submatrix_ne_zero.mpr ⟨id, g, by simpa using hdet⟩
  refine (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
  have h₁ := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  have h₂ := LinearMap.finrank_range_add_finrank_ker (M.submatrix f id).mulVecLin
  rw [← Matrix.rank] at h₁ h₂
  omega

/-- Over a field, under the same hypotheses, the columns of the kernel projector lie in the kernel
of `M`. -/
theorem mul_kerProjector (M : Matrix m n K) (f : Fin r → m) (g : Fin r → n)
    (hdet : (M.submatrix f g).det ≠ 0) (hrank : M.rank = r) : M * kerProjector M f g = 0 := by
  have hker := ker_submatrix_eq M f g hdet hrank
  ext a b
  have hcol : (fun y => kerProjector M f g y b) ∈ LinearMap.ker M.mulVecLin := by
    rw [← hker, LinearMap.mem_ker, Matrix.mulVecLin_apply]
    funext a'
    exact congrFun (congrFun (submatrix_mul_kerProjector M f g) a') b
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hcol
  exact congrFun hcol a

end KerProjector

namespace FQuiver


variable (Q : FQuiver) {K : Type*} [Field K] {ι κ : Fin Q.s → Type}

/-! ### Coordinates of pairs -/

/-- The coordinates of a pair of representations. -/
def pairCoord (V : Q.Rep K ι) (W : Q.Rep K κ) : Q.Entry ι ⊕ Q.Entry κ → K :=
  Sum.elim (Q.coord V) (Q.coord W)

/-- The first representation of the pair with coordinates `x`. -/
def pairFst (x : Q.Entry ι ⊕ Q.Entry κ → K) : Q.Rep K ι :=
  Q.ofCoord (x ∘ Sum.inl)

/-- The second representation of the pair with coordinates `x`. -/
def pairSnd (x : Q.Entry ι ⊕ Q.Entry κ → K) : Q.Rep K κ :=
  Q.ofCoord (x ∘ Sum.inr)

@[simp] theorem pairFst_pairCoord (V : Q.Rep K ι) (W : Q.Rep K κ) :
    Q.pairFst (Q.pairCoord V W) = V :=
  rfl

@[simp] theorem pairSnd_pairCoord (V : Q.Rep K ι) (W : Q.Rep K κ) :
    Q.pairSnd (Q.pairCoord V W) = W :=
  rfl

@[simp] theorem pairCoord_pairFst_pairSnd (x : Q.Entry ι ⊕ Q.Entry κ → K) :
    Q.pairCoord (Q.pairFst x) (Q.pairSnd x) = x := by
  funext y
  cases y <;> rfl

/-! ### The generic Ringel matrix -/

variable [∀ p, Fintype (ι p)] [∀ p, DecidableEq (ι p)] [∀ p, Fintype (κ p)]
  [∀ p, DecidableEq (κ p)]

variable (K ι κ)

/-- The first representation of the **universal pair**: its entries are the coordinate
variables of the pair space. -/
def univPairFst : Q.Rep (MvPolynomial (Q.Entry ι ⊕ Q.Entry κ) K) ι :=
  fun e j i => X (Sum.inl ⟨e, (i, j)⟩)

/-- The second representation of the universal pair. -/
def univPairSnd : Q.Rep (MvPolynomial (Q.Entry ι ⊕ Q.Entry κ) K) κ :=
  fun e j i => X (Sum.inr ⟨e, (i, j)⟩)

/-- The **generic Ringel matrix**: the Ringel matrix of the universal pair, a matrix of
polynomials in the coordinates of pairs. -/
def genericRingelMatrix :
    Matrix (Q.ArrowEntry ι κ) (VertexEntry ι κ) (MvPolynomial (Q.Entry ι ⊕ Q.Entry κ) K) :=
  Q.ringelMatrix (Q.univPairFst K ι κ) (Q.univPairSnd K ι κ)

variable {K ι κ}

omit [∀ p, Fintype (ι p)] [∀ p, DecidableEq (ι p)] [∀ p, Fintype (κ p)]
  [∀ p, DecidableEq (κ p)] in
theorem mapArrowHom_eval_univPairFst (x : Q.Entry ι ⊕ Q.Entry κ → K) :
    Q.mapArrowHom (eval x) (Q.univPairFst K ι κ) = Q.pairFst x := by
  funext e
  ext j i
  simp [univPairFst, pairFst, ofCoord]

omit [∀ p, Fintype (ι p)] [∀ p, DecidableEq (ι p)] [∀ p, Fintype (κ p)]
  [∀ p, DecidableEq (κ p)] in
theorem mapArrowHom_eval_univPairSnd (x : Q.Entry ι ⊕ Q.Entry κ → K) :
    Q.mapArrowHom (eval x) (Q.univPairSnd K ι κ) = Q.pairSnd x := by
  funext e
  ext j i
  simp [univPairSnd, pairSnd, ofCoord]

/-- **Evaluating the generic Ringel matrix** at the coordinates `x` of a pair gives its Ringel
matrix. -/
theorem map_eval_genericRingelMatrix (x : Q.Entry ι ⊕ Q.Entry κ → K) :
    (Q.genericRingelMatrix K ι κ).map (eval x) = Q.ringelMatrix (Q.pairFst x) (Q.pairSnd x) := by
  rw [genericRingelMatrix, ringelMatrix_map, mapArrowHom_eval_univPairFst,
    mapArrowHom_eval_univPairSnd]

theorem map_eval_pairCoord_genericRingelMatrix (V : Q.Rep K ι) (W : Q.Rep K κ) :
    (Q.genericRingelMatrix K ι κ).map (eval (Q.pairCoord V W)) = Q.ringelMatrix V W := by
  rw [map_eval_genericRingelMatrix, pairFst_pairCoord, pairSnd_pairCoord]

/-! ### Generic values -/

variable (K ι κ)

/-- The **generic rank of the Ringel map**: the largest rank of a Ringel map `d_{V,W}`. -/
def genericRingelRank : ℕ :=
  genericRank (Q.genericRingelMatrix K ι κ)

/-- The **generic `hom`**: the smallest value of `homDim V W`. -/
def genericHom : ℕ :=
  (∑ p, Fintype.card (κ p) * Fintype.card (ι p)) - Q.genericRingelRank K ι κ

/-- The **generic `ext`**: the smallest value of `extDim V W`. -/
def genericExt : ℕ :=
  (∑ e : Q.Arrow, Fintype.card (κ (Q.tgt e)) * Fintype.card (ι (Q.src e))) -
    Q.genericRingelRank K ι κ

variable {K ι κ}

theorem ringelRank_eq_rank_map_eval (x : Q.Entry ι ⊕ Q.Entry κ → K) :
    Q.ringelRank (Q.pairFst x) (Q.pairSnd x) =
      ((Q.genericRingelMatrix K ι κ).map (eval x)).rank := by
  rw [map_eval_genericRingelMatrix, rank_ringelMatrix]

theorem ringelRank_le_genericRingelRank (V : Q.Rep K ι) (W : Q.Rep K κ) :
    Q.ringelRank V W ≤ Q.genericRingelRank K ι κ := by
  have h := Q.ringelRank_eq_rank_map_eval (Q.pairCoord V W)
  rw [pairFst_pairCoord, pairSnd_pairCoord] at h
  rw [h]
  exact rank_map_eval_le_genericRank _ _

theorem exists_ringelRank_eq_genericRingelRank :
    ∃ (V : Q.Rep K ι) (W : Q.Rep K κ), Q.ringelRank V W = Q.genericRingelRank K ι κ := by
  obtain ⟨x, hx⟩ := exists_rank_map_eval_eq_genericRank (Q.genericRingelMatrix K ι κ)
  exact ⟨Q.pairFst x, Q.pairSnd x, by rw [ringelRank_eq_rank_map_eval, hx]; rfl⟩

theorem genericRingelRank_le_card_vertex :
    Q.genericRingelRank K ι κ ≤ ∑ p, Fintype.card (κ p) * Fintype.card (ι p) := by
  obtain ⟨V, W, h⟩ := Q.exists_ringelRank_eq_genericRingelRank (K := K) (ι := ι) (κ := κ)
  rw [← h, ← Q.homDim_add_ringelRank V W]
  exact Nat.le_add_left _ _

theorem genericRingelRank_le_card_arrow :
    Q.genericRingelRank K ι κ ≤
      ∑ e : Q.Arrow, Fintype.card (κ (Q.tgt e)) * Fintype.card (ι (Q.src e)) := by
  obtain ⟨V, W, h⟩ := Q.exists_ringelRank_eq_genericRingelRank (K := K) (ι := ι) (κ := κ)
  rw [← h, ← Q.extDim_add_ringelRank V W]
  exact Nat.le_add_left _ _

theorem genericHom_add_genericRingelRank :
    Q.genericHom K ι κ + Q.genericRingelRank K ι κ =
      ∑ p, Fintype.card (κ p) * Fintype.card (ι p) :=
  Nat.sub_add_cancel Q.genericRingelRank_le_card_vertex

theorem genericExt_add_genericRingelRank :
    Q.genericExt K ι κ + Q.genericRingelRank K ι κ =
      ∑ e : Q.Arrow, Fintype.card (κ (Q.tgt e)) * Fintype.card (ι (Q.src e)) :=
  Nat.sub_add_cancel Q.genericRingelRank_le_card_arrow

/-- **The generic `hom` is the minimum of `hom`.** -/
theorem genericHom_le_homDim (V : Q.Rep K ι) (W : Q.Rep K κ) :
    Q.genericHom K ι κ ≤ Q.homDim V W := by
  have h₁ := Q.homDim_add_ringelRank V W
  have h₂ := Q.genericHom_add_genericRingelRank (K := K) (ι := ι) (κ := κ)
  have h₃ := Q.ringelRank_le_genericRingelRank V W
  omega

/-- **The generic `ext` is the minimum of `ext`.** -/
theorem genericExt_le_extDim (V : Q.Rep K ι) (W : Q.Rep K κ) :
    Q.genericExt K ι κ ≤ Q.extDim V W := by
  have h₁ := Q.extDim_add_ringelRank V W
  have h₂ := Q.genericExt_add_genericRingelRank (K := K) (ι := ι) (κ := κ)
  have h₃ := Q.ringelRank_le_genericRingelRank V W
  omega

/-- **The Euler identity for generic values**: `genericHom − genericExt = ⟨dim ι, dim κ⟩`. -/
theorem genericHom_sub_genericExt :
    (Q.genericHom K ι κ : ℤ) - Q.genericExt K ι κ =
      Q.euler (fun p => (Fintype.card (ι p) : ℤ)) fun p => (Fintype.card (κ p) : ℤ) := by
  obtain ⟨V, W, h⟩ := Q.exists_ringelRank_eq_genericRingelRank (K := K) (ι := ι) (κ := κ)
  have h₁ := Q.homDim_add_ringelRank V W
  have h₂ := Q.extDim_add_ringelRank V W
  have h₃ := Q.genericHom_add_genericRingelRank (K := K) (ι := ι) (κ := κ)
  have h₄ := Q.genericExt_add_genericRingelRank (K := K) (ι := ι) (κ := κ)
  have hh : Q.homDim V W = Q.genericHom K ι κ := by omega
  have he : Q.extDim V W = Q.genericExt K ι κ := by omega
  rw [← hh, ← he, homDim_sub_extDim]

/-! ### Hom-generic pairs -/

/-- A pair `(V, W)` is **hom-generic** when its Ringel map has the generic rank, that is, when
`hom(V, W)` takes its smallest value. -/
def IsHomGeneric (V : Q.Rep K ι) (W : Q.Rep K κ) : Prop :=
  Q.ringelRank V W = Q.genericRingelRank K ι κ

theorem isHomGeneric_iff_homDim {V : Q.Rep K ι} {W : Q.Rep K κ} :
    Q.IsHomGeneric V W ↔ Q.homDim V W = Q.genericHom K ι κ := by
  have h₁ := Q.homDim_add_ringelRank V W
  have h₂ := Q.genericHom_add_genericRingelRank (K := K) (ι := ι) (κ := κ)
  have h₃ := Q.ringelRank_le_genericRingelRank V W
  unfold IsHomGeneric
  omega

theorem isHomGeneric_iff_extDim {V : Q.Rep K ι} {W : Q.Rep K κ} :
    Q.IsHomGeneric V W ↔ Q.extDim V W = Q.genericExt K ι κ := by
  have h₁ := Q.extDim_add_ringelRank V W
  have h₂ := Q.genericExt_add_genericRingelRank (K := K) (ι := ι) (κ := κ)
  have h₃ := Q.ringelRank_le_genericRingelRank V W
  unfold IsHomGeneric
  omega

/-- A pair is hom-generic if and only if `hom` is minimal there. -/
theorem isHomGeneric_iff_forall_homDim_le {V : Q.Rep K ι} {W : Q.Rep K κ} :
    Q.IsHomGeneric V W ↔ ∀ (V' : Q.Rep K ι) (W' : Q.Rep K κ), Q.homDim V W ≤ Q.homDim V' W' := by
  rw [isHomGeneric_iff_homDim]
  refine ⟨fun h V' W' => h ▸ Q.genericHom_le_homDim V' W', fun h => ?_⟩
  obtain ⟨V', W', h'⟩ := Q.exists_ringelRank_eq_genericRingelRank (K := K) (ι := ι) (κ := κ)
  have h'' : Q.homDim V' W' = Q.genericHom K ι κ := Q.isHomGeneric_iff_homDim.mp h'
  exact le_antisymm (h'' ▸ h V' W') (Q.genericHom_le_homDim V W)

theorem exists_isHomGeneric : ∃ (V : Q.Rep K ι) (W : Q.Rep K κ), Q.IsHomGeneric V W :=
  Q.exists_ringelRank_eq_genericRingelRank

/-- **Hom-genericity on a principal open set.** Some maximal minor of the generic Ringel matrix
is a nonzero polynomial, and every pair at which it does not vanish is hom-generic. -/
theorem exists_minor_isHomGeneric :
    ∃ (f : Fin (Q.genericRingelRank K ι κ) → Q.ArrowEntry ι κ)
      (g : Fin (Q.genericRingelRank K ι κ) → VertexEntry ι κ),
      ((Q.genericRingelMatrix K ι κ).submatrix f g).det ≠ 0 ∧
        ∀ x, eval x ((Q.genericRingelMatrix K ι κ).submatrix f g).det ≠ 0 →
          Q.IsHomGeneric (Q.pairFst x) (Q.pairSnd x) := by
  obtain ⟨f, g, h0, h⟩ := exists_minor_genericRank (Q.genericRingelMatrix K ι κ)
  exact ⟨f, g, h0, fun x hx => by
    rw [IsHomGeneric, ringelRank_eq_rank_map_eval]
    exact h x hx⟩

/-- **A generic pair is hom-generic.** -/
theorem eventually_isHomGeneric :
    ∀ᶠ x in genericFilter K (Q.Entry ι ⊕ Q.Entry κ),
      Q.IsHomGeneric (Q.pairFst x) (Q.pairSnd x) := by
  obtain ⟨f, g, h0, h⟩ := Q.exists_minor_isHomGeneric (K := K) (ι := ι) (κ := κ)
  exact eventually_genericFilter.mpr ⟨_, h0, h⟩

/-- **A maximal minor at a hom-generic pair.** If `(V, W)` is hom-generic, some minor of the
generic Ringel matrix of the generic size does not vanish at `(V, W)`. -/
theorem IsHomGeneric.exists_minor {V : Q.Rep K ι} {W : Q.Rep K κ} (h : Q.IsHomGeneric V W) :
    ∃ (f : Fin (Q.genericRingelRank K ι κ) → Q.ArrowEntry ι κ)
      (g : Fin (Q.genericRingelRank K ι κ) → VertexEntry ι κ),
      eval (Q.pairCoord V W) ((Q.genericRingelMatrix K ι κ).submatrix f g).det ≠ 0 := by
  have hr : Q.genericRingelRank K ι κ ≤
      ((Q.genericRingelMatrix K ι κ).map (eval (Q.pairCoord V W))).rank := by
    rw [map_eval_pairCoord_genericRingelMatrix, rank_ringelMatrix]
    exact h.ge
  obtain ⟨f, g, hfg⟩ := le_rank_iff_exists_det_submatrix_ne_zero.mp hr
  exact ⟨f, g, by rwa [eval_det_submatrix]⟩

/-- Hom-genericity is invariant under the group actions on both sides. -/
theorem isHomGeneric_act_iff (g : GLFamily K ι) (h : GLFamily K κ) (V : Q.Rep K ι)
    (W : Q.Rep K κ) : Q.IsHomGeneric (Q.act g V) (Q.act h W) ↔ Q.IsHomGeneric V W := by
  rw [isHomGeneric_iff_homDim, isHomGeneric_iff_homDim, homDim_act]

variable {ι' κ' : Fin Q.s → Type} [∀ p, Fintype (ι' p)] [∀ p, DecidableEq (ι' p)]
  [∀ p, Fintype (κ' p)] [∀ p, DecidableEq (κ' p)]

/-- The generic rank of the Ringel map depends on the vertex families only up to
isomorphism. -/
theorem genericRingelRank_eq_of_vertexIso (P : VertexIso K ι ι') (P' : VertexIso K κ κ') :
    Q.genericRingelRank K ι κ = Q.genericRingelRank K ι' κ' := by
  apply le_antisymm
  · obtain ⟨V, W, h⟩ := Q.exists_ringelRank_eq_genericRingelRank (K := K) (ι := ι) (κ := κ)
    rw [← h, ← Q.ringelRank_transport P P' V W]
    exact Q.ringelRank_le_genericRingelRank _ _
  · obtain ⟨V, W, h⟩ := Q.exists_ringelRank_eq_genericRingelRank (K := K) (ι := ι') (κ := κ')
    rw [← h, ← Q.ringelRank_transport P.symm P'.symm V W]
    exact Q.ringelRank_le_genericRingelRank _ _

/-- Hom-genericity is invariant under changes of coordinates on both sides. -/
theorem isHomGeneric_transport_iff (P : VertexIso K ι ι') (P' : VertexIso K κ κ')
    (V : Q.Rep K ι) (W : Q.Rep K κ) :
    Q.IsHomGeneric (Q.transport P V) (Q.transport P' W) ↔ Q.IsHomGeneric V W := by
  rw [IsHomGeneric, IsHomGeneric, Q.ringelRank_transport P P' V W,
    Q.genericRingelRank_eq_of_vertexIso P P']

/-- **Vanishing of the generic `ext`**: `genericExt = 0` if and only if `extDim V W = 0` for some
pair. -/
theorem genericExt_eq_zero_iff :
    Q.genericExt K ι κ = 0 ↔ ∃ (V : Q.Rep K ι) (W : Q.Rep K κ), Q.extDim V W = 0 := by
  constructor
  · intro h
    obtain ⟨V, W, hVW⟩ := Q.exists_isHomGeneric (K := K) (ι := ι) (κ := κ)
    exact ⟨V, W, (Q.isHomGeneric_iff_extDim.mp hVW).trans h⟩
  · rintro ⟨V, W, h⟩
    exact Nat.eq_zero_of_le_zero (h ▸ Q.genericExt_le_extDim V W)


/-! ### Hom-generic pairs minimize `hom` and `ext` -/

variable {Q}

theorem IsHomGeneric.homDim_le {V : Q.Rep K ι} {W : Q.Rep K κ} (h : Q.IsHomGeneric V W)
    (V' : Q.Rep K ι) (W' : Q.Rep K κ) : Q.homDim V W ≤ Q.homDim V' W' :=
  Q.isHomGeneric_iff_forall_homDim_le.mp h V' W'

/-- **Hom-generic pairs minimize `ext`.** -/
theorem IsHomGeneric.extDim_le {V : Q.Rep K ι} {W : Q.Rep K κ} (h : Q.IsHomGeneric V W)
    (V' : Q.Rep K ι) (W' : Q.Rep K κ) : Q.extDim V W ≤ Q.extDim V' W' :=
  (Q.extDim_le_extDim_iff V V' W W').mpr (h.homDim_le V' W')

theorem IsHomGeneric.ringelRank_le {V : Q.Rep K ι} {W : Q.Rep K κ} (h : Q.IsHomGeneric V W)
    (V' : Q.Rep K ι) (W' : Q.Rep K κ) : Q.ringelRank V' W' ≤ Q.ringelRank V W :=
  (Q.homDim_le_homDim_iff V V' W W').mp (h.homDim_le V' W')

/-! ### The unobstructedness lemma -/

variable [Infinite K]

/-- **Unobstructedness, deforming the source.** At a hom-generic pair `(V, W)`, for every
homomorphism `φ : V → W` and every `dV`, the arrow data `(φ_q dV_e)_{e : p → q}` lie in the image
of the Ringel map. -/
theorem IsHomGeneric.hom_mul_mem_range {V : Q.Rep K ι} {W : Q.Rep K κ}
    (h : Q.IsHomGeneric V W) {φ : VertexHom K ι κ} (hφ : φ ∈ LinearMap.ker (Q.ringel V W))
    (dV : Q.Rep K ι) :
    (fun e => φ (Q.tgt e) * dV e : Q.ArrowHom K ι κ) ∈ LinearMap.range (Q.ringel V W) := by
  have key := mem_range_of_forall_finrank_range_le (Q.ringel V W) (Q.ringel dV 0)
    (fun t => ?_) (LinearMap.mem_ker.mp hφ)
  · have hneg : (fun e => φ (Q.tgt e) * dV e : Q.ArrowHom K ι κ) = -(Q.ringel dV 0 φ) :=
      funext fun e => by simp
    rw [hneg]
    exact neg_mem key
  · have hsm : Q.ringel (t • dV) (0 : Q.Rep K κ) = t • Q.ringel dV 0 := by
      simpa using Q.ringel_smul t dV 0
    rw [← hsm, ← Q.ringel_add_left]
    exact h.ringelRank_le _ _

/-- **Unobstructedness, deforming the target.** At a hom-generic pair `(V, W)`, for every
homomorphism `φ : V → W` and every `dW`, the arrow data `(dW_e φ_p)_{e : p → q}` lie in the image
of the Ringel map. -/
theorem IsHomGeneric.mul_hom_mem_range {V : Q.Rep K ι} {W : Q.Rep K κ}
    (h : Q.IsHomGeneric V W) {φ : VertexHom K ι κ} (hφ : φ ∈ LinearMap.ker (Q.ringel V W))
    (dW : Q.Rep K κ) :
    (fun e => dW e * φ (Q.src e) : Q.ArrowHom K ι κ) ∈ LinearMap.range (Q.ringel V W) := by
  have key := mem_range_of_forall_finrank_range_le (Q.ringel V W) (Q.ringel 0 dW)
    (fun t => ?_) (LinearMap.mem_ker.mp hφ)
  · have hfun : (fun e => dW e * φ (Q.src e) : Q.ArrowHom K ι κ) = Q.ringel 0 dW φ :=
      funext fun e => by simp
    rw [hfun]
    exact key
  · have hsm : Q.ringel (0 : Q.Rep K ι) (t • dW) = t • Q.ringel 0 dW := by
      simpa using Q.ringel_smul t 0 dW
    rw [← hsm, ← Q.ringel_add_right]
    exact h.ringelRank_le _ _

/-! ### The quotient lemma -/

/-- **The quotient lemma.** Let `W = [[A, y], [0, C]]` and let `φ : V → W` be a homomorphism
whose image is the first block: its second-block rows vanish and its first-block rows are onto.
If `(V, W)` is hom-generic, then `ext(V, W) = ext(V, C)`: dividing `W` by the image of `φ` does
not change `ext(V, −)`. -/
theorem IsHomGeneric.extDim_blockRep_eq {κ₁ κ₂ : Fin Q.s → Type} [∀ p, Fintype (κ₁ p)]
    [∀ p, DecidableEq (κ₁ p)] [∀ p, Fintype (κ₂ p)] [∀ p, DecidableEq (κ₂ p)]
    {V : Q.Rep K ι} {A : Q.Rep K κ₁} {y : Q.ArrowHom K κ₂ κ₁} {C : Q.Rep K κ₂}
    (h : Q.IsHomGeneric V (Q.blockRep A y C)) {φ : VertexHom K ι (fun p => κ₁ p ⊕ κ₂ p)}
    (hφ : φ ∈ LinearMap.ker (Q.ringel V (Q.blockRep A y C)))
    (hbot : ∀ p j i, φ p (Sum.inr j) i = 0)
    (htop : ∀ p, Function.Surjective ((φ p).submatrix Sum.inl id).mulVecLin) :
    Q.extDim V (Q.blockRep A y C) = Q.extDim V C := by
  have hS : ∀ p, ∃ S : Matrix (ι p) (κ₁ p) K, (φ p).submatrix Sum.inl id * S = 1 := by
    intro p
    obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective _
      (LinearMap.range_eq_top.mpr (htop p))
    refine ⟨LinearMap.toMatrix' g, Matrix.toLin'.injective ?_⟩
    rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_one, Matrix.toLin'_apply', hg]
  choose S hS using hS
  refine Q.extDim_blockRep_eq_of_forall V A y C fun ξ => ?_
  convert h.hom_mul_mem_range hφ (fun e => S (Q.tgt e) * ξ e) using 1
  funext e
  ext (j | j) i
  · rw [arrowInl_apply_inl]
    have hmul : (φ (Q.tgt e) * (S (Q.tgt e) * ξ e)) (Sum.inl j) i =
        ((φ (Q.tgt e)).submatrix Sum.inl id * S (Q.tgt e) * ξ e) j i := by
      rw [Matrix.mul_assoc]
      rfl
    rw [hmul, hS, Matrix.one_mul]
  · rw [arrowInl_apply_inr, Matrix.mul_apply]
    simp [hbot]

section NormalForm

variable {ιK ιI ιC : Fin Q.s → Type} [∀ p, Fintype (ιK p)] [∀ p, DecidableEq (ιK p)]
  [∀ p, Fintype (ιI p)] [∀ p, DecidableEq (ιI p)] [∀ p, Fintype (ιC p)]
  [∀ p, DecidableEq (ιC p)]

variable (Q K ιK ιI ιC) in
/-- The **standard homomorphism** `[[0, 1], [0, 0]] : K^{ιK ⊕ ιI} → K^{ιI ⊕ ιC}`, with kernel the
first block and image the first block. -/
def normalHom : VertexHom K (fun p => ιK p ⊕ ιI p) (fun p => ιI p ⊕ ιC p) :=
  fun _ => Matrix.fromBlocks 0 1 0 0

omit [Infinite K] [∀ p, DecidableEq (ιK p)] [∀ p, DecidableEq (ιC p)] in
/-- The standard homomorphism is a homomorphism between the normal forms
`[[B, y₁], [0, I]]` and `[[I, y₂], [0, C]]`. -/
theorem normalHom_mem_ker (B : Q.Rep K ιK) (y₁ : Q.ArrowHom K ιI ιK) (I : Q.Rep K ιI)
    (y₂ : Q.ArrowHom K ιC ιI) (C : Q.Rep K ιC) :
    Q.normalHom K ιK ιI ιC ∈ LinearMap.ker (Q.ringel (Q.blockRep B y₁ I) (Q.blockRep I y₂ C)) := by
  rw [mem_ker_ringel]
  intro e
  simp [normalHom, Matrix.fromBlocks_multiply]

/-- **The quotient lemma in normal form.** If `V = [[B, y₁], [0, I]]` and
`W = [[I, y₂], [0, C]]` form a hom-generic pair, then `ext(V, W) = ext(V, C)`. -/
theorem IsHomGeneric.extDim_normalForm {B : Q.Rep K ιK} {y₁ : Q.ArrowHom K ιI ιK}
    {I : Q.Rep K ιI} {y₂ : Q.ArrowHom K ιC ιI} {C : Q.Rep K ιC}
    (h : Q.IsHomGeneric (Q.blockRep B y₁ I) (Q.blockRep I y₂ C)) :
    Q.extDim (Q.blockRep B y₁ I) (Q.blockRep I y₂ C) = Q.extDim (Q.blockRep B y₁ I) C := by
  refine h.extDim_blockRep_eq (Q.normalHom_mem_ker B y₁ I y₂ C)
    (fun p j i => by rcases i with i | i <;> rfl) fun p w => ⟨Sum.elim 0 w, ?_⟩
  funext j
  simp [normalHom, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.one_apply]

end NormalForm

/-! ### Parametrizing homomorphisms by polynomials -/

omit [Infinite K] in
/-- The Ringel matrix acts on coordinates as the Ringel map. -/
theorem ringelMatrix_mulVec_vertexCoord (V : Q.Rep K ι) (W : Q.Rep K κ) (ψ : VertexHom K ι κ) :
    Q.ringelMatrix V W *ᵥ vertexCoord K ι κ ψ = Q.arrowCoord K ι κ (Q.ringel V W ψ) := by
  rw [← Matrix.toLin'_apply, toLin'_ringelMatrix]
  simp

omit [Infinite K] in
theorem mem_ker_ringel_iff_mulVec {V : Q.Rep K ι} {W : Q.Rep K κ} {ψ : VertexHom K ι κ} :
    ψ ∈ LinearMap.ker (Q.ringel V W) ↔ Q.ringelMatrix V W *ᵥ vertexCoord K ι κ ψ = 0 := by
  rw [ringelMatrix_mulVec_vertexCoord, LinearMap.mem_ker, LinearEquiv.map_eq_zero_iff]

omit [Infinite K] in
/-- **Parametrizing homomorphisms by polynomials.** There are a nonzero polynomial `D` and a
square matrix `Π` of polynomials on the space of pairs such that at every pair `x` with
`D(x) ≠ 0`:
* the pair is hom-generic;
* every vector `Π(x) w` is (the coordinate vector of) a homomorphism;
* `Π(x)` acts on homomorphisms as multiplication by `D(x)`, so that every homomorphism is of the
  form `Π(x) w`.

`D` is a maximal minor of the generic Ringel matrix and `Π` its kernel projector. -/
theorem exists_homProjector :
    ∃ (D : MvPolynomial (Q.Entry ι ⊕ Q.Entry κ) K)
      (Pr : Matrix (VertexEntry ι κ) (VertexEntry ι κ) (MvPolynomial (Q.Entry ι ⊕ Q.Entry κ) K)),
      D ≠ 0 ∧ ∀ x, eval x D ≠ 0 →
        Q.IsHomGeneric (Q.pairFst x) (Q.pairSnd x) ∧
        (∀ w, (vertexCoord K ι κ).symm (Pr.map (eval x) *ᵥ w) ∈
          LinearMap.ker (Q.ringel (Q.pairFst x) (Q.pairSnd x))) ∧
        ∀ φ ∈ LinearMap.ker (Q.ringel (Q.pairFst x) (Q.pairSnd x)),
          Pr.map (eval x) *ᵥ vertexCoord K ι κ φ = eval x D • vertexCoord K ι κ φ := by
  obtain ⟨f, g, h0, h⟩ := exists_minor_genericRank (Q.genericRingelMatrix K ι κ)
  refine ⟨_, kerProjector (Q.genericRingelMatrix K ι κ) f g, h0, fun x hx => ?_⟩
  have hM := Q.map_eval_genericRingelMatrix x
  have hdet : eval x ((Q.genericRingelMatrix K ι κ).submatrix f g).det =
      ((Q.ringelMatrix (Q.pairFst x) (Q.pairSnd x)).submatrix f g).det := by
    rw [eval_det_submatrix, hM]
  have hrank : (Q.ringelMatrix (Q.pairFst x) (Q.pairSnd x)).rank =
      genericRank (Q.genericRingelMatrix K ι κ) := by
    rw [← hM]
    exact h x hx
  have hPr : (kerProjector (Q.genericRingelMatrix K ι κ) f g).map (eval x) =
      kerProjector (Q.ringelMatrix (Q.pairFst x) (Q.pairSnd x)) f g := by
    rw [kerProjector_map, hM]
  refine ⟨?_, fun w => ?_, fun φ hφ => ?_⟩
  · rw [IsHomGeneric, ringelRank_eq_rank_map_eval]
    exact h x hx
  · rw [mem_ker_ringel_iff_mulVec, LinearEquiv.apply_symm_apply, hPr, Matrix.mulVec_mulVec,
      mul_kerProjector _ f g (hdet ▸ hx) hrank, Matrix.zero_mulVec]
  · rw [hPr, kerProjector_mulVec_of_mulVec_eq_zero _ f g (mem_ker_ringel_iff_mulVec.mp hφ), hdet]

end FQuiver

end

end QuiverInvariants
