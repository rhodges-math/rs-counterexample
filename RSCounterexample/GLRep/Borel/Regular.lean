import RSCounterexample.GLRep.Borel.Induced
import RSCounterexample.FlagVarieties.LineBundle.Model
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Coordinate.HopfAlgebra

/-!
# The regular representations of `GL_n` on its coordinate ring

Let `𝒪(G) = K[x_ij][det⁻¹]` be the coordinate ring of `G = GL_n` over a commutative ring `K`
(Tau Ceti's `TauCeti.GeneralLinear.CoordinateRing`, here `FlagVarieties.GLCoord K n`). An invertible
matrix `g ∈ GL_n(K)` acts on `𝒪(G)` by K-algebra automorphisms in two commuting ways:

* **left translation** `(g · f)(x) = f(g⁻¹ x)` (`GLRep.leftTranslHom`), substituting `g⁻¹ X` for
  the generic matrix `X`;
* **right translation** `(g · f)(x) = f(x g)` (`GLRep.rightTranslHom`), substituting `X g`.

These are the representations `GLRep.leftRegularRep` and `GLRep.rightRegularRep` of `GL_n(K)`.

**Rationality.** Restricted to the Borel subgroup `B`, every matrix coefficient of the left
regular representation is a regular function on `B`
(`GLRep.hasLocalCoeffsIn_leftRegularRep_borel`): `x_ij` is sent to `∑_k (b⁻¹)_ik x_kj` and
`det⁻¹` to `det(b) det⁻¹`.

**Sections.** For an ideal `I ⊆ 𝒪(G)` stable under left and right translations by `B` (for
instance the ideal of the preimage in `G` of a `B`-stable closed subscheme of `G/B`) and a
weight `η ∈ ℤⁿ`, the semi-invariants

  `(𝒪(G)/I)^{(B, η)} = {f | f(x b) = η(b)⁻¹ f(x) for all b ∈ B}`

(`GLRep.borelSemiInvariants`) form a representation of `B` by left translation
(`GLRep.borelSemiInvariantRep`). This is the representation of `B` on the sections of the line
bundle `𝓛(η)` over the subscheme, in the conventions of
`RSCounterexample.FlagVarieties.Modules.Character`. When it is finite-dimensional it is rational
(`GLRep.isRationalBorelRep_borelSemiInvariantRep`).
-/

namespace GLRep

open MvPolynomial TauCeti

noncomputable section

/-! ### Linear substitutions of the generic matrix -/

section Subst

variable {K : Type*} [CommRing K] {n : ℕ}

/-- The substitution `f(X) ↦ f(M X)` of the generic matrix `X`. -/
def leftSubst (M : Matrix (Fin n) (Fin n) K) :
    MvPolynomial (Fin n × Fin n) K →ₐ[K] MvPolynomial (Fin n × Fin n) K :=
  aeval fun p => ∑ k, M p.1 k • X (k, p.2)

/-- The substitution `f(X) ↦ f(X M)` of the generic matrix `X`. -/
def rightSubst (M : Matrix (Fin n) (Fin n) K) :
    MvPolynomial (Fin n × Fin n) K →ₐ[K] MvPolynomial (Fin n × Fin n) K :=
  aeval fun p => ∑ k, M k p.2 • X (p.1, k)

@[simp]
theorem leftSubst_X (M : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    leftSubst M (X (i, j)) = ∑ k, M i k • X (k, j) :=
  aeval_X _ _

@[simp]
theorem rightSubst_X (M : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    rightSubst M (X (i, j)) = ∑ k, M k j • X (i, k) :=
  aeval_X _ _

theorem leftSubst_one : leftSubst (1 : Matrix (Fin n) (Fin n) K) = AlgHom.id K _ := by
  apply MvPolynomial.algHom_ext
  rintro ⟨i, j⟩
  simp [Matrix.one_apply]

theorem rightSubst_one : rightSubst (1 : Matrix (Fin n) (Fin n) K) = AlgHom.id K _ := by
  apply MvPolynomial.algHom_ext
  rintro ⟨i, j⟩
  simp [Matrix.one_apply]

theorem leftSubst_mul (M N : Matrix (Fin n) (Fin n) K) :
    leftSubst (M * N) = (leftSubst N).comp (leftSubst M) := by
  apply MvPolynomial.algHom_ext
  rintro ⟨i, j⟩
  simp only [leftSubst_X, AlgHom.comp_apply, map_sum, map_smul, Matrix.mul_apply,
    Finset.sum_smul, Finset.smul_sum, smul_smul]
  exact Finset.sum_comm

theorem rightSubst_mul (M N : Matrix (Fin n) (Fin n) K) :
    rightSubst (M * N) = (rightSubst M).comp (rightSubst N) := by
  apply MvPolynomial.algHom_ext
  rintro ⟨i, j⟩
  simp only [rightSubst_X, AlgHom.comp_apply, map_sum, map_smul, Matrix.mul_apply,
    Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [mul_comm]

/-- Left and right substitutions commute: both send `f` to `f(M X N)`. -/
theorem leftSubst_comp_rightSubst (M N : Matrix (Fin n) (Fin n) K) :
    (leftSubst M).comp (rightSubst N) = (rightSubst N).comp (leftSubst M) := by
  apply MvPolynomial.algHom_ext
  rintro ⟨i, j⟩
  simp only [rightSubst_X, leftSubst_X, AlgHom.comp_apply, map_sum, map_smul, Finset.smul_sum,
    smul_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [mul_comm]

/-- `det(M X) = det(M) det(X)`. -/
theorem leftSubst_det (M : Matrix (Fin n) (Fin n) K) :
    leftSubst M (Matrix.mvPolynomialX (Fin n) (Fin n) K).det =
      C M.det * (Matrix.mvPolynomialX (Fin n) (Fin n) K).det := by
  rw [AlgHom.map_det]
  have : (leftSubst M).mapMatrix (Matrix.mvPolynomialX (Fin n) (Fin n) K) =
      (C : K →+* MvPolynomial (Fin n × Fin n) K).mapMatrix M *
        Matrix.mvPolynomialX (Fin n) (Fin n) K := by
    ext i j
    simp [Matrix.mul_apply, smul_eq_C_mul]
  rw [this, Matrix.det_mul, ← RingHom.map_det]

/-- `det(X M) = det(X) det(M)`. -/
theorem rightSubst_det (M : Matrix (Fin n) (Fin n) K) :
    rightSubst M (Matrix.mvPolynomialX (Fin n) (Fin n) K).det =
      (Matrix.mvPolynomialX (Fin n) (Fin n) K).det * C M.det := by
  rw [AlgHom.map_det]
  have : (rightSubst M).mapMatrix (Matrix.mvPolynomialX (Fin n) (Fin n) K) =
      Matrix.mvPolynomialX (Fin n) (Fin n) K *
        (C : K →+* MvPolynomial (Fin n × Fin n) K).mapMatrix M := by
    ext i j
    simp [Matrix.mul_apply, smul_eq_C_mul, mul_comm]
  rw [this, Matrix.det_mul, ← RingHom.map_det]

end Subst

/-! ### The coordinate ring -/

section CoordinateRing

variable (K : Type*) [CommRing K] (n : ℕ)

export FlagVarieties (GLCoord)

/-- The generic determinant `det(x_ij)`, inverted in `𝒪(GL_n)`. -/
abbrev genericDet : MvPolynomial (Fin n × Fin n) K := (Matrix.mvPolynomialX (Fin n) (Fin n) K).det

variable {K n}

/-- The coordinate function `x_ij` in `𝒪(GL_n)`. -/
def glX (i j : Fin n) : GLCoord K n :=
  algebraMap (MvPolynomial (Fin n × Fin n) K) (GLCoord K n) (X (i, j))

variable (K n) in
/-- The function `det⁻¹` in `𝒪(GL_n)`. -/
def glDetInv : GLCoord K n := IsLocalization.Away.invSelf (genericDet K n)

theorem algebraMap_genericDet_mul_glDetInv :
    algebraMap (MvPolynomial (Fin n × Fin n) K) (GLCoord K n) (genericDet K n) *
      glDetInv K n = 1 :=
  IsLocalization.Away.mul_invSelf _

/-- `𝒪(GL_n)` is generated by the coordinates `x_ij` and `det⁻¹`. -/
theorem adjoin_glX_glDetInv :
    Algebra.adjoin K (Set.range (fun p : Fin n × Fin n => glX p.1 p.2) ∪ {glDetInv K n}) = ⊤ := by
  set S := Algebra.adjoin K (Set.range (fun p : Fin n × Fin n => glX p.1 p.2) ∪ {glDetInv K n})
  have hpoly : ∀ x, algebraMap (MvPolynomial (Fin n × Fin n) K) (GLCoord K n) x ∈ S := by
    have hle : Algebra.adjoin K (Set.range (X : Fin n × Fin n → MvPolynomial (Fin n × Fin n) K)) ≤
        S.comap (GeneralLinear.coordinateRingMap K n) :=
      Algebra.adjoin_le (by
        rintro _ ⟨p, rfl⟩
        exact Algebra.subset_adjoin (Or.inl ⟨p, rfl⟩))
    rw [MvPolynomial.adjoin_range_X] at hle
    exact fun x => hle Algebra.mem_top
  have hinv : glDetInv K n ∈ S := Algebra.subset_adjoin (Or.inr rfl)
  refine eq_top_iff.mpr fun z _ => ?_
  obtain ⟨m, a, hz⟩ := IsLocalization.Away.surj (genericDet K n) z
  have : z = algebraMap (MvPolynomial (Fin n × Fin n) K) (GLCoord K n) a *
      glDetInv K n ^ m := by
    rw [← hz, mul_assoc, ← mul_pow, algebraMap_genericDet_mul_glDetInv, one_pow, mul_one]
  rw [this]
  exact mul_mem (hpoly a) (pow_mem hinv m)

/-! ### Substitutions extended to the coordinate ring -/

theorem isUnit_leftSubst_genericDet {M : Matrix (Fin n) (Fin n) K} (hM : IsUnit M.det) :
    IsUnit ((GeneralLinear.coordinateRingMap K n).comp (leftSubst M) (genericDet K n)) := by
  rw [AlgHom.comp_apply, leftSubst_det, map_mul, ← MvPolynomial.algebraMap_eq, AlgHom.commutes]
  exact (hM.map _).mul (IsLocalization.Away.algebraMap_isUnit _)

theorem isUnit_rightSubst_genericDet {M : Matrix (Fin n) (Fin n) K} (hM : IsUnit M.det) :
    IsUnit ((GeneralLinear.coordinateRingMap K n).comp (rightSubst M) (genericDet K n)) := by
  rw [AlgHom.comp_apply, rightSubst_det, map_mul, ← MvPolynomial.algebraMap_eq, AlgHom.commutes]
  exact (IsLocalization.Away.algebraMap_isUnit _).mul (hM.map _)

/-- The algebra endomorphism `f ↦ f(M X)` of `𝒪(GL_n)`, for an invertible matrix `M`. -/
def leftSubstAway (M : Matrix (Fin n) (Fin n) K) (hM : IsUnit M.det) :
    GLCoord K n →ₐ[K] GLCoord K n :=
  IsLocalization.Away.liftAlgHom (genericDet K n) (isUnit_leftSubst_genericDet hM)

/-- The algebra endomorphism `f ↦ f(X M)` of `𝒪(GL_n)`, for an invertible matrix `M`. -/
def rightSubstAway (M : Matrix (Fin n) (Fin n) K) (hM : IsUnit M.det) :
    GLCoord K n →ₐ[K] GLCoord K n :=
  IsLocalization.Away.liftAlgHom (genericDet K n) (isUnit_rightSubst_genericDet hM)

theorem leftSubstAway_algebraMap {M : Matrix (Fin n) (Fin n) K} (hM : IsUnit M.det)
    (x : MvPolynomial (Fin n × Fin n) K) :
    leftSubstAway M hM (algebraMap _ _ x) =
      algebraMap (MvPolynomial (Fin n × Fin n) K) (GLCoord K n) (leftSubst M x) :=
  IsLocalization.Away.lift_eq (genericDet K n) (isUnit_leftSubst_genericDet hM) x

theorem rightSubstAway_algebraMap {M : Matrix (Fin n) (Fin n) K} (hM : IsUnit M.det)
    (x : MvPolynomial (Fin n × Fin n) K) :
    rightSubstAway M hM (algebraMap _ _ x) =
      algebraMap (MvPolynomial (Fin n × Fin n) K) (GLCoord K n) (rightSubst M x) :=
  IsLocalization.Away.lift_eq (genericDet K n) (isUnit_rightSubst_genericDet hM) x

theorem leftSubstAway_comp {M : Matrix (Fin n) (Fin n) K} (hM : IsUnit M.det) :
    (leftSubstAway M hM).comp (GeneralLinear.coordinateRingMap K n) =
      (GeneralLinear.coordinateRingMap K n).comp (leftSubst M) :=
  AlgHom.ext fun x => leftSubstAway_algebraMap hM x

theorem rightSubstAway_comp {M : Matrix (Fin n) (Fin n) K} (hM : IsUnit M.det) :
    (rightSubstAway M hM).comp (GeneralLinear.coordinateRingMap K n) =
      (GeneralLinear.coordinateRingMap K n).comp (rightSubst M) :=
  AlgHom.ext fun x => rightSubstAway_algebraMap hM x

theorem leftSubstAway_congr {M N : Matrix (Fin n) (Fin n) K} (hMN : M = N) (hM : IsUnit M.det)
    (hN : IsUnit N.det) : leftSubstAway M hM = leftSubstAway N hN := by
  subst hMN
  rfl

theorem rightSubstAway_congr {M N : Matrix (Fin n) (Fin n) K} (hMN : M = N) (hM : IsUnit M.det)
    (hN : IsUnit N.det) : rightSubstAway M hM = rightSubstAway N hN := by
  subst hMN
  rfl

theorem leftSubstAway_one (h : IsUnit (1 : Matrix (Fin n) (Fin n) K).det) :
    leftSubstAway 1 h = AlgHom.id K _ := by
  apply GeneralLinear.algHom_ext_away
  rw [leftSubstAway_comp, leftSubst_one]
  rfl

theorem rightSubstAway_one (h : IsUnit (1 : Matrix (Fin n) (Fin n) K).det) :
    rightSubstAway 1 h = AlgHom.id K _ := by
  apply GeneralLinear.algHom_ext_away
  rw [rightSubstAway_comp, rightSubst_one]
  rfl

theorem leftSubstAway_comp_leftSubstAway {M N : Matrix (Fin n) (Fin n) K} (hM : IsUnit M.det)
    (hN : IsUnit N.det) :
    (leftSubstAway N hN).comp (leftSubstAway M hM) =
      leftSubstAway (M * N) (by rw [Matrix.det_mul]; exact hM.mul hN) := by
  apply GeneralLinear.algHom_ext_away
  rw [AlgHom.comp_assoc, leftSubstAway_comp, ← AlgHom.comp_assoc, leftSubstAway_comp,
    AlgHom.comp_assoc, leftSubstAway_comp, leftSubst_mul]

theorem rightSubstAway_comp_rightSubstAway {M N : Matrix (Fin n) (Fin n) K} (hM : IsUnit M.det)
    (hN : IsUnit N.det) :
    (rightSubstAway M hM).comp (rightSubstAway N hN) =
      rightSubstAway (M * N) (by rw [Matrix.det_mul]; exact hM.mul hN) := by
  apply GeneralLinear.algHom_ext_away
  rw [AlgHom.comp_assoc, rightSubstAway_comp, ← AlgHom.comp_assoc, rightSubstAway_comp,
    AlgHom.comp_assoc, rightSubstAway_comp, rightSubst_mul]

theorem leftSubstAway_comp_rightSubstAway {M N : Matrix (Fin n) (Fin n) K} (hM : IsUnit M.det)
    (hN : IsUnit N.det) :
    (leftSubstAway M hM).comp (rightSubstAway N hN) =
      (rightSubstAway N hN).comp (leftSubstAway M hM) := by
  apply GeneralLinear.algHom_ext_away
  apply MvPolynomial.algHom_ext
  intro p
  simp only [AlgHom.comp_apply, GeneralLinear.coordinateRingMap_apply, leftSubstAway_algebraMap,
    rightSubstAway_algebraMap]
  exact congrArg _ (AlgHom.congr_fun (leftSubst_comp_rightSubst M N) (X p))

/-! ### Left and right translations -/

variable (K n) in
/-- **Left translation** of `GL_n(K)` on `𝒪(GL_n)`: `(g · f)(x) = f(g⁻¹ x)`. -/
def leftTranslHom : GL (Fin n) K →* (GLCoord K n →ₐ[K] GLCoord K n) where
  toFun g := leftSubstAway ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
    (Matrix.isUnits_det_units _)
  map_one' := by
    rw [leftSubstAway_congr (by rw [inv_one, Units.val_one]) _ (by simp)]
    exact leftSubstAway_one _
  map_mul' g h := by
    change _ = (leftSubstAway _ _).comp (leftSubstAway _ _)
    rw [leftSubstAway_comp_leftSubstAway]
    exact leftSubstAway_congr (by rw [mul_inv_rev, Units.val_mul]) _ _

variable (K n) in
/-- **Right translation** of `GL_n(K)` on `𝒪(GL_n)`: `(g · f)(x) = f(x g)`. -/
def rightTranslHom : GL (Fin n) K →* (GLCoord K n →ₐ[K] GLCoord K n) where
  toFun g := rightSubstAway (g : Matrix (Fin n) (Fin n) K) (Matrix.isUnits_det_units _)
  map_one' := by
    rw [rightSubstAway_congr Units.val_one _ (by simp)]
    exact rightSubstAway_one _
  map_mul' g h := by
    change _ = (rightSubstAway _ _).comp (rightSubstAway _ _)
    rw [rightSubstAway_comp_rightSubstAway]
    exact rightSubstAway_congr (Units.val_mul g h) _ _

theorem leftTranslHom_apply (g : GL (Fin n) K) :
    leftTranslHom K n g = leftSubstAway ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
      (Matrix.isUnits_det_units _) :=
  rfl

theorem rightTranslHom_apply (g : GL (Fin n) K) :
    rightTranslHom K n g =
      rightSubstAway (g : Matrix (Fin n) (Fin n) K) (Matrix.isUnits_det_units _) :=
  rfl

theorem leftTranslHom_glX (g : GL (Fin n) K) (i j : Fin n) :
    leftTranslHom K n g (glX i j) =
      ∑ k, ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i k • glX k j := by
  rw [leftTranslHom_apply, glX, leftSubstAway_algebraMap, leftSubst_X,
    ← GeneralLinear.coordinateRingMap_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul]
  rfl

theorem rightTranslHom_glX (g : GL (Fin n) K) (i j : Fin n) :
    rightTranslHom K n g (glX i j) =
      ∑ k, (g : Matrix (Fin n) (Fin n) K) k j • glX i k := by
  rw [rightTranslHom_apply, glX, rightSubstAway_algebraMap, rightSubst_X,
    ← GeneralLinear.coordinateRingMap_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul]
  rfl

/-- Left translation sends `det⁻¹` to `det(g) det⁻¹`. -/
theorem leftTranslHom_glDetInv (g : GL (Fin n) K) :
    leftTranslHom K n g (glDetInv K n) = (g : Matrix (Fin n) (Fin n) K).det • glDetInv K n := by
  set u := leftTranslHom K n g (glDetInv K n)
  set e := glDetInv K n
  set D := algebraMap (MvPolynomial (Fin n × Fin n) K) (GLCoord K n) (genericDet K n)
  set a := algebraMap K (GLCoord K n) ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det
  set c := algebraMap K (GLCoord K n) (g : Matrix (Fin n) (Fin n) K).det
  have h2 : D * e = 1 := algebraMap_genericDet_mul_glDetInv
  have hLD : leftTranslHom K n g D = a * D := by
    rw [leftTranslHom_apply, leftSubstAway_algebraMap, leftSubst_det, map_mul,
      ← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
  have h1 : a * D * u = 1 := by
    rw [← hLD, ← map_mul, h2, map_one]
  have h3 : c * a = 1 := by
    rw [← map_mul, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.det_one, map_one]
  rw [Algebra.smul_def]
  linear_combination (-u) * h2 + (c * e) * h1 - (u * D * e) * h3

/-- Left and right translations commute. -/
theorem leftTranslHom_comp_rightTranslHom (g h : GL (Fin n) K) :
    (leftTranslHom K n g).comp (rightTranslHom K n h) =
      (rightTranslHom K n h).comp (leftTranslHom K n g) :=
  leftSubstAway_comp_rightSubstAway (Matrix.isUnits_det_units _) (Matrix.isUnits_det_units _)

end CoordinateRing

/-! ### The regular representations -/

section Regular

variable (K : Type*) [Field K] (n : ℕ)

/-- The **left regular representation** of `GL_n(K)` on `𝒪(GL_n)`: `(g · f)(x) = f(g⁻¹ x)`. -/
abbrev leftRegularRep : Representation K (GL (Fin n) K) (GLCoord K n) :=
  algebraRep (leftTranslHom K n)

/-- The **right regular representation** of `GL_n(K)` on `𝒪(GL_n)`: `(g · f)(x) = f(x g)`. -/
abbrev rightRegularRep : Representation K (GL (Fin n) K) (GLCoord K n) :=
  algebraRep (rightTranslHom K n)

variable {K n}

theorem leftRegularRep_comp_rightRegularRep (g h : GL (Fin n) K) :
    leftRegularRep K n g ∘ₗ rightRegularRep K n h =
      rightRegularRep K n h ∘ₗ leftRegularRep K n g :=
  LinearMap.ext fun f => AlgHom.congr_fun (leftTranslHom_comp_rightTranslHom g h) f

/-! ### Rationality of the left regular representation of `B` -/

/-- The adjugate entries of an element of `B` are regular functions on `B`. -/
theorem adjugate_mem_borelFunctions (i k : Fin n) :
    (fun b : borel K n => ((b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).adjugate i k) ∈
      borelFunctions K n := by
  refine mem_coordFunctions.mpr
    ⟨rename Sum.inl ((Matrix.mvPolynomialX (Fin n) (Fin n) K).adjugate i k), fun b => ?_⟩
  rw [eval_rename]
  have h1 : (borelCoord K n b ∘ Sum.inl) =
      fun p : Fin n × Fin n => ((b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) p.1 p.2 :=
    rfl
  rw [h1]
  conv_lhs => rw [← Matrix.mvPolynomialX_mapMatrix_eval
    ((b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)]
  rw [← RingHom.map_adjugate]
  rfl

/-- The entries of the inverse of an element of `B` are regular functions on `B`. -/
theorem inv_apply_mem_borelFunctions (i k : Fin n) :
    (fun b : borel K n => (((b : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i k) ∈
      borelFunctions K n := by
  have : (fun b : borel K n =>
      (((b : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i k) =
      (∏ l, fun b : borel K n => (((borelDiag K n b l)⁻¹ : Kˣ) : K)) *
        fun b : borel K n => ((b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).adjugate i k := by
    funext b
    rw [Matrix.coe_units_inv, Matrix.inv_def, Pi.mul_apply, Finset.prod_apply, Matrix.smul_apply,
      smul_eq_mul, ← Matrix.GeneralLinearGroup.val_det_apply, Ring.inverse_unit, det_borel,
      ← Finset.prod_inv_distrib, Units.coe_prod]
  rw [this]
  exact mul_mem (prod_mem fun l _ => diag_inv_mem_borelFunctions l)
    (adjugate_mem_borelFunctions i k)

/-- The determinant is a regular function on `B`. -/
theorem det_mem_borelFunctions :
    (fun b : borel K n => ((b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det) ∈
      borelFunctions K n := by
  have : (fun b : borel K n => ((b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det) =
      ∏ l, fun b : borel K n => ((borelDiag K n b l : Kˣ) : K) := by
    funext b
    rw [Finset.prod_apply, ← Matrix.GeneralLinearGroup.val_det_apply, det_borel, Units.coe_prod]
  rw [this]
  exact prod_mem fun l _ => diag_mem_borelFunctions l

/-- **The matrix coefficients of the left regular representation of `B` on `𝒪(GL_n)` are regular
functions on `B`.** -/
theorem hasLocalCoeffsIn_leftRegularRep_borel :
    HasLocalCoeffsIn (borelFunctions K n) ((leftRegularRep K n).comp (borel K n).subtype) := by
  have h := hasLocalCoeffsIn_algebraRep (A := borelFunctions K n)
    ((leftTranslHom K n).comp (borel K n).subtype) adjoin_glX_glDetInv ?_
  · exact h
  rintro r (⟨p, rfl⟩ | hr)
  · have : orbitAlgHom ((leftTranslHom K n).comp (borel K n).subtype) (glX p.1 p.2) =
        fun b : borel K n => ∑ k, (fun b : borel K n =>
          (((b : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) p.1 k) b •
            glX k p.2 := by
      funext b
      exact leftTranslHom_glX _ _ _
    rw [this]
    exact sum_smul_mem_range_coeffTensorHom _ _ (fun k _ => inv_apply_mem_borelFunctions _ k) _
  · rw [Set.mem_singleton_iff] at hr
    subst hr
    have : orbitAlgHom ((leftTranslHom K n).comp (borel K n).subtype) (glDetInv K n) =
        fun b : borel K n => (fun b : borel K n =>
          ((b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det) b • glDetInv K n := by
      funext b
      exact leftTranslHom_glDetInv _
    rw [this]
    exact smul_mem_range_coeffTensorHom det_mem_borelFunctions _

end Regular

/-! ### Semi-invariants in quotients of the coordinate ring -/

section Quotient

variable {K : Type*} [Field K] {n : ℕ} (I : Ideal (GLCoord K n))

/-- The ideal `I` is stable under left translation by `B`. -/
def IsLeftBorelStable : Prop := ∀ b ∈ borel K n, I ≤ I.comap (leftTranslHom K n b)

/-- The ideal `I` is stable under right translation by `B`. -/
def IsRightBorelStable : Prop := ∀ b ∈ borel K n, I ≤ I.comap (rightTranslHom K n b)

/-- Left translation by `B` on `𝒪(GL_n)/I`. -/
def quotLeftTranslHom (hI : IsLeftBorelStable I) :
    borel K n →* (GLCoord K n ⧸ I →ₐ[K] GLCoord K n ⧸ I) where
  toFun b := Ideal.quotientMapₐ I (leftTranslHom K n b) (hI b b.2)
  map_one' := Ideal.Quotient.algHom_ext _ (AlgHom.ext fun x => by simp)
  map_mul' b b' := Ideal.Quotient.algHom_ext _ (AlgHom.ext fun x => by simp)

/-- Right translation by `B` on `𝒪(GL_n)/I`. -/
def quotRightTranslHom (hI : IsRightBorelStable I) :
    borel K n →* (GLCoord K n ⧸ I →ₐ[K] GLCoord K n ⧸ I) where
  toFun b := Ideal.quotientMapₐ I (rightTranslHom K n b) (hI b b.2)
  map_one' := Ideal.Quotient.algHom_ext _ (AlgHom.ext fun x => by simp)
  map_mul' b b' := Ideal.Quotient.algHom_ext _ (AlgHom.ext fun x => by simp)

/-- The representation of `B` on `𝒪(GL_n)/I` by left translation. -/
abbrev quotLeftRep (hI : IsLeftBorelStable I) :
    Representation K (borel K n) (GLCoord K n ⧸ I) :=
  algebraRep (quotLeftTranslHom I hI)

/-- The representation of `B` on `𝒪(GL_n)/I` by right translation. -/
abbrev quotRightRep (hI : IsRightBorelStable I) :
    Representation K (borel K n) (GLCoord K n ⧸ I) :=
  algebraRep (quotRightTranslHom I hI)

theorem quotLeftRep_comp_quotRightRep (hL : IsLeftBorelStable I) (hR : IsRightBorelStable I)
    (b b' : borel K n) :
    quotLeftRep I hL b ∘ₗ quotRightRep I hR b' = quotRightRep I hR b' ∘ₗ quotLeftRep I hL b := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  · change Ideal.Quotient.mk I (leftTranslHom K n b (rightTranslHom K n b' x)) =
      Ideal.Quotient.mk I (rightTranslHom K n b' (leftTranslHom K n b x))
    rw [← AlgHom.comp_apply, leftTranslHom_comp_rightTranslHom, AlgHom.comp_apply]

/-- The left translation representation of `B` on `𝒪(GL_n)/I` has regular matrix
coefficients. -/
theorem hasLocalCoeffsIn_quotLeftRep (hL : IsLeftBorelStable I) :
    HasLocalCoeffsIn (borelFunctions K n) (quotLeftRep I hL) :=
  hasLocalCoeffsIn_leftRegularRep_borel.of_surjective
    ⟨(Ideal.Quotient.mkₐ K I).toLinearMap, fun _ => rfl⟩ Ideal.Quotient.mk_surjective

/-- The **semi-invariants** `(𝒪(GL_n)/I)^{(B, η)}`: the classes `f` with
`f(x b) = η(b)⁻¹ f(x)` for all `b ∈ B`. -/
def borelSemiInvariants (hR : IsRightBorelStable I) (η : Fin n → ℤ) :
    Submodule K (GLCoord K n ⧸ I) :=
  semiInvariants (quotRightRep I hR) (borelChar K n η)

theorem mem_borelSemiInvariants {hR : IsRightBorelStable I} {η : Fin n → ℤ}
    {f : GLCoord K n ⧸ I} :
    f ∈ borelSemiInvariants I hR η ↔
      ∀ b, quotRightTranslHom I hR b f = (((borelChar K n η b)⁻¹ : Kˣ) : K) • f :=
  Iff.rfl

/-- The semi-invariants `(𝒪(GL_n)/I)^{(B, η)}` as a subrepresentation of the left translation
representation of `B`. -/
def borelSemiInvariantSubrep (hL : IsLeftBorelStable I) (hR : IsRightBorelStable I)
    (η : Fin n → ℤ) : Subrepresentation (quotLeftRep I hL) :=
  semiInvariantSubrep (quotLeftRep I hL) (quotRightRep I hR)
    (quotLeftRep_comp_quotRightRep I hL hR) (borelChar K n η)

/-- **The representation of `B` on `(𝒪(GL_n)/I)^{(B, η)}` by left translation**: for `I` the
ideal of the preimage in `GL_n` of a `B`-stable closed subscheme `X ⊆ G/B`, these are the sections
of `𝓛(η)` over `X` with the action of `B` induced by the line bundle. -/
abbrev borelSemiInvariantRep (hL : IsLeftBorelStable I) (hR : IsRightBorelStable I)
    (η : Fin n → ℤ) :
    Representation K (borel K n) (borelSemiInvariantSubrep I hL hR η).toSubmodule :=
  (borelSemiInvariantSubrep I hL hR η).toRepresentation

theorem hasLocalCoeffsIn_borelSemiInvariantRep (hL : IsLeftBorelStable I)
    (hR : IsRightBorelStable I) (η : Fin n → ℤ) :
    HasLocalCoeffsIn (borelFunctions K n) (borelSemiInvariantRep I hL hR η) :=
  (hasLocalCoeffsIn_quotLeftRep I hL).subrepresentation _

/-- **A finite-dimensional space of semi-invariants `(𝒪(GL_n)/I)^{(B, η)}` is a rational
representation of `B`.** -/
theorem isRationalBorelRep_borelSemiInvariantRep (hL : IsLeftBorelStable I)
    (hR : IsRightBorelStable I) (η : Fin n → ℤ)
    [FiniteDimensional K (borelSemiInvariantSubrep I hL hR η).toSubmodule] :
    IsRationalBorelRep (borelSemiInvariantRep I hL hR η) :=
  (hasLocalCoeffsIn_borelSemiInvariantRep I hL hR η).hasCoeffsIn

/-! ### Restriction -/

variable {I} {J : Ideal (GLCoord K n)}

/-- The quotient map `𝒪(GL_n)/I → 𝒪(GL_n)/J` for `I ≤ J` intertwines left translations. -/
def quotLeftRepFactor (hIJ : I ≤ J) (hI : IsLeftBorelStable I) (hJ : IsLeftBorelStable J) :
    (quotLeftRep I hI).IntertwiningMap (quotLeftRep J hJ) where
  toLinearMap := (Ideal.Quotient.factorₐ K hIJ).toLinearMap
  isIntertwining' b := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl

theorem quotLeftRepFactor_mk (hIJ : I ≤ J) (hI : IsLeftBorelStable I) (hJ : IsLeftBorelStable J)
    (x : GLCoord K n) :
    quotLeftRepFactor hIJ hI hJ (Ideal.Quotient.mk I x) = Ideal.Quotient.mk J x :=
  rfl

/-- **Restriction of sections**: for `I ≤ J` (that is, from a `B`-stable closed subscheme to a
smaller one), the quotient map `𝒪(GL_n)/I → 𝒪(GL_n)/J` sends `(B, η)`-semi-invariants to
`(B, η)`-semi-invariants, compatibly with the action of `B`. -/
def borelSemiInvariantRestrict (hIJ : I ≤ J) (hLI : IsLeftBorelStable I)
    (hRI : IsRightBorelStable I) (hLJ : IsLeftBorelStable J) (hRJ : IsRightBorelStable J)
    (η : Fin n → ℤ) :
    (borelSemiInvariantRep I hLI hRI η).IntertwiningMap (borelSemiInvariantRep J hLJ hRJ η) where
  toFun f := ⟨quotLeftRepFactor hIJ hLI hLJ f, fun b => by
    obtain ⟨f, hf⟩ := f
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective f
    have := hf b
    change Ideal.Quotient.mk J (rightTranslHom K n b x) =
      (((borelChar K n η b)⁻¹ : Kˣ) : K) • Ideal.Quotient.mk J x
    change Ideal.Quotient.mk I (rightTranslHom K n b x) =
      (((borelChar K n η b)⁻¹ : Kˣ) : K) • Ideal.Quotient.mk I x at this
    have h2 := congrArg (Ideal.Quotient.factorₐ K hIJ) this
    rwa [map_smul] at h2⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)
  isIntertwining' b := LinearMap.ext fun f =>
    Subtype.ext ((quotLeftRepFactor hIJ hLI hLJ).isIntertwining _ _ b (f : GLCoord K n ⧸ I))

theorem coe_borelSemiInvariantRestrict (hIJ : I ≤ J) (hLI : IsLeftBorelStable I)
    (hRI : IsRightBorelStable I) (hLJ : IsLeftBorelStable J) (hRJ : IsRightBorelStable J)
    (η : Fin n → ℤ) (f : (borelSemiInvariantSubrep I hLI hRI η).toSubmodule) :
    (borelSemiInvariantRestrict hIJ hLI hRI hLJ hRJ η f : GLCoord K n ⧸ J) =
      Ideal.Quotient.factorₐ K hIJ (f : GLCoord K n ⧸ I) :=
  rfl

end Quotient

end

end GLRep
