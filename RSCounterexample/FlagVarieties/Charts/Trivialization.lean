import RSCounterexample.FlagVarieties.Charts.BigCellFunction

/-!
# The orbit map is trivial over the big cells

For a permutation `v`, let `f_v ∈ 𝒪(GLₙ)` be the product of the determinants of the matrices
`bigCellBlock v j X` (`± ` the leading minors `Δ_{v(0..j-1)}^{0..j-1}`), and `C_v` the coordinate
ring of the big cell of `v`. Then (`bigCellTrivialization`)

  `𝒪(GLₙ)[1/f_v] ≃ₐ[R] C_v ⊗_R 𝒪(B)`,

the comorphism of `(x, b) ↦ s_v(x) · b`, where `s_v(x) = ẇ u(x)` is the adapted matrix of the
universal flag of the big cell. In other words `π⁻¹(big cell) = D(f_v) ≅ (big cell) × B`.
-/

noncomputable section

namespace FlagVarieties

open AlgebraicGeometry CategoryTheory
open Foundations Foundations.QuotientCharts
open scoped TensorProduct

universe u

variable (R : Type u) [CommRing R] {n : ℕ}

variable {R}

/-! ### Base change of matrix flags -/

theorem matrixFlag_congr {A : Type u} [CommRing A] {g g' : Matrix (Fin n) (Fin n) A}
    (h : g = g') (hg : IsUnit g.det) (hg' : IsUnit g'.det) :
    matrixFlag g hg = matrixFlag g' hg' := by
  subst h
  rfl

theorem matrixFlag_map {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (g : Matrix (Fin n) (Fin n) A) (hg : IsUnit g.det)
    (hg' : IsUnit (g.map (algebraMap A B)).det) :
    coordinateRingFlagBaseChange (B := B) (matrixFlag g hg) =
      matrixFlag (g.map (algebraMap A B)) hg' := by
  apply RingFlag.ext
  intro j
  rw [coordinateRingFlagBaseChange_step, coordinateGrassmannianBaseChange_submodule,
    matrixFlag_step, matrixFlag_step, stdSpan, stdSpan, Submodule.map_span, Submodule.map_span,
    Submodule.baseChange_span, Submodule.map_span]
  simp only [Set.image_image]
  congr 1
  apply Set.image_congr
  intro i _
  funext r
  simp [Matrix.toLin'_apply, Pi.basisFun_apply,
    TensorProduct.piScalarRight_apply, Algebra.smul_def]

/-! ### Maps out of the chart ring of a big cell -/

variable (v : Equiv.Perm (Fin n))

variable (R) in
/-- The adapted matrix `ẇ u` of the universal flag of the big cell chart. -/
abbrev bigCellUniversalMatrix : Matrix (Fin n) (Fin n) (bigCellRing R v) :=
  bigCellMatrix (inBigCell_bigCellUniversalFlag R v)

theorem permMatrix_map {A B F : Type*} [CommRing A] [CommRing B] [FunLike F A B]
    [RingHomClass F A B] (f : F) :
    (v.symm.toPEquiv.toMatrix : Matrix (Fin n) (Fin n) A).map f = v.symm.toPEquiv.toMatrix := by
  ext i j
  simp only [Matrix.map_apply, PEquiv.toMatrix_apply]
  split_ifs <;> simp

theorem isUnit_det_map {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    {g : Matrix (Fin n) (Fin n) A} (hg : IsUnit g.det) : IsUnit (g.map f).det :=
  isUnit_det_map_ringHom f hg

theorem isUnit_det_map_algHom {A B : Type*} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (f : A →ₐ[R] B) {g : Matrix (Fin n) (Fin n) A} (hg : IsUnit g.det) : IsUnit (g.map f).det :=
  isUnit_det_map_ringHom f.toRingHom hg

theorem map_map_algHom {A B C : Type*} [CommRing A] [CommRing B] [CommRing C] [Algebra R A]
    [Algebra R B] [Algebra R C] (M : Matrix (Fin n) (Fin n) A) (f : A →ₐ[R] B) (g : B →ₐ[R] C) :
    (M.map f).map g = M.map (g.comp f) :=
  Matrix.map_map

theorem blockTriangular_map_algHom {A B : Type*} [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] {M : Matrix (Fin n) (Fin n) A} (hM : M.BlockTriangular id) (f : A →ₐ[R] B) :
    (M.map f).BlockTriangular id :=
  blockTriangular_map hM f.toRingHom

theorem isLowerUnitriangular_map_algHom {A B : Type u} [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] {M : Matrix (Fin n) (Fin n) A} (hM : IsLowerUnitriangular M) (f : A →ₐ[R] B) :
    IsLowerUnitriangular (M.map f) :=
  hM.map f.toRingHom

/-- A matrix of the form `ẇ u b` (`u` lower unitriangular, `b` invertible upper triangular)
gives a flag in the big cell of `v`. -/
theorem inBigCell_matrixFlag_of_eq {A : Type u} [CommRing A] {g u b : Matrix (Fin n) (Fin n) A}
    (hu : IsLowerUnitriangular u) (hb : IsUnit b.det) (hup : b.BlockTriangular id)
    (h : g = (v.symm.toPEquiv.toMatrix : Matrix (Fin n) (Fin n) A) * u * b) (hg : IsUnit g.det) :
    InBigCell v (matrixFlag g hg) := by
  subst h
  rw [matrixFlag_mul_of_upper _ _ (isUnit_det_perm_mul v hu) hg hb hup]
  exact inBigCell_matrixFlag_perm_mul v hu

/-- Restricting the universal chart point along `a` classifies the flag of `W.map a`. -/
theorem spec_map_comp_bigCellChart {A : Type u} [CommRing A] [Algebra R A]
    (a : bigCellRing R v →ₐ[R] A) :
    Spec.map (CommRingCat.ofHom a.toRingHom) ≫ bigCellChart R v =
      FlagScheme.ofRingFlag R (matrixFlag ((bigCellUniversalMatrix R v).map a)
        (isUnit_det_map a.toRingHom (isUnit_det_bigCellMatrix _))) := by
  let : Algebra (bigCellRing R v) A := a.toRingHom.toAlgebra
  have : IsScalarTower R (bigCellRing R v) A := IsScalarTower.of_algHom a
  have e : FlagScheme.ofRingFlag R (bigCellUniversalFlag R v) =
      FlagScheme.ofRingFlag R (matrixFlag (bigCellUniversalMatrix R v)
        (isUnit_det_bigCellMatrix _)) := by
    rw [matrixFlag_bigCellMatrix]
  rw [bigCellChart_eq_ofRingFlag, e]
  change Spec.map (CommRingCat.ofHom (algebraMap (bigCellRing R v) A)) ≫ _ = _
  rw [FlagScheme.ofRingFlag_baseChange, matrixFlag_map _ _
    (isUnit_det_map a.toRingHom (isUnit_det_bigCellMatrix _))]
  rfl

/-- An `R`-algebra map out of the chart ring is determined by the image of the universal
adapted matrix. -/
theorem bigCellRing_algHom_ext {A : Type u} [CommRing A] [Algebra R A]
    {a a' : bigCellRing R v →ₐ[R] A}
    (h : (bigCellUniversalMatrix R v).map a = (bigCellUniversalMatrix R v).map a') : a = a' := by
  have h1 : Spec.map (CommRingCat.ofHom a.toRingHom) ≫ bigCellChart R v =
      Spec.map (CommRingCat.ofHom a'.toRingHom) ≫ bigCellChart R v := by
    rw [spec_map_comp_bigCellChart, spec_map_comp_bigCellChart]
    congr 1
    exact matrixFlag_congr h _ _
  have h2 := Spec.map_injective ((cancel_mono (bigCellChart R v)).mp h1)
  apply AlgHom.toRingHom_injective
  exact CommRingCat.hom_ext_iff.mp h2

/-- The universal adapted matrix maps to the adapted matrix of the classified flag. -/
theorem map_bigCellPoint {A : Type u} [CommRing A] [Algebra R A] {P : CoordinateFlag A n}
    (hP : InBigCell v P) :
    (bigCellUniversalMatrix R v).map (bigCellPoint R hP) = bigCellMatrix hP := by
  obtain ⟨u, hu, he⟩ := bigCellMatrix_eq_perm_mul (inBigCell_bigCellUniversalFlag R v)
  have hu' := isLowerUnitriangular_map_algHom hu (bigCellPoint R hP)
  have hW : (bigCellUniversalMatrix R v).map (bigCellPoint R hP) =
      (v.symm.toPEquiv.toMatrix : Matrix (Fin n) (Fin n) A) * u.map (bigCellPoint R hP) := by
    rw [bigCellUniversalMatrix, he, map_mul_algHom, permMatrix_map]
  rw [hW]
  refine (bigCellMatrix_eq_of_perm_mul hP hu' ?_).symm
  apply FlagScheme.ofRingFlag_injective (R := R)
  rw [← spec_bigCellPoint_bigCellChart hP, spec_map_comp_bigCellChart]
  congr 1
  exact matrixFlag_congr hW.symm _ _

/-! ### The coordinate rings of `D(f_v)` and of `bigCell v × B` -/

variable (R) in
/-- `𝒪(GLₙ)[1/f_v]`, the coordinate ring of `D(f_v) = π⁻¹(bigCell v)`. -/
def BigCellPreimageRing : Type u :=
  Localization.Away (bigCellFunction R v)

instance : CommRing (BigCellPreimageRing R v) :=
  inferInstanceAs (CommRing (Localization.Away (bigCellFunction R v)))

instance : Algebra (GLCoord R n) (BigCellPreimageRing R v) :=
  inferInstanceAs (Algebra (GLCoord R n) (Localization.Away (bigCellFunction R v)))

instance : Algebra R (BigCellPreimageRing R v) :=
  inferInstanceAs (Algebra R (Localization.Away (bigCellFunction R v)))

instance : IsScalarTower R (GLCoord R n) (BigCellPreimageRing R v) :=
  inferInstanceAs (IsScalarTower R (GLCoord R n) (Localization.Away (bigCellFunction R v)))

instance : IsLocalization.Away (bigCellFunction R v) (BigCellPreimageRing R v) :=
  inferInstanceAs
    (IsLocalization.Away (bigCellFunction R v) (Localization.Away (bigCellFunction R v)))

variable (R) in
/-- The restriction `𝒪(GLₙ) → 𝒪(GLₙ)[1/f_v]`. -/
def preimageInclusion : GLCoord R n →ₐ[R] BigCellPreimageRing R v :=
  IsScalarTower.toAlgHom R (GLCoord R n) (BigCellPreimageRing R v)

theorem preimageInclusion_apply (f : GLCoord R n) :
    preimageInclusion R v f = algebraMap (GLCoord R n) (BigCellPreimageRing R v) f :=
  rfl

variable (R) in
/-- `C_v ⊗_R 𝒪(B)`, the coordinate ring of `bigCell v × B`. -/
def BigCellProductRing : Type u :=
  bigCellRing R v ⊗[R] BorelCoord R n

instance : CommRing (BigCellProductRing R v) :=
  inferInstanceAs (CommRing (bigCellRing R v ⊗[R] BorelCoord R n))

instance : Algebra R (BigCellProductRing R v) :=
  inferInstanceAs (Algebra R (bigCellRing R v ⊗[R] BorelCoord R n))

variable (R) in
/-- The first factor `C_v → C_v ⊗ 𝒪(B)`. -/
def prodInl : bigCellRing R v →ₐ[R] BigCellProductRing R v :=
  Algebra.TensorProduct.includeLeft

variable (R) in
/-- The second factor `𝒪(B) → C_v ⊗ 𝒪(B)`. -/
def prodInr : BorelCoord R n →ₐ[R] BigCellProductRing R v :=
  Algebra.TensorProduct.includeRight

/-- The map out of `C_v ⊗ 𝒪(B)` given on the two factors. -/
def prodLift {A : Type u} [CommRing A] [Algebra R A] (α : bigCellRing R v →ₐ[R] A)
    (β : BorelCoord R n →ₐ[R] A) : BigCellProductRing R v →ₐ[R] A :=
  Algebra.TensorProduct.lift α β fun _ _ => Commute.all _ _

theorem prodLift_comp_prodInl {A : Type u} [CommRing A] [Algebra R A]
    (α : bigCellRing R v →ₐ[R] A) (β : BorelCoord R n →ₐ[R] A) :
    (prodLift v α β).comp (prodInl R v) = α :=
  Algebra.TensorProduct.lift_comp_includeLeft _ _ fun _ _ => Commute.all _ _

theorem prodLift_comp_prodInr {A : Type u} [CommRing A] [Algebra R A]
    (α : bigCellRing R v →ₐ[R] A) (β : BorelCoord R n →ₐ[R] A) :
    (prodLift v α β).comp (prodInr R v) = β :=
  Algebra.TensorProduct.lift_comp_includeRight _ _ fun _ _ => Commute.all _ _

theorem prod_algHom_ext {A : Type u} [CommRing A] [Algebra R A]
    {f g : BigCellProductRing R v →ₐ[R] A}
    (h₁ : f.comp (prodInl R v) = g.comp (prodInl R v))
    (h₂ : f.comp (prodInr R v) = g.comp (prodInr R v)) : f = g :=
  Algebra.TensorProduct.ext h₁ h₂

/-! ### The trivialization -/

theorem borelMatrix_map_blockTriangular {A : Type u} [CommRing A] [Algebra R A]
    (f : BorelCoord R n →ₐ[R] A) : ((borelMatrix R n).map f).BlockTriangular id :=
  blockTriangular_map_algHom (borelMatrix_blockTriangular R n) f

/-- `ẇ u ⊗ 1` written as `ẇ (u ⊗ 1)`. -/
theorem exists_universalMatrix_map {A : Type u} [CommRing A] [Algebra R A]
    (a : bigCellRing R v →ₐ[R] A) :
    ∃ u : Matrix (Fin n) (Fin n) A, IsLowerUnitriangular u ∧
      (bigCellUniversalMatrix R v).map a =
        (v.symm.toPEquiv.toMatrix : Matrix (Fin n) (Fin n) A) * u := by
  obtain ⟨u, hu, he⟩ := bigCellMatrix_eq_perm_mul (inBigCell_bigCellUniversalFlag R v)
  refine ⟨u.map a, isLowerUnitriangular_map_algHom hu a, ?_⟩
  rw [bigCellUniversalMatrix, he, map_mul_algHom, permMatrix_map]

variable (R) in
/-- The matrix `s_v(x) · b` over `C_v ⊗ 𝒪(B)`. -/
def trivMatrix : Matrix (Fin n) (Fin n) (BigCellProductRing R v) :=
  (bigCellUniversalMatrix R v).map (prodInl R v) * (borelMatrix R n).map (prodInr R v)

theorem isUnit_det_trivMatrix : IsUnit (trivMatrix R v).det := by
  rw [trivMatrix, Matrix.det_mul]
  exact (isUnit_det_map_algHom _ (isUnit_det_bigCellMatrix _)).mul
    (isUnit_det_map_algHom _ (isUnit_det_borelMatrix R n))

variable (R) in
/-- The comorphism of `bigCell v × B → GLₙ`, `(x, b) ↦ s_v(x) · b`. -/
def trivComorphism : GLCoord R n →ₐ[R] BigCellProductRing R v :=
  glPointOfMatrix R (trivMatrix R v) (isUnit_det_trivMatrix v)

theorem pointMatrix_trivComorphism :
    GLScheme.pointMatrix R n (trivComorphism R v) = trivMatrix R v :=
  pointMatrix_glPointOfMatrix R _ _

theorem isUnit_trivComorphism_bigCellFunction :
    IsUnit (trivComorphism R v (bigCellFunction R v)) := by
  refine (isUnit_map_bigCellFunction_iff v (trivComorphism R v)).mpr ?_
  obtain ⟨u, hu, hW⟩ := exists_universalMatrix_map v (prodInl R v)
  exact inBigCell_matrixFlag_of_eq v hu (isUnit_det_map_algHom _ (isUnit_det_borelMatrix R n))
    (borelMatrix_map_blockTriangular _) (by rw [pointMatrix_trivComorphism, trivMatrix, hW]) _

variable (R) in
/-- The comorphism `𝒪(GLₙ)[1/f_v] → C_v ⊗ 𝒪(B)` of `bigCell v × B → D(f_v)`,
`(x, b) ↦ s_v(x) · b`. -/
def trivForward : BigCellPreimageRing R v →ₐ[R] BigCellProductRing R v :=
  IsLocalization.Away.liftAlgHom (S := BigCellPreimageRing R v) (bigCellFunction R v)
    (isUnit_trivComorphism_bigCellFunction v)

theorem trivForward_algebraMap (f : GLCoord R n) :
    trivForward R v (algebraMap (GLCoord R n) (BigCellPreimageRing R v) f) =
      trivComorphism R v f :=
  IsLocalization.Away.lift_eq _ (isUnit_trivComorphism_bigCellFunction v) f

theorem trivForward_comp_preimageInclusion :
    (trivForward R v).comp (preimageInclusion R v) = trivComorphism R v :=
  AlgHom.ext fun f => trivForward_algebraMap v f

variable (R) in
/-- The generic matrix over `𝒪(GLₙ)[1/f_v]`. -/
def preimageMatrix : Matrix (Fin n) (Fin n) (BigCellPreimageRing R v) :=
  GLScheme.pointMatrix R n (preimageInclusion R v)

theorem isUnit_det_preimageMatrix : IsUnit (preimageMatrix R v).det :=
  (Matrix.isUnit_iff_isUnit_det _).mp (generalLinearMatrixAt_isUnit R _ n _)

theorem inBigCell_preimageMatrix :
    InBigCell v (matrixFlag (preimageMatrix R v) (isUnit_det_preimageMatrix v)) :=
  (isUnit_map_bigCellFunction_iff v (preimageInclusion R v)).mp
    (IsLocalization.Away.algebraMap_isUnit (bigCellFunction R v))

variable (R) in
/-- The `B`-component `s_v(π g)⁻¹ g` of the generic point of `D(f_v)`. -/
def preimageBorelMatrix : Matrix (Fin n) (Fin n) (BigCellPreimageRing R v) :=
  (bigCellMatrix (inBigCell_preimageMatrix (R := R) v))⁻¹ * preimageMatrix R v

theorem preimageBorelMatrix_upper : (preimageBorelMatrix R v).BlockTriangular id :=
  (matrixFlag_eq_iff _ _ (isUnit_det_bigCellMatrix _) (isUnit_det_preimageMatrix v)).mp
    (matrixFlag_bigCellMatrix _)

theorem isUnit_det_preimageBorelMatrix : IsUnit (preimageBorelMatrix R v).det := by
  rw [preimageBorelMatrix, Matrix.det_mul, Matrix.det_nonsing_inv]
  exact (isUnit_ringInverse.mpr (isUnit_det_bigCellMatrix _)).mul (isUnit_det_preimageMatrix v)

theorem mul_preimageBorelMatrix :
    bigCellMatrix (inBigCell_preimageMatrix (R := R) v) * preimageBorelMatrix R v =
      preimageMatrix R v := by
  rw [preimageBorelMatrix, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ (isUnit_det_bigCellMatrix _), Matrix.one_mul]

variable (R) in
/-- The point of `B` given by `s_v(π g)⁻¹ g`. -/
def trivBorelPart : BorelCoord R n →ₐ[R] BigCellPreimageRing R v :=
  borelPointOfMatrix R (preimageBorelMatrix R v) (isUnit_det_preimageBorelMatrix (R := R) v)
    (preimageBorelMatrix_upper (R := R) v)

theorem borelMatrix_map_trivBorelPart :
    (borelMatrix R n).map (trivBorelPart R v) = preimageBorelMatrix R v :=
  borelMatrix_map_borelPointOfMatrix R _ _ _

variable (R) in
/-- The comorphism `C_v ⊗ 𝒪(B) → 𝒪(GLₙ)[1/f_v]` of `g ↦ (π(g), s_v(π g)⁻¹ g)`. -/
def trivBackward : BigCellProductRing R v →ₐ[R] BigCellPreimageRing R v :=
  prodLift v (bigCellPoint R (inBigCell_preimageMatrix v)) (trivBorelPart R v)

theorem trivBackward_comp_trivComorphism :
    (trivBackward R v).comp (trivComorphism R v) = preimageInclusion R v := by
  apply glCoord_algHom_ext R
  rw [pointMatrix_comp, pointMatrix_trivComorphism, trivMatrix, map_mul_algHom,
    map_map_algHom, map_map_algHom, trivBackward, prodLift_comp_prodInl, prodLift_comp_prodInr,
    map_bigCellPoint, borelMatrix_map_trivBorelPart, mul_preimageBorelMatrix]
  rfl

theorem trivBackward_comp_trivForward :
    (trivBackward R v).comp (trivForward R v) = AlgHom.id R _ := by
  apply AlgHom.toRingHom_injective
  refine IsLocalization.ringHom_ext (Submonoid.powers (bigCellFunction R v))
    (RingHom.ext fun f => ?_)
  change trivBackward R v (trivForward R v (algebraMap _ _ f)) = algebraMap _ _ f
  rw [trivForward_algebraMap, ← preimageInclusion_apply, ← trivBackward_comp_trivComorphism]
  rfl

/-- The relation `s_v(π g) · (s_v(π g)⁻¹ g) = g`, read in `C_v ⊗ 𝒪(B)`. -/
theorem trivForward_map_relation :
    (bigCellMatrix (inBigCell_preimageMatrix (R := R) v)).map (trivForward R v) *
        (preimageBorelMatrix R v).map (trivForward R v) = trivMatrix R v := by
  rw [← map_mul_algHom, mul_preimageBorelMatrix, preimageMatrix, ← pointMatrix_comp,
    trivForward_comp_preimageInclusion, pointMatrix_trivComorphism]

theorem trivForward_bigCellMatrix :
    (bigCellMatrix (inBigCell_preimageMatrix (R := R) v)).map (trivForward R v) =
      (bigCellUniversalMatrix R v).map (prodInl R v) := by
  obtain ⟨uQ, huQ, hQ⟩ := bigCellMatrix_eq_perm_mul (inBigCell_preimageMatrix (R := R) v)
  obtain ⟨u, hu, hW⟩ := exists_universalMatrix_map v (prodInl R v)
  have hM : (bigCellMatrix (inBigCell_preimageMatrix (R := R) v)).map (trivForward R v) =
      (v.symm.toPEquiv.toMatrix : Matrix (Fin n) (Fin n) _) * uQ.map (trivForward R v) := by
    rw [hQ, map_mul_algHom, permMatrix_map]
  have hrel := trivForward_map_relation (R := R) v
  rw [trivMatrix, hM, hW] at hrel
  have he := eq_of_perm_mul_mul_eq v (isLowerUnitriangular_map_algHom huQ (trivForward R v)) hu
    (isUnit_det_map_algHom _ (isUnit_det_preimageBorelMatrix v))
    (isUnit_det_map_algHom _ (isUnit_det_borelMatrix R n))
    (blockTriangular_map_algHom (preimageBorelMatrix_upper v) _)
    (borelMatrix_map_blockTriangular _) hrel
  rw [hM, hW, he]

theorem trivForward_preimageBorelMatrix :
    (preimageBorelMatrix R v).map (trivForward R v) = (borelMatrix R n).map (prodInr R v) := by
  have hrel := trivForward_map_relation (R := R) v
  rw [trivForward_bigCellMatrix, trivMatrix] at hrel
  have hu : IsUnit ((bigCellUniversalMatrix R v).map (prodInl R v)).det :=
    isUnit_det_map_algHom _ (isUnit_det_bigCellMatrix _)
  exact ((Matrix.isUnit_iff_isUnit_det _).mpr hu).mul_left_cancel hrel

theorem trivForward_comp_trivBackward :
    (trivForward R v).comp (trivBackward R v) = AlgHom.id R _ := by
  apply prod_algHom_ext v
  · apply bigCellRing_algHom_ext v
    rw [AlgHom.id_comp, AlgHom.comp_assoc, trivBackward, prodLift_comp_prodInl,
      ← map_map_algHom, map_bigCellPoint, trivForward_bigCellMatrix]
  · apply borelMatrix_algHom_ext
    rw [AlgHom.id_comp, AlgHom.comp_assoc, trivBackward, prodLift_comp_prodInr,
      ← map_map_algHom, borelMatrix_map_trivBorelPart, trivForward_preimageBorelMatrix]

variable (R) in
/-- **Trivialization of the orbit map over a big cell**: the comorphism of
`bigCell v × B ≅ D(f_v) = π⁻¹(bigCell v)`, `(x, b) ↦ s_v(x) · b`, is an isomorphism
`𝒪(GLₙ)[1/f_v] ≃ₐ[R] C_v ⊗_R 𝒪(B)`. -/
def bigCellTrivialization : BigCellPreimageRing R v ≃ₐ[R] BigCellProductRing R v :=
  AlgEquiv.ofAlgHom (trivForward R v) (trivBackward R v) (trivForward_comp_trivBackward v)
    (trivBackward_comp_trivForward v)

theorem bigCellTrivialization_algebraMap (f : GLCoord R n) :
    bigCellTrivialization R v (algebraMap _ _ f) = trivComorphism R v f :=
  trivForward_algebraMap v f

end FlagVarieties
