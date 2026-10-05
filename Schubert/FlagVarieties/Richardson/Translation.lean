import Schubert.FlagVarieties.Richardson.Schemes

/-!
# Translation by `w₀` and opposite Schubert varieties

Over a commutative ring `R`, using the action `GL_n ×_R Fl_n ⟶ Fl_n`:

* `translate R g hg : Fl_n ⟶ Fl_n`, `x ↦ g · x`, for `g ∈ GL_n(R)`; on points it sends the flag of
  `M` to the flag of `g M` (`ofRingFlag_matrixFlag_translate`); `translate_comp`, `translate_one`,
  `translate_toSpec`; **`translateIso R g hg : Fl_n ≅ Fl_n`**, an automorphism over `Spec R`.
* `w₀ = Fin.revPerm` (the longest element) and `translateW₀ R = translate R ẇ₀ _`, an involution
  (`translateW₀_comp_self`).
* `B⁻ = ẇ₀ B ẇ₀`: `borelConj : 𝒪(B) → 𝒪(B⁻)` is an isomorphism (`isIso_borelConj`), and
  `oppSchubertOrbitMap_eq_comp`: `(b ↦ b · v̇E•) = (b ↦ ẇ₀ (ẇ₀ b ẇ₀) (w₀v)˙E•)`.
* **`oppositeSchubertVariety_eq_map`**: `X^v = t_{w₀}(X_{w₀ v})` as ideal sheaves, and
  `schubertVariety_eq_map`: `X_w = t_{w₀}(X^{w₀ w})`.

Consequences, over a field of characteristic `0`:

* **`oppositeSchubertVariety_le_iff`**: the opposite closure relation, `X^u ⊆ X^v ⟺ v ≤ u`
  (as ideal sheaves: `I(X^v) ≤ I(X^u)`).
* **`oppositeSchubertVariety_le_ker_permFlag_iff`**: `u̇E• ∈ X^v ⟺ v ≤ u`.
* **`richardsonVariety_le_ker_permFlag_iff`**: the `T`-fixed points of `X_w ∩ X^v` are the `u̇E•`
  with `v ≤ u ≤ w`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace FlagVarieties.Richardson

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Foundations Foundations.QuotientCharts Plucker
open PointModel (schubertVariety_le_iff)

universe u

variable (R : Type u) [CommRing R] {n : ℕ}

/-! ### Translation by an element of `GL_n(R)` -/

/-- **Translation by `g ∈ GL_n(R)`**, `x ↦ g · x`, through the action. -/
def translate (g : Matrix (Fin n) (Fin n) R) (hg : IsUnit g.det) :
    FlagScheme R n ⟶ FlagScheme R n :=
  pullback.lift (FlagScheme.toSpec R n ≫ GLScheme.point R n (glPointOfMatrix R g hg)) (𝟙 _)
    (by
      rw [Category.assoc, Category.id_comp]
      change _ ≫ generalLinearGroupPoint R R n _ ≫ (TauCeti.GeneralLinear.groupScheme R n).X.hom = _
      rw [generalLinearGroupPoint_toSpec, Algebra.algebraMap_self, CommRingCat.ofHom_id,
        Spec.map_id, Category.comp_id]) ≫
    FlagScheme.action R n

variable {R}

theorem spec_map_comp_point {A : Type u} [CommRing A] [Algebra R A]
    (k : TauCeti.GeneralLinear.CoordinateRing R n →ₐ[R] R) :
    Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ GLScheme.point R n k =
      GLScheme.point R n ((Algebra.ofId R A).comp k) := by
  change Spec.map _ ≫ Spec.map _ ≫ _ = Spec.map _ ≫ _
  rw [← Category.assoc, ← Spec.map_comp]
  rfl

/-- On points, translation sends `P` to `g · P`. -/
theorem ofRingFlag_translate {A : Type u} [CommRing A] [Algebra R A]
    (g : Matrix (Fin n) (Fin n) R) (hg : IsUnit g.det) (P : CoordinateFlag A n) :
    FlagScheme.ofRingFlag R P ≫ translate R g hg =
      FlagScheme.ofRingFlag R (P.transport
        (GLScheme.pointEquiv R n ((Algebra.ofId R A).comp (glPointOfMatrix R g hg)))) := by
  rw [translate, ← Category.assoc, ← FlagScheme.action_point]
  congr 1
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, ← Category.assoc,
      FlagScheme.ofRingFlag_toSpec, spec_map_comp_point]
  · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.comp_id]

/-- On flags of matrices, translation is left multiplication. -/
theorem ofRingFlag_matrixFlag_translate {A : Type u} [CommRing A] [Algebra R A]
    (g : Matrix (Fin n) (Fin n) R) (hg : IsUnit g.det) (M : Matrix (Fin n) (Fin n) A)
    (hM : IsUnit M.det) (hgM : IsUnit (g.map (algebraMap R A) * M).det) :
    FlagScheme.ofRingFlag R (matrixFlag M hM) ≫ translate R g hg =
      FlagScheme.ofRingFlag R (matrixFlag (g.map (algebraMap R A) * M) hgM) := by
  rw [ofRingFlag_translate]
  congr 1
  apply matrixFlag_transport
  change ⇑(Matrix.toLin' (GLScheme.pointMatrix R n ((Algebra.ofId R A).comp
    (glPointOfMatrix R g hg)))) = _
  rw [pointMatrix_comp, pointMatrix_glPointOfMatrix]
  rfl

theorem translate_toSpec (g : Matrix (Fin n) (Fin n) R) (hg : IsUnit g.det) :
    translate R g hg ≫ FlagScheme.toSpec R n = FlagScheme.toSpec R n := by
  rw [translate, Category.assoc, FlagScheme.action_toSpec, pullback.lift_snd_assoc,
    Category.id_comp]

theorem specChart_eq_matrixFlag (v : Equiv.Perm (Fin n)) :
    specChart R n v = FlagScheme.ofRingFlag R
      (matrixFlag (chartMatrix R n v) (isUnit_det_bigCellMatrix _)) := by
  rw [specChart, bigCellChart_eq_ofRingFlag]
  exact congrArg _ (matrixFlag_bigCellMatrix _).symm

theorem translate_comp (g h : Matrix (Fin n) (Fin n) R) (hg : IsUnit g.det) (hh : IsUnit h.det)
    (hhg : IsUnit (h * g).det) :
    translate R g hg ≫ translate R h hh = translate R (h * g) hhg := by
  refine (bigCellCover R n).hom_ext _ _ fun v => ?_
  change specChart R n v ≫ _ = specChart R n v ≫ _
  have hA := isUnit_det_bigCellMatrix (inBigCell_bigCellUniversalFlag R v)
  have h1 : IsUnit (g.map (algebraMap R (bigCellRing R v)) * chartMatrix R n v).det := by
    rw [Matrix.det_mul]
    exact (isUnit_det_map _ hg).mul hA
  have h2 : IsUnit (h.map (algebraMap R (bigCellRing R v)) *
      (g.map (algebraMap R (bigCellRing R v)) * chartMatrix R n v)).det := by
    rw [Matrix.det_mul]
    exact (isUnit_det_map _ hh).mul h1
  have h3 : IsUnit ((h * g).map (algebraMap R (bigCellRing R v)) * chartMatrix R n v).det := by
    rw [Matrix.det_mul]
    exact (isUnit_det_map _ hhg).mul hA
  rw [specChart_eq_matrixFlag, ← Category.assoc, ofRingFlag_matrixFlag_translate _ _ _ _ h1,
    ofRingFlag_matrixFlag_translate _ _ _ _ h2, ofRingFlag_matrixFlag_translate _ _ _ _ h3]
  congr 1
  apply matrixFlag_congr
  rw [Matrix.map_mul, mul_assoc]

theorem translate_congr {g g' : Matrix (Fin n) (Fin n) R} (e : g = g') (hg : IsUnit g.det)
    (hg' : IsUnit g'.det) : translate R g hg = translate R g' hg' := by
  subst e
  rfl

theorem translate_one :
    translate R (1 : Matrix (Fin n) (Fin n) R) (by rw [Matrix.det_one]; exact isUnit_one) =
      𝟙 (FlagScheme R n) := by
  refine (bigCellCover R n).hom_ext _ _ fun v => ?_
  change specChart R n v ≫ _ = specChart R n v ≫ _
  have hA := isUnit_det_bigCellMatrix (inBigCell_bigCellUniversalFlag R v)
  have h1 : IsUnit ((1 : Matrix (Fin n) (Fin n) R).map (algebraMap R (bigCellRing R v)) *
      chartMatrix R n v).det := by
    rw [Matrix.map_one _ (map_zero _) (map_one _), one_mul]
    exact hA
  rw [Category.comp_id, specChart_eq_matrixFlag, ofRingFlag_matrixFlag_translate _ _ _ _ h1]
  congr 1
  apply matrixFlag_congr
  rw [Matrix.map_one _ (map_zero _) (map_one _), one_mul]

/-- **Translation by `g ∈ GL_n(R)` is an automorphism of `Fl_n` over `R`**. -/
def translateIso (g : Matrix (Fin n) (Fin n) R) (hg : IsUnit g.det) :
    FlagScheme R n ≅ FlagScheme R n where
  hom := translate R g hg
  inv := translate R g⁻¹ (Matrix.isUnit_nonsing_inv_det g hg)
  hom_inv_id := by
    have h1 : IsUnit (Matrix.det (1 : Matrix (Fin n) (Fin n) R)) := by
      rw [Matrix.det_one]
      exact isUnit_one
    have h2 : IsUnit (g⁻¹ * g).det := by rwa [Matrix.nonsing_inv_mul g hg]
    rw [translate_comp _ _ _ _ h2, translate_congr (Matrix.nonsing_inv_mul g hg) h2 h1,
      translate_one]
  inv_hom_id := by
    have h1 : IsUnit (Matrix.det (1 : Matrix (Fin n) (Fin n) R)) := by
      rw [Matrix.det_one]
      exact isUnit_one
    have h2 : IsUnit (g * g⁻¹).det := by rwa [Matrix.mul_nonsing_inv g hg]
    rw [translate_comp _ _ _ _ h2, translate_congr (Matrix.mul_nonsing_inv g hg) h2 h1,
      translate_one]

/-! ### Permutation matrices and `w₀` -/

section Perm

variable {A : Type*} [CommRing A]

theorem permMatrix_mul (u v : Equiv.Perm (Fin n)) :
    permMatrix (A := A) n (u * v) = permMatrix n u * permMatrix n v := by
  rw [show permMatrix (A := A) n u * permMatrix n v = (permMatrix n v).submatrix u.symm id from
    PEquiv.toMatrix_toPEquiv_mul u.symm _]
  ext r c
  rw [Matrix.submatrix_apply, permMatrix_apply, permMatrix_apply]
  simp only [Equiv.Perm.mul_apply, id, Equiv.symm_apply_eq]

theorem permMatrix_one : permMatrix (A := A) n 1 = 1 := by
  ext r c
  rw [permMatrix_apply, Matrix.one_apply, Equiv.Perm.one_apply]

/-- The longest element `w₀`, `i ↦ n - 1 - i`. -/
abbrev w₀ : Equiv.Perm (Fin n) :=
  Fin.revPerm

theorem w₀_mul_self : (w₀ : Equiv.Perm (Fin n)) * w₀ = 1 :=
  Equiv.ext fun i => Fin.rev_rev i

theorem permMatrix_w₀_mul_self : permMatrix (A := A) n w₀ * permMatrix n w₀ = 1 := by
  rw [← permMatrix_mul, w₀_mul_self, permMatrix_one]

theorem w₀_conj_apply (M : Matrix (Fin n) (Fin n) A) (i j : Fin n) :
    (permMatrix (A := A) n w₀ * M * permMatrix (A := A) n w₀ : Matrix (Fin n) (Fin n) A) i j =
      M (Fin.rev i) (Fin.rev j) := by
  simp only [permMatrix, PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv,
    Matrix.submatrix_apply, id, Fin.revPerm_symm, Fin.revPerm_apply]

theorem permMatrix_map_eq {B F : Type*} [CommRing B] [FunLike F A B] [RingHomClass F A B]
    (f : F) (w : Equiv.Perm (Fin n)) : (permMatrix (A := A) n w).map f = permMatrix n w := by
  rw [permMatrix, permMatrix_map]
  rfl

/-- Conjugation by `ẇ₀` exchanges lower and upper triangular matrices. -/
theorem w₀_conj_upper {L : Matrix (Fin n) (Fin n) A} (hL : L.BlockTriangular OrderDual.toDual) :
    (permMatrix (A := A) n w₀ * L * permMatrix n w₀).BlockTriangular id := by
  intro i j hij
  rw [w₀_conj_apply]
  exact hL (show OrderDual.toDual (Fin.rev j) < OrderDual.toDual (Fin.rev i) from
    Fin.rev_lt_rev.mpr hij)

theorem w₀_conj_lower {U : Matrix (Fin n) (Fin n) A} (hU : U.BlockTriangular id) :
    (permMatrix (A := A) n w₀ * U * permMatrix n w₀).BlockTriangular OrderDual.toDual := by
  intro i j hij
  rw [w₀_conj_apply]
  exact hU (show Fin.rev j < Fin.rev i from Fin.rev_lt_rev.mpr hij)

theorem isUnit_det_w₀_conj {M : Matrix (Fin n) (Fin n) A} (hM : IsUnit M.det) :
    IsUnit (permMatrix (A := A) n w₀ * M * permMatrix n w₀).det := by
  rw [Matrix.det_mul, Matrix.det_mul]
  exact ((isUnit_det_permMatrix n w₀).mul hM).mul (isUnit_det_permMatrix n w₀)

theorem w₀_conj_w₀_conj (M : Matrix (Fin n) (Fin n) A) :
    permMatrix (A := A) n w₀ * (permMatrix n w₀ * M * permMatrix n w₀) * permMatrix n w₀ = M := by
  simp only [← mul_assoc]
  rw [permMatrix_w₀_mul_self, one_mul, mul_assoc, permMatrix_w₀_mul_self, mul_one]

end Perm

variable (R n) in
/-- **Translation by `w₀`**. -/
def translateW₀ : FlagScheme R n ⟶ FlagScheme R n :=
  translate R (permMatrix n w₀) (isUnit_det_permMatrix n w₀)

theorem ofRingFlag_matrixFlag_translateW₀ {A : Type u} [CommRing A] [Algebra R A]
    (M : Matrix (Fin n) (Fin n) A) (hM : IsUnit M.det)
    (hwM : IsUnit (permMatrix n w₀ * M).det) :
    FlagScheme.ofRingFlag R (matrixFlag M hM) ≫ translateW₀ R n =
      FlagScheme.ofRingFlag R (matrixFlag (permMatrix n w₀ * M) hwM) := by
  have h : IsUnit ((permMatrix (A := R) n w₀).map (algebraMap R A) * M).det := by
    rw [permMatrix, permMatrix_map]
    exact hwM
  rw [translateW₀, ofRingFlag_matrixFlag_translate _ _ _ _ h]
  congr 1
  apply matrixFlag_congr
  rw [permMatrix, permMatrix_map]
  rfl

variable (R n) in
/-- **`t_{w₀}` is an involution.** -/
theorem translateW₀_comp_self : translateW₀ R n ≫ translateW₀ R n = 𝟙 _ := by
  have h1 : IsUnit (Matrix.det (1 : Matrix (Fin n) (Fin n) R)) := by
    rw [Matrix.det_one]
    exact isUnit_one
  have h2 : IsUnit (permMatrix (A := R) n w₀ * permMatrix n w₀).det := by
    rwa [permMatrix_w₀_mul_self]
  rw [translateW₀, translate_comp _ _ _ _ h2, translate_congr permMatrix_w₀_mul_self h2 h1,
    translate_one]

instance : IsIso (translateW₀ R n) :=
  ⟨⟨translateW₀ R n, translateW₀_comp_self R n, translateW₀_comp_self R n⟩⟩

/-! ### Transporting ideal sheaves by `t_{w₀}` -/

variable (R n) in
theorem map_map_translateW₀ (I : (FlagScheme R n).IdealSheafData) :
    (I.map (translateW₀ R n)).map (translateW₀ R n) = I := by
  rw [← Scheme.IdealSheafData.map_comp, translateW₀_comp_self, Scheme.IdealSheafData.map_id]

theorem map_translateW₀_le_iff {I J : (FlagScheme R n).IdealSheafData} :
    I.map (translateW₀ R n) ≤ J.map (translateW₀ R n) ↔ I ≤ J := by
  refine ⟨fun h => ?_, fun h => Scheme.IdealSheafData.map_mono _ h⟩
  have := Scheme.IdealSheafData.map_mono (translateW₀ R n) h
  simp only at this
  rwa [map_map_translateW₀, map_map_translateW₀] at this

theorem ker_comp_translateW₀ {Y : Scheme.{u}} (f : Y ⟶ FlagScheme R n) :
    (f ≫ translateW₀ R n).ker = f.ker.map (translateW₀ R n) :=
  (Scheme.IdealSheafData.map_ker f _).symm

/-! ### `B⁻ = ẇ₀ B ẇ₀` -/

variable (R n) in
/-- The `A`-point of `B⁻` given by a lower triangular matrix. -/
def oppBorelPointOfMatrix {A : Type*} [CommRing A] [Algebra R A] (b : Matrix (Fin n) (Fin n) A)
    (hb : IsUnit b.det) (hlow : b.BlockTriangular OrderDual.toDual) :
    OppBorelCoord R n →ₐ[R] A :=
  Ideal.Quotient.liftₐ (oppBorelIdeal R n) (glPointOfMatrix R b hb) (by
    have hle : oppBorelIdeal R n ≤ RingHom.ker (glPointOfMatrix R b hb).toRingHom := by
      rw [oppBorelIdeal, Ideal.span_le]
      rintro _ ⟨⟨⟨i, j⟩, hij⟩, rfl⟩
      have h := congrFun (congrFun (genericMatrix_map_glPointOfMatrix R b hb) i) j
      simp only [Matrix.map_apply] at h
      simp only [SetLike.mem_coe, RingHom.mem_ker, AlgHom.toRingHom_eq_coe,
        AlgHom.coe_toRingHom, h]
      exact hlow (show OrderDual.toDual j < OrderDual.toDual i from hij)
    exact fun a ha => hle ha)

theorem oppBorelMatrix_map_oppBorelPointOfMatrix {A : Type*} [CommRing A] [Algebra R A]
    (b : Matrix (Fin n) (Fin n) A) (hb : IsUnit b.det)
    (hlow : b.BlockTriangular OrderDual.toDual) :
    (oppBorelMatrix R n).map (oppBorelPointOfMatrix R n b hb hlow) = b := by
  ext i j
  exact congrFun (congrFun (genericMatrix_map_glPointOfMatrix R b hb) i) j

theorem oppBorelMatrix_algHom_ext {A : Type*} [CommRing A] [Algebra R A]
    {k k' : OppBorelCoord R n →ₐ[R] A}
    (h : (oppBorelMatrix R n).map k = (oppBorelMatrix R n).map k') : k = k' := by
  apply Ideal.Quotient.algHom_ext
  apply genericMatrix_algHom_ext
  exact h

theorem isUnit_det_oppBorelMatrix : IsUnit (oppBorelMatrix R n).det :=
  isUnit_det_map_ringHom _ (TauCeti.GeneralLinear.isUnit_det_localizedGenericMatrix R n)

variable (R n) in
/-- `𝒪(B) → 𝒪(B⁻)`, the comorphism of `B⁻ → B`, `b ↦ ẇ₀ b ẇ₀`. -/
def borelConj : BorelCoord R n →ₐ[R] OppBorelCoord R n :=
  borelPointOfMatrix R (permMatrix n w₀ * oppBorelMatrix R n * permMatrix n w₀)
    (isUnit_det_w₀_conj isUnit_det_oppBorelMatrix)
    (w₀_conj_upper (oppBorelMatrix_blockTriangular R n))

variable (R n) in
/-- `𝒪(B⁻) → 𝒪(B)`, the comorphism of `B → B⁻`, `b ↦ ẇ₀ b ẇ₀`. -/
def oppBorelConj : OppBorelCoord R n →ₐ[R] BorelCoord R n :=
  oppBorelPointOfMatrix R n (permMatrix n w₀ * borelMatrix R n * permMatrix n w₀)
    (isUnit_det_w₀_conj (isUnit_det_borelMatrix R n))
    (w₀_conj_lower (borelMatrix_blockTriangular R n))

theorem borelMatrix_map_borelConj :
    (borelMatrix R n).map (borelConj R n) =
      permMatrix n w₀ * oppBorelMatrix R n * permMatrix n w₀ :=
  borelMatrix_map_borelPointOfMatrix R _ _ _

theorem oppBorelMatrix_map_oppBorelConj :
    (oppBorelMatrix R n).map (oppBorelConj R n) =
      permMatrix n w₀ * borelMatrix R n * permMatrix n w₀ :=
  oppBorelMatrix_map_oppBorelPointOfMatrix _ _ _

theorem map_w₀_conj {A B F : Type*} [CommRing A] [CommRing B] [FunLike F A B] (f : F)
    (M : Matrix (Fin n) (Fin n) A) :
    (permMatrix n w₀ * M * permMatrix n w₀).map f =
      permMatrix n w₀ * M.map f * permMatrix n w₀ := by
  ext i j
  rw [Matrix.map_apply, w₀_conj_apply, w₀_conj_apply, Matrix.map_apply]

theorem oppBorelConj_comp_borelConj :
    (oppBorelConj R n).comp (borelConj R n) = AlgHom.id R (BorelCoord R n) := by
  apply borelMatrix_algHom_ext
  rw [← map_map_algHom, borelMatrix_map_borelConj, map_w₀_conj, oppBorelMatrix_map_oppBorelConj,
    w₀_conj_w₀_conj]
  ext i j
  rfl

theorem borelConj_comp_oppBorelConj :
    (borelConj R n).comp (oppBorelConj R n) = AlgHom.id R (OppBorelCoord R n) := by
  apply oppBorelMatrix_algHom_ext
  rw [← map_map_algHom, oppBorelMatrix_map_oppBorelConj, map_w₀_conj, borelMatrix_map_borelConj,
    w₀_conj_w₀_conj]
  ext i j
  rfl

instance isIso_borelConj : IsIso (CommRingCat.ofHom (borelConj R n).toRingHom) := by
  refine (ConcreteCategory.isIso_iff_bijective _).mpr ⟨fun x y hxy => ?_, fun y => ?_⟩
  · have h := congrArg (oppBorelConj R n) hxy
    have hx := congrArg (fun φ => φ x) (oppBorelConj_comp_borelConj (R := R) (n := n))
    have hy := congrArg (fun φ => φ y) (oppBorelConj_comp_borelConj (R := R) (n := n))
    simp only [AlgHom.comp_apply, AlgHom.id_apply] at hx hy
    exact hx.symm.trans ((congrArg (oppBorelConj R n) hxy).trans hy)
  · refine ⟨oppBorelConj R n y, ?_⟩
    exact congrArg (fun φ => φ y) (borelConj_comp_oppBorelConj (R := R) (n := n))

/-! ### The opposite orbit map through `t_{w₀}` -/

theorem spec_map_ofRingFlag_matrixFlag {A B : Type u} [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] (k : A →ₐ[R] B) (M : Matrix (Fin n) (Fin n) A) (hM : IsUnit M.det)
    (hkM : IsUnit (M.map k).det) :
    Spec.map (CommRingCat.ofHom k.toRingHom) ≫ FlagScheme.ofRingFlag R (matrixFlag M hM) =
      FlagScheme.ofRingFlag R (matrixFlag (M.map k) hkM) := by
  let _ : Algebra A B := k.toRingHom.toAlgebra
  have _ : @IsScalarTower R A B Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq fun r => (k.commutes r).symm
  have h := FlagScheme.ofRingFlag_baseChange (R := R) (A := A) (B := B) (matrixFlag M hM)
  rw [matrixFlag_map _ _ hkM] at h
  exact h

/-- **`(b ↦ b · v̇E•) = t_{w₀} ∘ (b ↦ b · (w₀v)˙E•) ∘ (b ↦ ẇ₀ b ẇ₀)`.** -/
theorem oppSchubertOrbitMap_eq_comp (v : Equiv.Perm (Fin n)) :
    oppSchubertOrbitMap R n v = Spec.map (CommRingCat.ofHom (borelConj R n).toRingHom) ≫
      schubertOrbitMap R n (w₀ * v) ≫ translateW₀ R n := by
  have h1 : IsUnit (permMatrix n w₀ * (borelMatrix R n * permMatrix n (w₀ * v))).det := by
    rw [Matrix.det_mul]
    exact (isUnit_det_permMatrix n w₀).mul (isUnit_det_borel_mul_permMatrix R (w₀ * v))
  have h2 : IsUnit ((permMatrix n w₀ * (borelMatrix R n * permMatrix n (w₀ * v))).map
      (borelConj R n)).det := isUnit_det_map _ h1
  rw [schubertOrbitMap_eq, ofRingFlag_matrixFlag_translateW₀ _ _ h1,
    spec_map_ofRingFlag_matrixFlag _ _ _ h2, oppSchubertOrbitMap_eq]
  congr 1
  apply matrixFlag_congr
  rw [Matrix.map_mul, Matrix.map_mul, permMatrix_map_eq, permMatrix_map_eq,
    borelMatrix_map_borelConj, permMatrix_mul]
  simp only [← mul_assoc]
  rw [permMatrix_w₀_mul_self, one_mul, mul_assoc (oppBorelMatrix R n) (permMatrix n w₀),
    permMatrix_w₀_mul_self, mul_one]

/-- **`X^v = t_{w₀}(X_{w₀ v})`** as ideal sheaves. -/
theorem oppositeSchubertVariety_eq_map (v : Equiv.Perm (Fin n)) :
    oppositeSchubertVariety R n v = (schubertVariety R n (w₀ * v)).map (translateW₀ R n) := by
  rw [oppositeSchubertVariety, oppSchubertOrbitMap_eq_comp, Scheme.Hom.ker_comp_of_isIso,
    ker_comp_translateW₀, schubertVariety]

/-- **`X_w = t_{w₀}(X^{w₀ w})`** as ideal sheaves. -/
theorem schubertVariety_eq_map (w : Equiv.Perm (Fin n)) :
    schubertVariety R n w = (oppositeSchubertVariety R n (w₀ * w)).map (translateW₀ R n) := by
  rw [oppositeSchubertVariety_eq_map, ← mul_assoc, w₀_mul_self, one_mul, map_map_translateW₀]

/-- `t_{w₀}` sends the `T`-fixed point `u̇E•` to `(w₀u)˙E•`. -/
theorem permFlag_comp_translateW₀ (u : Equiv.Perm (Fin n)) :
    permFlag R n u ≫ translateW₀ R n = permFlag R n (w₀ * u) := by
  have h : IsUnit (permMatrix (A := R) n w₀ * permMatrix n u).det := by
    rw [← permMatrix_mul]
    exact isUnit_det_permMatrix n _
  rw [permFlag_eq_ofRingFlag, permFlag_eq_ofRingFlag, ofRingFlag_matrixFlag_translateW₀ _ _ h]
  congr 1
  apply matrixFlag_congr
  rw [permMatrix_mul]

/-! ### Consequences over a field of characteristic `0` -/

variable (K : Type u) [Field K] [CharZero K]

theorem w₀_mul_le_w₀_mul_iff (u v : Equiv.Perm (Fin n)) :
    w₀ * u ≤ᴮ w₀ * v ↔ v ≤ᴮ u := by
  rw [Equiv.Perm.mul_def, Equiv.Perm.mul_def]
  exact Schubert.FinPermutation.strongBruhatLE_trans_revPerm_iff u v

/-- **The opposite closure relation**: `X^u ⊆ X^v ⟺ v ≤ u`, i.e. `I(X^v) ≤ I(X^u) ⟺ v ≤ u`. -/
theorem oppositeSchubertVariety_le_iff {u v : Equiv.Perm (Fin n)} :
    oppositeSchubertVariety K n v ≤ oppositeSchubertVariety K n u ↔ v ≤ᴮ u := by
  rw [oppositeSchubertVariety_eq_map, oppositeSchubertVariety_eq_map, map_translateW₀_le_iff,
    schubertVariety_le_iff, w₀_mul_le_w₀_mul_iff]

/-- **`u̇E• ∈ X^v ⟺ v ≤ u`.** -/
theorem oppositeSchubertVariety_le_ker_permFlag_iff {u v : Equiv.Perm (Fin n)} :
    oppositeSchubertVariety K n v ≤ (permFlag K n u).ker ↔ v ≤ᴮ u := by
  have hk : (permFlag K n u).ker = (permFlag K n (w₀ * u)).ker.map (translateW₀ K n) := by
    rw [← ker_comp_translateW₀, permFlag_comp_translateW₀, ← mul_assoc, w₀_mul_self, one_mul]
  rw [oppositeSchubertVariety_eq_map, hk, map_translateW₀_le_iff,
    schubertVariety_le_ker_permFlag_iff, w₀_mul_le_w₀_mul_iff]

/-- **The `T`-fixed points of `X_w ∩ X^v`** are the `u̇E•` with `v ≤ u ≤ w`. -/
theorem richardsonVariety_le_ker_permFlag_iff {w v u : Equiv.Perm (Fin n)} :
    richardsonVariety K n w v ≤ (permFlag K n u).ker ↔ v ≤ᴮ u ∧ u ≤ᴮ w := by
  rw [richardsonVariety, sup_le_iff, schubertVariety_le_ker_permFlag_iff,
    oppositeSchubertVariety_le_ker_permFlag_iff, and_comm]

end FlagVarieties.Richardson
