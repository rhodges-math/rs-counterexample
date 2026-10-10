import RSCounterexample.FlagVarieties.Plucker.Embedding
import RSCounterexample.FlagVarieties.Normality.Unconditional

/-!
# The Plücker morphisms on points and on `GL_n`

Over a commutative ring `R`:

* `span_range_eq_top`: for matrix sections `s` as in `glued` and any invertible matrix `g` over any
  ring, the family `s g` generates the unit ideal (at a maximal ideal, the flag of `g` lies in some
  big cell over the residue field).
* **`ofRingFlag_glued`** (functor of points): the glued morphism sends the flag `g · E•` of an
  invertible `g` over `A` to the point `[s g]` of `ℙ(R^σ)`:
  `ofRingFlag (matrixFlag g) ≫ glued s = fromSections (s g)`. It is checked on the cover of
  `Spec A` by the basic opens of the big cell functions `f_v(g)`.
* **`specOrbitMap_plucker`**: for the orbit map `π : GL_n ⟶ Fl_n`,
  `π ≫ plucker R n k = fromSections (Δ_T(x))_T`, the flag minors of the generic matrix; likewise
  `specOrbitMap_pluckerSegre`. So the pulled-back Plücker coordinate `X_T` is the function `Δ_T`
  on `GL_n`, and the pulled-back chart `D₊(X_T)` is `D(Δ_T)`
  (`specOrbitMap_plucker_preimage_chart`).
* Over a field: `algebraMap_rowMinor` (the ring model's `Δ_T` is the minor of the generic matrix)
  and **`pluckerSectionBasis_apply`**: the basis of `H⁰(Fl_n, 𝓛(-ϖ_k))` given by the Plücker
  coordinates is the family of classes of the functions `Δ_T(x)`, i.e. of the pulled-back
  coordinates.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace FlagVarieties.Plucker

open AlgebraicGeometry CategoryTheory
open Foundations Foundations.QuotientCharts Demazure.FlagModule

universe u

variable (R : Type u) [CommRing R] {n : ℕ}

theorem fromSections_congr {X : Scheme.{u}} {σ : Type} {φ φ' : R →+* Γ(X, ⊤)}
    {s s' : σ → Γ(X, ⊤)} (hφ : φ = φ') (hs : s = s') (h : Ideal.span (Set.range s) = ⊤)
    (h' : Ideal.span (Set.range s') = ⊤) : fromSections φ s h = fromSections φ' s' h' := by
  subst hφ hs
  rfl

/-- The structure map `R → Γ(Spec A, 𝒪)` of an `R`-algebra `A`. -/
def specStructure (A : Type u) [CommRing A] [Algebra R A] : R →+* Γ(Spec (CommRingCat.of A), ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom.comp (algebraMap R A)

variable {R}

theorem exists_upper_of_matrixFlag_eq {A : Type u} [CommRing A] {g h : Matrix (Fin n) (Fin n) A}
    (hg : IsUnit g.det) (hh : IsUnit h.det) (e : matrixFlag g hg = matrixFlag h hh) :
    ∃ B : Matrix (Fin n) (Fin n) A, B.IsUpperTriangular ∧ IsUnit B.det ∧ h = g * B :=
  ⟨g⁻¹ * h, (matrixFlag_eq_iff g h hg hh).mp e, by
    rw [Matrix.det_mul, Matrix.det_nonsing_inv]
    exact hg.ringInverse.mul hh, (Matrix.mul_nonsing_inv_cancel_left _ _ hg).symm⟩

/-! ### Matrix sections on points -/

section Glue

variable {σ : Type} (s : ∀ {A : Type u} [CommRing A], Matrix (Fin n) (Fin n) A → σ → A)

/-- The family `s g`, as global sections of `Spec A`. -/
def specSections {A : Type u} [CommRing A] (g : Matrix (Fin n) (Fin n) A) (i : σ) :
    Γ(Spec (CommRingCat.of A), ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of A)).inv (s g i)

/-- On a flag in the big cell of `v`, some coordinate `s_i(g)` is a unit. -/
theorem exists_isUnit_of_inBigCell
    (hs_mul : ∀ {A : Type u} [CommRing A] (M B : Matrix (Fin n) (Fin n) A),
      B.IsUpperTriangular → IsUnit B.det → ∃ c : Aˣ, ∀ i, s (M * B) i = c * s M i)
    (hs_unit : ∀ (v : Equiv.Perm (Fin n)) {A : Type u} [CommRing A]
      (u : Matrix (Fin n) (Fin n) A), IsLowerUnitriangular u →
        ∃ i, IsUnit (s ((v.symm.toPEquiv.toMatrix : Matrix (Fin n) (Fin n) A) * u) i))
    {A : Type u} [CommRing A] {g : Matrix (Fin n) (Fin n) A} (hg : IsUnit g.det)
    {v : Equiv.Perm (Fin n)} (hP : InBigCell v (matrixFlag g hg)) : ∃ i, IsUnit (s g i) := by
  obtain ⟨u, hu, he⟩ := bigCellMatrix_eq_perm_mul hP
  obtain ⟨i, hi⟩ := hs_unit v u hu
  obtain ⟨B, hB, hBu, hgB⟩ :=
    exists_upper_of_matrixFlag_eq (isUnit_det_bigCellMatrix hP) hg (matrixFlag_bigCellMatrix hP)
  obtain ⟨c, hc⟩ := hs_mul (bigCellMatrix hP) B hB hBu
  refine ⟨i, ?_⟩
  have hsg : s g i = c * s (bigCellMatrix hP) i := (congrArg (fun M => s M i) hgB).trans (hc i)
  rw [hsg, he]
  exact c.isUnit.mul hi

/-- **For every invertible `g`, the family `s g` generates the unit ideal.** -/
theorem span_range_eq_top
    (hs_map : ∀ {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
      (M : Matrix (Fin n) (Fin n) A) (i : σ), s (M.map f) i = f (s M i))
    (hs_mul : ∀ {A : Type u} [CommRing A] (M B : Matrix (Fin n) (Fin n) A),
      B.IsUpperTriangular → IsUnit B.det → ∃ c : Aˣ, ∀ i, s (M * B) i = c * s M i)
    (hs_unit : ∀ (v : Equiv.Perm (Fin n)) {A : Type u} [CommRing A]
      (u : Matrix (Fin n) (Fin n) A), IsLowerUnitriangular u →
        ∃ i, IsUnit (s ((v.symm.toPEquiv.toMatrix : Matrix (Fin n) (Fin n) A) * u) i))
    {A : Type u} [CommRing A] {g : Matrix (Fin n) (Fin n) A} (hg : IsUnit g.det) :
    Ideal.span (Set.range (s g)) = ⊤ := by
  by_contra hne
  obtain ⟨p, hp, hle⟩ := Ideal.exists_le_maximal _ hne
  let := Ideal.Quotient.field p
  have hg' : IsUnit (g.map (Ideal.Quotient.mk p)).det := isUnit_det_map _ hg
  obtain ⟨v, hv⟩ := exists_inBigCell (matrixFlag (g.map (Ideal.Quotient.mk p)) hg')
  obtain ⟨i, hi⟩ := exists_isUnit_of_inBigCell s hs_mul hs_unit hg' hv
  rw [hs_map] at hi
  exact hi.ne_zero (Ideal.Quotient.eq_zero_iff_mem.mpr (hle (Ideal.subset_span ⟨i, rfl⟩)))

theorem span_specSections
    (hs_map : ∀ {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
      (M : Matrix (Fin n) (Fin n) A) (i : σ), s (M.map f) i = f (s M i))
    (hs_mul : ∀ {A : Type u} [CommRing A] (M B : Matrix (Fin n) (Fin n) A),
      B.IsUpperTriangular → IsUnit B.det → ∃ c : Aˣ, ∀ i, s (M * B) i = c * s M i)
    (hs_unit : ∀ (v : Equiv.Perm (Fin n)) {A : Type u} [CommRing A]
      (u : Matrix (Fin n) (Fin n) A), IsLowerUnitriangular u →
        ∃ i, IsUnit (s ((v.symm.toPEquiv.toMatrix : Matrix (Fin n) (Fin n) A) * u) i))
    {A : Type u} [CommRing A] {g : Matrix (Fin n) (Fin n) A} (hg : IsUnit g.det) :
    Ideal.span (Set.range (specSections s g)) = ⊤ :=
  span_range_map (s g) (span_range_eq_top s hs_map hs_mul hs_unit hg)
    (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom

/-- The functor-of-points description on a big cell. -/
theorem ofRingFlag_glued_of_inBigCell
    (hs_map : ∀ {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
      (M : Matrix (Fin n) (Fin n) A) (i : σ), s (M.map f) i = f (s M i))
    (hs_mul : ∀ {A : Type u} [CommRing A] (M B : Matrix (Fin n) (Fin n) A),
      B.IsUpperTriangular → IsUnit B.det → ∃ c : Aˣ, ∀ i, s (M * B) i = c * s M i)
    (hs_unit : ∀ (v : Equiv.Perm (Fin n)) {A : Type u} [CommRing A]
      (u : Matrix (Fin n) (Fin n) A), IsLowerUnitriangular u →
        ∃ i, IsUnit (s ((v.symm.toPEquiv.toMatrix : Matrix (Fin n) (Fin n) A) * u) i))
    {A : Type u} [CommRing A] [Algebra R A] {g : Matrix (Fin n) (Fin n) A} (hg : IsUnit g.det)
    {v : Equiv.Perm (Fin n)} (hP : InBigCell v (matrixFlag g hg)) :
    FlagScheme.ofRingFlag R (matrixFlag g hg) ≫ glued R s hs_map hs_mul hs_unit =
      fromSections (specStructure R A) (specSections s g)
        (span_specSections s hs_map hs_mul hs_unit hg) := by
  set a := bigCellPoint R hP
  rw [← spec_bigCellPoint_bigCellChart hP, Category.assoc]
  change Spec.map (CommRingCat.ofHom a.toRingHom) ≫ specChart R n v ≫
    glued R s hs_map hs_mul hs_unit = _
  rw [specChart_glued, chartMorphism, fromSections_naturality]
  obtain ⟨B, hB, hBu, hgB⟩ :=
    exists_upper_of_matrixFlag_eq (isUnit_det_bigCellMatrix hP) hg (matrixFlag_bigCellMatrix hP)
  obtain ⟨c, hc⟩ := hs_mul (bigCellMatrix hP) B hB hBu
  have hφ : (Spec.map (CommRingCat.ofHom a.toRingHom)).appTop.hom.comp (chartStructure R v) =
      specStructure R A := by
    ext r
    simp only [chartStructure, specStructure, RingHom.comp_apply]
    rw [appTop_ΓSpecIso_inv]
    exact congrArg (Scheme.ΓSpecIso (CommRingCat.of A)).inv (a.commutes r)
  have hfam : ∀ i, specSections s g i =
      (Units.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom.toMonoidHom c :
        Γ(Spec (CommRingCat.of A), ⊤)) *
        (Spec.map (CommRingCat.ofHom a.toRingHom)).appTop (chartSections R s v i) := by
    intro i
    have h1 : (CommRingCat.ofHom a.toRingHom) (s (chartMatrix R n v) i) =
        s (bigCellMatrix hP) i := by
      change a.toRingHom (s (chartMatrix R n v) i) = _
      rw [← hs_map]
      exact congrArg (fun M => s M i) (map_bigCellPoint v hP)
    have hsg : s g i = c * s (bigCellMatrix hP) i :=
      (congrArg (fun M => s M i) hgB).trans (hc i)
    rw [chartSections, appTop_ΓSpecIso_inv, h1, specSections, hsg, map_mul, Units.coe_map]
    rfl
  rw [hφ]
  exact (fromSections_eq_of_unit _ _ _ _ _ _ hfam).symm

/-- **The glued morphism on points**: it sends the flag `g · E•` of an invertible matrix `g` over
`A` to the point `[s g]`. -/
theorem ofRingFlag_glued
    (hs_map : ∀ {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
      (M : Matrix (Fin n) (Fin n) A) (i : σ), s (M.map f) i = f (s M i))
    (hs_mul : ∀ {A : Type u} [CommRing A] (M B : Matrix (Fin n) (Fin n) A),
      B.IsUpperTriangular → IsUnit B.det → ∃ c : Aˣ, ∀ i, s (M * B) i = c * s M i)
    (hs_unit : ∀ (v : Equiv.Perm (Fin n)) {A : Type u} [CommRing A]
      (u : Matrix (Fin n) (Fin n) A), IsLowerUnitriangular u →
        ∃ i, IsUnit (s ((v.symm.toPEquiv.toMatrix : Matrix (Fin n) (Fin n) A) * u) i))
    {A : Type u} [CommRing A] [Algebra R A] {g : Matrix (Fin n) (Fin n) A} (hg : IsUnit g.det) :
    FlagScheme.ofRingFlag R (matrixFlag g hg) ≫ glued R s hs_map hs_mul hs_unit =
      fromSections (specStructure R A) (specSections s g)
        (span_specSections s hs_map hs_mul hs_unit hg) := by
  let k := glPointOfMatrix R g hg
  let x : Equiv.Perm (Fin n) → A := fun v => k (bigCellFunction R v)
  have hx : Ideal.span (Set.range x) = ⊤ := by
    have := congrArg (Ideal.map k) (span_bigCellFunction R n)
    rwa [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at this
  refine (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of A) x hx).openCover.hom_ext _ _
    fun v => ?_
  change Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away (x v)))) ≫ _ =
    Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away (x v)))) ≫ _
  have hgB : IsUnit (g.map (algebraMap A (Localization.Away (x v)))).det := isUnit_det_map _ hg
  have hP : InBigCell v (matrixFlag (g.map (algebraMap A (Localization.Away (x v)))) hgB) := by
    have h1 := (isUnit_map_bigCellFunction_iff v
      ((IsScalarTower.toAlgHom R A (Localization.Away (x v))).comp k)).mp
        (IsLocalization.Away.algebraMap_isUnit (x v))
    have h2 : GLScheme.pointMatrix R n
        ((IsScalarTower.toAlgHom R A (Localization.Away (x v))).comp k) =
        g.map (algebraMap A (Localization.Away (x v))) := by
      rw [pointMatrix_comp, pointMatrix_glPointOfMatrix]
      rfl
    rwa [matrixFlag_congr h2 _ hgB] at h1
  rw [← Category.assoc, FlagScheme.ofRingFlag_baseChange, matrixFlag_map _ _ hgB,
    ofRingFlag_glued_of_inBigCell s hs_map hs_mul hs_unit hgB hP, fromSections_naturality]
  apply fromSections_congr
  · ext r
    simp only [specStructure, RingHom.comp_apply]
    rw [appTop_ΓSpecIso_inv]
    exact congrArg (Scheme.ΓSpecIso _).inv
      (IsScalarTower.algebraMap_apply R A (Localization.Away (x v)) r)
  · funext i
    simp only [specSections]
    rw [appTop_ΓSpecIso_inv, hs_map]
    rfl

end Glue

/-! ### The orbit map -/

variable (R n) in
/-- The orbit map `π : GL_n ⟶ Fl_n` is the flag of the generic matrix. -/
theorem specOrbitMap_eq_ofRingFlag :
    specOrbitMap R = FlagScheme.ofRingFlag R (matrixFlag (genericMatrix R n)
      (TauCeti.GeneralLinear.isUnit_det_localizedGenericMatrix R n)) := by
  have h1 : GLScheme.point R n (AlgHom.id R (GLCoord R n)) =
      (TauCeti.GeneralLinear.groupSchemeSpecIso R n).inv := by
    change Spec.map (CommRingCat.ofHom (RingHom.id (GLCoord R n))) ≫ _ = _
    rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
  have hpm : GLScheme.pointMatrix R n (AlgHom.id R (GLCoord R n)) = genericMatrix R n := by
    ext i j
    rfl
  rw [specOrbitMap, ← h1, FlagScheme.orbitMap_point]
  exact congrArg (FlagScheme.ofRingFlag R) (matrixFlag_congr hpm
    ((Matrix.isUnit_iff_isUnit_det _).mp (generalLinearMatrixAt_isUnit R _ n _)) _)

variable (n) in
/-- **The Plücker morphism on points**: the flag of `g` goes to its Plücker coordinates. -/
theorem ofRingFlag_plucker (k : Fin n) {A : Type u} [CommRing A] [Algebra R A]
    {g : Matrix (Fin n) (Fin n) A} (hg : IsUnit g.det) :
    FlagScheme.ofRingFlag R (matrixFlag g hg) ≫ plucker R n k =
      fromSections (specStructure R A) (specSections (fun M T => minor M T) g)
        (span_specSections _ (minorSec_map k) (minorSec_mul k) (minorSec_unit k) hg) :=
  ofRingFlag_glued _ (minorSec_map k) (minorSec_mul k) (minorSec_unit k) hg

variable (n) in
theorem ofRingFlag_pluckerSegre {A : Type u} [CommRing A] [Algebra R A]
    {g : Matrix (Fin n) (Fin n) A} (hg : IsUnit g.det) :
    FlagScheme.ofRingFlag R (matrixFlag g hg) ≫ pluckerSegre R n =
      fromSections (specStructure R A) (specSections segreSec g)
        (span_specSections _ segreSec_map segreSec_mul segreSec_unit hg) :=
  ofRingFlag_glued _ segreSec_map segreSec_mul segreSec_unit hg

variable (R n) in
/-- **The Plücker identity**: `π ≫ plucker R n k` is given by the flag minors `Δ_T` of the generic
matrix of `GL_n`. -/
theorem specOrbitMap_plucker (k : Fin n) :
    specOrbitMap R ≫ plucker R n k =
      fromSections (specStructure R (GLCoord R n))
        (specSections (fun M T => minor M T) (genericMatrix R n))
        (span_specSections _ (minorSec_map k) (minorSec_mul k) (minorSec_unit k)
          (TauCeti.GeneralLinear.isUnit_det_localizedGenericMatrix R n)) := by
  exact (congrArg (· ≫ plucker R n k) (specOrbitMap_eq_ofRingFlag R n)).trans
    (ofRingFlag_plucker n k _)

variable (R n) in
theorem specOrbitMap_pluckerSegre :
    specOrbitMap R ≫ pluckerSegre R n =
      fromSections (specStructure R (GLCoord R n)) (specSections segreSec (genericMatrix R n))
        (span_specSections _ segreSec_map segreSec_mul segreSec_unit
          (TauCeti.GeneralLinear.isUnit_det_localizedGenericMatrix R n)) := by
  exact (congrArg (· ≫ pluckerSegre R n) (specOrbitMap_eq_ofRingFlag R n)).trans
    (ofRingFlag_pluckerSegre n _)

variable (R) in
/-- The pull-back to `GL_n` of the chart `D₊(X_T)` is `D(Δ_T)`. -/
theorem specOrbitMap_plucker_preimage_chart {k : Fin n} (T : FlagMinorRowSet k) :
    (specOrbitMap R ≫ plucker R n k) ⁻¹ᵁ chart R (FlagMinorRowSet k) T =
      PrimeSpectrum.basicOpen (minor (genericMatrix R n) T) := by
  rw [specOrbitMap_plucker, fromSections_preimage_chart, specSections, basicOpen_eq_of_affine]

/-! ### The ring model over a field -/

section RingModel

open PointModel

theorem genericMatrix_apply_eq (i j : Fin n) :
    genericMatrix R n i j =
      algebraMap (MvPolynomial (Fin n × Fin n) R) (GLCoord R n) (MvPolynomial.X (i, j)) := by
  rw [genericMatrix, TauCeti.GeneralLinear.localizedGenericMatrix_apply,
    TauCeti.GeneralLinear.coordinateRingMap_apply]

/-- The ring model's flag minor `Δ_T` is the minor of the generic matrix. -/
theorem algebraMap_rowMinor (K : Type u) [Field K] {k : Fin n} (T : FlagMinorRowSet k) :
    algebraMap (MatrixEntryPolynomial K n) (GLCoord K n) (rowMinor K k T.rows) = minor
        (genericMatrix K n) T := by
  rw [rowMinor, RingHom.map_det, minor]
  congr 1

theorem minor_mem_semiInvSpace (K : Type u) [Field K] {k : Fin n} (T : FlagMinorRowSet k) :
    minor (genericMatrix K n) T ∈
      semiInvSpace (orbitSet K Finset.univ) (PointModel.shapeWeightZ (Pi.single k 1)) := by
  rw [← algebraMap_rowMinor]
  exact (minorToSemiInvSpace K Finset.univ (Pi.single k 1)
    ⟨_, rowMinor_mem_minorSpan_single k T⟩).2

/-- **The Plücker section basis is the family of pulled-back Plücker coordinates**: the basis
element of `H⁰(Fl_n, 𝓛(-ϖ_k))` indexed by `T` is the class of the function `Δ_T(x)` on `GL_n`,
which is the coordinate `X_T` pulled back along `π ≫ plucker R n k` (`specOrbitMap_plucker`). -/
theorem pluckerSectionBasisOfGlobalSectionsConstant_apply {K : Type u} [Field K] [IsAlgClosed K]
    [CharZero K]
    (hglobalSections : ∀ w : Equiv.Perm (Fin n), GlobalSectionsConstant K w) (k : Fin n)
        (T : FlagMinorRowSet k) :
    pluckerSectionBasisOfGlobalSectionsConstant hglobalSections k T =
      Submodule.Quotient.mk ⟨minor (genericMatrix K n) T, minor_mem_semiInvSpace K T⟩ := by
  rw [pluckerSectionBasisOfGlobalSectionsConstant, Module.Basis.map_apply]
  change minorRestriction K Finset.univ (Pi.single k 1) (pluckerBasis k T) = _
  rw [minorRestriction, LinearMap.comp_apply, Submodule.mkQ_apply]
  congr 1
  ext
  change algebraMap (MatrixEntryPolynomial K n) (GLCoord K n)
    ((pluckerBasis (K := K) k T : minorSpan K (Pi.single k 1)) : MatrixEntryPolynomial K n) = _
  rw [pluckerBasis_apply, algebraMap_rowMinor]

/-- The same for the unconditional basis. -/
theorem pluckerSectionBasis_apply {K : Type u} [Field K] [IsAlgClosed K]
    [CharZero K] (k : Fin n) (T : FlagMinorRowSet k) :
    PointModel.pluckerSectionBasis k T =
      Submodule.Quotient.mk ⟨minor (genericMatrix K n) T, minor_mem_semiInvSpace K T⟩ :=
  pluckerSectionBasisOfGlobalSectionsConstant_apply (globalSectionsConstant_of_charZero K n) k T

end RingModel

end FlagVarieties.Plucker
