import Schubert.FlagVarieties.Plucker.ProjSpace
import Schubert.FlagVarieties.Charts.Trivialization
import Schubert.FlagVarieties.Charts.Cover

/-!
# Morphisms from the flag scheme to projective spaces, glued on big cells

Over a commutative ring `R`, the big cells `bigCellChart R v : Spec C_v ⟶ Fl_n` form an open cover
of the flag scheme (`bigCellCover`). On `Spec C_v` the universal flag has the adapted matrix
`L_v = ẇ u` (`u` lower unitriangular).

`glued s …`: let `s` assign to every square matrix `M` over every ring a family `s M : σ → A` of
elements, natural in the ring, such that `s (M B) = c(B) · s M` for invertible upper triangular `B`
with a unit `c(B)`, and such that some coordinate of `s (ẇ u)` is a unit. Then the morphisms
`Spec C_v ⟶ ℙ(R^σ)` given by the unimodular families `s L_v` glue to a morphism
`Fl_n ⟶ ℙ(R^σ)`: on overlaps the two adapted matrices have the same flag, hence differ by an
invertible upper triangular matrix, and the two families differ by a unit (`fromSections_unit_mul`).

**The Plücker morphisms** (`plucker R n k : Fl_n ⟶ ℙ(∧^{k+1} R^n)`) are the case
`s M T = Δ_T(M)`, the flag minors of height `k` (`minorSec`); their product, the **Segre–Plücker
morphism** `pluckerSegre R n : Fl_n ⟶ ℙ(⊗_k ∧^{k+1} R^n)`, is the case
`s M (T_k)_k = ∏_k Δ_{T_k}(M)` (`segreSec`). On the big cell of `v`, the Plücker coordinate of
`v{0..k}` is a unit.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace FlagVarieties.Plucker

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Foundations Foundations.QuotientCharts

universe u

variable (R : Type u) [CommRing R] (n : ℕ)

/-! ### The big cells as an open cover -/

/-- The coordinate ring `C_v` of the big cell of `v`, as a commutative ring object. -/
abbrev ChartRing (v : Equiv.Perm (Fin n)) : CommRingCat.{u} :=
  CommRingCat.of (bigCellRing R v)

/-- The big cell chart `Spec C_v ⟶ Fl_n`. -/
def specChart (v : Equiv.Perm (Fin n)) : Spec (ChartRing R n v) ⟶ FlagScheme R n :=
  bigCellChart R v

instance (v : Equiv.Perm (Fin n)) : IsOpenImmersion (specChart R n v) :=
  inferInstanceAs (IsOpenImmersion (bigCellChart R v))

/-- **The big cells cover the flag scheme.** -/
def bigCellCover : (FlagScheme R n).OpenCover :=
  Scheme.Cover.mkOfCovers (Equiv.Perm (Fin n)) (fun v => Spec (ChartRing R n v)) (specChart R n)
    fun x => by
      obtain ⟨v, hv⟩ := exists_mem_bigCell R x
      obtain ⟨y, hy⟩ := Scheme.Hom.mem_opensRange.mp hv
      exact ⟨v, y, hy⟩

/-- The adapted matrix `ẇ u` of the universal flag of the big cell of `v`. -/
abbrev chartMatrix (v : Equiv.Perm (Fin n)) : Matrix (Fin n) (Fin n) (bigCellRing R v) :=
  bigCellUniversalMatrix R v

theorem specChart_toSpec (v : Equiv.Perm (Fin n)) :
    specChart R n v ≫ FlagScheme.toSpec R n =
      Spec.map (CommRingCat.ofHom (algebraMap R (bigCellRing R v))) := by
  rw [specChart, bigCellChart_eq_ofRingFlag, FlagScheme.ofRingFlag_toSpec]

variable {n}

/-! ### Glueing from matrix sections -/

section Glue

variable {σ : Type}

/-- The family `s L_v` on the big cell of `v`, as global sections of `Spec C_v`. -/
def chartSections (s : ∀ {A : Type u} [CommRing A], Matrix (Fin n) (Fin n) A → σ → A)
    (v : Equiv.Perm (Fin n)) : σ → Γ(Spec (ChartRing R n v), ⊤) :=
  fun i => (Scheme.ΓSpecIso (ChartRing R n v)).inv (s (chartMatrix R n v) i)

/-- The structure map `R → Γ(Spec C_v, 𝒪)`. -/
def chartStructure (v : Equiv.Perm (Fin n)) : R →+* Γ(Spec (ChartRing R n v), ⊤) :=
  (Scheme.ΓSpecIso (ChartRing R n v)).inv.hom.comp (algebraMap R (bigCellRing R v))

theorem span_chartSections (s : ∀ {A : Type u} [CommRing A], Matrix (Fin n) (Fin n) A → σ → A)
    (hs_unit : ∀ (v : Equiv.Perm (Fin n)) {A : Type u} [CommRing A]
      (u : Matrix (Fin n) (Fin n) A), IsLowerUnitriangular u →
        ∃ i, IsUnit (s ((v.symm.toPEquiv.toMatrix : Matrix (Fin n) (Fin n) A) * u) i))
    (v : Equiv.Perm (Fin n)) : Ideal.span (Set.range (chartSections R s v)) = ⊤ := by
  obtain ⟨u, hu, he⟩ := bigCellMatrix_eq_perm_mul (inBigCell_bigCellUniversalFlag R v)
  obtain ⟨i, hi⟩ := hs_unit v u hu
  have hi' : IsUnit (chartSections R s v i) := by
    rw [chartSections, chartMatrix, bigCellUniversalMatrix, he]
    exact hi.map _
  exact Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨i, rfl⟩) hi'

/-- The morphism on the big cell of `v`. -/
def chartMorphism (s : ∀ {A : Type u} [CommRing A], Matrix (Fin n) (Fin n) A → σ → A)
    (hs_unit : ∀ (v : Equiv.Perm (Fin n)) {A : Type u} [CommRing A]
      (u : Matrix (Fin n) (Fin n) A), IsLowerUnitriangular u →
        ∃ i, IsUnit (s ((v.symm.toPEquiv.toMatrix : Matrix (Fin n) (Fin n) A) * u) i))
    (v : Equiv.Perm (Fin n)) : Spec (ChartRing R n v) ⟶ projSpace R σ :=
  fromSections (chartStructure R v) (chartSections R s v) (span_chartSections R s hs_unit v)

omit [CommRing R] in
theorem appTop_ΓSpecIso_inv {A C : CommRingCat.{u}} (a : C ⟶ A) (x : C) :
    (Spec.map a).appTop ((Scheme.ΓSpecIso C).inv x) = (Scheme.ΓSpecIso A).inv (a x) := by
  have := congrArg (fun φ => φ.hom x) (Scheme.ΓSpecIso_inv_naturality a)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
  exact this.symm

/-- Two compatible maps to big cells induce the same `R`-algebra structure. -/
theorem structureMap_eq {v w : Equiv.Perm (Fin n)} {A : CommRingCat.{u}}
    (a : ChartRing R n v ⟶ A) (b : ChartRing R n w ⟶ A)
    (h : Spec.map a ≫ specChart R n v = Spec.map b ≫ specChart R n w) :
    a.hom.comp (algebraMap R (bigCellRing R v)) = b.hom.comp (algebraMap R (bigCellRing R w)) := by
  have h2 := congrArg (· ≫ FlagScheme.toSpec R n) h
  rw [Category.assoc, Category.assoc, specChart_toSpec R n v, specChart_toSpec R n w,
    ← Spec.map_comp, ← Spec.map_comp] at h2
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective h2)

/-- An `R`-algebra point of a big cell is the flag of the base-changed adapted matrix. -/
theorem specChart_comp_eq {v : Equiv.Perm (Fin n)} {A : CommRingCat.{u}} [Algebra R A]
    (a : bigCellRing R v →ₐ[R] A) :
    Spec.map (CommRingCat.ofHom a.toRingHom) ≫ specChart R n v =
      FlagScheme.ofRingFlag R (matrixFlag ((chartMatrix R n v).map a)
        (isUnit_det_map _ (isUnit_det_bigCellMatrix _))) := by
  let _ : Algebra (bigCellRing R v) A := a.toRingHom.toAlgebra
  have _ : @IsScalarTower R (bigCellRing R v) A Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq fun r => (a.commutes r).symm
  have hv := FlagScheme.ofRingFlag_baseChange (R := R) (A := bigCellRing R v) (B := A)
    (bigCellUniversalFlag R v)
  rw [← bigCellChart_eq_ofRingFlag] at hv
  have hm := matrixFlag_bigCellMatrix (inBigCell_bigCellUniversalFlag R v)
  rw [← hm, matrixFlag_map _ _ (isUnit_det_map _ (isUnit_det_bigCellMatrix _))] at hv
  exact hv

/-- On an affine scheme mapping to two big cells compatibly, the two chart morphisms agree. -/
theorem chartMorphism_compat (s : ∀ {A : Type u} [CommRing A], Matrix (Fin n) (Fin n) A → σ → A)
    (hs_map : ∀ {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
      (M : Matrix (Fin n) (Fin n) A) (i : σ), s (M.map f) i = f (s M i))
    (hs_mul : ∀ {A : Type u} [CommRing A] (M B : Matrix (Fin n) (Fin n) A),
      B.IsUpperTriangular → IsUnit B.det → ∃ c : Aˣ, ∀ i, s (M * B) i = c * s M i)
    (hs_unit : ∀ (v : Equiv.Perm (Fin n)) {A : Type u} [CommRing A]
      (u : Matrix (Fin n) (Fin n) A), IsLowerUnitriangular u →
        ∃ i, IsUnit (s ((v.symm.toPEquiv.toMatrix : Matrix (Fin n) (Fin n) A) * u) i))
    {v w : Equiv.Perm (Fin n)} {A : CommRingCat.{u}} (α : Spec A ⟶ Spec (ChartRing R n v))
    (β : Spec A ⟶ Spec (ChartRing R n w)) (h : α ≫ specChart R n v = β ≫ specChart R n w) :
    α ≫ chartMorphism R s hs_unit v = β ≫ chartMorphism R s hs_unit w := by
  obtain ⟨a, rfl⟩ : ∃ a, Spec.map a = α := ⟨_, Spec.map_preimage α⟩
  obtain ⟨b, rfl⟩ : ∃ b, Spec.map b = β := ⟨_, Spec.map_preimage β⟩
  -- the structure maps agree
  have hR := structureMap_eq R a b h
  -- the two adapted matrices have the same flag over `A`
  have hflag : ∃ B : Matrix (Fin n) (Fin n) A, B.IsUpperTriangular ∧ IsUnit B.det ∧
      (chartMatrix R n w).map b.hom = (chartMatrix R n v).map a.hom * B := by
    let _ : Algebra R A := (a.hom.comp (algebraMap R (bigCellRing R v))).toAlgebra
    let a' : bigCellRing R v →ₐ[R] A := { a.hom with commutes' := fun _ => rfl }
    let b' : bigCellRing R w →ₐ[R] A :=
      { b.hom with commutes' := fun r => (congrArg (fun φ => φ r) hR).symm }
    have hv := specChart_comp_eq R a'
    have hw := specChart_comp_eq R b'
    have heq := FlagScheme.ofRingFlag_injective (R := R) (hv.symm.trans (h.trans hw))
    rw [matrixFlag_eq_iff] at heq
    have hu : IsUnit ((chartMatrix R n v).map a.hom).det :=
      isUnit_det_map _ (isUnit_det_bigCellMatrix _)
    have hu' : IsUnit ((chartMatrix R n w).map b.hom).det :=
      isUnit_det_map _ (isUnit_det_bigCellMatrix _)
    refine ⟨((chartMatrix R n v).map a.hom)⁻¹ * (chartMatrix R n w).map b.hom, heq, ?_, ?_⟩
    · rw [Matrix.det_mul, Matrix.det_nonsing_inv]
      exact (hu.ringInverse).mul hu'
    · rw [Matrix.mul_nonsing_inv_cancel_left _ _ hu]
  obtain ⟨B, hB, hBu, hBe⟩ := hflag
  obtain ⟨c, hc⟩ := hs_mul ((chartMatrix R n v).map a.hom) B hB hBu
  rw [chartMorphism, chartMorphism, fromSections_naturality, fromSections_naturality]
  -- rewrite both families in terms of `A`
  have hφ : (Spec.map a).appTop.hom.comp (chartStructure R v) =
      (Spec.map b).appTop.hom.comp (chartStructure R w) := by
    ext r
    simp only [chartStructure, RingHom.comp_apply]
    rw [appTop_ΓSpecIso_inv, appTop_ΓSpecIso_inv]
    exact congrArg (Scheme.ΓSpecIso A).inv (congrArg (fun φ => φ r) hR)
  have e1 : ∀ i, (Spec.map b).appTop (chartSections R s w i) =
      (Scheme.ΓSpecIso A).inv (s ((chartMatrix R n w).map b.hom) i) := by
    intro i
    rw [chartSections, appTop_ΓSpecIso_inv, hs_map]
  have e2 : ∀ i, (Spec.map a).appTop (chartSections R s v i) =
      (Scheme.ΓSpecIso A).inv (s ((chartMatrix R n v).map a.hom) i) := by
    intro i
    rw [chartSections, appTop_ΓSpecIso_inv, hs_map]
  have hfam : ∀ i, (Spec.map b).appTop (chartSections R s w i) =
      (Units.map (Scheme.ΓSpecIso A).inv.hom.toMonoidHom c : Γ(Spec A, ⊤)) *
        (Spec.map a).appTop (chartSections R s v i) := by
    intro i
    rw [e1, e2, Units.coe_map]
    have := congrArg (Scheme.ΓSpecIso A).inv (hc i)
    rw [← hBe, map_mul] at this
    exact this
  rw [hφ]
  exact (fromSections_eq_of_unit _ _ _ _ _ _ hfam).symm

/-- **The morphism glued from the big cells.** -/
def glued (s : ∀ {A : Type u} [CommRing A], Matrix (Fin n) (Fin n) A → σ → A)
    (hs_map : ∀ {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
      (M : Matrix (Fin n) (Fin n) A) (i : σ), s (M.map f) i = f (s M i))
    (hs_mul : ∀ {A : Type u} [CommRing A] (M B : Matrix (Fin n) (Fin n) A),
      B.IsUpperTriangular → IsUnit B.det → ∃ c : Aˣ, ∀ i, s (M * B) i = c * s M i)
    (hs_unit : ∀ (v : Equiv.Perm (Fin n)) {A : Type u} [CommRing A]
      (u : Matrix (Fin n) (Fin n) A), IsLowerUnitriangular u →
        ∃ i, IsUnit (s ((v.symm.toPEquiv.toMatrix : Matrix (Fin n) (Fin n) A) * u) i)) :
    FlagScheme R n ⟶ projSpace R σ :=
  (bigCellCover R n).glueMorphisms (fun v => chartMorphism R s hs_unit v) fun v w => by
    refine (pullback ((bigCellCover R n).f v) ((bigCellCover R n).f w)).affineOpenCover.openCover
      |>.hom_ext _ _ fun j => ?_
    change _ ≫ pullback.fst _ _ ≫ chartMorphism R s hs_unit v =
      _ ≫ pullback.snd _ _ ≫ chartMorphism R s hs_unit w
    rw [← Category.assoc, ← Category.assoc]
    exact chartMorphism_compat R s hs_map hs_mul hs_unit _ _ (by
      rw [Category.assoc, Category.assoc]
      exact congrArg (_ ≫ ·) pullback.condition)

theorem specChart_glued (s : ∀ {A : Type u} [CommRing A], Matrix (Fin n) (Fin n) A → σ → A)
    (hs_map : ∀ {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
      (M : Matrix (Fin n) (Fin n) A) (i : σ), s (M.map f) i = f (s M i))
    (hs_mul : ∀ {A : Type u} [CommRing A] (M B : Matrix (Fin n) (Fin n) A),
      B.IsUpperTriangular → IsUnit B.det → ∃ c : Aˣ, ∀ i, s (M * B) i = c * s M i)
    (hs_unit : ∀ (v : Equiv.Perm (Fin n)) {A : Type u} [CommRing A]
      (u : Matrix (Fin n) (Fin n) A), IsLowerUnitriangular u →
        ∃ i, IsUnit (s ((v.symm.toPEquiv.toMatrix : Matrix (Fin n) (Fin n) A) * u) i))
    (v : Equiv.Perm (Fin n)) :
    specChart R n v ≫ glued R s hs_map hs_mul hs_unit = chartMorphism R s hs_unit v :=
  (bigCellCover R n).ι_glueMorphisms _ _ v

end Glue

end FlagVarieties.Plucker
