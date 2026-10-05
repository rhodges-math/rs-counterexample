import Schubert.FlagVarieties.LineBundle.BigCellData
import Schubert.FlagVarieties.Foundations.Schemes.AffinePointAlgebraHom

/-!
# `Flₙ = GLₙ / B`

Over every commutative ring `R`, the orbit map `π : GLₙ ⟶ Flₙ`, `g ↦ g · E•`, is a Zariski-locally
trivial `B`-torsor, and `Flₙ` is the quotient `GLₙ / B`:

* `FlagVarieties.exists_mulRight_eq`: two points `a, a' : T ⟶ GLₙ` of an affine scheme `T` with
  `π a = π a'` differ by a point `β : T ⟶ B`, `a' = a · β`;
* `FlagVarieties.mulRight_cancel`: and `β` is unique (`B` acts freely);
* `FlagVarieties.bigCellSection'` / `bigCellSection'_orbitMap`: `π` has a section over each big
  cell, and the big cells cover `Flₙ` (`FlagVarieties.bigCellCover`);
* `FlagVarieties.comp_eq_of_orbitMap_eq`: a `B`-invariant morphism out of `GLₙ` is constant on
  the fibres of `π`;
* **`FlagVarieties.isColimitOrbitMap`**: `π` is the coequalizer of the projection and the action
  `GLₙ ×_R B ⇉ GLₙ` in the category of schemes.
-/

noncomputable section

namespace FlagVarieties

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Foundations Foundations.QuotientCharts

universe u

variable (R : Type u) [CommRing R] (n : ℕ)

/-! ### The fibres of `π` are the `B`-orbits -/

variable {R n} in
/-- On `A`-points: if `g · E• = g' · E•` then `g' = g b` with `b = g⁻¹ g'` upper triangular. -/
theorem exists_point_mulRight_eq {A : Type u} [CommRing A] [Algebra R A]
    (k k' : GLCoord R n →ₐ[R] A)
    (h : GLScheme.point R n k ≫ FlagScheme.orbitMap R n =
      GLScheme.point R n k' ≫ FlagScheme.orbitMap R n) :
    ∃ b : BorelCoord R n →ₐ[R] A,
      pullback.lift (GLScheme.point R n k) (Spec.map (CommRingCat.ofHom b.toRingHom))
        (point_borel_condition k b) ≫ mulRight R n = GLScheme.point R n k' := by
  rw [FlagScheme.orbitMap_point, FlagScheme.orbitMap_point] at h
  let g := GLScheme.pointMatrix R n k
  let g' := GLScheme.pointMatrix R n k'
  have hg : IsUnit g.det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (generalLinearMatrixAt_isUnit R _ n _)
  have hg' : IsUnit g'.det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (generalLinearMatrixAt_isUnit R _ n _)
  have heq : matrixFlag g hg = matrixFlag g' hg' := FlagScheme.ofRingFlag_injective (R := R) h
  have hup : (g⁻¹ * g').BlockTriangular id := (matrixFlag_eq_iff g g' hg hg').mp heq
  have hc : IsUnit (g⁻¹ * g').det := by
    rw [Matrix.det_mul]
    exact (g.isUnit_nonsing_inv_det hg).mul hg'
  refine ⟨borelPointOfMatrix R (g⁻¹ * g') hc hup, ?_⟩
  rw [lift_mulRight]
  congr 1
  apply glCoord_algHom_ext R
  rw [pointMatrix_glPointOfMatrix, borelMatrix_map_borelPointOfMatrix]
  exact Matrix.mul_nonsing_inv_cancel_left g g' hg

variable {R n} in
theorem toSpec_eq_of_orbitMap_eq {T : Scheme.{u}} {a a' : T ⟶ GLScheme R n}
    (h : a ≫ FlagScheme.orbitMap R n = a' ≫ FlagScheme.orbitMap R n) :
    a ≫ (GLOver R n).hom = a' ≫ (GLOver R n).hom := by
  rw [← FlagScheme.orbitMap_toSpec, reassoc_of% h]

variable {R n} in
/-- **The fibres of `π` are `B`-orbits**: two points `a, a' : T ⟶ GLₙ` of an affine scheme with
`π a = π a'` differ by a point of `B`: `a' = a · β`. -/
theorem exists_mulRight_eq {T : Scheme.{u}} [IsAffine T] (a a' : T ⟶ GLScheme R n)
    (h : a ≫ FlagScheme.orbitMap R n = a' ≫ FlagScheme.orbitMap R n) :
    ∃ (β : T ⟶ BorelScheme R n) (hβ : a ≫ (GLOver R n).hom = β ≫ BorelScheme.toSpec R n),
      pullback.lift a β hβ ≫ mulRight R n = a' := by
  let e := T.isoSpec
  let p : Spec (CommRingCat.of Γ(T, ⊤)) ⟶ Spec (CommRingCat.of (GLCoord R n)) :=
    e.inv ≫ a ≫ (TauCeti.GeneralLinear.groupSchemeSpecIso R n).hom
  let q : Spec (CommRingCat.of Γ(T, ⊤)) ⟶ Spec (CommRingCat.of (GLCoord R n)) :=
    e.inv ≫ a' ≫ (TauCeti.GeneralLinear.groupSchemeSpecIso R n).hom
  have hpq : p ≫ Spec.map (CommRingCat.ofHom (algebraMap R (GLCoord R n))) =
      q ≫ Spec.map (CommRingCat.ofHom (algebraMap R (GLCoord R n))) := by
    have h2 := congrArg (fun f => e.inv ≫ f) (toSpec_eq_of_orbitMap_eq h)
    simp only [TauCeti.GeneralLinear.groupScheme_X_hom] at h2
    simpa only [p, q, Category.assoc] using h2
  let _ : Algebra R Γ(T, ⊤) := affinePointPairAlgebra R p q hpq
  let k := affinePointPairLeftHom R p q hpq
  let k' := affinePointPairRightHom R p q hpq
  have hk : GLScheme.point R n k = e.inv ≫ a := by
    change Spec.map (CommRingCat.ofHom k.toRingHom) ≫
      (TauCeti.GeneralLinear.groupSchemeSpecIso R n).inv = _
    rw [affinePointPairLeftHom_spec]
    simp [p]
  have hk' : GLScheme.point R n k' = e.inv ≫ a' := by
    change Spec.map (CommRingCat.ofHom k'.toRingHom) ≫
      (TauCeti.GeneralLinear.groupSchemeSpecIso R n).inv = _
    rw [affinePointPairRightHom_spec]
    simp [q]
  obtain ⟨b, hb⟩ := exists_point_mulRight_eq k k' (by
    rw [hk, hk', Category.assoc, h, Category.assoc])
  let β : T ⟶ BorelScheme R n := e.hom ≫ Spec.map (CommRingCat.ofHom b.toRingHom)
  have hβ : a ≫ (GLOver R n).hom = β ≫ BorelScheme.toSpec R n := by
    have h1 : a = e.hom ≫ GLScheme.point R n k := by rw [hk, Iso.hom_inv_id_assoc]
    rw [h1, Category.assoc, point_borel_condition k b]
    rfl
  refine ⟨β, hβ, ?_⟩
  rw [← cancel_epi e.inv, ← hk', ← hb, ← Category.assoc]
  congr 1
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, hk]
  · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Iso.inv_hom_id_assoc]

variable {R n} in
/-- **`B` acts freely**: `a · β = a · β'` implies `β = β'`. -/
theorem mulRight_cancel {T : Scheme.{u}} [IsAffine T] (a : T ⟶ GLScheme R n)
    (β β' : T ⟶ BorelScheme R n) (hβ : a ≫ (GLOver R n).hom = β ≫ BorelScheme.toSpec R n)
    (hβ' : a ≫ (GLOver R n).hom = β' ≫ BorelScheme.toSpec R n)
    (h : pullback.lift a β hβ ≫ mulRight R n = pullback.lift a β' hβ' ≫ mulRight R n) :
    β = β' := by
  let e := T.isoSpec
  let p : Spec (CommRingCat.of Γ(T, ⊤)) ⟶ Spec (CommRingCat.of (BorelCoord R n)) := e.inv ≫ β
  let q : Spec (CommRingCat.of Γ(T, ⊤)) ⟶ Spec (CommRingCat.of (BorelCoord R n)) := e.inv ≫ β'
  have hpq : p ≫ Spec.map (CommRingCat.ofHom (algebraMap R (BorelCoord R n))) =
      q ≫ Spec.map (CommRingCat.ofHom (algebraMap R (BorelCoord R n))) := by
    change e.inv ≫ β ≫ BorelScheme.toSpec R n = e.inv ≫ β' ≫ BorelScheme.toSpec R n
    rw [← hβ, ← hβ']
  let _ : Algebra R Γ(T, ⊤) := affinePointPairAlgebra R p q hpq
  let kb := affinePointPairLeftHom R p q hpq
  let kb' := affinePointPairRightHom R p q hpq
  have hkb : Spec.map (CommRingCat.ofHom kb.toRingHom) = e.inv ≫ β :=
    affinePointPairLeftHom_spec R p q hpq
  have hkb' : Spec.map (CommRingCat.ofHom kb'.toRingHom) = e.inv ≫ β' :=
    affinePointPairRightHom_spec R p q hpq
  have hga : (e.inv ≫ a ≫ (TauCeti.GeneralLinear.groupSchemeSpecIso R n).hom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (GLCoord R n))) =
      Spec.map (CommRingCat.ofHom (algebraMap R Γ(T, ⊤))) := by
    have h1 := affinePointPairAlgebra_spec R p q hpq
    rw [h1]
    simp only [Category.assoc]
    change _ = (e.inv ≫ β) ≫ BorelScheme.toSpec R n
    rw [Category.assoc, ← TauCeti.GeneralLinear.groupScheme_X_hom, hβ]
  let k := affinePointAlgebraHom R _ hga
  have hk : GLScheme.point R n k = e.inv ≫ a := by
    change Spec.map (CommRingCat.ofHom k.toRingHom) ≫
      (TauCeti.GeneralLinear.groupSchemeSpecIso R n).inv = _
    rw [affinePointAlgebraHom_spec]
    simp
  have e1 : e.inv ≫ pullback.lift a β hβ =
      pullback.lift (GLScheme.point R n k) (Spec.map (CommRingCat.ofHom kb.toRingHom))
        (point_borel_condition k kb) := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, hk]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, hkb]
  have e2 : e.inv ≫ pullback.lift a β' hβ' =
      pullback.lift (GLScheme.point R n k) (Spec.map (CommRingCat.ofHom kb'.toRingHom))
        (point_borel_condition k kb') := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, hk]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, hkb']
  have h3 := congrArg (fun f => e.inv ≫ f) h
  simp only [← Category.assoc] at h3
  rw [e1, e2, lift_mulRight, lift_mulRight] at h3
  have h4 := Spec.map_injective ((cancel_mono (TauCeti.GeneralLinear.groupSchemeSpecIso R n).inv).mp
    h3)
  have h5 : glPointOfMatrix R (GLScheme.pointMatrix R n k * (borelMatrix R n).map kb)
      (isUnit_det_pointMatrix_mul k kb) =
      glPointOfMatrix R (GLScheme.pointMatrix R n k * (borelMatrix R n).map kb')
        (isUnit_det_pointMatrix_mul k kb') :=
    AlgHom.toRingHom_injective (congrArg CommRingCat.Hom.hom h4)
  have h6 := congrArg (GLScheme.pointMatrix R n) h5
  rw [pointMatrix_glPointOfMatrix, pointMatrix_glPointOfMatrix] at h6
  have hg : IsUnit (GLScheme.pointMatrix R n k).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (generalLinearMatrixAt_isUnit R _ n _)
  have h7 : (borelMatrix R n).map kb = (borelMatrix R n).map kb' := by
    rw [← Matrix.nonsing_inv_mul_cancel_left _ ((borelMatrix R n).map kb) hg, h6,
      Matrix.nonsing_inv_mul_cancel_left _ _ hg]
  have h8 : kb = kb' := borelMatrix_algHom_ext h7
  rw [← cancel_epi e.inv, ← hkb, ← hkb', h8]

/-! ### Sections over the big cells -/

theorem isOpenCover_bigCell : TopologicalSpace.IsOpenCover (bigCell R (n := n)) := by
  rw [TopologicalSpace.IsOpenCover, eq_top_iff]
  intro x _
  obtain ⟨v, hv⟩ := exists_mem_bigCell R x
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨v, hv⟩

/-- The big cells, as an open cover of `Flₙ`. -/
abbrev bigCellCover : (FlagScheme R n).OpenCover where
  I₀ := Equiv.Perm (Fin n)
  X v := bigCell R v
  f v := (bigCell R v).ι
  mem₀ := ((FlagScheme R n).openCoverOfIsOpenCover (bigCell R) (isOpenCover_bigCell R n)).mem₀

/-- The section `s_v : bigCell v ⟶ GLₙ` of `π`. -/
def bigCellSection' (v : Equiv.Perm (Fin n)) : (bigCell R v).toScheme ⟶ GLScheme R n :=
  (bigCellLocalData R v).e

@[reassoc (attr := simp)] theorem bigCellSection'_orbitMap (v : Equiv.Perm (Fin n)) :
    bigCellSection' R n v ≫ FlagScheme.orbitMap R n = (bigCell R v).ι :=
  (bigCellLocalData R v).e_q

/-! ### The coequalizer -/

variable {R n}

/-- **`B`-invariant morphisms are constant on the fibres of `π`.** -/
theorem comp_eq_of_orbitMap_eq {W Y : Scheme.{u}} (h : GLScheme R n ⟶ Y)
    (hh : mulRight R n ≫ h = pullback.fst _ _ ≫ h) (a a' : W ⟶ GLScheme R n)
    (ha : a ≫ FlagScheme.orbitMap R n = a' ≫ FlagScheme.orbitMap R n) : a ≫ h = a' ≫ h := by
  refine Scheme.hom_ext_of_forall _ _ fun x => ?_
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    W.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  refine ⟨U, hxU, ?_⟩
  have : IsAffine U := hU
  obtain ⟨β, hβ, e⟩ := exists_mulRight_eq (Scheme.Opens.ι U ≫ a) (Scheme.Opens.ι U ≫ a')
    (by rw [Category.assoc, ha, Category.assoc])
  rw [← Category.assoc (Scheme.Opens.ι U) a' h, ← e, Category.assoc, hh, pullback.lift_fst_assoc,
    Category.assoc]

/-- The morphism `Flₙ ⟶ Y` induced by a `B`-invariant morphism `GLₙ ⟶ Y`. -/
def orbitDesc {Y : Scheme.{u}} (h : GLScheme R n ⟶ Y)
    (hh : mulRight R n ≫ h = pullback.fst _ _ ≫ h) : FlagScheme R n ⟶ Y :=
  (bigCellCover R n).glueMorphisms (fun v => bigCellSection' R n v ≫ h) (fun x y => by
    rw [← Category.assoc, ← Category.assoc]
    apply comp_eq_of_orbitMap_eq h hh
    rw [Category.assoc, Category.assoc, bigCellSection'_orbitMap, bigCellSection'_orbitMap]
    exact pullback.condition)

theorem bigCell_ι_orbitDesc {Y : Scheme.{u}} (h : GLScheme R n ⟶ Y)
    (hh : mulRight R n ≫ h = pullback.fst _ _ ≫ h) (v : Equiv.Perm (Fin n)) :
    (bigCell R v).ι ≫ orbitDesc h hh = bigCellSection' R n v ≫ h :=
  Scheme.Cover.ι_glueMorphisms (bigCellCover R n) _ _ v

theorem orbitMap_orbitDesc {Y : Scheme.{u}} (h : GLScheme R n ⟶ Y)
    (hh : mulRight R n ≫ h = pullback.fst _ _ ≫ h) :
    FlagScheme.orbitMap R n ≫ orbitDesc h hh = h := by
  refine Scheme.hom_ext_of_forall _ _ fun x => ?_
  obtain ⟨v, hv⟩ := exists_mem_bigCell R (FlagScheme.orbitMap R n x)
  refine ⟨FlagScheme.orbitMap R n ⁻¹ᵁ bigCell R v, hv, ?_⟩
  rw [← morphismRestrict_ι_assoc, bigCell_ι_orbitDesc, ← Category.assoc]
  apply comp_eq_of_orbitMap_eq h hh
  rw [Category.assoc, bigCellSection'_orbitMap, morphismRestrict_ι]

/-- **`Flₙ = GLₙ / B`**: the orbit map `π` is the coequalizer of the projection and the right
action `GLₙ ×_R B ⇉ GLₙ`, in the category of schemes, over every commutative ring. -/
def isColimitOrbitMap :
    IsColimit (Cofork.ofπ (FlagScheme.orbitMap R n) (mulRight_orbitMap R n)) :=
  Cofork.IsColimit.mk' _ fun s => ⟨orbitDesc s.π s.condition, orbitMap_orbitDesc _ _,
    fun {m} hm => (bigCellCover R n).hom_ext _ _ fun v => by
      change (bigCell R v).ι ≫ m = (bigCell R v).ι ≫ orbitDesc s.π s.condition
      rw [bigCell_ι_orbitDesc, ← bigCellSection'_orbitMap_assoc]
      exact congrArg (fun f => bigCellSection' R n v ≫ f) hm⟩

end FlagVarieties
