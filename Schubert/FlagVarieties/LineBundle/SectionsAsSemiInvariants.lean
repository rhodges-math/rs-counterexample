import Schubert.FlagVarieties.LineBundle.Comparison

/-!
# Sections as semi-invariants: `H⁰(X, 𝓛(η)) ≅ (𝒪(GLₙ) ⧸ I_X^G)^{(B, η)}`

For a closed subscheme `X ⊆ Flₙ` with ideal sheaf `I`, let `J = preimageIdeal R n I ⊆ 𝒪(GLₙ)` be the
ideal of `π⁻¹(X)`. Global functions on `P_X = π⁻¹(X)` are `𝒪(GLₙ) ⧸ J` (`preimageQuotEquiv`), and a
function is semi-invariant of weight `η` iff its defect `ρ(f) - f ⊗ η⁻¹` vanishes in
`(𝒪(GLₙ) ⧸ J) ⊗ 𝒪(B)` (`isSemiInvariant_preimageRestrictSections_iff`).
-/

noncomputable section

namespace FlagVarieties

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

universe u

variable (R : Type u) [CommRing R] (n : ℕ)

instance : IsAffine (GLScheme R n) :=
  IsAffine.of_isIso (TauCeti.GeneralLinear.groupSchemeSpecIso R n).hom

instance : IsAffine (GLBorel R n) :=
  IsAffine.of_isIso (glBorelSpecIso R n).hom

theorem glCoordToGlobal_bijective : Function.Bijective (glCoordToGlobal R n) := by
  have : IsIso ((TauCeti.GeneralLinear.groupSchemeSpecIso R n).hom.app ⊤) := inferInstance
  exact ConcreteCategory.bijective_of_isIso
    ((Scheme.ΓSpecIso (CommRingCat.of (GLCoord R n))).inv ≫
      (TauCeti.GeneralLinear.groupSchemeSpecIso R n).hom.app ⊤)

/-! ### Functions on `π⁻¹(X)` -/

variable (I : (FlagScheme R n).IdealSheafData)

/-- `f ↦ j^* f`, from `𝒪(GLₙ)` to global functions on `P_X`. -/
def preimageRestrictSections : GLCoord R n →+* Γ(preimageScheme R n I, ⊤) :=
  (preimageι R n I).appTop.hom.comp (glCoordToGlobal R n)

theorem ker_preimageRestrictSections :
    RingHom.ker (preimageRestrictSections R n I) = preimageIdeal R n I := by
  ext f
  rw [RingHom.mem_ker, preimageIdeal, Ideal.mem_comap, Scheme.IdealSheafData.comap,
    Scheme.Hom.ker_apply]
  rfl

theorem preimageRestrictSections_surjective : Function.Surjective
    (preimageRestrictSections R n I) :=
  (IsClosedImmersion.isAffine_surjective_of_isAffine (preimageι R n I)).2.comp
    (glCoordToGlobal_bijective R n).2

/-- **Global functions on `π⁻¹(X)` are `𝒪(GLₙ) ⧸ J`.** -/
def preimageQuotEquiv : (GLCoord R n ⧸ preimageIdeal R n I) ≃+* Γ(preimageScheme R n I, ⊤) :=
  (Ideal.quotEquivOfEq (ker_preimageRestrictSections R n I).symm).trans
    (RingHom.quotientKerEquivOfSurjective (preimageRestrictSections_surjective R n I))

theorem preimageQuotEquiv_mk (f : GLCoord R n) :
    preimageQuotEquiv R n I (Ideal.Quotient.mk _ f) = preimageRestrictSections R n I f :=
  rfl

/-! ### Global functions on `GLₙ ×_R B` -/

/-- Global functions on `GLₙ ×_R B` are `𝒪(GLₙ) ⊗ 𝒪(B)`. -/
def glBorelEval : Γ(GLBorel R n, ⊤) →+* GLBorelCoord R n :=
  ((glBorelUniversalPoint R n).appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of (GLBorelCoord R n))).hom).hom

theorem glBorelEval_bijective : Function.Bijective (glBorelEval R n) := by
  have : IsIso (glBorelUniversalPoint R n) := inferInstanceAs (IsIso (glBorelSpecIso R n).inv)
  have h1 := ConcreteCategory.bijective_of_isIso ((glBorelUniversalPoint R n).app ⊤)
  have h2 := ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (CommRingCat.of (GLBorelCoord R n))).hom
  exact h2.comp h1

/-- The coaction `f ↦ f(g b)`, into the wrapped ring `𝒪(GLₙ) ⊗ 𝒪(B)`. -/
abbrev rightCoactionW : GLCoord R n →ₐ[R] GLBorelCoord R n :=
  glPointOfMatrix R (GLScheme.pointMatrix R n (GLBorelCoord.inl R n) * (borelMatrix R n).map
      (GLBorelCoord.inr R n))
    (isUnit_det_pointMatrix_mul _ _)

theorem glBorelEval_mulRight (f : GLCoord R n) :
    glBorelEval R n ((mulRight R n).appTop.hom (glCoordToGlobal R n f)) = rightCoactionW R n f := by
  have h : glBorelUniversalPoint R n ≫ mulRight R n = GLScheme.point R n (rightCoactionW R n) := by
    rw [glBorelUniversalPoint_eq, lift_mulRight]
  have e : (glBorelUniversalPoint R n).appTop.hom
      ((mulRight R n).appTop.hom (glCoordToGlobal R n f)) =
      (Scheme.ΓSpecIso (CommRingCat.of (GLBorelCoord R n))).inv (rightCoactionW R n f) := by
    rw [← point_appTop_glCoordToGlobal, ← h]
    rfl
  change (Scheme.ΓSpecIso _).hom.hom ((glBorelUniversalPoint R n).appTop.hom _) = _
  rw [e, ← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]

theorem glBorelEval_fst (f : GLCoord R n) :
    glBorelEval R n ((pullback.fst (GLOver R n).hom (BorelScheme.toSpec R n)).appTop.hom
      (glCoordToGlobal R n f)) = GLBorelCoord.inl R n f := by
  have e : (glBorelUniversalPoint R n).appTop.hom ((pullback.fst (GLOver R n).hom
      (BorelScheme.toSpec R n)).appTop.hom (glCoordToGlobal R n f)) =
      (Scheme.ΓSpecIso (CommRingCat.of (GLBorelCoord R n))).inv (GLBorelCoord.inl R n f) := by
    rw [← point_appTop_glCoordToGlobal, ← glBorelUniversalPoint_fst]
    rfl
  change (Scheme.ΓSpecIso _).hom.hom ((glBorelUniversalPoint R n).appTop.hom _) = _
  rw [e, ← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]

theorem glBorelEval_twist (η : Fin n → ℤ) :
    glBorelEval R n ((glBorelAction R n).twist η) =
      GLBorelCoord.inr R n (((borelCharacterUnit R n η)⁻¹ : (BorelCoord R n)ˣ) :
          BorelCoord R n) := by
  have e : (glBorelUniversalPoint R n).appTop.hom ((glBorelAction R n).twist η) =
      (Scheme.ΓSpecIso (CommRingCat.of (GLBorelCoord R n))).inv
        (GLBorelCoord.inr R n (((borelCharacterUnit R n η)⁻¹ : (BorelCoord R n)ˣ) :
            BorelCoord R n)) := by
    change (glBorelUniversalPoint R n ≫ pullback.snd _ _).appTop.hom _ = _
    rw [glBorelUniversalPoint_snd, ← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]
    rfl
  change (Scheme.ΓSpecIso _).hom.hom ((glBorelUniversalPoint R n).appTop.hom _) = _
  rw [e, ← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]

/-! ### Functions on `π⁻¹(X) ×_R B` -/

/-- `(𝒪(GLₙ) ⧸ J) ⊗_R 𝒪(B)`, the coordinate ring of `π⁻¹(X) ×_R B`. -/
def PreimageTensorRing : Type u :=
  (GLCoord R n ⧸ preimageIdeal R n I) ⊗[R] BorelCoord R n

instance : CommRing (PreimageTensorRing R n I) :=
  inferInstanceAs (CommRing ((GLCoord R n ⧸ preimageIdeal R n I) ⊗[R] BorelCoord R n))

instance : Algebra R (PreimageTensorRing R n I) :=
  inferInstanceAs (Algebra R ((GLCoord R n ⧸ preimageIdeal R n I) ⊗[R] BorelCoord R n))

/-- The first factor `𝒪(GLₙ) ⧸ J → (𝒪(GLₙ) ⧸ J) ⊗ 𝒪(B)`. -/
def tensorInl : (GLCoord R n ⧸ preimageIdeal R n I) →ₐ[R] PreimageTensorRing R n I :=
  Algebra.TensorProduct.includeLeft

/-- The second factor `𝒪(B) → (𝒪(GLₙ) ⧸ J) ⊗ 𝒪(B)`. -/
def tensorInr : BorelCoord R n →ₐ[R] PreimageTensorRing R n I :=
  Algebra.TensorProduct.includeRight

/-- `(𝒪(GLₙ) ⊗ 𝒪(B)) → (𝒪(GLₙ) ⧸ J) ⊗ 𝒪(B)`. -/
def preimageTensorMap : GLBorelCoord R n →ₐ[R] PreimageTensorRing R n I :=
  Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R (preimageIdeal R n I))
    (AlgHom.id R (BorelCoord R n))

theorem preimageTensorMap_inl :
    (preimageTensorMap R n I).comp (GLBorelCoord.inl R n) =
      (tensorInl R n I).comp (Ideal.Quotient.mkₐ R (preimageIdeal R n I)) :=
  Algebra.TensorProduct.map_comp_includeLeft _ _

theorem preimageTensorMap_inr :
    (preimageTensorMap R n I).comp (GLBorelCoord.inr R n) = tensorInr R n I :=
  Algebra.TensorProduct.map_comp_includeRight _ _

theorem ker_preimageTensorMap :
    RingHom.ker (preimageTensorMap R n I) = (preimageIdeal R n I).map (GLBorelCoord.inl R n) := by
  have h := Algebra.TensorProduct.rTensor_ker (R := R) (C := BorelCoord R n)
    (Ideal.Quotient.mkₐ R (preimageIdeal R n I)) Ideal.Quotient.mk_surjective
  have hk : RingHom.ker (Ideal.Quotient.mkₐ R (preimageIdeal R n I)) = preimageIdeal R n I :=
    Ideal.Quotient.mkₐ_ker R _
  rw [hk] at h
  exact h

/-- The ring isomorphism `Γ(GLₙ ×_R B) ≃ 𝒪(GLₙ) ⊗ 𝒪(B)`. -/
abbrev glBorelEvalEquiv : Γ(GLBorel R n, ⊤) ≃+* GLBorelCoord R n :=
  RingEquiv.ofBijective (glBorelEval R n) (glBorelEval_bijective R n)

theorem preimageProdMap_appTop_fst (x : GLCoord R n) :
    (preimageProdMap R n I).appTop.hom ((pullback.fst (GLOver R n).hom
      (BorelScheme.toSpec R n)).appTop.hom (glCoordToGlobal R n x)) =
      (pullback.fst (preimageToSpec R n I) (BorelScheme.toSpec R n)).appTop.hom
        (preimageRestrictSections R n I x) := by
  change (preimageProdMap R n I ≫ pullback.fst _ _).appTop.hom _ =
    (pullback.fst _ _ ≫ preimageι R n I).appTop.hom _
  rw [preimageProdMap, pullback.lift_fst]

/-- If `(mk ⊗ id)(d) = 0`, then `d` vanishes on `π⁻¹(X) ×_R B`. -/
theorem preimageProdMap_appTop_eq_zero_of {d : Γ(GLBorel R n, ⊤)}
    (hd : preimageTensorMap R n I (glBorelEval R n d) = 0) :
    (preimageProdMap R n I).appTop.hom d = 0 := by
  let ζ : GLBorelCoord R n →+* Γ(PreimageProd R n I, ⊤) :=
    (preimageProdMap R n I).appTop.hom.comp (glBorelEvalEquiv R n).symm.toRingHom
  have hle : (preimageIdeal R n I).map (GLBorelCoord.inl R n) ≤ RingHom.ker ζ := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, RingHom.mem_ker]
    have e : (glBorelEvalEquiv R n).symm (GLBorelCoord.inl R n x) = (pullback.fst (GLOver R n).hom
        (BorelScheme.toSpec R n)).appTop.hom (glCoordToGlobal R n x) := by
      rw [RingEquiv.symm_apply_eq]
      exact (glBorelEval_fst R n x).symm
    change (preimageProdMap R n I).appTop.hom
        ((glBorelEvalEquiv R n).symm (GLBorelCoord.inl R n x)) = 0
    rw [e, preimageProdMap_appTop_fst]
    have hx' : preimageRestrictSections R n I x = 0 := by
      rw [← RingHom.mem_ker, ker_preimageRestrictSections]
      exact hx
    rw [hx', map_zero]
  have hmem : glBorelEval R n d ∈ RingHom.ker ζ := by
    apply hle
    rw [← ker_preimageTensorMap]
    exact hd
  rw [RingHom.mem_ker] at hmem
  change (preimageProdMap R n I).appTop.hom ((glBorelEvalEquiv R n).symm (glBorelEval R n d)) = 0
    at hmem
  rwa [show (glBorelEvalEquiv R n).symm (glBorelEval R n d) = d from
    (glBorelEvalEquiv R n).symm_apply_apply d] at hmem

/-- `Spec(𝒪(GLₙ) ⧸ J) ⊆ GLₙ` lies in `π⁻¹(X)`. -/
theorem ker_preimageι_le :
    (preimageι R n I).ker ≤
      (GLScheme.point R n (Ideal.Quotient.mkₐ R (preimageIdeal R n I))).ker := by
  apply Scheme.IdealSheafData.le_of_isAffine
  rw [Scheme.Hom.ker_apply, Scheme.Hom.ker_apply]
  intro y hy
  obtain ⟨f, rfl⟩ := (glCoordToGlobal_bijective R n).2 y
  have hf : f ∈ preimageIdeal R n I := by
    rw [← ker_preimageRestrictSections, RingHom.mem_ker]
    exact hy
  rw [RingHom.mem_ker]
  change (GLScheme.point R n (Ideal.Quotient.mkₐ R (preimageIdeal R n I))).appTop.hom _ = 0
  rw [point_appTop_glCoordToGlobal, Ideal.Quotient.mkₐ_eq_mk,
    Ideal.Quotient.eq_zero_iff_mem.mpr hf, map_zero]

/-- `Spec(𝒪(GLₙ) ⧸ J) ⟶ π⁻¹(X)`. -/
def preimageSpecMap : Spec (CommRingCat.of (GLCoord R n ⧸ preimageIdeal R n I)) ⟶
    preimageScheme R n I :=
  IsClosedImmersion.lift (preimageι R n I) _ (ker_preimageι_le R n I)

@[reassoc] theorem preimageSpecMap_ι : preimageSpecMap R n I ≫ preimageι R n I =
    GLScheme.point R n (Ideal.Quotient.mkₐ R (preimageIdeal R n I)) :=
  IsClosedImmersion.lift_fac _ _ _

theorem preimageTensorSpec_condition :
    (Spec.map (CommRingCat.ofHom (tensorInl R n I).toRingHom) ≫
        preimageSpecMap R n I) ≫ preimageToSpec R n I =
      Spec.map (CommRingCat.ofHom (tensorInr R n I).toRingHom) ≫ BorelScheme.toSpec R n := by
  rw [Category.assoc, preimageToSpec, preimageSpecMap_ι_assoc, point_toSpec,
    spec_map_borelScheme_toSpec, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2

/-- `Spec((𝒪(GLₙ) ⧸ J) ⊗ 𝒪(B)) ⟶ π⁻¹(X) ×_R B`. -/
def preimageTensorSpecMap :
    Spec (CommRingCat.of (PreimageTensorRing R n I)) ⟶ PreimageProd R n I :=
  pullback.lift _ _ (preimageTensorSpec_condition R n I)

theorem preimageTensorSpecMap_prodMap :
    preimageTensorSpecMap R n I ≫ preimageProdMap R n I =
      Spec.map (CommRingCat.ofHom (preimageTensorMap R n I).toRingHom) ≫
          glBorelUniversalPoint R n := by
  apply pullback.hom_ext
  · rw [Category.assoc, preimageProdMap, pullback.lift_fst, preimageTensorSpecMap,
      pullback.lift_fst_assoc, Category.assoc, preimageSpecMap_ι, spec_map_comp_point,
      Category.assoc, glBorelUniversalPoint_fst, spec_map_comp_point, preimageTensorMap_inl]
  · rw [Category.assoc, preimageProdMap, pullback.lift_snd, Category.comp_id,
      preimageTensorSpecMap, pullback.lift_snd, Category.assoc, glBorelUniversalPoint_snd,
          ← Spec.map_comp,
      ← CommRingCat.ofHom_comp]
    congr 2

/-- If `d` vanishes on `π⁻¹(X) ×_R B`, then `(mk ⊗ id)(d) = 0`. -/
theorem preimageTensorMap_eq_zero_of {d : Γ(GLBorel R n, ⊤)}
    (hd : (preimageProdMap R n I).appTop.hom d = 0) :
    preimageTensorMap R n I (glBorelEval R n d) = 0 := by
  apply (Scheme.ΓSpecIso (CommRingCat.of
    (PreimageTensorRing R n I))).commRingCatIsoToRingEquiv.symm.injective
  rw [map_zero]
  change (Scheme.ΓSpecIso (CommRingCat.of (PreimageTensorRing R n I))).inv.hom
    ((preimageTensorMap R n I).toRingHom (glBorelEval R n d)) = 0
  rw [← CommRingCat.hom_ofHom (preimageTensorMap R n I).toRingHom, ← CommRingCat.comp_apply,
    Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
  have e : (Scheme.ΓSpecIso (CommRingCat.of (GLBorelCoord R n))).inv.hom (glBorelEval R n d) =
      (glBorelUniversalPoint R n).appTop.hom d := by
    change (Scheme.ΓSpecIso _).inv.hom ((Scheme.ΓSpecIso _).hom.hom _) = _
    rw [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]
    rfl
  rw [e]
  change (Spec.map (CommRingCat.ofHom (preimageTensorMap R n I).toRingHom) ≫
    glBorelUniversalPoint R n).appTop.hom d = 0
  rw [← preimageTensorSpecMap_prodMap]
  change (preimageTensorSpecMap R n I).appTop.hom ((preimageProdMap R n I).appTop.hom d) = 0
  rw [hd, map_zero]

/-! ### Semi-invariant functions on `π⁻¹(X)` -/

theorem rightCoactionW_eq :
    rightCoactionW R n = (rightCoaction R n : GLCoord R n →ₐ[R] GLBorelCoord R n) := by
  apply glCoord_algHom_ext R
  rw [pointMatrix_glPointOfMatrix]
  exact (map_rightCoaction_genericMatrix R n).symm

theorem preimageTensorMap_rightCoactionW (f : GLCoord R n) :
    preimageTensorMap R n I (rightCoactionW R n f) =
      (rightCoactionMod R n (preimageIdeal R n I) f : PreimageTensorRing R n I) := by
  rw [rightCoactionW_eq]
  rfl

theorem preimageTensorMap_inl_mul_inr (f : GLCoord R n) (b : BorelCoord R n) :
    preimageTensorMap R n I (GLBorelCoord.inl R n f * GLBorelCoord.inr R n b) =
      (Ideal.Quotient.mk (preimageIdeal R n I) f ⊗ₜ[R] b : PreimageTensorRing R n I) := by
  rw [map_mul]
  change (Ideal.Quotient.mk (preimageIdeal R n I) f ⊗ₜ[R] (1 : BorelCoord R n)) *
    ((1 : GLCoord R n ⧸ preimageIdeal R n I) ⊗ₜ[R] b) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem preimageTensorMap_defect (η : Fin n → ℤ) (f : GLCoord R n) :
    preimageTensorMap R n I (rightCoactionW R n f - GLBorelCoord.inl R n f *
        GLBorelCoord.inr R n (((borelCharacterUnit R n η)⁻¹ : (BorelCoord R n)ˣ) :
            BorelCoord R n)) =
      (semiInvariantDefect R n (preimageIdeal R n I) η f : PreimageTensorRing R n I) := by
  rw [map_sub, preimageTensorMap_rightCoactionW, preimageTensorMap_inl_mul_inr]
  rfl

/-- **Semi-invariant functions on `π⁻¹(X)`**: the restriction of `f ∈ 𝒪(GLₙ)` to `π⁻¹(X)` is
semi-invariant of weight `η` iff `ρ(f) = f ⊗ η⁻¹` in `(𝒪(GLₙ) ⧸ J) ⊗ 𝒪(B)`. -/
theorem isSemiInvariant_preimageRestrictSections_iff (η : Fin n → ℤ) (f : GLCoord R n) :
    (preimageAction R n I).IsSemiInvariant η (W := ⊤) (preimageRestrictSections R n I f) ↔
      semiInvariantDefect R n (preimageIdeal R n I) η f = 0 := by
  set F := glCoordToGlobal R n f
  have e1 : (preimageAction R n I).act.appTop.hom (preimageRestrictSections R n I f) =
      (preimageProdMap R n I).appTop.hom ((mulRight R n).appTop.hom F) :=
    congrArg (fun φ => (CommRingCat.Hom.hom (Scheme.Hom.appTop φ)) F)
      (preimageHom R n I).act_j'
  have e2 : (preimageAction R n I).actionFst.appTop.hom (preimageRestrictSections R n I f) =
      (preimageProdMap R n I).appTop.hom
        ((pullback.fst (GLOver R n).hom (BorelScheme.toSpec R n)).appTop.hom F) :=
    (preimageProdMap_appTop_fst R n I f).symm
  have e3 : (preimageAction R n I).twist η =
      (preimageProdMap R n I).appTop.hom ((glBorelAction R n).twist η) :=
    (congrArg (fun φ => (CommRingCat.Hom.hom (Scheme.Hom.appTop φ))
      ((Scheme.ΓSpecIso (CommRingCat.of (BorelCoord R n))).inv
        (((borelCharacterUnit R n η)⁻¹ : (BorelCoord R n)ˣ) : BorelCoord R n)))
      (preimageHom R n I).prodMap_actionSnd).symm
  refine ((preimageAction R n I).isSemiInvariant_top_iff η _).trans ?_
  rw [e1, e2, e3]
  have key : (preimageProdMap R n I).appTop.hom ((mulRight R n).appTop.hom F) =
      (preimageProdMap R n I).appTop.hom ((glBorelAction R n).twist η) *
        (preimageProdMap R n I).appTop.hom
          ((pullback.fst (GLOver R n).hom (BorelScheme.toSpec R n)).appTop.hom F) ↔
      (preimageProdMap R n I).appTop.hom ((mulRight R n).appTop.hom F -
        (show Γ(GLBorel R n, ⊤) from (glBorelAction R n).twist η) *
          (pullback.fst (GLOver R n).hom (BorelScheme.toSpec R n)).appTop.hom F) = 0 := by
    rw [map_sub, map_mul, sub_eq_zero]
  refine key.trans ?_
  have hd : glBorelEval R n ((mulRight R n).appTop.hom F -
      (show Γ(GLBorel R n, ⊤) from (glBorelAction R n).twist η) *
      (pullback.fst (GLOver R n).hom (BorelScheme.toSpec R n)).appTop.hom F) =
      rightCoactionW R n f - GLBorelCoord.inl R n f *
        GLBorelCoord.inr R n (((borelCharacterUnit R n η)⁻¹ : (BorelCoord R n)ˣ) :
            BorelCoord R n) := by
    rw [map_sub, map_mul, glBorelEval_mulRight, glBorelEval_twist, glBorelEval_fst, mul_comm]
  constructor
  · intro h
    have h' := preimageTensorMap_eq_zero_of R n I h
    rw [hd, preimageTensorMap_defect] at h'
    exact h'
  · intro h
    apply preimageProdMap_appTop_eq_zero_of
    rw [hd, preimageTensorMap_defect]
    exact h

/-! ### The base ring -/

theorem glCoordToGlobal_algebraMap (r : R) :
    glCoordToGlobal R n (algebraMap R (GLCoord R n) r) =
      (GLOver R n).hom.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r) := by
  rw [TauCeti.GeneralLinear.groupScheme_X_hom]
  change _ = (TauCeti.GeneralLinear.groupSchemeSpecIso R n).hom.appTop.hom
    ((Spec.map (CommRingCat.ofHom (algebraMap R (GLCoord R n)))).appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r))
  rw [← CommRingCat.comp_apply ((Scheme.ΓSpecIso (CommRingCat.of R)).inv),
    ← Scheme.ΓSpecIso_inv_naturality]
  rfl

/-- The base ring acts on functions on `π⁻¹(X)` through `𝒪(GLₙ)`. -/
theorem preimageProj_baseRing (r : R) :
    (preimageProj R n I).appTop.hom (Scheme.Modules.baseRingToGlobalSections R I.subscheme r) =
      preimageRestrictSections R n I (algebraMap R (GLCoord R n) r) := by
  rw [Scheme.Modules.baseRingToGlobalSections_apply, preimageRestrictSections, RingHom.comp_apply,
    glCoordToGlobal_algebraMap]
  change (preimageProj R n I ≫ I.subschemeι ≫ FlagScheme.toSpec R n).appTop.hom _ =
    (preimageι R n I ≫ (GLOver R n).hom).appTop.hom _
  rw [← Category.assoc, ← pullback.condition, Category.assoc, FlagScheme.orbitMap_toSpec]

/-! ### Sections as semi-invariants -/

variable (η : Fin n → ℤ)

/-- A global section of `𝓛_X(η)`, as a function on `π⁻¹(X)`. -/
def sectionX (x : Γ(lineBundleX R n I η, ⊤)) : Γ(preimageScheme R n I, ⊤) :=
  (((preimageAction R n I).semiInvariantι η).app ⊤).hom x

theorem sectionX_add (x y : Γ(lineBundleX R n I η, ⊤)) :
    sectionX R n I η (x + y) = sectionX R n I η x + sectionX R n I η y :=
  map_add _ x y

theorem sectionX_smul (a : Γ(I.subscheme, ⊤)) (x : Γ(lineBundleX R n I η, ⊤)) :
    sectionX R n I η (a • x) = (preimageProj R n I).appTop.hom a * sectionX R n I η x := by
  rw [sectionX, Scheme.Modules.Hom.app_smul]
  rfl

theorem sectionX_injective : Function.Injective (sectionX R n I η) :=
  kernel_ι_app_injective ((preimageAction R n I).pullbackAct -
    (preimageAction R n I).pullbackTwist η) ⊤

theorem isSemiInvariant_sectionX (x : Γ(lineBundleX R n I η, ⊤)) :
    (preimageAction R n I).IsSemiInvariant η (W := ⊤) (sectionX R n I η x) :=
  ((preimageAction R n I).mem_range_semiInvariantι_app_iff η ⊤ _).mp ⟨x, rfl⟩

/-- The global sections of `𝓛_X(η)` as functions on `π⁻¹(X)`, read in `𝒪(GLₙ) ⧸ J`. -/
def sectionsXToQuot :
    Γ(lineBundleX R n I η, ⊤) →ₗ[R] GLCoord R n ⧸ preimageIdeal R n I where
  toFun x := (preimageQuotEquiv R n I).symm (sectionX R n I η x)
  map_add' x y := by
    rw [sectionX_add, map_add]
  map_smul' r x := by
    rw [Scheme.Modules.base_smul_globalSections, sectionX_smul, map_mul, preimageProj_baseRing,
      ← preimageQuotEquiv_mk, RingEquiv.symm_apply_apply]
    exact (Algebra.smul_def (A := GLCoord R n ⧸ preimageIdeal R n I) r _).symm

theorem sectionsXToQuot_mem (x : Γ(lineBundleX R n I η, ⊤)) :
    sectionsXToQuot R n I η x ∈ quotientSemiInvariants R n (preimageIdeal R n I) η := by
  obtain ⟨f, hf⟩ := preimageRestrictSections_surjective R n I (sectionX R n I η x)
  have hs := isSemiInvariant_sectionX R n I η x
  rw [← hf, isSemiInvariant_preimageRestrictSections_iff] at hs
  refine ⟨f, hs, ?_⟩
  change Ideal.Quotient.mk _ f = (preimageQuotEquiv R n I).symm (sectionX R n I η x)
  rw [← hf, ← preimageQuotEquiv_mk, RingEquiv.symm_apply_apply]

/-- **The global sections of `𝓛_X(η)` are the semi-invariants of weight `η` in `𝒪(GLₙ) ⧸ J`.** -/
def sectionsXEquiv : Γ(lineBundleX R n I η, ⊤) ≃ₗ[R] quotientSemiInvariants R n
    (preimageIdeal R n I) η :=
  LinearEquiv.ofBijective ((sectionsXToQuot R n I η).codRestrict _ (sectionsXToQuot_mem R n I η))
    (by
      constructor
      · intro x y hxy
        apply sectionX_injective R n I η
        have h := congrArg Subtype.val hxy
        exact (preimageQuotEquiv R n I).symm.injective h
      · rintro ⟨q, f, hf, rfl⟩
        have hs : (preimageAction R n I).IsSemiInvariant η (W := ⊤)
            (preimageRestrictSections R n I f) :=
          (isSemiInvariant_preimageRestrictSections_iff R n I η f).mpr hf
        obtain ⟨x, hx⟩ := ((preimageAction R n I).mem_range_semiInvariantι_app_iff η ⊤ _).mpr hs
        refine ⟨x, Subtype.ext ?_⟩
        change (preimageQuotEquiv R n I).symm (sectionX R n I η x) = _
        rw [show sectionX R n I η x = preimageRestrictSections R n I f from hx,
          ← preimageQuotEquiv_mk, RingEquiv.symm_apply_apply]
        rfl)

/-- `H⁰(X, i^* 𝓛(η)) ≅ H⁰(X, 𝓛_X(η))`, from `i^* 𝓛(η) ≅ 𝓛_X(η)`. -/
def sectionsComparison : sections R n I η ≃ₗ[R] Γ(lineBundleX R n I η, ⊤) :=
  have := isIso_lineBundleComparison R n I η
  LinearEquiv.ofBijective
    { toFun := ((lineBundleComparison R n I η).app ⊤).hom
      map_add' := map_add _
      map_smul' := fun r x => by
        rw [Scheme.Modules.base_smul_globalSections, Scheme.Modules.Hom.app_smul]
        rfl }
    (ConcreteCategory.bijective_of_isIso ((lineBundleComparison R n I η).app ⊤))

/-- **Sections as semi-invariants** (`sectionsEquivSemiInvariants`): for a closed subscheme
`X ⊆ Flₙ` with ideal sheaf `I`, `H⁰(X, 𝓛(η)) = Γ(X, i^* 𝓛(η))` is the module of semi-invariants of
weight `η` in `𝒪(π⁻¹X)`, `(𝒪(GLₙ) ⧸ J)^{(B, η)} = {f : ρ(f) = f ⊗ η⁻¹}`, where
`J = preimageIdeal R n I` is the ideal of
`π⁻¹(X) ⊆ GLₙ`. -/
def sectionsEquivSemiInvariants : sections R n I η ≃ₗ[R] quotientSemiInvariants R n
    (preimageIdeal R n I) η :=
  (sectionsComparison R n I η).trans (sectionsXEquiv R n I η)

/-- `sectionsEquivSemiInvariants` sends a section to the class of its function on `π⁻¹(X)`. -/
theorem preimageQuotEquiv_sectionsEquivSemiInvariants (s : sections R n I η) :
    preimageQuotEquiv R n I (sectionsEquivSemiInvariants R n I η s : GLCoord R n ⧸ preimageIdeal R n
        I) =
      sectionX R n I η (((lineBundleComparison R n I η).app ⊤).hom s) :=
  RingEquiv.apply_symm_apply _ _

end FlagVarieties
