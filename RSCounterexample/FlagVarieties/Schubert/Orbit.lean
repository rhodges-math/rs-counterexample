import RSCounterexample.FlagVarieties.Schubert.Flat
import RSCounterexample.FlagVarieties.Schubert.Preimage
import RSCounterexample.FlagVarieties.Charts.BigCellFunction
import RSCounterexample.FlagVarieties.Foundations.Schemes.AffinePointAlgebraHom

/-!
# The preimage of a Schubert variety in `GLₙ`

The ideal of `π⁻¹(X_w) ⊆ GLₙ` is the orbit ideal of `w`, the ideal of the closure of the double
coset `B ẇ B` (`FlagVarieties.preimageIdeal_schubertVariety`), when `𝒪(B)` is flat over `R`; in
particular over every field (`FlagVarieties.preimageIdeal_schubertVariety_eq_schubertOrbitIdeal`).

Since `π` is flat, `π⁻¹(X_w)` is the scheme-theoretic image of the base change
`Q = GLₙ ×_{Flₙ} B ⟶ GLₙ` of the orbit morphism `b ↦ b · ẇE•` (`FlagVarieties.comap_ker_eq_ker`).
The scheme `Q` is affine, and on points: if `g · E• = b · ẇE•` then `b' = (b ẇ)⁻¹ g` is upper
triangular and `g = b ẇ b'` (`FlagVarieties.exists_eq_comp_schubertOrbitComorphism`). So every
function in the orbit ideal vanishes on `Q`.
-/

noncomputable section

namespace FlagVarieties

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Foundations Foundations.QuotientCharts

universe u

variable (R : Type u) [CommRing R] (n : ℕ)

/-! ### Affineness -/

theorem isAffine_glScheme : IsAffine (GLScheme R n) :=
  IsAffine.of_isIso (TauCeti.GeneralLinear.groupSchemeSpecIso R n).hom

/-- The orbit map `π : GLₙ ⟶ Flₙ` is affine (`GLₙ` is affine and `Flₙ` is separated). -/
theorem isAffineHom_orbitMap : IsAffineHom (FlagScheme.orbitMap R n) := by
  have := isAffine_glScheme R n
  have := FlagScheme.isSeparated_toSpec R n
  exact IsAffineHom.of_comp _ (FlagScheme.toSpec R n)

@[reassoc (attr := simp)] theorem schubertOrbitMap_toSpec (w : Equiv.Perm (Fin n)) :
    schubertOrbitMap R n w ≫ FlagScheme.toSpec R n = BorelScheme.toSpec R n := by
  simp only [schubertOrbitMap, FlagScheme.orbitMapAt, Category.assoc, FlagScheme.action_toSpec,
    pullback.lift_snd_assoc, permFlag_toSpec, Category.comp_id, borelInclusion_toSpec]

/-- The orbit morphism `b ↦ b · ẇE•` is affine. -/
theorem isAffineHom_schubertOrbitMap (w : Equiv.Perm (Fin n)) :
    IsAffineHom (schubertOrbitMap R n w) := by
  have := FlagScheme.isSeparated_toSpec R n
  exact IsAffineHom.of_comp _ (FlagScheme.toSpec R n)

/-! ### Points over the Schubert cell -/

variable {R n}

/-- **Points of `GLₙ` over the orbit of `ẇE•`**: if `g · E• = b · ẇE•`, then `g = b ẇ b'` with
`b' = (b ẇ)⁻¹ g` upper triangular. -/
theorem exists_eq_comp_schubertOrbitComorphism {A : Type u} [CommRing A] [Algebra R A]
    (w : Equiv.Perm (Fin n)) (k : GLCoord R n →ₐ[R] A) (b : BorelCoord R n →ₐ[R] A)
    (h : GLScheme.point R n k ≫ FlagScheme.orbitMap R n =
      Spec.map (CommRingCat.ofHom b.toRingHom) ≫ schubertOrbitMap R n w) :
    ∃ b' : BorelCoord R n →ₐ[R] A, k = (pairLift b b').comp (schubertOrbitComorphism R n w) := by
  rw [FlagScheme.orbitMap_point, schubertOrbitMap_point] at h
  let g := GLScheme.pointMatrix R n k
  have hg : IsUnit g.det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (generalLinearMatrixAt_isUnit R _ n _)
  let m := (borelMatrix R n).map b * permMatrix n w
  have hm : IsUnit m.det := isUnit_det_borelMatrix_map_mul_permMatrix R n w b
  have heq : matrixFlag g hg = matrixFlag m hm := FlagScheme.ofRingFlag_injective (R := R) h
  have hup : (m⁻¹ * g).BlockTriangular id := (matrixFlag_eq_iff m g hm hg).mp heq.symm
  have hc : IsUnit (m⁻¹ * g).det := by
    rw [Matrix.det_mul]
    exact (m.isUnit_nonsing_inv_det hm).mul hg
  refine ⟨borelPointOfMatrix R (m⁻¹ * g) hc hup, ?_⟩
  apply glCoord_algHom_ext R
  let ℓ := pairLift b (borelPointOfMatrix R (m⁻¹ * g) hc hup)
  have hmap : ∀ M N : Matrix (Fin n) (Fin n) (BorelPairRing R n),
      (M * N).map ℓ = M.map ℓ * N.map ℓ := fun M N => Matrix.map_mul (f := ℓ.toRingHom)
  have hl : ((borelMatrix R n).map (pairInl R n)).map ℓ = (borelMatrix R n).map b := by
    rw [Matrix.map_map, ← AlgHom.coe_comp, pairLift_comp_pairInl]
  have hr : ((borelMatrix R n).map (pairInr R n)).map ℓ = m⁻¹ * g := by
    rw [Matrix.map_map, ← AlgHom.coe_comp, pairLift_comp_pairInr,
      borelMatrix_map_borelPointOfMatrix]
  have hp : (permMatrix (A := BorelPairRing R n) n w).map ℓ = permMatrix n w :=
    permMatrix_map (v := w) ℓ
  rw [pointMatrix_comp, schubertOrbitComorphism, pointMatrix_glPointOfMatrix, schubertOrbitMatrix,
    hmap, hmap, hl, hr, hp]
  exact (Matrix.mul_nonsing_inv_cancel_left m g hm).symm

/-- **Functions in the orbit ideal vanish over the orbit of `ẇE•`**: if `T` is affine and
`g : T ⟶ GLₙ`, `b : T ⟶ B` satisfy `g · E• = b · ẇE•`, then every `x ∈ schubertOrbitIdeal w`
vanishes along `g`. -/
theorem appTop_glCoordToGlobal_eq_zero {T : Scheme.{u}} [IsAffine T] (w : Equiv.Perm (Fin n))
    (g : T ⟶ GLScheme R n) (b : T ⟶ BorelScheme R n)
    (h : g ≫ FlagScheme.orbitMap R n = b ≫ schubertOrbitMap R n w) {x : GLCoord R n}
    (hx : x ∈ schubertOrbitIdeal R n w) : g.appTop (glCoordToGlobal R n x) = 0 := by
  let e := T.isoSpec
  let p : Spec (CommRingCat.of Γ(T, ⊤)) ⟶ Spec (CommRingCat.of (GLCoord R n)) :=
    e.inv ≫ g ≫ (TauCeti.GeneralLinear.groupSchemeSpecIso R n).hom
  let q : Spec (CommRingCat.of Γ(T, ⊤)) ⟶ Spec (CommRingCat.of (BorelCoord R n)) := e.inv ≫ b
  have h1 : g ≫ (GLOver R n).hom = b ≫ BorelScheme.toSpec R n := by
    rw [← FlagScheme.orbitMap_toSpec, reassoc_of% h, schubertOrbitMap_toSpec]
  have hpq : p ≫ Spec.map (CommRingCat.ofHom (algebraMap R (GLCoord R n))) =
      q ≫ Spec.map (CommRingCat.ofHom (algebraMap R (BorelCoord R n))) := by
    have h2 := congrArg (fun f => e.inv ≫ f) h1
    simp only [TauCeti.GeneralLinear.groupScheme_X_hom] at h2
    simpa only [p, q, Category.assoc] using h2
  let _ : Algebra R Γ(T, ⊤) := affinePointPairAlgebra R p q hpq
  let k := affinePointPairLeftHom R p q hpq
  let kb := affinePointPairRightHom R p q hpq
  have hk : GLScheme.point R n k = e.inv ≫ g := by
    change Spec.map (CommRingCat.ofHom k.toRingHom) ≫
      (TauCeti.GeneralLinear.groupSchemeSpecIso R n).inv = _
    rw [affinePointPairLeftHom_spec]
    simp [p]
  have hb : Spec.map (CommRingCat.ofHom kb.toRingHom) = e.inv ≫ b :=
    affinePointPairRightHom_spec R p q hpq
  have hcond : GLScheme.point R n k ≫ FlagScheme.orbitMap R n =
      Spec.map (CommRingCat.ofHom kb.toRingHom) ≫ schubertOrbitMap R n w := by
    rw [hk, hb, Category.assoc, h, Category.assoc]
  obtain ⟨b', hb'⟩ := exists_eq_comp_schubertOrbitComorphism w k kb hcond
  have hkx : k x = 0 := by
    rw [hb', AlgHom.comp_apply]
    rw [schubertOrbitIdeal, RingHom.mem_ker] at hx
    change pairLift kb b' ((schubertOrbitComorphism R n w).toRingHom x) = 0
    rw [hx, map_zero]
  have h0 := point_appTop_glCoordToGlobal k x
  rw [hkx, map_zero, hk, Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at h0
  exact (asIso (e.inv.app ⊤)).commRingCatIsoToRingEquiv.injective (h0.trans (map_zero _).symm)

/-! ### The preimage of `X_w` -/

variable (R n)

set_option backward.isDefEq.respectTransparency false in
/-- **The closure of `B ẇ B` is contained in `π⁻¹(X_w)`** (when `𝒪(B)` is flat over `R`). -/
theorem schubertOrbitIdeal_le_preimageIdeal [Module.Flat R (BorelCoord R n)]
    (w : Equiv.Perm (Fin n)) :
    schubertOrbitIdeal R n w ≤ preimageIdeal R n (schubertVariety R n w) := by
  intro x hx
  have := isAffine_glScheme R n
  have := isAffineHom_orbitMap R n
  have := isAffineHom_schubertOrbitMap R n w
  let φ := schubertOrbitMap R n w
  let π := FlagScheme.orbitMap R n
  have : IsAffineHom (pullback.snd π φ.imageι) := MorphismProperty.pullback_snd _ _ inferInstance
  let ψ := pullback.fst (pullback.snd π φ.imageι) φ.toImage ≫ pullback.fst π φ.imageι
  let β := pullback.snd (pullback.snd π φ.imageι) φ.toImage
  have hψ : ψ ≫ π = β ≫ φ := by
    simp only [ψ, β, Category.assoc]
    rw [pullback.condition, ← Category.assoc, pullback.condition, Category.assoc,
      Scheme.Hom.toImage_imageι]
  have h0 := appTop_glCoordToGlobal_eq_zero w ψ β hψ hx
  rw [preimageIdeal, Ideal.mem_comap]
  change glCoordToGlobal R n x ∈ (φ.ker.comap π).ideal ⟨⊤, isAffineOpen_top _⟩
  rw [comap_ker_eq_ker, Scheme.Hom.ker_apply, RingHom.mem_ker]
  exact h0

/-- **`π⁻¹(X_w)` is the closure of `B ẇ B`**: the ideal of the scheme-theoretic preimage of the
Schubert variety `X_w` in `GLₙ` is the orbit ideal of `w` (when `𝒪(B)` is flat over `R`). -/
theorem preimageIdeal_schubertVariety [Module.Flat R (BorelCoord R n)] (w : Equiv.Perm (Fin n)) :
    preimageIdeal R n (schubertVariety R n w) = schubertOrbitIdeal R n w :=
  le_antisymm (preimageIdeal_schubertVariety_le w) (schubertOrbitIdeal_le_preimageIdeal R n w)

/-- **`π⁻¹(X_w)` is the closure of `B ẇ B`, over a field.** -/
theorem preimageIdeal_schubertVariety_eq_schubertOrbitIdeal (K : Type u) [Field K] (n : ℕ) :
    ∀ w, preimageIdeal K n (schubertVariety K n w) = schubertOrbitIdeal K n w :=
  preimageIdeal_schubertVariety K n

end FlagVarieties
