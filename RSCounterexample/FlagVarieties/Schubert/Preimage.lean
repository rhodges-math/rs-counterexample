import RSCounterexample.FlagVarieties.Schubert.Basic
import RSCounterexample.FlagVarieties.Charts.Trivialization
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# Preimages in `GLₙ` and orbit ideals

* `FlagVarieties.preimageIdeal R n I`: for a closed subscheme `X ⊆ Flₙ` with ideal sheaf `I`, the
  ideal of `𝒪(GLₙ)` of the scheme-theoretic preimage `π⁻¹(X) = X ×_{Flₙ} GLₙ ⊆ GLₙ` under the orbit
  map `π(g) = g · E•`.
* `FlagVarieties.permMatrix w`: the permutation matrix `ẇ`, `ẇ eᵢ = e_{w(i)}`.
* `FlagVarieties.schubertOrbitComorphism R n w : 𝒪(GLₙ) → 𝒪(B) ⊗ 𝒪(B)`, the comorphism of
  `B × B → GLₙ`, `(b, b') ↦ b ẇ b'`, and its kernel `schubertOrbitIdeal R n w`, the ideal of the
  closure of the double coset `B ẇ B`.
* `FlagVarieties.preimageIdeal_schubertVariety_le`: `π⁻¹(X_w) ⊆ closure(B ẇ B)`.
-/

noncomputable section

namespace FlagVarieties

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Foundations Foundations.QuotientCharts
open scoped TensorProduct

universe u

variable (R : Type u) [CommRing R] (n : ℕ)

/-- The identification of `𝒪(GLₙ)` with the global functions on `GLₙ`. -/
def glCoordToGlobal : GLCoord R n →+* Γ(GLScheme R n, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of (GLCoord R n))).inv ≫
    (TauCeti.GeneralLinear.groupSchemeSpecIso R n).hom.appTop).hom

/-- **The ideal of `π⁻¹(X) ⊆ GLₙ`**, for a closed subscheme `X ⊆ Flₙ` with ideal sheaf `I`: the
ideal of `𝒪(GLₙ)` of the scheme-theoretic preimage `X ×_{Flₙ} GLₙ` under the orbit map. -/
def preimageIdeal (I : (FlagScheme R n).IdealSheafData) : Ideal (GLCoord R n) :=
  ((I.comap (FlagScheme.orbitMap R n)).ideal ⟨⊤, isAffineOpen_top _⟩).comap (glCoordToGlobal R n)

/-- The permutation matrix `ẇ` of `w`: `ẇ eᵢ = e_{w(i)}`. -/
def permMatrix {A : Type*} [CommRing A] (w : Equiv.Perm (Fin n)) : Matrix (Fin n) (Fin n) A :=
  (w.symm.toPEquiv.toMatrix : Matrix (Fin n) (Fin n) A)

theorem permMatrix_apply {A : Type*} [CommRing A] (w : Equiv.Perm (Fin n)) (r c : Fin n) :
    permMatrix (A := A) n w r c = if r = w c then 1 else 0 := by
  have e : c = w.symm r ↔ r = w c := by rw [Equiv.eq_symm_apply, eq_comm]
  simp only [permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def,
    Option.some.injEq]
  split_ifs with h1 h2 h2 <;> first | rfl | exact absurd (e.mp h1.symm) h2 |
    exact absurd (e.mpr h2).symm h1

theorem isUnit_det_permMatrix {A : Type*} [CommRing A] (w : Equiv.Perm (Fin n)) :
    IsUnit (permMatrix (A := A) n w).det := by
  rw [permMatrix, Matrix.det_permutation]
  exact (Equiv.Perm.sign w.symm).isUnit.map (Int.castRingHom A)

/-! ### The coordinate ring of `B × B` -/

/-- `𝒪(B) ⊗_R 𝒪(B)`, the coordinate ring of `B × B`. -/
def BorelPairRing : Type u :=
  BorelCoord R n ⊗[R] BorelCoord R n

instance : CommRing (BorelPairRing R n) :=
  inferInstanceAs (CommRing (BorelCoord R n ⊗[R] BorelCoord R n))

instance : Algebra R (BorelPairRing R n) :=
  inferInstanceAs (Algebra R (BorelCoord R n ⊗[R] BorelCoord R n))

/-- The first factor `𝒪(B) → 𝒪(B) ⊗ 𝒪(B)`. -/
def pairInl : BorelCoord R n →ₐ[R] BorelPairRing R n :=
  Algebra.TensorProduct.includeLeft

/-- The second factor `𝒪(B) → 𝒪(B) ⊗ 𝒪(B)`. -/
def pairInr : BorelCoord R n →ₐ[R] BorelPairRing R n :=
  Algebra.TensorProduct.includeRight

variable {R n} in
/-- The map out of `𝒪(B) ⊗ 𝒪(B)` given on the two factors. -/
def pairLift {A : Type u} [CommRing A] [Algebra R A] (α β : BorelCoord R n →ₐ[R] A) :
    BorelPairRing R n →ₐ[R] A :=
  Algebra.TensorProduct.lift α β fun _ _ => Commute.all _ _

variable {R n} in
theorem pairLift_comp_pairInl {A : Type u} [CommRing A] [Algebra R A]
    (α β : BorelCoord R n →ₐ[R] A) : (pairLift α β).comp (pairInl R n) = α :=
  Algebra.TensorProduct.lift_comp_includeLeft _ _ fun _ _ => Commute.all _ _

variable {R n} in
theorem pairLift_comp_pairInr {A : Type u} [CommRing A] [Algebra R A]
    (α β : BorelCoord R n →ₐ[R] A) : (pairLift α β).comp (pairInr R n) = β :=
  Algebra.TensorProduct.lift_comp_includeRight _ _ fun _ _ => Commute.all _ _

variable {R n} in
theorem pair_algHom_ext {A : Type u} [CommRing A] [Algebra R A] {f g : BorelPairRing R n →ₐ[R] A}
    (h₁ : f.comp (pairInl R n) = g.comp (pairInl R n))
    (h₂ : f.comp (pairInr R n) = g.comp (pairInr R n)) : f = g :=
  Algebra.TensorProduct.ext h₁ h₂

/-! ### The orbit comorphism -/

/-- The matrix `b ẇ b'` over `𝒪(B) ⊗ 𝒪(B)`, with `b`, `b'` the two generic upper triangular
matrices. -/
def schubertOrbitMatrix (w : Equiv.Perm (Fin n)) : Matrix (Fin n) (Fin n) (BorelPairRing R n) :=
  (borelMatrix R n).map (pairInl R n) * permMatrix n w * (borelMatrix R n).map (pairInr R n)

theorem isUnit_det_borelMatrix_map_mul_permMatrix {A : Type u} [CommRing A] [Algebra R A]
    (w : Equiv.Perm (Fin n)) (k : BorelCoord R n →ₐ[R] A) :
    IsUnit ((borelMatrix R n).map k * permMatrix n w).det := by
  rw [Matrix.det_mul]
  exact (isUnit_det_map_algHom k (isUnit_det_borelMatrix R n)).mul (isUnit_det_permMatrix n w)

theorem isUnit_det_schubertOrbitMatrix (w : Equiv.Perm (Fin n)) :
    IsUnit (schubertOrbitMatrix R n w).det := by
  rw [schubertOrbitMatrix, Matrix.det_mul]
  exact (isUnit_det_borelMatrix_map_mul_permMatrix R n w _).mul
    (isUnit_det_map_algHom _ (isUnit_det_borelMatrix R n))

/-- The comorphism `𝒪(GLₙ) → 𝒪(B) ⊗ 𝒪(B)` of the map `B × B → GLₙ`, `(b, b') ↦ b ẇ b'`. -/
def schubertOrbitComorphism (w : Equiv.Perm (Fin n)) : GLCoord R n →ₐ[R] BorelPairRing R n :=
  glPointOfMatrix R (schubertOrbitMatrix R n w) (isUnit_det_schubertOrbitMatrix R n w)

/-- **The orbit ideal of `w`**: the functions on `GLₙ` vanishing on the double coset `B ẇ B`, i.e.
the kernel of `f ↦ ((b, b') ↦ f(b ẇ b'))`. -/
def schubertOrbitIdeal (w : Equiv.Perm (Fin n)) : Ideal (GLCoord R n) :=
  RingHom.ker (schubertOrbitComorphism R n w).toRingHom

/-! ### Points of Schubert orbit maps -/

variable {R n}

theorem standardRingFlag_eq_matrixFlag {A : Type u} [CommRing A] :
    FlagScheme.standardRingFlag n A = matrixFlag (1 : Matrix (Fin n) (Fin n) A) (by simp) := by
  apply RingFlag.ext
  intro j
  rw [matrixFlag_step, Matrix.toLin'_one, Submodule.map_id, standardRingFlag_step_eq_stdSpan]

theorem permRingFlag_eq_matrixFlag (w : Equiv.Perm (Fin n)) (A : Type u) [CommRing A] :
    permRingFlag n w A = matrixFlag (permMatrix (A := A) n w) (isUnit_det_permMatrix n w) := by
  apply RingFlag.ext
  intro j
  rw [permRingFlag_step, matrixFlag_step, stdSpan, Submodule.map_span, Set.image_image]
  congr 1
  apply Set.image_congr
  intro i _
  funext r
  simp [permMatrix_apply, Matrix.toLin'_apply, Pi.basisFun_apply, Pi.single_apply]

theorem matrixFlag_transport {A : Type u} [CommRing A] (g h : Matrix (Fin n) (Fin n) A)
    (hg : IsUnit g.det) (hgh : IsUnit (h * g).det) (e : (Fin n → A) ≃ₗ[A] _)
    (he : ⇑e = Matrix.toLin' h) :
    (matrixFlag g hg).transport e = matrixFlag (h * g) hgh := by
  apply RingFlag.ext
  intro j
  rw [RingFlag.transport_step, matrixFlag_step, matrixFlag_step, Matrix.toLin'_mul,
    Submodule.map_comp]
  congr 1
  exact LinearMap.ext fun x => congrFun he x

theorem point_borelInclusion {A : Type u} [CommRing A] [Algebra R A]
    (k : BorelCoord R n →ₐ[R] A) :
    Spec.map (CommRingCat.ofHom k.toRingHom) ≫ borelInclusion R n =
      GLScheme.point R n (k.comp (Ideal.Quotient.mkₐ R (borelCoordIdeal R n))) := by
  rw [borelInclusion, ← Category.assoc, ← Spec.map_comp]
  rfl

/-- On points, `b ↦ b · ẇE•` is the flag of `b ẇ`. -/
theorem schubertOrbitMap_point {A : Type u} [CommRing A] [Algebra R A] (w : Equiv.Perm (Fin n))
    (k : BorelCoord R n →ₐ[R] A) :
    Spec.map (CommRingCat.ofHom k.toRingHom) ≫ schubertOrbitMap R n w =
      FlagScheme.ofRingFlag R (matrixFlag ((borelMatrix R n).map k * permMatrix n w)
        (isUnit_det_borelMatrix_map_mul_permMatrix R n w k)) := by
  rw [schubertOrbitMap, ← Category.assoc, point_borelInclusion]
  refine (FlagScheme.orbitMapAt_point (permRingFlag n w R) (permFlag_toSpec R n w) _).trans ?_
  congr 1
  rw [permRingFlag_baseChange, permRingFlag_eq_matrixFlag]
  apply matrixFlag_transport
  rfl

/-- `π(b ẇ b') = b · ẇE•`: the orbit comorphism lands over the Schubert orbit map. -/
theorem point_schubertOrbitComorphism_orbitMap (w : Equiv.Perm (Fin n)) :
    GLScheme.point R n (schubertOrbitComorphism R n w) ≫ FlagScheme.orbitMap R n =
      Spec.map (CommRingCat.ofHom (pairInl R n).toRingHom) ≫ schubertOrbitMap R n w := by
  rw [schubertOrbitMap_point, FlagScheme.orbitMap_point]
  have e1 : (FlagScheme.standardRingFlag n _).transport
      (GLScheme.pointEquiv R n (schubertOrbitComorphism R n w)) =
      matrixFlag (GLScheme.pointMatrix R n (schubertOrbitComorphism R n w))
        ((Matrix.isUnit_iff_isUnit_det _).mp (generalLinearMatrixAt_isUnit R _ n _)) := rfl
  rw [e1]
  congr 1
  exact (matrixFlag_congr' (pointMatrix_glPointOfMatrix R _ _)
    (hg' := isUnit_det_schubertOrbitMatrix R n w)).trans
    (matrixFlag_mul_of_upper ((borelMatrix R n).map (pairInl R n) * permMatrix n w)
      ((borelMatrix R n).map (pairInr R n)) (isUnit_det_borelMatrix_map_mul_permMatrix R n w _)
      (isUnit_det_schubertOrbitMatrix R n w)
      (isUnit_det_map_algHom _ (isUnit_det_borelMatrix R n))
      (borelMatrix_map_blockTriangular _))

/-! ### `π⁻¹(X_w)` is contained in the closure of `B ẇ B` -/

/-- Global functions on `GLₙ`, evaluated at an `A`-point. -/
theorem point_appTop_glCoordToGlobal {A : Type u} [CommRing A] [Algebra R A]
    (k : GLCoord R n →ₐ[R] A) (x : GLCoord R n) :
    (GLScheme.point R n k).appTop (glCoordToGlobal R n x) =
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv (k x) := by
  have e : (TauCeti.GeneralLinear.groupSchemeSpecIso R n).hom.appTop ≫
      (GLScheme.point R n k).appTop = (Spec.map (CommRingCat.ofHom k.toRingHom)).appTop := by
    change (TauCeti.GeneralLinear.groupSchemeSpecIso R n).hom.appTop ≫
      (Spec.map (CommRingCat.ofHom k.toRingHom) ≫
        (TauCeti.GeneralLinear.groupSchemeSpecIso R n).inv).appTop = _
    rw [← Scheme.Hom.comp_appTop, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have h1 : (GLScheme.point R n k).appTop (glCoordToGlobal R n x) =
      (Spec.map (CommRingCat.ofHom k.toRingHom)).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of (GLCoord R n))).inv x) := by
    rw [← e]
    rfl
  rw [h1, ← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

/-- **`π⁻¹(X_w) ⊆ closure(B ẇ B)`**: the ideal of the preimage of `X_w` is contained in the orbit
ideal of `w`. -/
theorem preimageIdeal_schubertVariety_le (w : Equiv.Perm (Fin n)) :
    preimageIdeal R n (schubertVariety R n w) ≤ schubertOrbitIdeal R n w := by
  intro x hx
  let I := schubertVariety R n w
  let h := GLScheme.point R n (schubertOrbitComorphism R n w)
  let k : Spec (CommRingCat.of (BorelPairRing R n)) ⟶ I.subscheme :=
    Spec.map (CommRingCat.ofHom (pairInl R n).toRingHom) ≫ (schubertOrbitMap R n w).toImage
  have hk : h ≫ FlagScheme.orbitMap R n = k ≫ I.subschemeι := by
    rw [point_schubertOrbitComorphism_orbitMap]
    change _ = (Spec.map _ ≫ (schubertOrbitMap R n w).toImage) ≫ (schubertOrbitMap R n w).imageι
    rw [Category.assoc, Scheme.Hom.toImage_imageι]
  have hh : h = pullback.lift h k hk ≫ pullback.fst (FlagScheme.orbitMap R n) I.subschemeι :=
    (pullback.lift_fst _ _ _).symm
  -- `x` vanishes on `π⁻¹(X_w)`
  have hx' : (pullback.fst (FlagScheme.orbitMap R n) I.subschemeι).appTop
      (glCoordToGlobal R n x) = 0 := by
    have := hx
    rw [preimageIdeal, Ideal.mem_comap, Scheme.IdealSheafData.comap,
      Scheme.Hom.ker_apply] at this
    exact this
  have h0 : h.appTop (glCoordToGlobal R n x) = 0 := by
    rw [hh, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hx', map_zero]
  rw [point_appTop_glCoordToGlobal] at h0
  rw [schubertOrbitIdeal, RingHom.mem_ker]
  exact
    (Scheme.ΓSpecIso (CommRingCat.of (BorelPairRing R n))).commRingCatIsoToRingEquiv.symm.injective
    (h0.trans (map_zero _).symm)

end FlagVarieties
