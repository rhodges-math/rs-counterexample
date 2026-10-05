import Schubert.FlagVarieties.Schubert.PreimageLattice
import Schubert.FlagVarieties.Schubert.Orbit
import Schubert.FlagVarieties.LineBundle.BorelFlat

/-!
# The action of `B` on `B`-stable closed subschemes of `Flₙ`

* `FlagVarieties.borelFlagAction R n : B ×_R Flₙ ⟶ Flₙ`, `(b, V•) ↦ b · V•` (the restriction of
  `FlagScheme.action` along `B ⊆ GLₙ`), with `FlagVarieties.borelFlagProj` the projection to `Flₙ`;
  on points: `FlagVarieties.point_borelFlagAction`.
* `FlagVarieties.IsBorelStableSubscheme I`: the closed subscheme `X` (ideal sheaf `I`) is
  `B`-stable, `a⁻¹(X) ⊇ pr₂⁻¹(X)` as closed subschemes of `B ×_R Flₙ`.
* **`FlagVarieties.borelSubschemeAction I hI : B ×_R X ⟶ X`**, the action on a `B`-stable `X`, with
  `FlagVarieties.borelSubschemeAction_ι` (it is the action of `Flₙ` restricted to `B ×_R X`) and
  the projection `FlagVarieties.borelSubschemeProj I : B ×_R X ⟶ X`.
* Stability: `isBorelStableSubscheme_top`, `_inf`, `_schubertVariety`, `_schubertUnion`,
  `_schubertBoundary` (every commutative ring `R`).
-/

noncomputable section

namespace FlagVarieties

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Foundations Foundations.QuotientCharts
open scoped TensorProduct

universe u

variable (R : Type u) [CommRing R] (n : ℕ)

/-! ### The action of `B` on `Flₙ` -/

instance flat_borelSchemeToSpec : Flat (BorelScheme.toSpec R n) := by
  rw [BorelScheme.toSpec, Flat.SpecMap_iff, CommRingCat.hom_ofHom, RingHom.flat_algebraMap_iff]
  infer_instance

/-- `B ×_R Flₙ`. -/
abbrev BorelFlagProd : Scheme.{u} :=
  pullback (BorelScheme.toSpec R n) (FlagScheme.toSpec R n)

/-- **The action `B ×_R Flₙ ⟶ Flₙ`**, `(b, V•) ↦ b · V•`. -/
def borelFlagAction : BorelFlagProd R n ⟶ FlagScheme R n :=
  pullback.map _ _ _ _ (borelInclusion R n) (𝟙 _) (𝟙 _)
    (by rw [Category.comp_id, borelInclusion_toSpec]) (by simp) ≫
    FlagScheme.action R n

/-- The projection `B ×_R Flₙ ⟶ Flₙ`. -/
abbrev borelFlagProj : BorelFlagProd R n ⟶ FlagScheme R n :=
  pullback.snd _ _

set_option backward.isDefEq.respectTransparency false in
instance flat_borelFlagProj : Flat (borelFlagProj R n) :=
  MorphismProperty.pullback_snd _ _ inferInstance

variable {R n} in
/-- On points, `(b, V•) ↦ b · V•`. -/
theorem point_borelFlagAction {A : Type u} [CommRing A] [Algebra R A]
    (k : BorelCoord R n →ₐ[R] A) (P : CoordinateFlag A n)
    (h : Spec.map (CommRingCat.ofHom k.toRingHom) ≫ BorelScheme.toSpec R n =
      FlagScheme.ofRingFlag R P ≫ FlagScheme.toSpec R n) :
    pullback.lift (Spec.map (CommRingCat.ofHom k.toRingHom)) (FlagScheme.ofRingFlag R P) h ≫
        borelFlagAction R n =
      FlagScheme.ofRingFlag R (P.transport
        (GLScheme.pointEquiv R n (k.comp (Ideal.Quotient.mkₐ R (borelCoordIdeal R n))))) := by
  rw [← FlagScheme.action_point, borelFlagAction, ← Category.assoc]
  congr 1
  apply pullback.hom_ext
  · simp only [pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
    exact point_borelInclusion k
  · simp [pullback.map]

/-! ### `B`-stable closed subschemes -/

/-- **The closed subscheme `X` of `Flₙ` (ideal sheaf `I`) is `B`-stable**: in `B ×_R Flₙ`, the
preimage `a⁻¹(X)` under the action contains `pr₂⁻¹(X) = B ×_R X`. -/
def IsBorelStableSubscheme (I : (FlagScheme R n).IdealSheafData) : Prop :=
  I.comap (borelFlagAction R n) ≤ I.comap (borelFlagProj R n)

variable {R n}

/-- `B ×_R X`. -/
abbrev BorelSubschemeProd (I : (FlagScheme R n).IdealSheafData) : Scheme.{u} :=
  pullback (BorelScheme.toSpec R n) (I.subschemeι ≫ FlagScheme.toSpec R n)

/-- `B ×_R X ⟶ B ×_R Flₙ`. -/
def borelSubschemeProdMap (I : (FlagScheme R n).IdealSheafData) :
    BorelSubschemeProd I ⟶ BorelFlagProd R n :=
  pullback.map _ _ _ _ (𝟙 _) I.subschemeι (𝟙 _) (by simp) (by simp)

/-- The projection `B ×_R X ⟶ X`. -/
abbrev borelSubschemeProj (I : (FlagScheme R n).IdealSheafData) :
    BorelSubschemeProd I ⟶ I.subscheme :=
  pullback.snd _ _

theorem borelSubschemeProdMap_proj (I : (FlagScheme R n).IdealSheafData) :
    borelSubschemeProdMap I ≫ borelFlagProj R n = borelSubschemeProj I ≫ I.subschemeι := by
  simp [borelSubschemeProdMap, pullback.map]

/-- `B ×_R X` is the closed subscheme `pr₂⁻¹(X)` of `B ×_R Flₙ`. -/
theorem ker_borelSubschemeProdMap (I : (FlagScheme R n).IdealSheafData) :
    (borelSubschemeProdMap I).ker = I.comap (borelFlagProj R n) := by
  have e : borelSubschemeProdMap I = (pullbackLeftPullbackSndIso (BorelScheme.toSpec R n)
      (FlagScheme.toSpec R n) I.subschemeι).inv ≫ pullback.fst _ _ := by
    apply pullback.hom_ext <;> simp [borelSubschemeProdMap, pullback.map]
  rw [e, Scheme.Hom.ker_comp_of_isIso,
    Scheme.IdealSheafData.ker_fst_of_isClosedImmersion, Scheme.IdealSheafData.ker_subschemeι]

theorem le_ker_borelSubschemeProdMap_comp {I : (FlagScheme R n).IdealSheafData}
    (hI : IsBorelStableSubscheme R n I) :
    I.subschemeι.ker ≤ (borelSubschemeProdMap I ≫ borelFlagAction R n).ker := by
  rw [Scheme.IdealSheafData.ker_subschemeι, ← Scheme.IdealSheafData.map_ker,
    ker_borelSubschemeProdMap, Scheme.IdealSheafData.le_map_iff_comap_le]
  exact hI

/-- **The action `B ×_R X ⟶ X` on a `B`-stable closed subscheme `X ⊆ Flₙ`.** -/
def borelSubschemeAction (I : (FlagScheme R n).IdealSheafData) (hI : IsBorelStableSubscheme R n I) :
    BorelSubschemeProd I ⟶ I.subscheme :=
  IsClosedImmersion.lift I.subschemeι (borelSubschemeProdMap I ≫ borelFlagAction R n)
    (le_ker_borelSubschemeProdMap_comp hI)

@[reassoc (attr := simp)]
theorem borelSubschemeAction_ι (I : (FlagScheme R n).IdealSheafData)
    (hI : IsBorelStableSubscheme R n I) :
    borelSubschemeAction I hI ≫ I.subschemeι = borelSubschemeProdMap I ≫ borelFlagAction R n :=
  IsClosedImmersion.lift_fac _ _ _

/-! ### Unions -/

variable (R n) in
theorem isBorelStableSubscheme_top : IsBorelStableSubscheme R n ⊤ := by
  simp only [IsBorelStableSubscheme, Scheme.IdealSheafData.comap_top, le_refl]

theorem IsBorelStableSubscheme.inf {I J : (FlagScheme R n).IdealSheafData}
    (hI : IsBorelStableSubscheme R n I) (hJ : IsBorelStableSubscheme R n J) :
    IsBorelStableSubscheme R n (I ⊓ J) := by
  refine (le_inf (Scheme.IdealSheafData.comap_mono _ inf_le_left)
    (Scheme.IdealSheafData.comap_mono _ inf_le_right)).trans ((inf_le_inf hI hJ).trans ?_)
  rw [comap_inf_of_flat]

/-! ### Schubert varieties -/

variable (R n)

/-- The multiplication of `B`, `𝒪(B) → 𝒪(B) ⊗ 𝒪(B)`, `b ↦ b₁ b₂`. -/
def pairComul : BorelCoord R n →ₐ[R] BorelPairRing R n :=
  borelPointOfMatrix R ((borelMatrix R n).map (pairInl R n) * (borelMatrix R n).map (pairInr R n))
    (by
      rw [Matrix.det_mul]
      exact (isUnit_det_map_algHom _ (isUnit_det_borelMatrix R n)).mul
        (isUnit_det_map_algHom _ (isUnit_det_borelMatrix R n)))
    ((borelMatrix_map_blockTriangular _).mul (borelMatrix_map_blockTriangular _))

/-- `Spec (𝒪(B) ⊗ 𝒪(B)) ≅ B ×_R B`. -/
def borelPairSpecIso :
    Spec (CommRingCat.of (BorelPairRing R n)) ≅
      pullback (BorelScheme.toSpec R n) (BorelScheme.toSpec R n) :=
  (pullbackSpecIso R (BorelCoord R n) (BorelCoord R n)).symm

@[reassoc (attr := simp)]
theorem borelPairSpecIso_hom_fst :
    (borelPairSpecIso R n).hom ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (pairInl R n).toRingHom) :=
  pullbackSpecIso_inv_fst R (BorelCoord R n) (BorelCoord R n)

@[reassoc (attr := simp)]
theorem borelPairSpecIso_hom_snd :
    (borelPairSpecIso R n).hom ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (pairInr R n).toRingHom) :=
  pullbackSpecIso_inv_snd R (BorelCoord R n) (BorelCoord R n)

@[reassoc]
theorem borelPairSpecIso_inv_pairInl :
    (borelPairSpecIso R n).inv ≫ Spec.map (CommRingCat.ofHom (pairInl R n).toRingHom) =
      pullback.fst _ _ := by
  rw [← borelPairSpecIso_hom_fst, Iso.inv_hom_id_assoc]

@[reassoc]
theorem borelPairSpecIso_inv_pairInr :
    (borelPairSpecIso R n).inv ≫ Spec.map (CommRingCat.ofHom (pairInr R n).toRingHom) =
      pullback.snd _ _ := by
  rw [← borelPairSpecIso_hom_snd, Iso.inv_hom_id_assoc]

/-- The multiplication `B ×_R B ⟶ B`. -/
def borelMul : pullback (BorelScheme.toSpec R n) (BorelScheme.toSpec R n) ⟶ BorelScheme R n :=
  (borelPairSpecIso R n).inv ≫ Spec.map (CommRingCat.ofHom (pairComul R n).toRingHom)

variable {R n}

/-- **`b · (b' ẇE•) = (b b') ẇE•`**, on the base change of the orbit map along `B ×_R Flₙ ⟶ Flₙ`. -/
theorem fst_borelFlagAction_eq (w : Equiv.Perm (Fin n)) :
    pullback.fst (borelFlagProj R n) (schubertOrbitMap R n w) ≫ borelFlagAction R n =
      pullback.lift (pullback.fst (borelFlagProj R n) (schubertOrbitMap R n w) ≫ pullback.fst _ _)
        (pullback.snd (borelFlagProj R n) (schubertOrbitMap R n w))
        (by rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition,
          Category.assoc, schubertOrbitMap_toSpec]) ≫
        borelMul R n ≫ schubertOrbitMap R n w := by
  set p := borelFlagProj R n
  set o := schubertOrbitMap R n w
  set sL := Spec.map (CommRingCat.ofHom (pairInl R n).toRingHom) with hsL
  set sR := Spec.map (CommRingCat.ofHom (pairInr R n).toRingHom) with hsR
  have hoR : sR ≫ o = _ := schubertOrbitMap_point w (pairInr R n)
  have hLR : sL ≫ BorelScheme.toSpec R n = sR ≫ BorelScheme.toSpec R n := by
    rw [hsL, hsR, ← borelPairSpecIso_hom_fst, ← borelPairSpecIso_hom_snd, Category.assoc,
      Category.assoc, pullback.condition]
  have h1 : sL ≫ BorelScheme.toSpec R n = (sR ≫ o) ≫ FlagScheme.toSpec R n := by
    rw [Category.assoc, schubertOrbitMap_toSpec, hLR]
  let x : Spec (CommRingCat.of (BorelPairRing R n)) ⟶ BorelFlagProd R n := pullback.lift _ _ h1
  have hx1 : x ≫ pullback.fst _ _ = sL := pullback.lift_fst _ _ _
  have h2 : x ≫ p = sR ≫ o := pullback.lift_snd _ _ _
  let ψ : Spec (CommRingCat.of (BorelPairRing R n)) ⟶ pullback p o := pullback.lift x _ h2
  have hψ1 : ψ ≫ pullback.fst p o = x := pullback.lift_fst _ _ _
  have hψ2 : ψ ≫ pullback.snd p o = sR := pullback.lift_snd _ _ _
  let b := pullback.fst p o ≫ pullback.fst (BorelScheme.toSpec R n) (FlagScheme.toSpec R n)
  let b' := pullback.snd p o
  have hb : b ≫ BorelScheme.toSpec R n = b' ≫ BorelScheme.toSpec R n := by
    simp only [b, b', Category.assoc, pullback.condition, p]
    rw [← Category.assoc, pullback.condition, Category.assoc, schubertOrbitMap_toSpec]
  have hψ : ψ ≫ pullback.lift b b' hb = (borelPairSpecIso R n).hom := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, borelPairSpecIso_hom_fst, ← Category.assoc, hψ1, hx1]
    · rw [Category.assoc, pullback.lift_snd, borelPairSpecIso_hom_snd, hψ2]
  let ψinv : pullback p o ⟶ Spec (CommRingCat.of (BorelPairRing R n)) :=
    pullback.lift b b' hb ≫ (borelPairSpecIso R n).inv
  have hiso : IsIso ψ := by
    refine ⟨⟨ψinv, ?_, ?_⟩⟩
    · rw [← Category.assoc, hψ, Iso.hom_inv_id]
    · have hinvL : ψinv ≫ sL = b := by
        rw [Category.assoc, borelPairSpecIso_inv_pairInl, pullback.lift_fst]
      have hinvR : ψinv ≫ sR = b' := by
        rw [Category.assoc, borelPairSpecIso_inv_pairInr, pullback.lift_snd]
      apply pullback.hom_ext
      · apply pullback.hom_ext
        · rw [Category.id_comp, Category.assoc, Category.assoc, ← Category.assoc ψ, hψ1, hx1,
            hinvL]
        · rw [Category.id_comp, Category.assoc, Category.assoc, ← Category.assoc ψ, hψ1,
            pullback.lift_snd, ← Category.assoc, hinvR]
          exact pullback.condition.symm
      · rw [Category.id_comp, Category.assoc, hψ2, hinvR]
  rw [← cancel_epi ψ]
  -- the left side on points
  have hlhs : ψ ≫ pullback.fst p o ≫ borelFlagAction R n =
      FlagScheme.ofRingFlag R ((matrixFlag ((borelMatrix R n).map (pairInr R n) * permMatrix n w)
        (isUnit_det_borelMatrix_map_mul_permMatrix R n w (pairInr R n))).transport
        (GLScheme.pointEquiv R n
          ((pairInl R n).comp (Ideal.Quotient.mkₐ R (borelCoordIdeal R n))))) := by
    have hx : x = pullback.lift sL
        (FlagScheme.ofRingFlag R (matrixFlag ((borelMatrix R n).map (pairInr R n) *
          permMatrix n w) (isUnit_det_borelMatrix_map_mul_permMatrix R n w (pairInr R n))))
        (by rw [h1, hoR]) := by
      apply pullback.hom_ext
      · rw [hx1, pullback.lift_fst]
      · rw [pullback.lift_snd, pullback.lift_snd]
        exact hoR
    rw [← Category.assoc, hψ1, hx]
    exact point_borelFlagAction (pairInl R n) _ _
  -- the right side on points
  have hrhs : ψ ≫ pullback.lift b b' hb ≫ borelMul R n ≫ schubertOrbitMap R n w =
      FlagScheme.ofRingFlag R (matrixFlag ((borelMatrix R n).map (pairComul R n) *
        permMatrix n w) (isUnit_det_borelMatrix_map_mul_permMatrix R n w (pairComul R n))) := by
    rw [← Category.assoc, hψ, borelMul, Category.assoc, Iso.hom_inv_id_assoc]
    exact schubertOrbitMap_point w (pairComul R n)
  rw [hlhs, hrhs]
  congr 1
  rw [matrixFlag_transport _ _ _ (by
      rw [Matrix.det_mul]
      exact ((Matrix.isUnit_iff_isUnit_det _).mp (generalLinearMatrixAt_isUnit R _ n _)).mul
        (isUnit_det_borelMatrix_map_mul_permMatrix R n w (pairInr R n)))
    _ rfl]
  apply matrixFlag_congr'
  rw [pairComul, borelMatrix_map_borelPointOfMatrix, Matrix.mul_assoc]
  rfl

/-- **Schubert varieties are `B`-stable.** -/
theorem isBorelStableSubscheme_schubertVariety (w : Equiv.Perm (Fin n)) :
    IsBorelStableSubscheme R n (schubertVariety R n w) := by
  have := isAffineHom_schubertOrbitMap R n w
  rw [IsBorelStableSubscheme, schubertVariety, comap_ker_eq_ker_fst (borelFlagProj R n),
    ← Scheme.IdealSheafData.le_map_iff_comap_le, Scheme.IdealSheafData.map_ker,
    fst_borelFlagAction_eq, ← Category.assoc]
  exact Scheme.Hom.le_ker_comp _ _

/-- **Schubert unions are `B`-stable.** -/
theorem isBorelStableSubscheme_schubertUnion (S : Finset (Equiv.Perm (Fin n))) :
    IsBorelStableSubscheme R n (schubertUnion R n S) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have h : schubertUnion R n ∅ = ⊤ := by simp [schubertUnion]
    rw [h]
    exact isBorelStableSubscheme_top R n
  | insert w S _ ih =>
    rw [schubertUnion, Finset.iInf_insert]
    exact (isBorelStableSubscheme_schubertVariety w).inf ih

/-- **Schubert boundaries are `B`-stable.** -/
theorem isBorelStableSubscheme_schubertBoundary (σ : Equiv.Perm (Fin n)) :
    IsBorelStableSubscheme R n (schubertBoundary R n σ) :=
  isBorelStableSubscheme_schubertUnion _

end FlagVarieties
