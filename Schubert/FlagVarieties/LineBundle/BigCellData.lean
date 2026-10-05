import Schubert.FlagVarieties.Charts.OrbitMap
import Schubert.FlagVarieties.LineBundle.Basic
import Schubert.FlagVarieties.LineBundle.LocalIso

/-!
# The orbit map is trivial over the big cells

For a permutation `v`, the right action of `B` on `π⁻¹(bigCell v) = D(f_v)` is trivialized by
the section `s_v` of `π` over the big cell (`bigCellSection`): every `g ∈ D(f_v)` is
`g = s_v(π g) · β(g)` with `β(g) = s_v(π g)⁻¹ g ∈ B`.

* `FlagVarieties.lift_mulRight`: right multiplication on points, `(g, b) ↦ g b`;
* `FlagVarieties.bigCellLocalData R v`: the local data `(e, t) = (s_v, (s_v ∘ π, β))` of the
  `B`-scheme `GLₙ ⟶ Flₙ` over `bigCell v` (`BorelAction.LocalData`).
-/

noncomputable section

namespace FlagVarieties

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Foundations Foundations.QuotientCharts
open scoped TensorProduct

universe u

variable {R : Type u} [CommRing R] {n : ℕ}

theorem spec_map_comp_point {A B : Type u} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
    (a : A →ₐ[R] B) (k : GLCoord R n →ₐ[R] A) :
    Spec.map (CommRingCat.ofHom a.toRingHom) ≫ GLScheme.point R n k =
      GLScheme.point R n (a.comp k) := by
  change Spec.map _ ≫ Spec.map _ ≫ _ = Spec.map _ ≫ _
  rw [← Category.assoc, ← Spec.map_comp]
  rfl

theorem point_toSpec {A : Type u} [CommRing A] [Algebra R A] (k : GLCoord R n →ₐ[R] A) :
    GLScheme.point R n k ≫ (GLOver R n).hom =
      Spec.map (CommRingCat.ofHom (algebraMap R A)) :=
  generalLinearGroupPoint_toSpec R A n k

theorem spec_map_borelScheme_toSpec {A : Type u} [CommRing A] [Algebra R A]
    (b : BorelCoord R n →ₐ[R] A) :
    Spec.map (CommRingCat.ofHom b.toRingHom) ≫ BorelScheme.toSpec R n =
      Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
  rw [BorelScheme.toSpec, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact b.comp_algebraMap

theorem point_borel_condition {A : Type u} [CommRing A] [Algebra R A]
    (k : GLCoord R n →ₐ[R] A) (b : BorelCoord R n →ₐ[R] A) :
    GLScheme.point R n k ≫ (GLOver R n).hom =
      Spec.map (CommRingCat.ofHom b.toRingHom) ≫ BorelScheme.toSpec R n := by
  rw [point_toSpec, spec_map_borelScheme_toSpec]

theorem isUnit_det_pointMatrix_mul {A : Type u} [CommRing A] [Algebra R A]
    (k : GLCoord R n →ₐ[R] A) (b : BorelCoord R n →ₐ[R] A) :
    IsUnit (GLScheme.pointMatrix R n k * (borelMatrix R n).map b).det := by
  rw [Matrix.det_mul]
  exact ((Matrix.isUnit_iff_isUnit_det _).mp (generalLinearMatrixAt_isUnit R _ n _)).mul
    (isUnit_det_map_algHom b (isUnit_det_borelMatrix R n))

/-- **Right multiplication on points**: `(g, b) ↦ g b`. -/
theorem lift_mulRight {A : Type u} [CommRing A] [Algebra R A] (k : GLCoord R n →ₐ[R] A)
    (b : BorelCoord R n →ₐ[R] A) :
    pullback.lift (GLScheme.point R n k) (Spec.map (CommRingCat.ofHom b.toRingHom))
        (point_borel_condition k b) ≫ mulRight R n =
      GLScheme.point R n (glPointOfMatrix R (GLScheme.pointMatrix R n k * (borelMatrix R n).map b)
        (isUnit_det_pointMatrix_mul k b)) := by
  let ℓ : GLCoord R n ⊗[R] BorelCoord R n →ₐ[R] A :=
    Algebra.TensorProduct.lift k b fun _ _ => Commute.all _ _
  have e : pullback.lift (GLScheme.point R n k) (Spec.map (CommRingCat.ofHom b.toRingHom))
      (point_borel_condition k b) =
      Spec.map (CommRingCat.ofHom ℓ.toRingHom) ≫ (glBorelSpecIso R n).inv := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, glBorelSpecIso_inv_fst, spec_map_comp_point]
      congr 1
      exact (Algebra.TensorProduct.lift_comp_includeLeft k b fun _ _ => Commute.all _ _).symm
    · rw [pullback.lift_snd, Category.assoc, glBorelSpecIso_inv_snd, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp]
      congr 2
      exact RingHom.ext fun x => by simp [ℓ]
  rw [e, Category.assoc, mulRight, Iso.inv_hom_id_assoc, ← Category.assoc, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  change GLScheme.point R n (ℓ.comp (rightCoaction R n)) = _
  congr 1
  apply glCoord_algHom_ext R
  rw [pointMatrix_glPointOfMatrix]
  change ((genericMatrix R n).map (rightCoaction R n)).map ℓ = _
  rw [map_rightCoaction_genericMatrix]
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply, map_sum, map_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp [ℓ]
  rfl

/-! ### Local triviality data over a big cell -/

variable (R) (v : Equiv.Perm (Fin n))

theorem glBorelAction_q : (glBorelAction R n).q = FlagScheme.orbitMap R n :=
  rfl

/-- `bigCell v ≅ Spec C_v`, through the chart. -/
def bigCellIso : (bigCell R v).toScheme ≅ bigCellChartScheme R v :=
  IsOpenImmersion.isoOfRangeEq (bigCell R v).ι (bigCellChart R v)
    (by rw [Scheme.Opens.range_ι]; rfl)

@[reassoc] theorem bigCellIso_hom_chart :
    (bigCellIso R v).hom ≫ bigCellChart R v = (bigCell R v).ι :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- `π⁻¹(bigCell v) ≅ Spec 𝒪(GLₙ)[1/f_v]`. -/
def preimageIso : (FlagScheme.orbitMap R n ⁻¹ᵁ bigCell R v).toScheme ≅
    Spec (CommRingCat.of (BigCellPreimageRing R v)) :=
  IsOpenImmersion.isoOfRangeEq (Scheme.Opens.ι _) (preimageChart R v)
    (by rw [Scheme.Opens.range_ι, ← Scheme.Hom.coe_opensRange, preimageChart_opensRange])

@[reassoc] theorem preimageIso_hom_chart :
    (preimageIso R v).hom ≫ preimageChart R v = (FlagScheme.orbitMap R n ⁻¹ᵁ bigCell R v).ι :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- `π : D(f_v) ⟶ bigCell v`, read in the charts. -/
def chartMap : Spec (CommRingCat.of (BigCellPreimageRing R v)) ⟶ bigCellChartScheme R v :=
  Spec.map (CommRingCat.ofHom (preimageChartComorphism R v).toRingHom)

theorem preimageChart_orbitMap' :
    preimageChart R v ≫ FlagScheme.orbitMap R n = chartMap R v ≫ bigCellChart R v :=
  preimageChart_orbitMap R v

/-- The comorphism of the section `s_v : bigCell v ⟶ GLₙ`. -/
abbrev bigCellSectionComorphism : GLCoord R n →ₐ[R] bigCellRing R v :=
  glPointOfMatrix R _ (isUnit_det_bigCellMatrix (inBigCell_bigCellUniversalFlag R v))

/-- `g ↦ (s_v(π g), β(g))` on `D(f_v)`, with `β(g) = s_v(π g)⁻¹ g`. -/
def trivMap : Spec (CommRingCat.of (BigCellPreimageRing R v)) ⟶ GLBorel R n :=
  pullback.lift
    (GLScheme.point R n ((preimageChartComorphism R v).comp (bigCellSectionComorphism R v)))
    (Spec.map (CommRingCat.ofHom (trivBorelPart R v).toRingHom))
    (point_borel_condition _ _)

theorem trivMap_mulRight : trivMap R v ≫ mulRight R n = preimageChart R v := by
  rw [trivMap, lift_mulRight]
  congr 1
  apply glCoord_algHom_ext R
  rw [pointMatrix_glPointOfMatrix, pointMatrix_comp, pointMatrix_glPointOfMatrix,
    preimageChartComorphism, map_bigCellPoint, borelMatrix_map_trivBorelPart,
    mul_preimageBorelMatrix]
  rfl

theorem trivMap_pr₁ : trivMap R v ≫ pullback.fst _ _ = chartMap R v ≫ bigCellSection R v := by
  rw [trivMap, pullback.lift_fst]
  exact (spec_map_comp_point _ _).symm

/-- **Local triviality data of `GLₙ ⟶ Flₙ` over the big cell of `v`**: the section
`e = s_v` and `t = (s_v ∘ π, β)`. -/
def bigCellLocalData : (glBorelAction R n).LocalData (bigCell R v) where
  e := (bigCellIso R v).hom ≫ bigCellSection R v
  e_q := by
    change (bigCellIso R v).hom ≫ bigCellSection R v ≫ FlagScheme.orbitMap R n = _
    rw [bigCellSection_orbitMap, bigCellIso_hom_chart]
  t := (preimageIso R v).hom ≫ trivMap R v
  t_act := by
    change (preimageIso R v).hom ≫ trivMap R v ≫ mulRight R n = _
    rw [trivMap_mulRight, preimageIso_hom_chart]
    rfl
  t_actionFst := by
    change ((preimageIso R v).hom ≫ trivMap R v) ≫ pullback.fst _ _ =
      FlagScheme.orbitMap R n ∣_ bigCell R v ≫ (bigCellIso R v).hom ≫ bigCellSection R v
    rw [Category.assoc, trivMap_pr₁, ← Category.assoc, ← Category.assoc]
    congr 1
    rw [← cancel_mono (bigCellChart R v), Category.assoc, ← preimageChart_orbitMap',
      preimageIso_hom_chart_assoc, Category.assoc, bigCellIso_hom_chart, morphismRestrict_ι]

end FlagVarieties
