import Schubert.FlagVarieties.Flag.Basic
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.LocalRing.Module

/-!
# Properness of the flag scheme

`Flₙ ⟶ Spec R` is proper for every commutative ring `R` (`FlagScheme.isProper_toSpec`).

We use the valuative criterion. Let `V` be a valuation ring with fraction field `L`. A complete
flag `W•` of `Lⁿ` extends to the flag of saturations `Wⱼ ∩ Vⁿ` of `Vⁿ`: each quotient
`Vⁿ / (Wⱼ ∩ Vⁿ)` embeds in the `L`-vector space `Lⁿ / Wⱼ`, so it is finitely generated and torsion
free, hence flat (a valuation ring is Bézout) and then free (`V` is local). Its rank is
`dim_L (Lⁿ / Wⱼ)`, because `Lⁿ / Wⱼ` is its localization at the nonzero elements of `V`.
-/

noncomputable section

namespace FlagVarieties

open AlgebraicGeometry CategoryTheory
open Foundations Foundations.QuotientCharts

universe u

namespace Saturation

variable {V : Type u} [CommRing V] [IsDomain V] {L : Type u} [Field L] [Algebra V L]
  [IsFractionRing V L] {n : ℕ}

variable (V L n) in
/-- The coordinatewise inclusion `Vⁿ → Lⁿ`. -/
abbrev inclusion : (Fin n → V) →ₗ[V] (Fin n → L) :=
  LinearMap.compLeft (Algebra.linearMap V L) (Fin n)

omit [IsDomain V] in
theorem inclusion_injective : Function.Injective (inclusion V L n) := by
  intro x y h
  funext i
  exact IsFractionRing.injective V L (congrFun h i)

variable (V) in
/-- The saturation `W ∩ Vⁿ` of a subspace `W ⊆ Lⁿ`. -/
def saturate (W : Submodule L (Fin n → L)) : Submodule V (Fin n → V) :=
  (W.restrictScalars V).comap (inclusion V L n)

omit [IsDomain V] [IsFractionRing V L] in
theorem mem_saturate {W : Submodule L (Fin n → L)} {x : Fin n → V} :
    x ∈ saturate V W ↔ inclusion V L n x ∈ W := Iff.rfl

omit [IsDomain V] [IsFractionRing V L] in
theorem saturate_mono {W W' : Submodule L (Fin n → L)} (h : W ≤ W') :
    saturate V W ≤ saturate V W' :=
  fun _ hx => h hx

omit [IsDomain V] in
theorem saturate_bot : saturate V (⊥ : Submodule L (Fin n → L)) = ⊥ := by
  ext x
  simp only [mem_saturate, Submodule.mem_bot]
  constructor
  · intro hx
    apply inclusion_injective (L := L)
    rw [hx, map_zero]
  · rintro rfl
    simp

omit [IsDomain V] [IsFractionRing V L] in
theorem saturate_top : saturate V (⊤ : Submodule L (Fin n → L)) = ⊤ := by
  ext x
  simp [mem_saturate]

omit [IsDomain V] in
/-- Every vector of `Lⁿ` has a nonzero multiple in `Vⁿ`. -/
theorem exists_smul_mem_range (x : Fin n → L) :
    ∃ d : nonZeroDivisors V, ∃ y : Fin n → V, inclusion V L n y = (d : V) • x := by
  classical
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors V)
    (Finset.univ.image x)
  refine ⟨d, fun i => (hd (x i) (Finset.mem_image_of_mem x (Finset.mem_univ i))).choose, ?_⟩
  funext i
  exact (hd (x i) (Finset.mem_image_of_mem x (Finset.mem_univ i))).choose_spec

variable (V) in
/-- The induced map of quotients `Vⁿ / (W ∩ Vⁿ) → Lⁿ / W`. -/
def quotMap (W : Submodule L (Fin n → L)) :
    ((Fin n → V) ⧸ saturate V W) →ₗ[V] ((Fin n → L) ⧸ W) :=
  (saturate V W).liftQ ((W.mkQ.restrictScalars V).comp (inclusion V L n)) (fun x hx => by
    simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.coe_restrictScalars, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hx)

omit [IsDomain V] [IsFractionRing V L] in
@[simp] theorem quotMap_mk (W : Submodule L (Fin n → L)) (x : Fin n → V) :
    quotMap V W (Submodule.Quotient.mk x) = Submodule.Quotient.mk (inclusion V L n x) := rfl

omit [IsDomain V] [IsFractionRing V L] in
theorem quotMap_injective (W : Submodule L (Fin n → L)) :
    Function.Injective (quotMap V W) := by
  rw [← LinearMap.ker_eq_bot, quotMap]
  apply Submodule.ker_liftQ_eq_bot
  intro x hx
  simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.coe_restrictScalars, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hx
  exact hx

theorem torsion_quot_eq_bot (W : Submodule L (Fin n → L)) :
    Submodule.torsion V ((Fin n → V) ⧸ saturate V W) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨r, hr⟩ := (Submodule.mem_torsion_iff x).mp hx
  rw [Submodule.mem_bot]
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hr0 : algebraMap V L (r : V) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors r.2
  have h0 : (r : V) • y ∈ saturate V W := by
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
    exact hr
  rw [Submodule.Quotient.mk_eq_zero, mem_saturate]
  rw [mem_saturate, map_smul, ← algebraMap_smul L] at h0
  have h2 := W.smul_mem (algebraMap V L (r : V))⁻¹ h0
  rwa [smul_smul, inv_mul_cancel₀ hr0, one_smul] at h2

variable [ValuationRing V]

instance flat_quot (W : Submodule L (Fin n → L)) :
    Module.Flat V ((Fin n → V) ⧸ saturate V W) :=
  (Module.Flat.flat_iff_torsion_eq_bot_of_isBezout).mpr (torsion_quot_eq_bot W)

instance free_quot (W : Submodule L (Fin n → L)) :
    Module.Free V ((Fin n → V) ⧸ saturate V W) :=
  Module.free_of_flat_of_isLocalRing

instance projective_quot (W : Submodule L (Fin n → L)) :
    Module.Projective V ((Fin n → V) ⧸ saturate V W) :=
  Module.Projective.of_free

omit [ValuationRing V] in
theorem isLocalizedModule_quotMap (W : Submodule L (Fin n → L)) :
    IsLocalizedModule (nonZeroDivisors V) (quotMap V W) where
  map_units r := by
    have hr0 : algebraMap V L (r : V) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors r.2
    rw [Module.End.isUnit_iff]
    constructor
    · intro x y h
      rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply,
        ← algebraMap_smul L (r : V) x, ← algebraMap_smul L (r : V) y] at h
      have := congrArg (fun z => (algebraMap V L (r : V))⁻¹ • z) h
      simpa only [smul_smul, inv_mul_cancel₀ hr0, one_smul] using this
    · intro y
      refine ⟨(algebraMap V L (r : V))⁻¹ • y, ?_⟩
      rw [Module.algebraMap_end_apply, ← algebraMap_smul L (r : V), smul_smul,
        mul_inv_cancel₀ hr0, one_smul]
  surj y := by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨d, z, hz⟩ := exists_smul_mem_range (V := V) (L := L) x
    refine ⟨(Submodule.Quotient.mk z, d), ?_⟩
    rw [quotMap_mk, hz, Submodule.Quotient.mk_smul]
    rfl
  exists_of_eq {x y} h := ⟨1, by simpa using quotMap_injective W h⟩

omit [ValuationRing V] in
/-- `dim_L (Lⁿ / W)` is the `V`-rank of `Vⁿ / (W ∩ Vⁿ)`. -/
theorem finrank_quot (W : Submodule L (Fin n → L)) :
    Module.finrank V ((Fin n → V) ⧸ saturate V W) = Module.finrank L ((Fin n → L) ⧸ W) := by
  have := isLocalizedModule_quotMap (V := V) (L := L) W
  have hb : IsBaseChange L (quotMap V W) :=
    IsLocalizedModule.isBaseChange (nonZeroDivisors V) L _
  exact hb.finrank_eq.symm

omit [ValuationRing V] in
/-- The `L`-span of the saturation is the subspace itself. -/
theorem span_inclusion_saturate (W : Submodule L (Fin n → L)) :
    Submodule.span L (inclusion V L n '' saturate V W) = W := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  · intro x hx
    obtain ⟨d, z, hz⟩ := exists_smul_mem_range (V := V) (L := L) x
    have hd0 : algebraMap V L (d : V) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.2
    have hzW : z ∈ saturate V W := by
      rw [mem_saturate, hz]
      exact W.smul_of_tower_mem (d : V) hx
    have hx' : x = (algebraMap V L (d : V))⁻¹ • inclusion V L n z := by
      rw [hz, ← algebraMap_smul L (d : V) x, smul_smul, inv_mul_cancel₀ hd0, one_smul]
    rw [hx']
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨z, hzW, rfl⟩)

/-- The saturation of a point of the Grassmannian over `L`. -/
def satGrassmannian {d : ℕ} (W : Module.Grassmannian L (Fin n → L) d) :
    Module.Grassmannian V (Fin n → V) d where
  toSubmodule := saturate V W.toSubmodule
  finite_quotient := inferInstance
  projective_quotient := inferInstance
  rankAtStalk_eq p := by
    have h := W.rankAtStalk_eq ⊥
    simp only [Module.rankAtStalk_eq_finrank_of_free, Pi.natCast_apply, Nat.cast_id] at h ⊢
    rw [finrank_quot, h]

/-- The flag of saturations of a complete flag of `Lⁿ`. -/
def satFlag (P : CoordinateFlag L n) : CoordinateFlag V n where
  step j := satGrassmannian (P.step j)
  step_mono _ _ hij := saturate_mono (P.step_mono hij)
  step_zero := by
    change saturate V (P.step 0).toSubmodule = ⊥
    rw [P.step_zero, saturate_bot]
  step_last := by
    change saturate V (P.step (Fin.last n)).toSubmodule = ⊤
    rw [P.step_last, saturate_top]

/-- Extending scalars of the flag of saturations back to `L` recovers the flag. -/
theorem baseChange_satFlag (P : CoordinateFlag L n) :
    coordinateRingFlagBaseChange (B := L) (satFlag (V := V) P) = P := by
  apply RingFlag.ext
  intro j
  rw [coordinateRingFlagBaseChange_step, coordinateGrassmannianBaseChange_submodule,
    Submodule.baseChange_eq_span, Submodule.map_span, Submodule.map_coe, Set.image_image]
  conv_rhs => rw [← span_inclusion_saturate (V := V) (P.step j).toSubmodule]
  congr 1
  apply Set.image_congr
  intro x _
  funext i
  simp [TensorProduct.piScalarRight_apply, Algebra.smul_def]

end Saturation

namespace FlagScheme

variable (R : Type u) [CommRing R] (n : ℕ)

/-- Existence in the valuative criterion for `Flₙ ⟶ Spec R`. -/
theorem valuativeCriterion_existence_toSpec :
    ValuativeCriterion.Existence (toSpec R n) := by
  intro S
  let φ := Spec.preimage S.i₂
  let : Algebra R S.R := φ.hom.toAlgebra
  let : Algebra R S.K := ((algebraMap S.R S.K).comp (algebraMap R S.R)).toAlgebra
  have : IsScalarTower R S.R S.K := IsScalarTower.of_algebraMap_eq' rfl
  have hφ : Spec.map (CommRingCat.ofHom (algebraMap R S.R)) = S.i₂ := Spec.map_preimage S.i₂
  have h₁ : S.i₁ ≫ toSpec R n = Spec.map (CommRingCat.ofHom (algebraMap R S.K)) := by
    rw [S.commSq.w, ← hφ, ← Spec.map_comp]
    rfl
  obtain ⟨P, hP⟩ := exists_eq_ofRingFlag S.i₁ h₁
  refine ⟨⟨⟨ofRingFlag R (Saturation.satFlag (V := S.R) P), ?_, ?_⟩⟩⟩
  · rw [ofRingFlag_baseChange, Saturation.baseChange_satFlag, hP]
  · rw [ofRingFlag_toSpec, hφ]

instance universallyClosed_toSpec : UniversallyClosed (toSpec R n) :=
  UniversallyClosed.of_valuativeCriterion _ (valuativeCriterion_existence_toSpec R n)

/-- The complete flag scheme is proper over `Spec R`. -/
instance isProper_toSpec : IsProper (toSpec R n) where

end FlagScheme

end FlagVarieties
