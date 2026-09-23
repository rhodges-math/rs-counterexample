import Schubert.RS.Representation.OrderedPBWBasis

namespace Schubert.RS.Representation

noncomputable section
attribute [local instance 100] LieRing.ofAssociativeRing

/-- Augmentation of the actual enveloping algebra, from its universal property. -/
def augmentation (n : ℕ) : Enveloping n →ₐ[ℂ] ℂ :=
  UniversalEnvelopingAlgebra.lift ℂ (0 : upperNilpotent n →ₗ⁅ℂ⁆ ℂ)

@[simp] theorem augmentation_root {n : ℕ} (r : PositiveRoot n) :
    augmentation n (rootOperator r) = 0 := by
  simp [augmentation, rootOperator]

theorem augmentation_zero_on_jp {n : ℕ} (u : Fin n → ℕ) {a : Enveloping n}
    (ha : a ∈ jpLeftIdeal u) : augmentation n a = 0 := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨r, rfl⟩ := ha
    simp [jpExponent]
  | zero => simp
  | add a b ha hb ia ib => simp [ia, ib]
  | smul c a ha ia =>
    change augmentation n (c * a) = 0
    rw [map_mul, ia, mul_zero]

/-- Augmentation descends through the genuine left ideal as a complex-linear map. -/
def quotientAugmentation {n : ℕ} (u : Fin n → ℕ) : PresentationQuotient u →ₗ[ℂ] ℂ :=
  ((jpLeftIdeal u).restrictScalars ℂ).liftQ (augmentation n).toLinearMap (by
    intro a ha
    exact augmentation_zero_on_jp u ha)

@[simp] theorem quotientAugmentation_mk {n : ℕ} (u : Fin n → ℕ) (a : Enveloping n) :
    quotientAugmentation u (Submodule.Quotient.mk a) = augmentation n a := rfl

@[simp] theorem quotientAugmentation_generator {n : ℕ} (u : Fin n → ℕ) :
    quotientAugmentation u (presentationGenerator u) = 1 := by
  simp [presentationGenerator]

theorem presentationGenerator_ne_zero {n : ℕ} (u : Fin n → ℕ) :
    presentationGenerator u ≠ 0 := by
  intro h
  have := congrArg (quotientAugmentation u) h
  simp at this

private theorem dominant_root_mem {n : ℕ} (u : Fin n → ℕ) (hu : Antitone u)
    (r : PositiveRoot n) : rootOperator r ∈ jpLeftIdeal u := by
  have h : u r.val.2 ≤ u r.val.1 := hu (le_of_lt r.property)
  have hm : rootOperator r ^ jpExponent u r ∈ jpLeftIdeal u :=
    Submodule.subset_span ⟨r, rfl⟩
  simpa [jpExponent_eq_one u r h] using hm

/-- Every ordered root monomial reduces to its augmentation in the dominant
quotient. Factoring the last positive power uses only LEFT-ideal closure. -/
theorem dominant_ordered_product {n : ℕ} (u : Fin n → ℕ) (hu : Antitone u)
    (powers : PositiveRoot n → ℕ) (roots : List (PositiveRoot n)) :
    (Submodule.Quotient.mk ((roots.map fun r => rootOperator r ^ powers r).prod) :
      PresentationQuotient u) =
      augmentation n ((roots.map fun r => rootOperator r ^ powers r).prod) •
        presentationGenerator u := by
  induction roots using List.reverseRecOn with
  | nil => simp [presentationGenerator]
  | append_singleton roots r ih =>
    simp only [List.map_append, List.map_singleton, List.prod_append, List.prod_singleton]
    cases hp : powers r with
    | zero => simpa only [hp, pow_zero, mul_one] using ih
    | succ k =>
      have hm : (roots.map fun r => rootOperator r ^ powers r).prod *
          rootOperator r ^ (k + 1) ∈ jpLeftIdeal u := by
        rw [pow_succ, ← mul_assoc]
        exact (jpLeftIdeal u).smul_mem _ (dominant_root_mem u hu r)
      rw [(Submodule.Quotient.mk_eq_zero _).mpr hm]
      simp

/-- PBW is used only as the explicit ordered-basis input, not as a quotient
character theorem. -/
theorem dominant_mk_eq {n : ℕ} (u : Fin n → ℕ) (hu : Antitone u)
    (hpbw : HasOrderedPBWBasis n) (a : Enveloping n) :
    (Submodule.Quotient.mk a : PresentationQuotient u) =
      augmentation n a • presentationGenerator u := by
  obtain ⟨b, hb⟩ := hpbw (defaultRootOrdering n)
  have hm : ((jpLeftIdeal u).restrictScalars ℂ).mkQ =
      (LinearMap.toSpanSingleton ℂ (PresentationQuotient u) (presentationGenerator u)).comp
        (augmentation n).toLinearMap := by
    apply b.ext
    intro powers
    change (Submodule.Quotient.mk (b powers) : PresentationQuotient u) =
      augmentation n (b powers) • presentationGenerator u
    rw [hb, orderedRootMonomial_eq]
    exact dominant_ordered_product u hu powers _
  exact LinearMap.congr_fun hm a

/-- The dominant cyclic quotient is one-dimensional under the ordered PBW
basis hypothesis. -/
def dominantQuotientEquiv {n : ℕ} (u : Fin n → ℕ) (hu : Antitone u)
    (hpbw : HasOrderedPBWBasis n) : PresentationQuotient u ≃ₗ[ℂ] ℂ where
  toFun := quotientAugmentation u
  invFun c := c • presentationGenerator u
  left_inv v := by
    refine Submodule.Quotient.induction_on (jpLeftIdeal u) v ?_
    intro a
    exact (dominant_mk_eq u hu hpbw a).symm
  right_inv c := by simp
  map_add' a b := map_add (quotientAugmentation u) a b
  map_smul' c a := map_smul (quotientAugmentation u) c a

theorem dominant_finrank {n : ℕ} (u : Fin n → ℕ) (hu : Antitone u)
    (hpbw : HasOrderedPBWBasis n) : Module.finrank ℂ (PresentationQuotient u) = 1 := by
  simpa using (dominantQuotientEquiv u hu hpbw).finrank_eq

end
end Schubert.RS.Representation
