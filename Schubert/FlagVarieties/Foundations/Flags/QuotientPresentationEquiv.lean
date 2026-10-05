import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Canonical changes between two presentations of the same quotient

Surjective maps with the same kernel have a unique target
identification preserving every original quotient image. Uniqueness
proves the identity, inverse and cocycle laws used to glue quotient families.
-/

noncomputable section

namespace FlagVarieties.Foundations.QuotientCharts

variable {A M N P Q : Type*} [CommRing A]
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
  [AddCommGroup P] [Module A P] [AddCommGroup Q] [Module A Q]
  (q : M →ₗ[A] N) (r : M →ₗ[A] P)
  (hq : Function.Surjective q) (hr : Function.Surjective r)
  (hker : LinearMap.ker q = LinearMap.ker r)

/-- The canonical target identification obtained from the common kernel. -/
def quotientPresentationEquiv : N ≃ₗ[A] P :=
  (q.quotKerEquivOfSurjective hq).symm.trans
    ((Submodule.quotEquivOfEq _ _ hker).trans (r.quotKerEquivOfSurjective hr))

/-- Every original quotient vector is retained under the identification. -/
@[simp] theorem quotientPresentationEquiv_apply (m : M) :
    quotientPresentationEquiv q r hq hr hker (q m) = r m := by
  have he : (q.quotKerEquivOfSurjective hq).symm (q m) = Submodule.Quotient.mk m := by
    apply (q.quotKerEquivOfSurjective hq).injective
    simp
  simp [quotientPresentationEquiv, he]

theorem quotientPresentationEquiv_comp :
    (quotientPresentationEquiv q r hq hr hker).toLinearMap.comp q = r := by
  ext m
  exact quotientPresentationEquiv_apply q r hq hr hker m

/-- Preserving the original quotient map uniquely determines the target map. -/
theorem quotientPresentationEquiv_unique (t : N →ₗ[A] P) (ht : t.comp q = r) :
    (quotientPresentationEquiv q r hq hr hker).toLinearMap = t := by
  ext x
  obtain ⟨m, rfl⟩ := hq x
  exact (quotientPresentationEquiv_apply q r hq hr hker m).trans
    (LinearMap.congr_fun ht m).symm

@[simp] theorem quotientPresentationEquiv_refl :
    quotientPresentationEquiv q q hq hq rfl = LinearEquiv.refl A N := by
  ext x
  obtain ⟨m, rfl⟩ := hq x
  simp

/-- The transition for the reversed pair is the inverse. -/
theorem quotientPresentationEquiv_symm :
    (quotientPresentationEquiv q r hq hr hker).symm =
      quotientPresentationEquiv r q hr hq hker.symm := by
  ext y
  obtain ⟨m, rfl⟩ := hr y
  apply (quotientPresentationEquiv q r hq hr hker).injective
  simp

/-- Triple-overlap cocycles follow from the quotient maps. -/
theorem quotientPresentationEquiv_trans
    (s : M →ₗ[A] Q) (hs : Function.Surjective s)
    (hker' : LinearMap.ker r = LinearMap.ker s) :
    (quotientPresentationEquiv q r hq hr hker).trans
        (quotientPresentationEquiv r s hr hs hker') =
      quotientPresentationEquiv q s hq hs (hker.trans hker') := by
  ext x
  obtain ⟨m, rfl⟩ := hq x
  simp

end FlagVarieties.Foundations.QuotientCharts
