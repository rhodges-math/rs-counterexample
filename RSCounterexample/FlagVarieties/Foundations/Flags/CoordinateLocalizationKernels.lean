import RSCounterexample.FlagVarieties.Foundations.Flags.CoordinateGrassmannianComparison
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.Algebra.Module.LocalizedModule.Submodule

/-!
# Coordinate localization and clearing denominators in quotient kernels

The coordinate map is scalar extension of each entry. Its localization
structure comes from the canonical finite-coordinate tensor equivalence.
Membership in a localized kernel is equivalent to membership after clearing
one denominator in the original kernel.
-/

noncomputable section

namespace FlagVarieties.Foundations.QuotientCharts

open TensorProduct

variable {A : Type*} [CommRing A]

/-- The original vector lies in a localized submodule precisely after clearing a denominator. -/
theorem localized_submodule_mem_image_iff
    {M N : Type*} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    (S : Submonoid A) (B : Type*) [CommRing B] [Algebra A B] [IsLocalization S B]
    [Module B N] [IsScalarTower A B N]
    (f : M →ₗ[A] N) [IsLocalizedModule S f] (P : Submodule A M) (m : M) :
    f m ∈ P.localized' B S f ↔ ∃ s : S, (s : A) • m ∈ P := by
  constructor
  · rintro ⟨z, hz, s, hs⟩
    have he := (IsLocalizedModule.mk'_eq_iff (S := S) (f := f)).mp hs
    rw [Submonoid.smul_def, ← map_smul] at he
    obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_iff_exists S f).mp he
    refine ⟨t * s, ?_⟩
    change (t : A) • z = (t : A) • ((s : A) • m) at ht
    change ((t : A) * (s : A)) • m ∈ P
    rw [mul_smul, ← ht]
    exact P.smul_mem t hz
  · rintro ⟨s, hs⟩
    exact ⟨(s : A) • m, hs, s, IsLocalizedModule.mk'_cancel (S := S) f m s⟩

/-- Canonical scalar extension in the original finite coordinates. -/
def coordinateScalarMap (B : Type*) [CommRing B] [Algebra A B] (n : ℕ) :
    (Fin n → A) →ₗ[A] (Fin n → B) :=
  ((TensorProduct.piScalarRight A B B (Fin n)).restrictScalars A).toLinearMap.comp
    (TensorProduct.mk A B (Fin n → A) 1)

@[simp] theorem coordinateScalarMap_apply
    (B : Type*) [CommRing B] [Algebra A B] {n : ℕ} (v : Fin n → A) (i : Fin n) :
    coordinateScalarMap B n v i = algebraMap A B (v i) := by
  simp [coordinateScalarMap, Algebra.smul_def]

/-- The coordinate map is a module localization. -/
instance coordinateScalarMap_isLocalized
    (S : Submonoid A) (B : Type*) [CommRing B] [Algebra A B] [IsLocalization S B]
    (n : ℕ) : IsLocalizedModule S (coordinateScalarMap B n : (Fin n → A) →ₗ[A] _) :=
  IsLocalizedModule.of_linearEquiv S (TensorProduct.mk A B (Fin n → A) 1)
    ((TensorProduct.piScalarRight A B B (Fin n)).restrictScalars A)

/-- Coordinate localization agrees with the tensor-image description of a submodule. -/
theorem coordinate_localized_submodule
    (S : Submonoid A) (B : Type*) [CommRing B] [Algebra A B] [IsLocalization S B]
    {n : ℕ} (P : Submodule A (Fin n → A)) :
    P.localized' B S (coordinateScalarMap B n) =
      (P.baseChange B).map (TensorProduct.piScalarRight A B B (Fin n)).toLinearMap := by
  rw [Submodule.localized'_eq_span, Submodule.baseChange_eq_span, Submodule.map_span]
  rw [Submodule.map_coe, Set.image_image]
  rfl

/-- Vectors of the original kernel remain in its scalar extension. -/
theorem coordinateScalarMap_mem_baseChange
    (B : Type*) [CommRing B] [Algebra A B] {n d : ℕ}
    (P : Module.Grassmannian A (Fin n → A) d) {v : Fin n → A}
    (hv : v ∈ P.toSubmodule) :
    coordinateScalarMap B n v ∈ (coordinateGrassmannianBaseChange B P).toSubmodule := by
  rw [coordinateGrassmannianBaseChange_submodule]
  refine ⟨1 ⊗ₜ[A] v, ?_, rfl⟩
  rw [Submodule.baseChange_eq_span]
  exact Submodule.subset_span ⟨v, hv, rfl⟩

/-- Coordinate quotient kernels admit the expected principal denominator test. -/
theorem coordinateScalarMap_mem_away_baseChange_iff
    (a : A) {n d : ℕ} (P : Module.Grassmannian A (Fin n → A) d) (v : Fin n → A) :
    coordinateScalarMap (Localization.Away a) n v ∈
        (coordinateGrassmannianBaseChange (Localization.Away a) P).toSubmodule ↔
      ∃ k : ℕ, a ^ k • v ∈ P.toSubmodule := by
  rw [coordinateGrassmannianBaseChange_submodule, ← coordinate_localized_submodule
    (.powers a), localized_submodule_mem_image_iff]
  constructor
  · rintro ⟨⟨_, k, rfl⟩, hk⟩
    exact ⟨k, hk⟩
  · rintro ⟨k, hk⟩
    exact ⟨⟨a ^ k, ⟨k, rfl⟩⟩, hk⟩

end FlagVarieties.Foundations.QuotientCharts
