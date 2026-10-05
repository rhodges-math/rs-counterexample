import Schubert.FlagVarieties.Foundations.Flags.CoordinateGrassmannianComparison
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.LocalProperties.Submodule

/-!
# Principal-local detection of coordinate quotient equality

The tensor image of a submodule under localization is its localized
submodule. Equality of these images on a principal cover therefore detects
equality of the original kernels, and hence of the coordinate Grassmannian
quotients. No flatness, global basis, or nonempty-cover premise is needed.
-/

namespace FlagVarieties.Foundations.QuotientCharts

open TensorProduct

variable {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]

/-- Tensor-image scalar extension to a localization is the localized submodule. -/
theorem submodule_baseChange_localization_eq (S : Submonoid A) (P : Submodule A M) :
    P.baseChange (Localization S) =
      P.localized' (Localization S) S (TensorProduct.mk A (Localization S) M 1) := by
  rw [Submodule.baseChange_eq_span, Submodule.localized'_eq_span]
  rfl

/-- Equality of localized tensor images on a unit-ideal family detects submodule equality. -/
theorem submodule_eq_of_baseChange_away_eq {I : Type*} (s : I → A)
    (hcover : Ideal.span (Set.range s) = ⊤) {P Q : Submodule A M}
    (h : ∀ i, P.baseChange (Localization.Away (s i)) =
      Q.baseChange (Localization.Away (s i))) : P = Q := by
  apply Submodule.eq_of_isLocalized'_span (Set.range s) hcover
    (fun r => Localization.Away r.1)
    (fun r => Localization.Away r.1 ⊗[A] M)
    (fun r => TensorProduct.mk A (Localization.Away r.1) M 1)
  rintro ⟨r, i, rfl⟩
  simpa only [← submodule_baseChange_localization_eq] using h i

/-- Coordinate quotient kernels are determined on any principal cover. -/
theorem coordinateGrassmannian_eq_of_baseChange_away_eq {I : Type*} (s : I → A)
    (hcover : Ideal.span (Set.range s) = ⊤) {n d : ℕ}
    (P Q : Module.Grassmannian A (Fin n → A) d)
    (h : ∀ i, coordinateGrassmannianBaseChange (Localization.Away (s i)) P =
      coordinateGrassmannianBaseChange (Localization.Away (s i)) Q) : P = Q := by
  apply Module.Grassmannian.ext
  apply submodule_eq_of_baseChange_away_eq s hcover
  intro i
  have hk := congrArg Module.Grassmannian.toSubmodule (h i)
  rw [coordinateGrassmannianBaseChange_submodule,
    coordinateGrassmannianBaseChange_submodule] at hk
  exact Submodule.map_injective_of_injective
    (TensorProduct.piScalarRight A (Localization.Away (s i))
      (Localization.Away (s i)) (Fin n)).injective hk

end FlagVarieties.Foundations.QuotientCharts
