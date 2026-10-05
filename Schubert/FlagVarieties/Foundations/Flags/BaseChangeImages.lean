import Schubert.FlagVarieties.Foundations.Flags.RingBaseChange
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Tensor images and the Grassmannian base-change kernels

Right exactness identifies the two descriptions without a flatness premise.
Scalar extension preserves sums and images.
-/

namespace FlagVarieties.Foundations

open TensorProduct AlgebraTensorModule

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] (B : Type*) [CommRing B] [Algebra R B]

theorem baseChange_mkQ_ker (P : Submodule R M) :
    LinearMap.ker (P.mkQ.baseChange B) = P.baseChange B := by
  ext x
  have h := SetLike.ext_iff.mp (_root_.lTensor_mkQ B P) x
  change P.mkQ.lTensor B x = 0 ↔ ∃ y, P.subtype.lTensor B y = x at h
  simpa only [LinearMap.mem_ker, Submodule.baseChange, LinearMap.mem_range,
    LinearMap.baseChange_eq_ltensor] using h

theorem baseChange_range (f : M →ₗ[R] N) :
    (LinearMap.range f).baseChange B = LinearMap.range (f.baseChange B) := by
  ext x
  have h := SetLike.ext_iff.mp (LinearMap.lTensor_range B (g := f)) x
  change (∃ y, f.lTensor B y = x) ↔ ∃ y, (LinearMap.range f).subtype.lTensor B y = x at h
  simpa only [Submodule.baseChange, LinearMap.mem_range, LinearMap.baseChange_eq_ltensor] using
    h.symm

theorem baseChange_map (P : Submodule R M) (f : M →ₗ[R] N) :
    (P.map f).baseChange B = (P.baseChange B).map (f.baseChange B) := by
  have hp : P.map f = LinearMap.range (f.comp P.subtype) := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  rw [hp, baseChange_range, LinearMap.baseChange_comp, LinearMap.range_comp]
  rfl

theorem baseChange_sup (P Q : Submodule R M) :
    (P ⊔ Q).baseChange B = P.baseChange B ⊔ Q.baseChange B := by
  have h : P ⊔ Q = Submodule.span R ((P : Set M) ∪ (Q : Set M)) := by simp
  rw [h, Submodule.baseChange_span, Set.image_union, Submodule.span_union,
    ← Submodule.baseChange_span, ← Submodule.baseChange_span]
  simp

universe u v w

variable {S : Type u} [CommRing S] {V : Type v} [AddCommGroup V] [Module S V]
  {A : Type w} [CommRing A] [Algebra S A]
  (C : Type w) [CommRing C] [Algebra S C] [Algebra A C] [IsScalarTower S A C]

/-- The kernel definition used by the Grassmannian functor is the transported
tensor image of the original submodule, even for nonflat scalar extension. -/
theorem grassmannian_baseChange_ker_eq_image (P : Submodule A (A ⊗[S] V)) :
    LinearMap.ker (Module.Grassmannian.baseChangeMkQ C P) =
      (P.baseChange C).map (cancelBaseChange S A C C V).toLinearMap := by
  rw [Module.Grassmannian.baseChangeMkQ, LinearMap.ker_comp, baseChange_mkQ_ker]
  exact ((P.baseChange C).map_equiv_eq_comap_symm (cancelBaseChange S A C C V)).symm

end FlagVarieties.Foundations
