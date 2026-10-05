import Schubert.FlagVarieties.Foundations.Flags.Ring

/-!
# Arbitrary base change of ring-valued flags

The steps use Mathlib's Grassmannian base change: tensor the quotient
map and take its kernel. Incidence is preserved by the canonical transition
between nested quotients. No flatness condition on the base-change algebra
is imposed. This gives the incidence functor, not its representability.
-/

namespace FlagVarieties.Foundations

universe u v w

open TensorProduct AlgebraTensorModule CategoryTheory

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

section Quotient
variable {A : Type*} [CommRing A] {V : Type*} [AddCommGroup V] [Module A V]

/-- The canonical surjection between nested quotients. -/
def quotientTransition (P Q : Submodule A V) (h : P ≤ Q) : (V ⧸ P) →ₗ[A] (V ⧸ Q) :=
  P.mapQ Q LinearMap.id (by simpa using h)

@[simp] theorem quotientTransition_mk (P Q : Submodule A V) (h : P ≤ Q) (x : V) :
    quotientTransition P Q h (Submodule.Quotient.mk x) = Submodule.Quotient.mk x := rfl

theorem quotientTransition_comp_mkQ (P Q : Submodule A V) (h : P ≤ Q) :
    (quotientTransition P Q h).comp P.mkQ = Q.mkQ := by ext x; rfl

theorem quotientTransition_surjective (P Q : Submodule A V) (h : P ≤ Q) :
    Function.Surjective (quotientTransition P Q h) := by
  intro y
  obtain ⟨x, rfl⟩ := Q.mkQ_surjective y
  exact ⟨P.mkQ x, rfl⟩

end Quotient

section BaseChange
variable {A B : Type w} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
  [Algebra A B] [IsScalarTower R A B]

theorem baseChangeMkQ_factor (P Q : Submodule A (A ⊗[R] M)) (h : P ≤ Q) :
    Module.Grassmannian.baseChangeMkQ B Q =
      ((quotientTransition P Q h).baseChange B).comp
        (Module.Grassmannian.baseChangeMkQ B P) := by
  unfold Module.Grassmannian.baseChangeMkQ
  rw [← LinearMap.comp_assoc, ← LinearMap.baseChange_comp, quotientTransition_comp_mkQ]

theorem baseChangeMkQ_ker_mono (P Q : Submodule A (A ⊗[R] M)) (h : P ≤ Q) :
    LinearMap.ker (Module.Grassmannian.baseChangeMkQ B P) ≤
      LinearMap.ker (Module.Grassmannian.baseChangeMkQ B Q) := by
  rw [baseChangeMkQ_factor P Q h]
  intro x hx
  change (quotientTransition P Q h).baseChange B
    (Module.Grassmannian.baseChangeMkQ B P x) = 0
  rw [show Module.Grassmannian.baseChangeMkQ B P x = 0 from hx, map_zero]

theorem baseChangeMkQ_bot_ker :
    LinearMap.ker (Module.Grassmannian.baseChangeMkQ B (⊥ : Submodule A (A ⊗[R] M))) = ⊥ := by
  apply LinearMap.ker_eq_bot.mpr
  unfold Module.Grassmannian.baseChangeMkQ
  apply Function.Injective.comp _ (cancelBaseChange R A B B M).symm.injective
  change Function.Injective
    (((⊥ : Submodule A (A ⊗[R] M)).quotEquivOfEqBot rfl).symm.baseChange A B)
  exact LinearEquiv.injective _

theorem baseChangeMkQ_top_ker :
    LinearMap.ker (Module.Grassmannian.baseChangeMkQ B (⊤ : Submodule A (A ⊗[R] M))) = ⊤ := by
  have hq : (⊤ : Submodule A (A ⊗[R] M)).mkQ = 0 := Subsingleton.elim _ _
  simp [Module.Grassmannian.baseChangeMkQ, hq]

end BaseChange

namespace RingFlag

variable {A B : Type w} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
  {n : ℕ} (f : A →ₐ[R] B)

/-- Base change preserves every rank and every incidence relation. -/
def map (F : RingFlag A (A ⊗[R] M) n) : RingFlag B (B ⊗[R] M) n :=
  letI : Algebra A B := f.toAlgebra
  letI : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' <| IsScalarTower.algebraMap_eq R A B
  { step j := Module.Grassmannian.map f (F.step j)
    step_mono := by
      intro i j hij
      change LinearMap.ker (Module.Grassmannian.baseChangeMkQ B (F.step i).toSubmodule) ≤
        LinearMap.ker (Module.Grassmannian.baseChangeMkQ B (F.step j).toSubmodule)
      exact baseChangeMkQ_ker_mono _ _ (F.step_mono hij)
    step_zero := by
      change LinearMap.ker (Module.Grassmannian.baseChangeMkQ B (F.step 0).toSubmodule) = ⊥
      rw [F.step_zero]
      exact baseChangeMkQ_bot_ker
    step_last := by
      change LinearMap.ker
        (Module.Grassmannian.baseChangeMkQ B (F.step (Fin.last n)).toSubmodule) = ⊤
      rw [F.step_last]
      exact baseChangeMkQ_top_ker }

@[simp] theorem map_step (F : RingFlag A (A ⊗[R] M) n) (j : Fin (n + 1)) :
    (map f F).step j = Module.Grassmannian.map f (F.step j) := rfl

@[simp] theorem map_id (A : CommAlgCat.{w, u} R) (F : RingFlag A (A ⊗[R] M) n) :
    map (.id R A) F = F := by
  apply RingFlag.ext
  intro j
  exact congrArg Module.Grassmannian.toSubmodule
    (Module.Grassmannian.map_id (n - j.val) A (F.step j))

variable {C : Type w} [CommRing C] [Algebra R C] (g : B →ₐ[R] C)

theorem map_comp (F : RingFlag A (A ⊗[R] M) n) :
    map (g.comp f) F = map g (map f F) := by
  apply RingFlag.ext
  intro j
  exact congrArg Module.Grassmannian.toSubmodule
    (Module.Grassmannian.map_comp (n - j.val) f g (F.step j))

attribute [local ext high] ConcreteCategory.hom_ext

/-- The flag-incidence functor on algebras, prior to representability. -/
def functor (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (n : ℕ) : CommAlgCat.{w, u} R ⥤ Type (max v w) where
  obj A := RingFlag A (A ⊗[R] M) n
  map f := ↾map f.hom
  map_id A := by ext F : 1; exact map_id A F
  map_comp f g := by ext F : 1; exact map_comp f.hom g.hom F

end RingFlag
end FlagVarieties.Foundations
