import RSCounterexample.FlagVarieties.Foundations.Flags.RingBaseChange

/-!
# Split quotients and their finite projective kernels

These are the module-theoretic facts used to recover the successive locally
free quotients of a ring flag. All maps are the split linear maps;
finite generation and projectivity of the kernel are proved by a retraction.
-/

namespace FlagVarieties.Foundations

variable {R M Q : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup Q] [Module R Q]

/-- Projection onto the kernel along a chosen section. -/
def splitKernelProjection (f : M →ₗ[R] Q) (s : Q →ₗ[R] M)
    (h : f.comp s = LinearMap.id) : M →ₗ[R] LinearMap.ker f :=
  (LinearMap.id - s.comp f).codRestrict (LinearMap.ker f) (by
    intro x
    change f (x - s (f x)) = 0
    rw [map_sub, show f (s (f x)) = f x from LinearMap.congr_fun h (f x), sub_self])

@[simp] theorem splitKernelProjection_coe (f : M →ₗ[R] Q) (s : Q →ₗ[R] M)
    (h : f.comp s = LinearMap.id) (x : M) :
    (splitKernelProjection f s h x : M) = x - s (f x) := rfl

@[simp] theorem splitKernelProjection_apply_kernel (f : M →ₗ[R] Q) (s : Q →ₗ[R] M)
    (h : f.comp s = LinearMap.id) (x : LinearMap.ker f) :
    splitKernelProjection f s h x = x := by
  apply Subtype.ext
  change x.val - s (f x.val) = x.val
  rw [show f x.val = 0 from x.property, map_zero, sub_zero]

theorem splitKernelProjection_surjective (f : M →ₗ[R] Q) (s : Q →ₗ[R] M)
    (h : f.comp s = LinearMap.id) : Function.Surjective (splitKernelProjection f s h) :=
  fun x => ⟨x, splitKernelProjection_apply_kernel f s h x⟩

theorem projective_kernel_of_split [Module.Projective R M]
    (f : M →ₗ[R] Q) (s : Q →ₗ[R] M) (h : f.comp s = LinearMap.id) :
    Module.Projective R (LinearMap.ker f) :=
  Module.Projective.of_split (LinearMap.ker f).subtype (splitKernelProjection f s h)
    (by apply LinearMap.ext; intro x; exact splitKernelProjection_apply_kernel f s h x)

theorem finite_kernel_of_split [Module.Finite R M]
    (f : M →ₗ[R] Q) (s : Q →ₗ[R] M) (h : f.comp s = LinearMap.id) :
    Module.Finite R (LinearMap.ker f) :=
  Module.Finite.of_surjective (splitKernelProjection f s h) (splitKernelProjection_surjective f s h)

/-- The splitting map `x ↦ (x-s(f(x)), f(x))`. -/
def splitKernelEquiv (f : M →ₗ[R] Q) (s : Q →ₗ[R] M)
    (h : f.comp s = LinearMap.id) : M ≃ₗ[R] (LinearMap.ker f × Q) :=
  { (splitKernelProjection f s h).prod f with
    invFun x := x.1.val + s x.2
    left_inv x := by change (x - s (f x)) + s (f x) = x; simp
    right_inv x := by
      apply Prod.ext
      · apply Subtype.ext
        change (x.1.val + s x.2) - s (f (x.1.val + s x.2)) = x.1.val
        rw [map_add, show f x.1.val = 0 from x.1.property,
          show f (s x.2) = x.2 from LinearMap.congr_fun h x.2, zero_add]
        simp
      · change f (x.1.val + s x.2) = x.2
        rw [map_add, show f x.1.val = 0 from x.1.property,
          show f (s x.2) = x.2 from LinearMap.congr_fun h x.2, zero_add] }

theorem splitKernel_rankAtStalk [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R Q] [Module.Projective R Q]
    (f : M →ₗ[R] Q) (s : Q →ₗ[R] M) (h : f.comp s = LinearMap.id)
    (p : PrimeSpectrum R) :
    Module.rankAtStalk (R := R) M p =
      Module.rankAtStalk (R := R) (LinearMap.ker f) p + Module.rankAtStalk (R := R) Q p := by
  let := projective_kernel_of_split f s h
  let := finite_kernel_of_split f s h
  have he := Module.rankAtStalk_eq_of_equiv (splitKernelEquiv f s h)
  rw [Module.rankAtStalk_prod] at he
  exact congrFun he p

end FlagVarieties.Foundations
