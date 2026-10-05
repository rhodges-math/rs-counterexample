import Mathlib.RingTheory.Grassmannian
import Schubert.FlagVarieties.Foundations.Flags.Field

/-!
# Flags with finite projective quotients over rings

Each step is a Mathlib Grassmannian point with quotient rank `n-j`.
The steps are nested, with the usual zero and full endpoints. This is the
ring-valued incidence model for families of flags. Its base
change is `coordinateRingFlagBaseChange`
(`Schemes/SimultaneousFlagCoordinateBaseChange.lean`), and ring flags are
classified by the flag scheme in
`Schemes/SelectedFlagAffineRingClassification.lean`. Over a field the
equivalence below recovers the complete flags `CompleteFlag`.
-/

namespace FlagVarieties.Foundations

universe u v

/-- Nested Grassmannian points in the quotient convention. -/
structure RingFlag (R : Type u) [CommRing R] (M : Type v)
    [AddCommGroup M] [Module R M] (n : ℕ) where
  /-- The step of index `j`: a point of the Grassmannian of `M` with quotient of rank `n - j`. -/
  step : (j : Fin (n + 1)) → Module.Grassmannian R M (n - j.val)
  step_mono : Monotone (fun j => (step j).toSubmodule)
  step_zero : (step 0).toSubmodule = ⊥
  step_last : (step (Fin.last n)).toSubmodule = ⊤

namespace RingFlag

variable {R : Type u} [CommRing R] {M : Type v}
  [AddCommGroup M] [Module R M] {n : ℕ}

@[ext] theorem ext {F G : RingFlag R M n}
    (h : ∀ j, (F.step j).toSubmodule = (G.step j).toSubmodule) : F = G := by
  have hs : F.step = G.step := funext fun j => Module.Grassmannian.ext (h j)
  cases F
  cases G
  cases hs
  rfl

theorem step_le_step (F : RingFlag R M n) {i j : Fin (n + 1)} (h : i ≤ j) :
    (F.step i).toSubmodule ≤ (F.step j).toSubmodule := F.step_mono h

section Field

open Schubert.Geometry Module

variable {K : Type u} [Field K]

/-- The original field flag determines its Grassmannian incidence data. -/
noncomputable def ofFieldFlag (F : CompleteFlag K n) :
    RingFlag K (CoordinateSpace K n) n where
  step j :=
    { toSubmodule := F.step j
      finite_quotient := inferInstance
      projective_quotient := inferInstance
      rankAtStalk_eq p := by
        rw [Module.rankAtStalk_eq_finrank_of_free]
        change finrank K (CoordinateSpace K n ⧸ F.step j) = n - j.val
        rw [Submodule.finrank_quotient, FieldFlags.step_finrank]
        simp [CoordinateSpace] }
  step_mono := F.step_mono
  step_zero := F.step_zero
  step_last := F.step_last

@[simp] theorem ofFieldFlag_step (F : CompleteFlag K n) (j : Fin (n + 1)) :
    ((ofFieldFlag F).step j).toSubmodule = F.step j := rfl

/-- Over a field, the stalk-rank condition is the quotient dimension. -/
theorem field_quotient_finrank (F : RingFlag K (CoordinateSpace K n) n)
    (j : Fin (n + 1)) :
    finrank K (CoordinateSpace K n ⧸ (F.step j).toSubmodule) = n - j.val := by
  have h := (F.step j).rankAtStalk_eq (⟨⊥, inferInstance⟩ : PrimeSpectrum K)
  simpa using h

set_option backward.isDefEq.respectTransparency false in
theorem field_step_finrank (F : RingFlag K (CoordinateSpace K n) n)
    (j : Fin (n + 1)) : finrank K (F.step j).toSubmodule = j.val := by
  have hq := field_quotient_finrank F j
  have hdim := (F.step j).toSubmodule.finrank_quotient_add_finrank
  have hj := j.isLt
  rw [hq] at hdim
  simp only [CoordinateSpace, Module.finrank_pi, Fintype.card_fin] at hdim
  change (n - j.val) + finrank K (F.step j).toSubmodule = n at hdim
  omega

theorem field_step_covBy (F : RingFlag K (CoordinateSpace K n) n) (i : Fin n) :
    (F.step i.castSucc).toSubmodule ⋖ (F.step i.succ).toSubmodule := by
  refine ⟨Submodule.lt_of_le_of_finrank_lt_finrank
    (F.step_mono (show i.castSucc ≤ i.succ from Nat.le_succ i.val)) ?_, ?_⟩
  · rw [field_step_finrank, field_step_finrank]
    exact Nat.lt_succ_self i.val
  · intro S hleft hright
    have h₁ := Submodule.finrank_lt_finrank_of_lt hleft
    have h₂ := Submodule.finrank_lt_finrank_of_lt hright
    rw [field_step_finrank] at h₁ h₂
    simp only [Fin.val_castSucc, Fin.val_succ] at h₁ h₂
    omega

/-- Recover the existing field flag from the ring incidence model. -/
def toFieldFlag (F : RingFlag K (CoordinateSpace K n) n) : CompleteFlag K n where
  step j := (F.step j).toSubmodule
  step_zero := F.step_zero
  step_last := F.step_last
  step_covBy := field_step_covBy F

@[simp] theorem toFieldFlag_step (F : RingFlag K (CoordinateSpace K n) n)
    (j : Fin (n + 1)) : (toFieldFlag F).step j = (F.step j).toSubmodule := rfl

@[simp] theorem toFieldFlag_ofFieldFlag (F : CompleteFlag K n) :
    toFieldFlag (ofFieldFlag F) = F := by
  apply FieldFlags.flag_ext
  rfl

@[simp] theorem ofFieldFlag_toFieldFlag (F : RingFlag K (CoordinateSpace K n) n) :
    ofFieldFlag (toFieldFlag F) = F := by
  ext j
  rfl

/-- The two definitions of field-valued flags agree on their steps. -/
noncomputable def fieldEquiv :
    RingFlag K (CoordinateSpace K n) n ≃ CompleteFlag K n where
  toFun := toFieldFlag
  invFun := ofFieldFlag
  left_inv := ofFieldFlag_toFieldFlag
  right_inv := toFieldFlag_ofFieldFlag

end Field
end RingFlag
end FlagVarieties.Foundations
