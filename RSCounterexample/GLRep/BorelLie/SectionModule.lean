import RSCounterexample.GLRep.BorelLie.BModule
import RSCounterexample.FlagVarieties.Modules.BModuleModel

/-!
# The section modules through the functor `toBModule`

The `BModule` `FlagVarieties.sectionBModule m hS` (the section module `H⁰(X_S, 𝓛(−λ))` of the
ring model, with the `𝔫⁺`-action transported from the Demazure library's model) is the `BModule`
attached by `GLRep.IsRationalBorelRep.toBModule` to the rational `B`-representation on
`H⁰(X_S, 𝓛(−λ))`:

* `sectionBModule_nil_eq`: the two `𝔫⁺`-actions are equal (they agree on the root vectors);
* **`sectionBModuleIsoToBModule`**: the identity map is an isomorphism of `BModule`s
  `sectionBModule m hS ≃ᴮ (isRationalBorelRep_sectionRep hS _).toBModule`;
* `toBModuleIsoDual`: hence, composing with `sectionBModuleIso`, the functor sends
  `H⁰(X_S, 𝓛(−λ))` to a `B`-module isomorphic to `(demazureUnionModule m S)^∨`.
-/

namespace GLRep

open Module Demazure.FlagModule Demazure.BModules Demazure.SchubertUnions
  Demazure.Filtrations Demazure.HighestWeight
open FlagVarieties FlagVarieties.PointModel.Complex FlagVarieties.SectionRep

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : ℕ} {m : ColumnShape n} {S : Finset (Equiv.Perm (Fin n))} (hS : BruhatLower S)

/-- The rational `B`-representation on `H⁰(X_S, 𝓛(−λ))`, `λ = shapeWeightZ m`. -/
abbrev sectionIsRational (m : ColumnShape n) :
    IsRationalBorelRep (sectionRep S (-shapeWeightZ m)) :=
  isRationalBorelRep_sectionRep hS (isAntidominant_neg_shapeWeightZ m)

/-- The `𝔫⁺`-action on the section module is the one of the functor `toBModule`. -/
theorem sectionBModule_nil_eq (X : upperNilpotent n)
    (v : (sectionSubrep S (-shapeWeightZ m)).toSubmodule) :
    (sectionBModule m hS).nil X v = (sectionIsRational hS m).toBModule.nil X v := by
  have h : (sectionBModule m hS).nil.toLinearMap =
      ((sectionIsRational hS m).toBModule.nil.toLinearMap :
        upperNilpotent n →ₗ[ℂ] Module.End ℂ (sectionSubrep S (-shapeWeightZ m)).toSubmodule) := by
    apply upperNilpotent_linearMap_ext
    intro r
    refine LinearMap.ext fun v => ?_
    change (sectionBModule m hS).nil (rootVector r) v =
      (sectionIsRational hS m).toBModule.nil (rootVector r) v
    obtain ⟨⟨a, b⟩, hab⟩ := r
    exact (sectionBModule_nil_rootVector hS hab v).trans
      ((sectionIsRational hS m).toBModule_nil_rootVector ⟨(a, b), hab⟩ v).symm
  exact LinearMap.congr_fun (LinearMap.congr_fun h X) v

/-- **The section `B`-module is the image of `H⁰(X_S, 𝓛(−λ))` under the functor `toBModule`**:
the identity map is an isomorphism of `BModule`s. -/
def sectionBModuleIsoToBModule :
    sectionBModule m hS ≃ᴮ (sectionIsRational hS m).toBModule where
  toLinearEquiv := LinearEquiv.refl ℂ _
  map_nil X v := sectionBModule_nil_eq hS X v
  map_torus _ _ := rfl

/-- **The functor `toBModule` sends `H⁰(X_S, 𝓛(−λ))` to `(demazureUnionModule m S)^∨`.** -/
def toBModuleIsoDual :
    (sectionIsRational hS m).toBModule ≃ᴮ (demazureUnionModule m S).dual :=
  (sectionBModuleIsoToBModule hS).symm.trans (sectionBModuleIso hS)

end

end GLRep
