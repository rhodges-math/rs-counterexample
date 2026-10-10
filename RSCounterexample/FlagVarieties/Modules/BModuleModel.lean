import RSCounterexample.FlagVarieties.Modules.FlagModel
import RSCounterexample.GLRep.Borel.BorelLieDual
import RSCounterexample.Demazure.Filtrations.SectionModules

/-!
# The explicit isomorphism with the `B`-module model

The `Demazure` library models the section modules by `B`-modules in the sense of
`Demazure.BModules.BModule` (a torus action and an action of `𝔫⁺`): the dual of the Demazure
union `demazureUnionModule m S` (`Demazure.Filtrations.sectionModuleOf`). This file identifies
it with the section module `H⁰(X_S, 𝓛(−λ))` of the ring model, with the torus acting through `B`
and `𝔫⁺` acting through the differentials of the `B`-action
(`GLRep.IsRationalBorelRep.borelLie`):

* in the flag-minor model, the differential of `u_ab(t) = 1 + tE_ab` is the matrix-unit
  derivation `E_ab` (`FlagVarieties.coe_borelLie_flagModel`);
* on the Demazure module `D_S` it is the action of the root vector on `demazureUnion m S`
  (`FlagVarieties.demazureUnionEquiv_borelLie`), and the torus actions agree
  (`FlagVarieties.demazureUnionEquiv_torus`);
* dually, **`H⁰(X_S, 𝓛(−λ)) ≃ (demazureUnionModule m S)^∨`**
  (`FlagVarieties.sectionEquivDemazureUnionDual`) intertwines the torus actions
  (`FlagVarieties.sectionEquivDemazureUnionDual_torus`) and sends the differential `D_ab` to the
  contragredient action of the root vector `E_ab`
  (`FlagVarieties.sectionEquivDemazureUnionDual_borelLie`).

There is no hypothesis: `Γ(X_w, 𝒪) = ℂ` is `globalSectionsConstant_complex`.
-/

open Schubert GLRep TauCeti Module Demazure.FlagModule Demazure.HighestWeight
  Demazure.SchubertUnions Demazure.Filtrations Demazure.BModules FinPermutation

namespace FlagVarieties

open PointModel.Complex SectionRep

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : ℕ} {a b : Fin n}

/-! ### The differential in the flag-minor model -/

theorem rationalBorel_flagModel (m : ColumnShape n) :
    IsRationalBorelRep ((flagOrbitRepresentation m).comp (borel ℂ n).subtype) :=
  (isRationalRep_flagOrbitRepresentation m).restrictBorel

theorem transvection_eq_one_add_smul (t : ℂ) :
    Matrix.transvection a b t = 1 + t • Matrix.single a b (1 : ℂ) := by
  rw [Matrix.transvection, Matrix.smul_single, smul_eq_mul, mul_one]

/-- **In the flag-minor model, `D_ab` is the matrix-unit derivation `E_ab`.** -/
theorem coe_borelLie_flagModel (m : ColumnShape n) (hab : a < b) (p : flagOrbitSpan m) :
    (((rationalBorel_flagModel m).borelLie hab p : flagOrbitSpan m) : MatrixPolynomial n) =
      matrixUnitDerivation a b p := by
  have key := (rationalBorel_flagModel m).borelLie_apply_eq_of_forall hab
    (flagOrbitSpan m).subtype p (N := (rootSubstitution a b (p : MatrixPolynomial n)).natDegree + 2)
    (by omega) (fun k => (rootSubstitution a b (p : MatrixPolynomial n)).coeff k)
    (fun t => by
      change polynomialGL n (transvectionGL hab.ne t) (p : MatrixPolynomial n) = _
      change rowAction ((transvectionGL hab.ne t : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)
        (p : MatrixPolynomial n) = _
      rw [coe_transvectionGL, transvection_eq_one_add_smul, ← rootSubstitution_eval,
        Polynomial.eval_eq_sum_range'
          (n := (rootSubstitution a b (p : MatrixPolynomial n)).natDegree + 2) (by omega)]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← map_pow, mul_comm, ← MvPolynomial.smul_eq_C_mul])
  rw [Submodule.subtype_apply] at key
  rw [key]
  have h1 := rootSubstitution_coeff a b hab.ne (p : MatrixPolynomial n) 1
  rw [Nat.factorial_one, one_smul, derivationIter_succ, derivationIter_zero] at h1
  exact h1

/-! ### The Demazure module and the Demazure union -/

variable (m : ColumnShape n) (S : Finset (Equiv.Perm (Fin n)))

/-- The Demazure module `D_S` of the flag-minor model, a subrepresentation of `B`. -/
abbrev flagDemazureSubrep :=
  demazureSubrep (flagOrbitRepresentation m) (highestFlagVec m) S

/-- A shortcut instance (the generic search through `Subrepresentation` is slow). -/
instance : AddCommGroup (flagDemazureSubrep m S).toSubmodule := Submodule.addCommGroup _

theorem rationalBorel_flagDemazure :
    IsRationalBorelRep (flagDemazureSubrep m S).toRepresentation :=
  HasCoeffsIn.subrepresentation (rationalBorel_flagModel m) (flagDemazureSubrep m S)

/-- `D_S` is `demazureUnion m S`. -/
def demazureUnionEquiv :
    (flagDemazureSubrep m S).toSubmodule ≃ₗ[ℂ] demazureUnionModule m S :=
  (Submodule.equivMapOfInjective (flagOrbitSpan m).subtype Subtype.val_injective _).trans
    (LinearEquiv.ofEq _ _ (map_demazureSubrep_flagModel m S))

theorem coe_demazureUnionEquiv (u : (flagDemazureSubrep m S).toSubmodule) :
    (show ↥(demazureUnion m S) from demazureUnionEquiv m S u).val =
      ((u : flagOrbitSpan m) : MatrixPolynomial n) :=
  rfl

/-- The torus actions agree. -/
theorem demazureUnionEquiv_torus (t : Fin n → ℂˣ) (u : (flagDemazureSubrep m S).toSubmodule) :
    demazureUnionEquiv m S ((flagDemazureSubrep m S).toRepresentation (borelTorus ℂ n t) u) =
      (demazureUnionModule m S).torus t (demazureUnionEquiv m S u) :=
  rfl

/-- **The differential `D_ab` on `D_S` is the action of the root vector `E_ab`.** -/
theorem demazureUnionEquiv_borelLie (hab : a < b) (u : (flagDemazureSubrep m S).toSubmodule) :
    demazureUnionEquiv m S ((rationalBorel_flagDemazure m S).borelLie hab u) =
      (demazureUnionModule m S).nil (rootVector ⟨(a, b), hab⟩) (demazureUnionEquiv m S u) := by
  have h1 := coe_borelLie_flagModel m hab (u : flagOrbitSpan m)
  have h2 := (rationalBorel_flagModel m).subtype_borelLie (flagDemazureSubrep m S) hab u
  apply Subtype.ext (p := fun x => x ∈ demazureUnion m S)
  change (((rationalBorel_flagDemazure m S).borelLie hab u : flagOrbitSpan m) :
      MatrixPolynomial n) = matrixUnitDerivation a b ((u : flagOrbitSpan m) : MatrixPolynomial n)
  rw [← h1, ← h2]

/-! ### Duals -/

/-- The dual identification `D_S^∨ ≃ demazureUnion(m, S)^∨`. -/
def demazureUnionDualEquiv :
    Module.Dual ℂ (flagDemazureSubrep m S).toSubmodule ≃ₗ[ℂ] (demazureUnionModule m S).dual :=
  (demazureUnionEquiv m S).symm.dualMap

theorem demazureUnionDualEquiv_apply (φ : Module.Dual ℂ (flagDemazureSubrep m S).toSubmodule)
    (x : demazureUnionModule m S) :
    (show Module.Dual ℂ (demazureUnionModule m S) from demazureUnionDualEquiv m S φ) x =
      φ ((demazureUnionEquiv m S).symm x) :=
  rfl

theorem demazureUnionEquiv_symm_torus (t : Fin n → ℂˣ) (x : demazureUnionModule m S) :
    (demazureUnionEquiv m S).symm ((demazureUnionModule m S).torus t x) =
      (flagDemazureSubrep m S).toRepresentation (borelTorus ℂ n t)
        ((demazureUnionEquiv m S).symm x) := by
  rw [LinearEquiv.symm_apply_eq, demazureUnionEquiv_torus, LinearEquiv.apply_symm_apply]

theorem demazureUnionEquiv_symm_nil (hab : a < b) (x : demazureUnionModule m S) :
    (demazureUnionEquiv m S).symm ((demazureUnionModule m S).nil (rootVector ⟨(a, b), hab⟩) x) =
      (rationalBorel_flagDemazure m S).borelLie hab ((demazureUnionEquiv m S).symm x) := by
  rw [LinearEquiv.symm_apply_eq, demazureUnionEquiv_borelLie, LinearEquiv.apply_symm_apply]

theorem demazureUnionDualEquiv_torus (t : Fin n → ℂˣ)
    (φ : Module.Dual ℂ (flagDemazureSubrep m S).toSubmodule) :
    demazureUnionDualEquiv m S
        ((flagDemazureSubrep m S).toRepresentation.dual (borelTorus ℂ n t) φ) =
      (demazureUnionModule m S).dual.torus t (demazureUnionDualEquiv m S φ) := by
  refine LinearMap.ext fun x => ?_
  change φ ((flagDemazureSubrep m S).toRepresentation ((borelTorus ℂ n t)⁻¹ : borel ℂ n)
      ((demazureUnionEquiv m S).symm x)) =
    φ ((demazureUnionEquiv m S).symm ((demazureUnionModule m S).torus t⁻¹ x))
  rw [demazureUnionEquiv_symm_torus, map_inv (borelTorus ℂ n)]

theorem demazureUnionDualEquiv_borelLie (hab : a < b)
    (φ : Module.Dual ℂ (flagDemazureSubrep m S).toSubmodule) :
    demazureUnionDualEquiv m S (((rationalBorel_flagDemazure m S).dual).borelLie hab φ) =
      (demazureUnionModule m S).dual.nil (rootVector ⟨(a, b), hab⟩)
        (demazureUnionDualEquiv m S φ) := by
  refine LinearMap.ext fun x => ?_
  change ((rationalBorel_flagDemazure m S).dual.borelLie hab φ)
      ((demazureUnionEquiv m S).symm x) =
    -(φ ((demazureUnionEquiv m S).symm
      ((demazureUnionModule m S).nil (rootVector ⟨(a, b), hab⟩) x)))
  rw [(rationalBorel_flagDemazure m S).borelLie_dual_apply, demazureUnionEquiv_symm_nil]
  rfl

/-! ### Sections: the explicit isomorphism -/

theorem isAntidominant_neg_shapeWeightZ : IsAntidominant (-shapeWeightZ m) := fun i j hij => by
  show -(shapeWeight m i : ℤ) ≤ -(shapeWeight m j : ℤ)
  exact neg_le_neg (by exact_mod_cast shapeWeight_antitone m hij)

variable {m S}
variable (hS : BruhatLower S)

/-- **`H⁰(X_S, 𝓛(−λ)) ≃ (demazureUnionModule m S)^∨`**, the `B`-module model of the section
module. -/
def sectionEquivDemazureUnionDual :
    (sectionSubrep S (-shapeWeightZ m)).toSubmodule ≃ₗ[ℂ] (demazureUnionModule m S).dual :=
  (flagModelSectionEquiv m hS).toLinearEquiv.symm.trans (demazureUnionDualEquiv m S)

theorem sectionEquivDemazureUnionDual_apply (s : (sectionSubrep S (-shapeWeightZ m)).toSubmodule) :
    sectionEquivDemazureUnionDual hS s =
      demazureUnionDualEquiv m S ((flagModelSectionEquiv m hS).toLinearEquiv.symm s) :=
  rfl

theorem flagModelSectionEquiv_symm_apply (g : borel ℂ n)
    (s : (sectionSubrep S (-shapeWeightZ m)).toSubmodule) :
    (flagModelSectionEquiv m hS).toLinearEquiv.symm (sectionRep S (-shapeWeightZ m) g s) =
      (flagDemazureSubrep m S).toRepresentation.dual g
        ((flagModelSectionEquiv m hS).toLinearEquiv.symm s) :=
  (flagModelSectionEquiv m hS).symm.toIntertwiningMap.isIntertwining _ _ g s

/-- **The torus actions correspond.** -/
theorem sectionEquivDemazureUnionDual_torus (t : Fin n → ℂˣ)
    (s : (sectionSubrep S (-shapeWeightZ m)).toSubmodule) :
    sectionEquivDemazureUnionDual hS (sectionRep S (-shapeWeightZ m) (borelTorus ℂ n t) s) =
      (demazureUnionModule m S).dual.torus t (sectionEquivDemazureUnionDual hS s) := by
  rw [sectionEquivDemazureUnionDual_apply, flagModelSectionEquiv_symm_apply,
      demazureUnionDualEquiv_torus]
  rfl

/-- **The differential `D_ab` of the `B`-action on `H⁰(X_S, 𝓛(−λ))` is the contragredient action
of the root vector `E_ab`.** -/
theorem sectionEquivDemazureUnionDual_borelLie (hab : a < b)
    (s : (sectionSubrep S (-shapeWeightZ m)).toSubmodule) :
    sectionEquivDemazureUnionDual hS
        ((isRationalBorelRep_sectionRep hS (isAntidominant_neg_shapeWeightZ m)).borelLie
          hab s) =
      (demazureUnionModule m S).dual.nil (rootVector ⟨(a, b), hab⟩)
        (sectionEquivDemazureUnionDual hS s) := by
  have hnat := (isRationalBorelRep_sectionRep hS
    (isAntidominant_neg_shapeWeightZ m)).borelLie_comp_of_intertwining
    (rationalBorel_flagDemazure m S).dual hab
    (flagModelSectionEquiv m hS).toLinearEquiv.symm.toLinearMap
    (fun g s => flagModelSectionEquiv_symm_apply hS g s) s
  rw [sectionEquivDemazureUnionDual_apply, LinearEquiv.coe_coe] at *
  rw [hnat, demazureUnionDualEquiv_borelLie]
  rfl

/-! ### The `B`-module structure on the sections -/

theorem sectionEquivDemazureUnionDual_symm_torus (t : Fin n → ℂˣ)
    (x : (demazureUnionModule m S).dual) :
    (sectionEquivDemazureUnionDual hS).symm ((demazureUnionModule m S).dual.torus t x) =
      sectionRep S (-shapeWeightZ m) (borelTorus ℂ n t)
          ((sectionEquivDemazureUnionDual hS).symm x) := by
  rw [LinearEquiv.symm_apply_eq, sectionEquivDemazureUnionDual_torus, LinearEquiv.apply_symm_apply]

variable (m) in
/-- **The section module `H⁰(X_S, 𝓛(−λ))` as a `B`-module** (`Demazure.BModules.BModule`): the
torus acts through `B`, and
`𝔫⁺` acts so that `E_ab` acts by the differential `D_ab` of the `B`-action
(`FlagVarieties.sectionBModule_nil_rootVector`). -/
def sectionBModule : BModule n where
  carrier := (sectionSubrep S (-shapeWeightZ m)).toSubmodule
  instFiniteDimensional :=
    finiteDimensional_sectionRep_of_isAntidominant hS (isAntidominant_neg_shapeWeightZ m)
  nil := (sectionEquivDemazureUnionDual (m := m) hS).symm.lieConj.toLieHom.comp
    (demazureUnionModule m S).dual.nil
  torus := (sectionRep S (-shapeWeightZ m)).comp (borelTorus ℂ n)
  torus_nil t X v := by
    change sectionRep S (-shapeWeightZ m) (borelTorus ℂ n t)
        ((sectionEquivDemazureUnionDual (m := m) hS).symm ((demazureUnionModule m S).dual.nil X
          (sectionEquivDemazureUnionDual (m := m) hS v))) =
      (sectionEquivDemazureUnionDual (m := m) hS).symm
          ((demazureUnionModule m S).dual.nil (torusLie t X)
        (sectionEquivDemazureUnionDual (m := m) hS
            (sectionRep S (-shapeWeightZ m) (borelTorus ℂ n t) v)))
    rw [← sectionEquivDemazureUnionDual_symm_torus, sectionEquivDemazureUnionDual_torus,
        (demazureUnionModule m S).dual.torus_nil]
  weightDiagonal := by
    have hw : ∀ μ, Demazure.FlagModule.torusWeightSpace
        ((sectionRep S (-shapeWeightZ m)).comp (borelTorus ℂ n)) μ =
        (Demazure.FlagModule.torusWeightSpace (demazureUnionModule m S).dual.torus μ).map
          (sectionEquivDemazureUnionDual (m := m) hS).symm.toLinearMap := by
      intro μ
      ext x
      constructor
      · intro hx
        refine ⟨sectionEquivDemazureUnionDual (m := m) hS x, fun t => ?_,
          (sectionEquivDemazureUnionDual (m := m) hS).symm_apply_apply x⟩
        rw [← sectionEquivDemazureUnionDual_torus]
        have := hx t
        change sectionRep S (-shapeWeightZ m) (borelTorus ℂ n t) x = _ at this
        rw [this, LinearEquiv.map_smul]
      · rintro ⟨y, hy, rfl⟩ t
        change sectionRep S (-shapeWeightZ m) (borelTorus ℂ n t)
          ((sectionEquivDemazureUnionDual (m := m) hS).symm y) = _
        rw [← sectionEquivDemazureUnionDual_symm_torus, hy t, LinearEquiv.map_smul]
        rfl
    have htop := (demazureUnionModule m S).dual.weightDiagonal
    simp only [IsWeightDiagonal, hw, ← Submodule.map_iSup]
    rw [htop, Submodule.map_top, LinearEquiv.range]

theorem sectionBModule_nil_apply (X : Demazure.FlagModule.upperNilpotent n)
    (v : (sectionSubrep S (-shapeWeightZ m)).toSubmodule) :
    (sectionBModule m hS).nil X v =
      (sectionEquivDemazureUnionDual hS).symm ((demazureUnionModule m S).dual.nil X
        (sectionEquivDemazureUnionDual hS v)) :=
  rfl

/-- **The explicit isomorphism with the `B`-module model**:
`H⁰(X_S, 𝓛(−λ)) ≅ (demazureUnionModule m S)^∨` as `B`-modules. -/
def sectionBModuleIso : sectionBModule m hS ≃ᴮ (demazureUnionModule m S).dual where
  toLinearEquiv := sectionEquivDemazureUnionDual hS
  map_nil X v := by
    change sectionEquivDemazureUnionDual hS ((sectionEquivDemazureUnionDual hS).symm
      ((demazureUnionModule m S).dual.nil X (sectionEquivDemazureUnionDual hS v))) = _
    exact LinearEquiv.apply_symm_apply _ _
  map_torus t v := sectionEquivDemazureUnionDual_torus hS t v

/-- In `sectionBModule`, the root vector `E_ab` acts by the differential `D_ab` of the action of
`B`. -/
theorem sectionBModule_nil_rootVector (hab : a < b)
    (s : (sectionSubrep S (-shapeWeightZ m)).toSubmodule) :
    (sectionBModule m hS).nil (rootVector ⟨(a, b), hab⟩) s =
      (isRationalBorelRep_sectionRep hS (isAntidominant_neg_shapeWeightZ m)).borelLie
        hab s := by
  rw [sectionBModule_nil_apply, ← sectionEquivDemazureUnionDual_borelLie,
      LinearEquiv.symm_apply_apply]

theorem sectionBModule_torus (t : Fin n → ℂˣ) :
    ((sectionBModule m hS).torus t :
        Module.End ℂ (sectionSubrep S (-shapeWeightZ m)).toSubmodule) =
      sectionRep S (-shapeWeightZ m) (borelTorus ℂ n t) :=
  rfl

end

end FlagVarieties
