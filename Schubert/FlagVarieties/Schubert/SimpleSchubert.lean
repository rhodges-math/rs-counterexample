import Schubert.FlagVarieties.Schubert.AllRings
import Schubert.FlagVarieties.Schubert.ParabolicOrbit
import Schubert.FlagVarieties.Schubert.ProjectiveLineCharts
import Schubert.FlagVarieties.Flag.QuotientClosed
import Schubert.FlagVarieties.LineBundle.SectionsAsSemiInvariants

/-!
# `X_{sᵢ} = Pᵢ / B ≅ ℙ¹`

For a simple reflection `sᵢ` (`i + 1 < n`) and every commutative ring `R`:

* `FlagVarieties.preimageIdeal_simpleSchubert`: `π⁻¹(X_{sᵢ}) = Pᵢ`;
* `FlagVarieties.simpleSchubertToLine R n i hi : X_{sᵢ} ⟶ ℙ¹`, `gB ↦ [g_{ii} : g_{i+1,i}]`, induced
  (`X_{sᵢ} = Pᵢ / B`, `FlagVarieties.isColimitPreimageProj`) by the `B`-invariant morphism
  `Pᵢ ⟶ ℙ¹` given by the `i`-th column (`FlagVarieties.parabolicToLine`);
* `FlagVarieties.lineChartSection R n i hi k : Spec R[X₀,X₁]_{(X_k)} ⟶ X_{sᵢ}`, the sections over
  the two standard charts of `ℙ¹`, with `lineChartSection_toLine`.
-/

noncomputable section

namespace FlagVarieties

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Foundations.ProjectiveLine ProjectiveLineCharts
open scoped TensorProduct

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ### `fromPair` and semi-invariant pairs -/

section General

variable {R : Type u} [CommRing R] {n : ℕ}

theorem fromPair_congr {X : Scheme.{u}} {φ φ' : R →+* Γ(X, ⊤)} {δ δ' ε ε' : Γ(X, ⊤)}
    (h1 : φ = φ') (h2 : δ = δ') (h3 : ε = ε') (h : IsCoprime δ ε) (h' : IsCoprime δ' ε') :
    fromPair φ δ ε h = fromPair φ' δ' ε' h' := by
  subst h1 h2 h3
  rfl

/-- **A pair of semi-invariant functions of the same weight defines a `B`-invariant morphism to
`ℙ¹`.** -/
theorem fromPair_act_eq {T : Scheme.{u}} (E : BorelAction R n T) (φ : R →+* Γ(E.P, ⊤))
    (δ ε : Γ(E.P, ⊤)) (h : IsCoprime δ ε) (η : Fin n → ℤ)
    (hφ : ∀ r, E.act.appTop (φ r) = E.actionFst.appTop (φ r))
    (hδ : E.act.appTop δ = E.twist η * E.actionFst.appTop δ)
    (hε : E.act.appTop ε = E.twist η * E.actionFst.appTop ε) :
    E.act ≫ fromPair φ δ ε h = E.actionFst ≫ fromPair φ δ ε h := by
  rw [fromPair_naturality, fromPair_naturality]
  let u := (E.isUnit_twist η).unit
  have hu : (u : Γ(E.actionDomain, ⊤)) = E.twist η := IsUnit.unit_spec _
  have hcop := isCoprime_unit_scale _ _ (h.map E.actionFst.appTop.hom) u
  refine (fromPair_congr (φ' := E.actionFst.appTop.hom.comp φ)
    (δ' := (u : Γ(E.actionDomain, ⊤)) * E.actionFst.appTop δ)
        (ε' := (u : Γ(E.actionDomain, ⊤)) * E.actionFst.appTop ε)
    (RingHom.ext fun r => hφ r) (hδ.trans (by rw [hu])) (hε.trans (by rw [hu])) _ hcop).trans ?_
  exact fromPair_unit_mul _ _ _ (h.map E.actionFst.appTop.hom) u

variable (R n)

theorem rightCoactionMod_genericMatrix {J : Ideal (GLCoord R n)} (r c : Fin n)
    (hJ : ∀ k : Fin n, k < c → genericMatrix R n r k ∈ J) :
    rightCoactionMod R n J (genericMatrix R n r c) =
      Ideal.Quotient.mk J (genericMatrix R n r c) ⊗ₜ borelMatrix R n c c := by
  have h := congrFun (congrFun (map_rightCoaction_genericMatrix R n) r) c
  simp only [Matrix.map_apply, Matrix.mul_apply] at h
  rw [rightCoactionMod, AlgHom.comp_apply, h, map_sum, Finset.sum_eq_single c]
  · rw [Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, Algebra.TensorProduct.map_tmul]
    rfl
  · intro k _ hk
    rw [Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, Algebra.TensorProduct.map_tmul]
    rcases lt_or_gt_of_ne hk with hlt | hgt
    · change Ideal.Quotient.mk J _ ⊗ₜ _ = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr (hJ k hlt), TensorProduct.zero_tmul]
    · change _ ⊗ₜ borelMatrix R n k c = 0
      rw [borelMatrix_blockTriangular R n hgt, TensorProduct.tmul_zero]
  · intro hc
    exact absurd (Finset.mem_univ c) hc

theorem inv_borelCharacterUnit_neg_single (c : Fin n) :
    (((borelCharacterUnit R n (-Pi.single c 1))⁻¹ : (BorelCoord R n)ˣ) : BorelCoord R n) =
      borelMatrix R n c c := by
  rw [borelCharacterUnit_neg, inv_inv, borelCharacterUnit, Finset.prod_eq_single c]
  · rw [Pi.single_eq_same, zpow_one]
    rfl
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj, zpow_zero]
  · intro hc
    exact absurd (Finset.mem_univ c) hc

/-- A column entry `x_{rc}` whose row vanishes to the left of `c` is semi-invariant of weight
`-e_c`. -/
theorem semiInvariantDefect_genericMatrix {J : Ideal (GLCoord R n)} (r c : Fin n)
    (hJ : ∀ k : Fin n, k < c → genericMatrix R n r k ∈ J) :
    semiInvariantDefect R n J (-Pi.single c 1) (genericMatrix R n r c) = 0 := by
  rw [semiInvariantDefect_apply, rightCoactionMod_genericMatrix R n r c hJ,
    inv_borelCharacterUnit_neg_single, sub_self]

theorem semiInvariantDefect_algebraMap (J : Ideal (GLCoord R n)) (r : R) :
    semiInvariantDefect R n J 0 (algebraMap R (GLCoord R n) r) = 0 := by
  rw [semiInvariantDefect_apply, AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply,
    borelCharacterUnit_zero, inv_one, Units.val_one, Ideal.Quotient.mk_algebraMap, sub_self]

end General

/-! ### `X_{sᵢ}` and `π⁻¹(X_{sᵢ}) = Pᵢ` -/

variable (R : Type u) [CommRing R] (n : ℕ) (i : ℕ) (hi : i + 1 < n)

/-- The Schubert variety `X_{sᵢ}` of a simple reflection. -/
abbrev simpleSchubert : (FlagScheme R n).IdealSheafData :=
  schubertVariety R n (simpleReflection n i hi)

/-- **`π⁻¹(X_{sᵢ}) = Pᵢ`.** -/
theorem preimageIdeal_simpleSchubert :
    preimageIdeal R n (simpleSchubert R n i hi) = parabolicIdeal R n i := by
  rw [simpleSchubert, preimageIdeal_schubertVariety_commRing, schubertOrbitIdeal_simpleReflection]

/-- The row `i`. -/
abbrev rowA : Fin n := ⟨i, by omega⟩

/-- The row `i + 1`. -/
abbrev rowB : Fin n := ⟨i + 1, hi⟩

theorem genericMatrix_mem_preimageIdeal (r c : Fin n)
    (h : parabolicBlock n i c < parabolicBlock n i r) :
    genericMatrix R n r c ∈ preimageIdeal R n (simpleSchubert R n i hi) := by
  rw [preimageIdeal_simpleSchubert]
  exact Ideal.subset_span ⟨⟨(r, c), h⟩, rfl⟩

/-! ### The morphism `Pᵢ ⟶ ℙ¹`, `p ↦ [p_{ii} : p_{i+1,i}]` -/

/-- The entry `p_{ii}` on `π⁻¹(X_{sᵢ}) = Pᵢ`. -/
abbrev lineCoordA : Γ(preimageScheme R n (simpleSchubert R n i hi), ⊤) :=
  preimageRestrictSections R n _ (genericMatrix R n (rowA n i hi) (rowA n i hi))

/-- The entry `p_{i+1,i}` on `π⁻¹(X_{sᵢ}) = Pᵢ`. -/
abbrev lineCoordB : Γ(preimageScheme R n (simpleSchubert R n i hi), ⊤) :=
  preimageRestrictSections R n _ (genericMatrix R n (rowB n i hi) (rowA n i hi))

/-- The structure map `R → Γ(Pᵢ)`. -/
abbrev lineStructure : R →+* Γ(preimageScheme R n (simpleSchubert R n i hi), ⊤) :=
  (preimageRestrictSections R n _).comp (algebraMap R (GLCoord R n))

theorem isCoprime_lineCoord : IsCoprime (lineCoordA R n i hi) (lineCoordB R n i hi) := by
  have h := isCoprime_mk_parabolic R n i hi (J := preimageIdeal R n (simpleSchubert R n i hi))
    (by rw [preimageIdeal_simpleSchubert])
  exact h.map (preimageQuotEquiv R n _).toRingHom

/-- **`Pᵢ ⟶ ℙ¹`, `p ↦ [p_{ii} : p_{i+1,i}]`.** -/
def parabolicToLine : preimageScheme R n (simpleSchubert R n i hi) ⟶ scheme R :=
  fromPair (lineStructure R n i hi) (lineCoordA R n i hi) (lineCoordB R n i hi)
    (isCoprime_lineCoord R n i hi)

theorem lineCoord_isSemiInvariant (r : Fin n) (hr : r = rowA n i hi ∨ r = rowB n i hi) :
    (preimageAction R n (simpleSchubert R n i hi)).act.appTop
        (preimageRestrictSections R n _ (genericMatrix R n r (rowA n i hi))) =
      (preimageAction R n _).twist (-Pi.single (rowA n i hi) 1) *
        (preimageAction R n _).actionFst.appTop
          (preimageRestrictSections R n _ (genericMatrix R n r (rowA n i hi))) := by
  refine (BorelAction.isSemiInvariant_top_iff _ _ _).mp
    ((isSemiInvariant_preimageRestrictSections_iff R n _ _ _).mpr ?_)
  apply semiInvariantDefect_genericMatrix
  intro k hk
  apply genericMatrix_mem_preimageIdeal
  rw [parabolicBlock_lt_iff]
  have hk' : k.val < i := hk
  rcases hr with rfl | rfl
  · exact ⟨hk', by simp⟩
  · exact ⟨by simp; omega, by simp; omega⟩

theorem lineStructure_isSemiInvariant (r : R) :
    (preimageAction R n (simpleSchubert R n i hi)).act.appTop (lineStructure R n i hi r) =
      (preimageAction R n _).actionFst.appTop (lineStructure R n i hi r) := by
  have h := (BorelAction.isSemiInvariant_top_iff (preimageAction R n (simpleSchubert R n i hi)) 0
    (lineStructure R n i hi r)).mp
    ((isSemiInvariant_preimageRestrictSections_iff R n _ 0 _).mpr
      (semiInvariantDefect_algebraMap R n _ r))
  rw [h]
  have h1 : (preimageAction R n (simpleSchubert R n i hi)).twist 0 = 1 := by
    rw [BorelAction.twist, borelCharacterUnit_zero, inv_one, Units.val_one, map_one, map_one]
  rw [h1, one_mul]

/-- **`Pᵢ ⟶ ℙ¹` is `B`-invariant.** -/
theorem parabolicToLine_act :
    preimageAct R n (simpleSchubert R n i hi) ≫ parabolicToLine R n i hi =
      pullback.fst _ _ ≫ parabolicToLine R n i hi :=
  fromPair_act_eq (preimageAction R n _) _ _ _ _ (-Pi.single (rowA n i hi) 1)
    (lineStructure_isSemiInvariant R n i hi)
    (lineCoord_isSemiInvariant R n i hi _ (Or.inl rfl))
    (lineCoord_isSemiInvariant R n i hi _ (Or.inr rfl))

/-- **`X_{sᵢ} = Pᵢ / B ⟶ ℙ¹`**, `gB ↦ [g_{ii} : g_{i+1,i}]`. -/
def simpleSchubertToLine : (simpleSchubert R n i hi).subscheme ⟶ scheme R :=
  preimageDesc (parabolicToLine R n i hi) (parabolicToLine_act R n i hi)

@[reassoc] theorem preimageProj_simpleSchubertToLine :
    preimageProj R n (simpleSchubert R n i hi) ≫ simpleSchubertToLine R n i hi =
      parabolicToLine R n i hi :=
  preimageProj_preimageDesc _ _

end FlagVarieties
