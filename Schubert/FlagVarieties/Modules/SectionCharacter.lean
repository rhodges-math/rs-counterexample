import Schubert.FlagVarieties.PointModel.Complex.SectionBasis
import Schubert.FlagVarieties.Modules.RingModel
import Schubert.Demazure.Filtrations.SchubertLayerCharacters
import Schubert.FlagVarieties.Schubert.GlobalSectionsRingForm

/-!
# Characters of the section modules over Schubert unions

For a Bruhat ideal `S` and a dominant weight `λ` (the shape of a column sequence `h`), the ring
model `sectionSpace S λ` (`FlagVarieties.PointModel.Complex.sectionSpace`: semi-invariants of weight
`λ` in the sign convention of `PointModel.Complex`, modulo the orbit ideal) is the space of sections
`sectionRep S (−λ)`
(`FlagVarieties.SectionRep.sectionSpaceEquiv`). Transporting the standard-monomial basis
(`FlagVarieties.PointModel.Complex.sectionBasisOfGlobalSectionsConstant`, indexed by
`chainSet h S`), whose vectors are weight vectors of weight minus the row content
(`FlagVarieties.SectionRep.sectionRep_borelTorus_basis`), gives the character

  `ch H⁰(X_S, 𝓛(−λ)) = ∑_{T ∈ chainSet h S} x^{wt T}`
  (`FlagVarieties.SectionRep.ch_sectionRep_neg`),

which is the sum of the atoms `𝒜_{τλ}` over `τ ∈ S ∩ W^λ`
(`FlagVarieties.SectionRep.ch_sectionRep_neg_eq_sum_atom`). The basis uses the equality
`Γ(X_w, 𝒪) = ℂ` (`FlagVarieties.PointModel.Complex.GlobalSectionsConstant`), proved in
(`FlagVarieties.globalSectionsConstant_complex`); the results here have no hypothesis.
-/

open Schubert GLRep TauCeti Demazure Demazure.FlagModule Demazure.SchubertUnions FinPermutation

namespace FlagVarieties

open PointModel.Complex

noncomputable section

variable {n : ℕ}

/-! ### Semi-invariance in the two sign conventions -/

theorem borelChar_val_eq_borelCharValue (η : Fin n → ℤ) (b : borel ℂ n) :
    (borelChar ℂ n η b : ℂ) = borelCharValue η ((b : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) := by
  rw [borelChar_apply, Units.coe_prod, borelCharValue]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Units.val_zpow_eq_zpow_val, borelDiag_apply_val]

theorem borelChar_neg_inv_val (η : Fin n → ℤ) (b : borel ℂ n) :
    (((borelChar ℂ n (-η) b)⁻¹ : ℂˣ) : ℂ) =
      borelCharValue η ((b : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) := by
  rw [borelChar_neg, MonoidHom.inv_apply, inv_inv, borelChar_val_eq_borelCharValue]

/-- Semi-invariance of weight `η` on `Z` (`PointModel.Complex`) is pointwise semi-invariance of
weight
`−η` (`GLRep`). -/
theorem isSemiInvOn_iff {Z : Set (GL (Fin n) ℂ)} {η : Fin n → ℤ} {t : GLCoord ℂ n} :
    IsSemiInvOn Z η t ↔ ∀ g ∈ Z, ∀ b : borel ℂ n,
      glEval (g * (b : GL (Fin n) ℂ)) t = (((borelChar ℂ n (-η) b)⁻¹ : ℂˣ) : ℂ) * glEval g t := by
  simp only [IsSemiInvOn, borelChar_neg_inv_val]
  exact ⟨fun h g hg b => h g hg b b.2, fun h g hg b hb => h g hg ⟨b, hb⟩⟩

namespace SectionRep

/-! ### The two section spaces agree -/

/-- The map from the semi-invariants of weight `η` on `π⁻¹ X_S` (`PointModel.Complex`) to the
sections of
`𝓛(−η)`. -/
def semiInvToSection (S : Finset (Equiv.Perm (Fin n))) (η : Fin n → ℤ) :
    semiInvSpace (orbitSet S) η →ₗ[ℂ] (sectionSubrep S (-η)).toSubmodule where
  toFun t := ⟨Ideal.Quotient.mk _ (t : GLCoord ℂ n),
    (mk_mem_sectionSubrep_iff S (-η) t).mpr (isSemiInvOn_iff.mp t.2)⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' c t := Subtype.ext (map_smul (Ideal.Quotient.mkₐ ℂ (orbitIdeal S)) c (t : GLCoord ℂ n))

theorem semiInvToSection_surjective (S : Finset (Equiv.Perm (Fin n))) (η : Fin n → ℤ) :
    Function.Surjective (semiInvToSection S η) := by
  rintro ⟨f, hf⟩
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective f
  exact ⟨⟨t, isSemiInvOn_iff.mpr ((mk_mem_sectionSubrep_iff S (-η) t).mp hf)⟩, rfl⟩

theorem ker_semiInvToSection (S : Finset (Equiv.Perm (Fin n))) (η : Fin n → ℤ) :
    LinearMap.ker (semiInvToSection S η) = semiInvVanishing S η := by
  ext t
  rw [LinearMap.mem_ker, semiInvVanishing, Submodule.mem_comap, Submodule.restrictScalars_mem,
    Submodule.coe_subtype]
  constructor
  · intro ht
    exact Ideal.Quotient.eq_zero_iff_mem.mp (congrArg Subtype.val ht)
  · intro ht
    exact Subtype.ext (Ideal.Quotient.eq_zero_iff_mem.mpr ht)

/-- **The ring model `PointModel.Complex.sectionSpace S η` of `H⁰(X_S, 𝓛(−η))` is
`sectionRep S (−η)`.** -/
def sectionSpaceEquiv (S : Finset (Equiv.Perm (Fin n))) (η : Fin n → ℤ) :
    sectionSpace S η ≃ₗ[ℂ] (sectionSubrep S (-η)).toSubmodule :=
  (Submodule.quotEquivOfEq _ _ (ker_semiInvToSection S η).symm).trans
    ((semiInvToSection S η).quotKerEquivOfSurjective (semiInvToSection_surjective S η))

theorem sectionSpaceEquiv_mk (S : Finset (Equiv.Perm (Fin n))) (η : Fin n → ℤ)
    (t : semiInvSpace (orbitSet S) η) :
    sectionSpaceEquiv S η (Submodule.Quotient.mk t) = semiInvToSection S η t :=
  rfl

/-! ### Torus weights of standard monomials -/

/-- Left translation by `t ∈ T` multiplies a standard product by `t^{−wt}`. -/
theorem leftTranslHom_borelTorus_flagColumnProduct {d : ℕ} (h : Fin d → Fin n)
    (T : (j : Fin d) → FlagMinorRowSet (h j)) (t : Fin n → ℂˣ) :
    leftTranslHom ℂ n (borelTorus ℂ n t : GL (Fin n) ℂ)
        (algebraMap (MatrixPolynomial n) (GLCoord ℂ n) (flagColumnProduct h T)) =
      weightCharHom ℂ (-tupleWeight h T) t •
        algebraMap (MatrixPolynomial n) (GLCoord ℂ n) (flagColumnProduct h T) := by
  refine glCoord_ext fun g => ?_
  rw [glEval_leftTranslHom, map_smul, smul_eq_mul, glEval_algebraMap, glEval_algebraMap]
  change PointModel.Complex.evalAt _ (flagColumnProduct h T) = _ *
      PointModel.Complex.evalAt _ (flagColumnProduct h T)
  have hmat : ((((borelTorus ℂ n t : GL (Fin n) ℂ))⁻¹ * g : GL (Fin n) ℂ) :
      Matrix (Fin n) (Fin n) ℂ) = Matrix.diagonal (fun i => ((t i)⁻¹ : ℂ)) * g := by
    rw [Units.val_mul, coe_borelTorus, ← map_inv, diagGL_coe]
    simp
  rw [hmat, evalAt_diagonal_mul_flagColumnProduct]
  congr 1
  rw [weightCharHom_apply, weightChar_apply, torusCharacter_def, Units.coe_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [tupleWeight, Pi.neg_apply, zpow_neg, zpow_natCast, Units.val_inv_eq_inv_val,
    Units.val_pow_eq_pow_val, inv_pow]

/-- **The standard-monomial basis of the sections of `𝓛(−λ)` over `X_S`**
(`PointModel.Complex.sectionBasisOfGlobalSectionsConstant`,
transported). -/
def sectionRepBasis
    {S : Finset (Equiv.Perm (Fin n))} (hS : BruhatLower S) {d : ℕ} (h : Fin d → Fin n) :
    Module.Basis {T // T ∈ chainSet h S} ℂ
      (sectionSubrep S (-shapeWeightZ (columnMultiplicity h))).toSubmodule :=
  (sectionBasisOfGlobalSectionsConstant (globalSectionsConstant_complex _) hS h).map
      (sectionSpaceEquiv S _)

theorem coe_sectionRepBasis
    {S : Finset (Equiv.Perm (Fin n))} (hS : BruhatLower S) {d : ℕ} (h : Fin d → Fin n)
    (T : {T // T ∈ chainSet h S}) :
    (sectionRepBasis hS h T : GLCoord ℂ n ⧸ orbitIdeal S) =
      Ideal.Quotient.mk _ (algebraMap (MatrixPolynomial n) (GLCoord ℂ n)
        (flagColumnProduct h T.1)) := by
  rw [sectionRepBasis, Module.Basis.map_apply, sectionBasisOfGlobalSectionsConstant_apply]
  rfl

/-- The basis vectors are weight vectors, of weight minus their row content. -/
theorem sectionRep_borelTorus_basis
    {S : Finset (Equiv.Perm (Fin n))} (hS : BruhatLower S) {d : ℕ} (h : Fin d → Fin n)
    (t : Fin n → ℂˣ) (T : {T // T ∈ chainSet h S}) :
    sectionRep S (-shapeWeightZ (columnMultiplicity h)) (borelTorus ℂ n t)
        (sectionRepBasis hS h T) =
      weightCharHom ℂ (-tupleWeight h T.1) t • sectionRepBasis hS h T := by
  apply Subtype.ext
  change quotLeftTranslHom (orbitIdeal S) (isLeftBorelStable_orbitIdeal S) (borelTorus ℂ n t)
      (sectionRepBasis hS h T : GLCoord ℂ n ⧸ orbitIdeal S) = _
  rw [Submodule.coe_smul, coe_sectionRepBasis]
  change Ideal.Quotient.mk _ (leftTranslHom ℂ n (borelTorus ℂ n t : GL (Fin n) ℂ) _) = _
  rw [leftTranslHom_borelTorus_flagColumnProduct, ← Ideal.Quotient.mkₐ_eq_mk ℂ, map_smul]

theorem finiteDimensional_sectionRep
    {S : Finset (Equiv.Perm (Fin n))} (hS : BruhatLower S) {d : ℕ} (h : Fin d → Fin n) :
    FiniteDimensional ℂ (sectionSubrep S (-shapeWeightZ (columnMultiplicity h))).toSubmodule :=
  Module.Finite.of_basis (sectionRepBasis hS h)

/-! ### Characters -/

/-- **The character of the sections of `𝓛(−λ)` over a Schubert union**:
`ch H⁰(X_S, 𝓛(−λ)) = ∑_{T ∈ chainSet h S} x^{wt T}`. -/
theorem ch_sectionRep_neg
    {S : Finset (Equiv.Perm (Fin n))} (hS : BruhatLower S) {d : ℕ} (h : Fin d → Fin n) :
    ch (sectionRep S (-shapeWeightZ (columnMultiplicity h))) = toLaurent (chainCharacter h S) := by
  rw [ch_eq_sum_of_basis (sectionRepBasis hS h) (fun T => -tupleWeight h T.1)
    (sectionRep_borelTorus_basis hS h), chainCharacter, map_sum,
    ← Finset.sum_coe_sort (chainSet h S)]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [neg_neg, toLaurent_compositionMonomial]
  rfl

/-- **The character of the sections of `𝓛(−λ)` over a Schubert union is a sum of atoms**:
`ch H⁰(X_S, 𝓛(−λ)) = ∑_{τ ∈ S ∩ W^λ} 𝒜_{τλ}`. -/
theorem ch_sectionRep_neg_eq_sum_atom
    {S : Finset (Equiv.Perm (Fin n))} (hS : BruhatLower S) {d : ℕ} (h : Fin d → Fin n) :
    ch (sectionRep S (-shapeWeightZ (columnMultiplicity h))) =
      toLaurent (∑ τ ∈ S.filter (IsMinCosetRep (shapeWeight (columnMultiplicity h))),
        atom (extremalWeight (columnMultiplicity h) τ)) := by
  classical
  rw [ch_sectionRep_neg hS h, chainCharacter_eq_sum_exact h S hS, Finset.sum_filter]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [exactCharacter_eq]
  split_ifs <;> rfl

/-- **The character of `H⁰(X_w, 𝓛(−λ))` is the key polynomial `κ_{wλ}`.** -/
theorem ch_sectionRep_lowerSet
    (w : Equiv.Perm (Fin n)) {d : ℕ} (h : Fin d → Fin n) :
    ch (sectionRep (lowerSet w) (-shapeWeightZ (columnMultiplicity h))) =
      toLaurent (key (extremalWeight (columnMultiplicity h) w)) := by
  have hset : chainSet h (lowerSet w) = chainSet h {w} := by
    ext T
    rw [mem_chainSet_lowerSet, mem_chainSet]
    exact ⟨fun hc => ⟨w, Finset.mem_singleton_self w, hc⟩, fun ⟨v, hv, hc⟩ => by
      rw [Finset.mem_singleton] at hv
      exact hv ▸ hc⟩
  rw [ch_sectionRep_neg (bruhatLower_lowerSet w) h, ← chainCharacter_singleton h w,
    chainCharacter, chainCharacter, hset]

end SectionRep

end

end FlagVarieties
