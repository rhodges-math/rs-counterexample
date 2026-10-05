import Schubert.FlagVarieties.Normality.SectionRing
import Schubert.FlagVarieties.LineBundle.Density
import Schubert.FlagVarieties.LineBundle.SectionsRestriction
import Mathlib.Algebra.CharZero.Infinite

/-!
# Projective normality, Borel–Weil and the section ring at the sheaf level, over any field

The comparison between the scheme-theoretic semi-invariants and the pointwise ring model
(`FlagVarieties.quotientSemiInvariants_eq_borelSemiInvariants`, over `ℂ`) uses only that `𝒪(B)`
embeds into the functions on `B(K)` (`borelCoord_eq_zero_of_forall`), which holds over every
infinite field. Here it is redone over an infinite field `K`:

* `mk_mem_quotientSemiInvariants_orbitIdeal_iff`: for the orbit ideal `I_S` of any finite set `S` of
  permutations, the class of `t ∈ 𝒪(GLₙ)` lies in `quotientSemiInvariants K n I_S η` iff
  `t(g b) = (−η)(b) t(g)` for all `g ∈ ⋃_{w ∈ S} B ẇ B` and `b ∈ B(K)`; `isBorelStable_orbitIdeal`;
* `sectionsEquivSectionSpace hI η`: for a closed subscheme `X ⊆ Flₙ` with `π⁻¹ X` cut out by `I_S`,
  `H⁰(X, 𝓛(−η))` is the ring model `sectionSpace K S η`.

With `preimageIdeal_schubertUnion_eq_orbitIdeal` (infinite fields), the ring-model results of
`Normality/Unconditional` become statements about the geometric sections of the Schubert union
subschemes `X_S = schubertUnion K n S`, over an algebraically closed field `K` of characteristic
`0`:

* **Projective normality** (`sectionsRestrict_surjective`): restriction
  `H⁰(Flₙ, 𝓛(−λ)) → H⁰(X_S, 𝓛(−λ))` is surjective for a Bruhat ideal `S` and dominant `λ`; also
  `H⁰(X_S, 𝓛(−λ)) → H⁰(X_{S'}, 𝓛(−λ))` for Bruhat ideals `S' ⊆ S`;
* **Borel–Weil** (`minorSpanEquivSections`): `A_λ ≅ H⁰(Flₙ, 𝓛(−λ))`, `a ↦` the class of `a`, and
  `finrank_sections_bot : dim H⁰(Flₙ, 𝓛(−λ)) = #chainSet h Sₙ`;
* **the section bases** (`schubertSectionsBasis`: the standard-monomial basis of `H⁰(X_S, 𝓛(−λ))`,
  `finrank_schubertSections`; `pluckerSectionsBasis`: the Plücker coordinates of height `k` are a
  basis of `H⁰(Flₙ, 𝓛(−ϖ_k))`);
* **the section ring** (`geometricSectionRingEquiv`): `A ⧸ I_S` is the dominant section ring
  `⨁_λ H⁰(X_S, 𝓛(−λ))` of `X_S` built from the geometric sections; its product of homogeneous
  sections is `sectionsMul` (`sectionsDirectSumEquiv_of_mul_of`).

Here `Flₙ` is the ideal sheaf `⊥`; `schubertUnion_univ` shows `X_{Sₙ} = Flₙ`.
-/

noncomputable section

open Schubert Demazure.FlagModule Demazure.SchubertUnions FinPermutation
open scoped TensorProduct DirectSum

universe u

namespace FlagVarieties.PointModel

/-! ### Characters at points of `B(K)` -/

section Points

variable {K : Type*} [Field K] {n : ℕ}

theorem borelChar_val_eq_borelCharValue (η : Fin n → ℤ) (b : GLRep.borel K n) :
    (GLRep.borelChar K n η b : K) = borelCharValue η
        ((b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  rw [GLRep.borelChar_apply, Units.coe_prod, borelCharValue]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Units.val_zpow_eq_zpow_val, GLRep.borelDiag_apply_val]

theorem inv_borelChar_val (η : Fin n → ℤ) (b : GLRep.borel K n) :
    (((GLRep.borelChar K n η b)⁻¹ : Kˣ) : K) =
      borelCharValue (-η) ((b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  rw [← borelChar_val_eq_borelCharValue, GLRep.borelChar_neg, MonoidHom.inv_apply]

/-- Restriction of polynomials to `𝒪(GLₙ)/J`, over `K`. -/
def geometricRestrictHom (J : Ideal (GLCoord K n)) :
    MatrixEntryPolynomial K n →ₐ[K] GLCoord K n ⧸ J :=
  (Ideal.Quotient.mkₐ K J).comp (IsScalarTower.toAlgHom K (MatrixEntryPolynomial K n) (GLCoord K n))

end Points

/-! ### Scheme-theoretic and pointwise semi-invariants, over an infinite field -/

section Bridge

variable {K : Type*} [Field K] [Infinite K] {n : ℕ} {S : Finset (Equiv.Perm (Fin n))}

/-- The orbit ideal is stable under the (scheme-theoretic) right action of `B`. -/
theorem isBorelStable_orbitIdeal : IsBorelStable K n (orbitIdeal K S) := fun f hf => by
  rw [RingHom.mem_ker]
  refine tensor_ext_borelCoordPoint fun b => ?_
  change TensorProduct.rid K _
    ((borelCoordPoint b).toLinearMap.lTensor _ (rightCoactionMod K n (orbitIdeal K S) f)) = _
  rw [rid_lTensor_rightCoactionMod, LinearMap.map_zero, LinearEquiv.map_zero,
    Ideal.Quotient.eq_zero_iff_mem, mem_orbitIdeal]
  intro g hg
  rw [GLRep.glEval_rightTranslHom]
  exact mem_orbitIdeal.mp hf _ (orbitSet_mul_borel hg b.2)

/-- **The semi-invariants of `𝒪(GLₙ)/I_S` are the pointwise ones** (any infinite field;
`quotientSemiInvariants_eq_borelSemiInvariants` over `ℂ`). -/
theorem mk_mem_quotientSemiInvariants_orbitIdeal_iff (η : Fin n → ℤ) (t : GLCoord K n) :
    Ideal.Quotient.mk (orbitIdeal K S) t ∈ quotientSemiInvariants K n (orbitIdeal K S) η ↔
      IsSemiInvOn (orbitSet K S) (-η) t := by
  rw [mem_quotientSemiInvariants_iff isBorelStable_orbitIdeal]
  constructor
  · intro h g hg b hb
    have := congrArg (fun x => TensorProduct.rid K (GLCoord K n ⧸ orbitIdeal K S)
      ((borelCoordPoint ⟨b, hb⟩).toLinearMap.lTensor (GLCoord K n ⧸ orbitIdeal K S) x)) h
    rw [rid_lTensor_rightCoactionMod, LinearMap.lTensor_tmul, TensorProduct.rid_tmul,
      AlgHom.toLinearMap_apply, borelCoordPoint_borelCharacterUnit_inv, inv_borelChar_val,
      ← Ideal.Quotient.mkₐ_eq_mk K, ← map_smul, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq,
      mem_orbitIdeal] at this
    have h2 := this g hg
    rw [map_sub, map_smul, GLRep.glEval_rightTranslHom, smul_eq_mul, sub_eq_zero] at h2
    exact h2
  · intro h
    refine tensor_ext_borelCoordPoint fun b => ?_
    rw [rid_lTensor_rightCoactionMod, LinearMap.lTensor_tmul, TensorProduct.rid_tmul,
      AlgHom.toLinearMap_apply, borelCoordPoint_borelCharacterUnit_inv, inv_borelChar_val,
      ← Ideal.Quotient.mkₐ_eq_mk K, ← map_smul, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq,
      mem_orbitIdeal]
    intro g hg
    rw [map_sub, map_smul, GLRep.glEval_rightTranslHom, smul_eq_mul, h g hg b b.2, sub_self]

theorem mk_mem_quotientSemiInvariants_iff_of_eq {J : Ideal (GLCoord K n)} (hJ : J = orbitIdeal K S)
    (η : Fin n → ℤ) (t : GLCoord K n) :
    Ideal.Quotient.mk J t ∈ quotientSemiInvariants K n J η ↔ IsSemiInvOn (orbitSet K S) (-η) t := by
  subst hJ
  exact mk_mem_quotientSemiInvariants_orbitIdeal_iff η t

/-- The scheme-theoretic `H⁰(X_S, 𝓛(−λ))` piece is the ring-model piece `sectionPiece K S m`, over
any infinite field. -/
theorem dominantSemiInvariants_orbitIdeal (m : ColumnShape n) :
    dominantSemiInvariants (orbitIdeal K S) m = sectionPiece K S m := by
  ext x
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [mem_dominantSemiInvariants, mk_mem_quotientSemiInvariants_orbitIdeal_iff, neg_neg,
    mk_mem_sectionPiece_iff]

/-- The class map from the ring model to the semi-invariants, for `J = I_S`. -/
def semiInvToSemiInvariants {J : Ideal (GLCoord K n)} (hJ : J = orbitIdeal K S) (η : Fin n → ℤ) :
    semiInvSpace (orbitSet K S) η →ₗ[K] quotientSemiInvariants K n J (-η) where
  toFun t := ⟨Ideal.Quotient.mk J (t : GLCoord K n),
    (mk_mem_quotientSemiInvariants_iff_of_eq hJ (-η) t).mpr (by rw [neg_neg]; exact t.2)⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' c t := Subtype.ext (map_smul (Ideal.Quotient.mkₐ K J) c (t : GLCoord K n))

theorem semiInvToSemiInvariants_surjective {J : Ideal (GLCoord K n)} (hJ : J = orbitIdeal K S)
    (η : Fin n → ℤ) : Function.Surjective (semiInvToSemiInvariants hJ η) := by
  rintro ⟨x, hx⟩
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective x
  have ht := (mk_mem_quotientSemiInvariants_iff_of_eq hJ (-η) t).mp hx
  rw [neg_neg] at ht
  exact ⟨⟨t, ht⟩, rfl⟩

theorem ker_semiInvToSemiInvariants {J : Ideal (GLCoord K n)} (hJ : J = orbitIdeal K S)
    (η : Fin n → ℤ) : LinearMap.ker (semiInvToSemiInvariants hJ η) = semiInvVanishing K S η := by
  ext t
  rw [LinearMap.mem_ker, semiInvVanishing, Submodule.mem_comap, Submodule.restrictScalars_mem,
    Submodule.coe_subtype, ← hJ]
  constructor
  · intro ht
    exact Ideal.Quotient.eq_zero_iff_mem.mp (congrArg Subtype.val ht)
  · intro ht
    exact Subtype.ext (Ideal.Quotient.eq_zero_iff_mem.mpr ht)

/-- **`(𝒪(GLₙ)/I_S)^{(B, −η)}` is the ring model `sectionSpace K S η`**. -/
def semiInvariantsEquivSectionSpace {J : Ideal (GLCoord K n)} (hJ : J = orbitIdeal K S)
    (η : Fin n → ℤ) : quotientSemiInvariants K n J (-η) ≃ₗ[K] sectionSpace K S η :=
  ((Submodule.quotEquivOfEq _ _ (ker_semiInvToSemiInvariants hJ η).symm).trans
    ((semiInvToSemiInvariants hJ η).quotKerEquivOfSurjective
      (semiInvToSemiInvariants_surjective hJ η))).symm

theorem semiInvariantsEquivSectionSpace_symm_mk {J : Ideal (GLCoord K n)}
    (hJ : J = orbitIdeal K S) (η : Fin n → ℤ) (t : semiInvSpace (orbitSet K S) η) :
    (semiInvariantsEquivSectionSpace hJ η).symm (Submodule.Quotient.mk t) =
      semiInvToSemiInvariants hJ η t :=
  rfl

theorem mk_mem_dominantSemiInvariants_iff {J : Ideal (GLCoord K n)} (hJ : J = orbitIdeal K S)
    (m : ColumnShape n) (t : GLCoord K n) :
    Ideal.Quotient.mk J t ∈ dominantSemiInvariants J m ↔
      IsSemiInvOn (orbitSet K S) (shapeWeightZ m) t := by
  rw [mem_dominantSemiInvariants, mk_mem_quotientSemiInvariants_iff_of_eq hJ, neg_neg]

theorem geometricRestrictHom_mem {J : Ideal (GLCoord K n)} (hJ : J = orbitIdeal K S) :
    ∀ m, ∀ p ∈ minorSpan K m, geometricRestrictHom J p ∈ dominantSemiInvariants J m :=
  fun m _ hp =>
    (mk_mem_dominantSemiInvariants_iff hJ m _).mpr (isSemiInvOn_of_mem_minorSpan hp _)

omit [Infinite K] in
theorem geometricRestrictHom_eq_zero_iff {J : Ideal (GLCoord K n)} (hJ : J = orbitIdeal K S)
    {m : ColumnShape n} (a : minorSpan K m) :
    geometricRestrictHom J a = 0 ↔ (a : MatrixEntryPolynomial K n) ∈ vanishSpan K m S := by
  subst hJ
  exact restrictHom_eq_zero_iff K S a

end Bridge

/-! ### Sections of Schubert unions -/

section Sections

variable {K : Type u} [Field K] {n : ℕ} {S : Finset (Equiv.Perm (Fin n))}

/-- **`H⁰(X, 𝓛(−η))` is the ring model `sectionSpace K S η`**, for a closed subscheme
`X ⊆ Flₙ` whose preimage in `GLₙ` is cut out by the orbit ideal `I_S`. -/
def sectionsEquivSectionSpace [Infinite K] {I : (FlagScheme K n).IdealSheafData}
    (hI : preimageIdeal K n I = orbitIdeal K S) (η : Fin n → ℤ) :
    sections K n I (-η) ≃ₗ[K] sectionSpace K S η :=
  (sectionsEquivSemiInvariants K n I (-η)).trans (semiInvariantsEquivSectionSpace hI η)

theorem sectionsEquivSemiInvariants_sectionsEquivSectionSpace_symm_mk [Infinite K]
    {I : (FlagScheme K n).IdealSheafData} (hI : preimageIdeal K n I = orbitIdeal K S)
    (η : Fin n → ℤ) (t : semiInvSpace (orbitSet K S) η) :
    (sectionsEquivSemiInvariants K n I (-η) ((sectionsEquivSectionSpace hI η).symm
        (Submodule.Quotient.mk t)) : GLCoord K n ⧸ preimageIdeal K n I) =
      Ideal.Quotient.mk _ (t : GLCoord K n) := by
  rw [sectionsEquivSectionSpace, LinearEquiv.symm_trans_apply, LinearEquiv.apply_symm_apply]
  rfl

variable (K n S) in
/-- The ideal of `π⁻¹(X_S)` is the orbit ideal (any infinite field). -/
theorem preimageIdeal_schubertUnion [Infinite K] :
    preimageIdeal K n (schubertUnion K n S) = orbitIdeal K S :=
  preimageIdeal_schubertUnion_eq_orbitIdeal K n S

variable (K n) in
/-- The ideal of `π⁻¹(Flₙ) = GLₙ` is `0 = I_{Sₙ}`. -/
theorem preimageIdeal_bot [Infinite K] :
    preimageIdeal K n ⊥ = orbitIdeal K (Finset.univ : Finset (Equiv.Perm (Fin n))) :=
  le_antisymm ((preimageIdeal_mono K n bot_le).trans (preimageIdeal_schubertUnion K n _).le)
    (by rw [orbitIdeal_univ]; exact bot_le)

variable (K n) in
/-- `X_{Sₙ} = Flₙ`. -/
theorem schubertUnion_univ [Infinite K] :
    schubertUnion K n (Finset.univ : Finset (Equiv.Perm (Fin n))) = ⊥ :=
  preimageIdeal_injective K n
    ((preimageIdeal_schubertUnion K n _).trans (preimageIdeal_bot K n).symm)

end Sections

/-! ### Sheaf-level forms over an algebraically closed field of characteristic `0` -/

section CharZero

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ}
  {S : Finset (Equiv.Perm (Fin n))}

/-- **Projective normality at the sheaf level**: for a Bruhat ideal `S` and a dominant weight
`λ = λ_m`,
restriction `H⁰(Flₙ, 𝓛(−λ)) → H⁰(X_S, 𝓛(−λ))` is surjective. -/
theorem sectionsRestrict_surjective (hS : BruhatLower S) (m : ColumnShape n) :
    Function.Surjective (sectionsRestrict K n (bot_le : ⊥ ≤ schubertUnion K n S)
      (-shapeWeightZ m)) := by
  intro s
  have hIS := preimageIdeal_schubertUnion K n S
  obtain ⟨f, hf⟩ := Ideal.Quotient.mk_surjective
    (sectionsEquivSemiInvariants K n (schubertUnion K n S) (-shapeWeightZ m) s).1
  have hfs := (sectionsEquivSemiInvariants K n (schubertUnion K n S) (-shapeWeightZ m) s).2
  rw [← hf, mk_mem_quotientSemiInvariants_iff_of_eq hIS, neg_neg] at hfs
  obtain ⟨a, ha, hfa⟩ := PointModel.schubertUnion_normality m hS f hfs
  have hsemi : IsSemiInvOn (orbitSet K (Finset.univ : Finset (Equiv.Perm (Fin n))))
      (shapeWeightZ m) (algebraMap (MatrixEntryPolynomial K n) (GLCoord K n) a) :=
    isSemiInvOn_of_mem_minorSpan ha _
  refine ⟨(sectionsEquivSectionSpace (preimageIdeal_bot K n) (shapeWeightZ m)).symm
    (Submodule.Quotient.mk ⟨_, hsemi⟩), ?_⟩
  apply (sectionsEquivSemiInvariants K n (schubertUnion K n S) (-shapeWeightZ m)).injective
  apply Subtype.ext
  rw [sectionsEquivSemiInvariants_sectionsRestrict, coe_semiInvariantsRestrict,
    sectionsEquivSemiInvariants_sectionsEquivSectionSpace_symm_mk, Ideal.Quotient.factorₐ_apply_mk,
        ← hf,
    Ideal.Quotient.eq, hIS, ← neg_mem_iff, neg_sub]
  exact hfa

omit [IsAlgClosed K] [CharZero K] in
theorem schubertUnion_anti {S' : Finset (Equiv.Perm (Fin n))} (hSS : S' ⊆ S) :
    schubertUnion K n S ≤ schubertUnion K n S' :=
  biInf_mono fun _ hw => hSS hw

/-- Restriction `H⁰(X_S, 𝓛(−λ)) → H⁰(X_{S'}, 𝓛(−λ))` is surjective for Bruhat ideals
`S' ⊆ S`. -/
theorem sectionsRestrict_surjective_of_subset {S' : Finset (Equiv.Perm (Fin n))}
    (hS' : BruhatLower S') (hSS : S' ⊆ S) (m : ColumnShape n) :
    Function.Surjective (sectionsRestrict K n (schubertUnion_anti hSS) (-shapeWeightZ m)) := by
  intro s
  obtain ⟨s₀, rfl⟩ := sectionsRestrict_surjective hS' m s
  refine ⟨sectionsRestrict K n (bot_le : ⊥ ≤ schubertUnion K n S) (-shapeWeightZ m) s₀, ?_⟩
  apply (sectionsEquivSemiInvariants K n (schubertUnion K n S') (-shapeWeightZ m)).injective
  apply Subtype.ext
  rw [sectionsEquivSemiInvariants_sectionsRestrict, coe_semiInvariantsRestrict,
    sectionsEquivSemiInvariants_sectionsRestrict, coe_semiInvariantsRestrict,
    sectionsEquivSemiInvariants_sectionsRestrict, coe_semiInvariantsRestrict]
  obtain ⟨f, hf⟩ := Ideal.Quotient.mk_surjective
      (sectionsEquivSemiInvariants K n ⊥ (-shapeWeightZ m) s₀).1
  rw [← hf, Ideal.Quotient.factorₐ_apply_mk, Ideal.Quotient.factorₐ_apply_mk,
    Ideal.Quotient.factorₐ_apply_mk]

/-! #### Borel–Weil -/

theorem minorRestriction_univ_bijective (m : ColumnShape n) :
    Function.Bijective (minorRestriction K (Finset.univ : Finset (Equiv.Perm (Fin n))) m) := by
  refine ⟨LinearMap.ker_eq_bot.mp ?_, PointModel.minorRestriction_surjective bruhatLower_univ m⟩
  rw [ker_minorRestriction, vanishSpan_univ, Submodule.comap_bot, Submodule.ker_subtype]

/-- **Borel–Weil at the sheaf level**: `A_λ ≅ H⁰(Flₙ, 𝓛(−λ))`, a flag-minor polynomial going to
its class. -/
def minorSpanEquivSections (m : ColumnShape n) :
    minorSpan K m ≃ₗ[K] sections K n ⊥ (-shapeWeightZ m) :=
  (LinearEquiv.ofBijective _ (minorRestriction_univ_bijective m)).trans
    (sectionsEquivSectionSpace (preimageIdeal_bot K n) (shapeWeightZ m)).symm

theorem sectionsEquivSemiInvariants_minorSpanEquivSections (m : ColumnShape n) (a : minorSpan K m) :
    (sectionsEquivSemiInvariants K n ⊥ (-shapeWeightZ m) (minorSpanEquivSections m a) :
        GLCoord K n ⧸ preimageIdeal K n ⊥) =
      Ideal.Quotient.mk _ (algebraMap (MatrixEntryPolynomial K n) (GLCoord K n) a) :=
  sectionsEquivSemiInvariants_sectionsEquivSectionSpace_symm_mk (preimageIdeal_bot K n)
      (shapeWeightZ m) _

/-- **Dimension of `H⁰(Flₙ, 𝓛(−λ))`**: `#chainSet h Sₙ` for any column sequence `h` of shape `λ`. -/
theorem finrank_sections_bot {d : ℕ} (h : Fin d → Fin n) :
    Module.finrank K (sections K n ⊥ (-shapeWeightZ (columnMultiplicity h))) =
      (chainSet h Finset.univ).card := by
  rw [(sectionsEquivSectionSpace (preimageIdeal_bot K n) _).finrank_eq,
    PointModel.finrank_sectionSpace bruhatLower_univ h]

/-! #### Section bases -/

/-- **The standard-monomial basis of `H⁰(X_S, 𝓛(−λ))`** for the geometric sections of the Schubert
union `X_S`, indexed by `chainSet h S`. -/
def schubertSectionsBasis (hS : BruhatLower S) {d : ℕ} (h : Fin d → Fin n) :
    Module.Basis {T // T ∈ chainSet h S} K
      (sections K n (schubertUnion K n S) (-shapeWeightZ (columnMultiplicity h))) :=
  (PointModel.sectionBasis hS h).map
    (sectionsEquivSectionSpace (preimageIdeal_schubertUnion K n S) _).symm

theorem schubertSectionsBasis_apply (hS : BruhatLower S) {d : ℕ} (h : Fin d → Fin n)
    (T : {T // T ∈ chainSet h S}) :
    schubertSectionsBasis hS h T =
      (sectionsEquivSectionSpace (preimageIdeal_schubertUnion K n S) _).symm
        (standardSection K h S T.1) := by
  rw [schubertSectionsBasis, Module.Basis.map_apply, PointModel.sectionBasis_apply]

/-- `dim H⁰(X_S, 𝓛(−λ)) = #chainSet h S` for the geometric sections. -/
theorem finrank_schubertSections (hS : BruhatLower S) {d : ℕ} (h : Fin d → Fin n) :
    Module.finrank K
        (sections K n (schubertUnion K n S) (-shapeWeightZ (columnMultiplicity h))) =
      (chainSet h S).card := by
  rw [(sectionsEquivSectionSpace (preimageIdeal_schubertUnion K n S) _).finrank_eq,
    PointModel.finrank_sectionSpace hS h]

/-- **The Plücker coordinates of height `k` are a basis of `H⁰(Flₙ, 𝓛(−ϖ_k))`**. -/
def pluckerSectionsBasis (k : Fin n) :
    Module.Basis (FlagMinorRowSet k) K (sections K n ⊥ (-shapeWeightZ (Pi.single k 1))) :=
  (PointModel.pluckerSectionBasis k).map
    (sectionsEquivSectionSpace (preimageIdeal_bot K n) _).symm

theorem finrank_sections_bot_single (k : Fin n) :
    Module.finrank K (sections K n ⊥ (-shapeWeightZ (Pi.single k 1))) = n.choose (k.val + 1) := by
  rw [(sectionsEquivSectionSpace (preimageIdeal_bot K n) _).finrank_eq,
    PointModel.finrank_sections_single k]

/-! #### The section ring -/

theorem geometricPiece_surjective {J : Ideal (GLCoord K n)} (hJ : J = orbitIdeal K S)
    (hS : BruhatLower S) (m : ColumnShape n) :
    Function.Surjective (gradedPiece (geometricRestrictHom J) (geometricRestrictHom_mem hJ) m) := by
  rintro ⟨y, hy⟩
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨a, ha, hat⟩ := PointModel.schubertUnion_normality m hS t
    ((mk_mem_dominantSemiInvariants_iff hJ m t).mp hy)
  refine ⟨⟨a, ha⟩, Subtype.ext ?_⟩
  have hat' : t - algebraMap (MatrixEntryPolynomial K n) (GLCoord K n) a ∈ J := by
    rw [hJ]
    exact hat
  exact (Ideal.Quotient.eq.mpr hat').symm

variable (S) in
/-- Restriction from the flag-minor algebra to the dominant section ring of `X_S`, over `K`. -/
def geometricRestrictMap :
    FlagMinorAlgebra K n →ₐ[K] dominantSectionRing (preimageIdeal K n (schubertUnion K n S)) :=
  gradedMap (geometricRestrictHom _) (geometricRestrictHom_mem (preimageIdeal_schubertUnion K n S))

theorem geometricRestrictMap_surjective (hS : BruhatLower S) :
    Function.Surjective (geometricRestrictMap S (K := K)) :=
  gradedMap_surjective _ _ (geometricPiece_surjective (preimageIdeal_schubertUnion K n S) hS)

omit [CharZero K] in
theorem ker_geometricRestrictMap :
    RingHom.ker (geometricRestrictMap S (K := K)) = flagMinorIdeal K S := by
  ext x
  rw [RingHom.mem_ker, geometricRestrictMap, gradedMap_eq_zero_iff, mem_flagMinorIdeal]
  exact forall_congr' fun m =>
    geometricRestrictHom_eq_zero_iff (preimageIdeal_schubertUnion K n S) (x m)

/-- **Projective normality of Schubert unions with the geometric sections, over `K`**: the dominant
section ring `⨁_λ H⁰(X_S, 𝓛(−λ))` of the Schubert union subscheme `X_S ⊆ Flₙ` is `A ⧸ I_S`, for
`K` algebraically closed of characteristic `0` (`geometricSectionRingEquiv` over `ℂ`). -/
def geometricSectionRingEquiv (hS : BruhatLower S) :
    (FlagMinorAlgebra K n ⧸ flagMinorIdeal K S) ≃ₐ[K]
      dominantSectionRing (preimageIdeal K n (schubertUnion K n S)) :=
  let e₁ : (FlagMinorAlgebra K n ⧸ flagMinorIdeal K S) ≃ₐ[K]
      (FlagMinorAlgebra K n ⧸ RingHom.ker (geometricRestrictMap S (K := K))) :=
    Ideal.quotientEquivAlgOfEq K ker_geometricRestrictMap.symm
  e₁.trans (Ideal.quotientKerAlgEquivOfSurjective (geometricRestrictMap_surjective hS))

theorem geometricSectionRingEquiv_mk_of (hS : BruhatLower S) (m : ColumnShape n)
    (a : minorSpan K m) :
    geometricSectionRingEquiv hS (Ideal.Quotient.mk _ (DirectSum.of _ m a)) =
      DirectSum.of (fun m => ↥(dominantSemiInvariants
          (preimageIdeal K n (schubertUnion K n S)) m)) m
        ⟨geometricRestrictHom _ a,
          geometricRestrictHom_mem (preimageIdeal_schubertUnion K n S) m a a.2⟩ :=
  gradedMap_of _ _ m a

/-- Over `ℂ`, the product of the geometric sections (`sectionsMul`) is the product of `A ⧸ I_S`. -/
theorem geometricSectionRingEquiv_symm_of_mul_of {S : Finset (Equiv.Perm (Fin n))}
    (hS : BruhatLower S) {m m' : ColumnShape n}
    (s : sections ℂ n (schubertUnion ℂ n S) (-shapeWeightZ m))
    (t : sections ℂ n (schubertUnion ℂ n S) (-shapeWeightZ m')) :
    (geometricSectionRingEquiv (K := ℂ) hS).symm
          (sectionsDirectSumEquiv ℂ n _ (DirectSum.of _ m s)) *
        (geometricSectionRingEquiv (K := ℂ) hS).symm
          (sectionsDirectSumEquiv ℂ n _ (DirectSum.of _ m' t)) =
      (geometricSectionRingEquiv (K := ℂ) hS).symm (sectionsDirectSumEquiv ℂ n _
        (DirectSum.of _ (m + m')
          (sectionsCongr ℂ n _ (neg_shapeWeightZ_add m m') (sectionsMul ℂ n _ _ _ s t)))) := by
  rw [← map_mul, sectionsDirectSumEquiv_of_mul_of]

end CharZero

end FlagVarieties.PointModel
