import RSCounterexample.FlagVarieties.PointModel.ComplexComparison

/-!
# Section spaces of Schubert unions and their dimensions

`sectionSpace K S η` is the ring model of `H⁰(X_S, 𝓛(η))`: the `B`-semi-invariant functions of
weight `-η` on `π⁻¹ X_S`, modulo the orbit ideal (`sectionsEquivSemiInvariants`
identifies it with the geometric sections).

* `minorRestriction K S m : A_m →ₗ sectionSpace K S λ`, `λ = shapeWeight m`: restriction from the
  flag-minor algebra.
* `ker_minorRestriction`: its kernel is `I_S^A ∩ A_m`.
* `minorRestriction_surjective_of_globalSectionsConstant` (**projective normality**, given
  `GlobalSectionsConstant`).
* `finrank_sectionSpace`: `dim H⁰(X_S, 𝓛(-λ)) = #chainSet h S` for a Bruhat ideal `S` and any column
  sequence `h` of shape `m`.
-/

open Schubert Demazure.FlagModule Demazure.SchubertUnions FinPermutation

namespace FlagVarieties.PointModel

noncomputable section

variable {K : Type*} [Field K] {n : ℕ}

/-- The functions in `𝒪(GL_n)` that are semi-invariant of weight `η` on `Z`. -/
def semiInvSpace (Z : Set (GL (Fin n) K)) (η : Fin n → ℤ) : Submodule K (GLCoord K n) where
  carrier := {t | IsSemiInvOn Z η t}
  add_mem' {t t'} ht ht' g hg b hb := by
    rw [map_add, map_add, ht g hg b hb, ht' g hg b hb, mul_add]
  zero_mem' g _ b _ := by rw [map_zero, map_zero, mul_zero]
  smul_mem' c t ht g hg b hb := by
    rw [map_smul, map_smul, ht g hg b hb, smul_eq_mul, smul_eq_mul, mul_left_comm]

theorem mem_semiInvSpace {Z : Set (GL (Fin n) K)} {η : Fin n → ℤ} {t : GLCoord K n} :
    t ∈ semiInvSpace Z η ↔ IsSemiInvOn Z η t :=
  Iff.rfl

/-- The semi-invariants vanishing on `π⁻¹ X_S`. -/
def semiInvVanishing (K : Type*) [Field K] (S : Finset (Equiv.Perm (Fin n))) (η : Fin n → ℤ) :
    Submodule K (semiInvSpace (orbitSet K S) η) :=
  ((orbitIdeal K S).restrictScalars K).comap (semiInvSpace (orbitSet K S) η).subtype

/-- **The ring model of `H⁰(X_S, 𝓛(-η))`**: semi-invariants of weight `η` on `π⁻¹ X_S`, modulo the
functions vanishing there. -/
abbrev sectionSpace (K : Type*) [Field K] (S : Finset (Equiv.Perm (Fin n))) (η : Fin n → ℤ) :=
  semiInvSpace (orbitSet K S) η ⧸ semiInvVanishing K S η

/-- The inclusion `A_m → semiInvSpace`. -/
def minorToSemiInvSpace (K : Type*) [Field K] (S : Finset (Equiv.Perm (Fin n)))
    (m : ColumnShape n) :
    minorSpan K m →ₗ[K] semiInvSpace (orbitSet K S) (shapeWeightZ m) where
  toFun a := ⟨algebraMap (MatrixEntryPolynomial K n) (GLCoord K n) a,
    isSemiInvOn_of_mem_minorSpan a.2 _⟩
  map_add' a b := by
    ext
    simp
  map_smul' c a := by
    ext
    change algebraMap (MatrixEntryPolynomial K n) (GLCoord K n)
        (c • (a : MatrixEntryPolynomial K n)) =
      c • algebraMap (MatrixEntryPolynomial K n) (GLCoord K n) a
    rw [Algebra.smul_def, Algebra.smul_def, map_mul,
      ← IsScalarTower.algebraMap_apply K (MatrixEntryPolynomial K n) (GLCoord K n)]

/-- **Restriction from the flag-minor algebra**, `A_λ → H⁰(X_S, 𝓛(-λ))`. -/
def minorRestriction (K : Type*) [Field K] (S : Finset (Equiv.Perm (Fin n))) (m : ColumnShape n) :
    minorSpan K m →ₗ[K] sectionSpace K S (shapeWeightZ m) :=
  (semiInvVanishing K S (shapeWeightZ m)).mkQ.comp (minorToSemiInvSpace K S m)

theorem minorRestriction_eq_zero_iff {S : Finset (Equiv.Perm (Fin n))} {m : ColumnShape n}
    (a : minorSpan K m) : minorRestriction K S m a = 0 ↔ (a : MatrixEntryPolynomial K n) ∈
        vanishSpan K m S := by
  rw [minorRestriction, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
    semiInvVanishing, Submodule.mem_comap, Submodule.restrictScalars_mem, mem_vanishSpan]
  simp only [Submodule.coe_subtype, minorToSemiInvSpace, LinearMap.coe_mk, AddHom.coe_mk,
    mem_orbitIdeal, glEval_algebraMap_eq_evalAt]
  exact ⟨fun h => ⟨a.2, h⟩, fun h => h.2⟩

/-- **The kernel of restriction is `I_S^A ∩ A_m`.** -/
theorem ker_minorRestriction (S : Finset (Equiv.Perm (Fin n))) (m : ColumnShape n) :
    LinearMap.ker (minorRestriction K S m) = (vanishSpan K m S).comap (minorSpan K m).subtype := by
  ext a
  rw [LinearMap.mem_ker, minorRestriction_eq_zero_iff, Submodule.mem_comap, Submodule.coe_subtype]

/-- **Projective normality**: restriction `A_λ → H⁰(X_S, 𝓛(-λ))` is surjective. -/
theorem minorRestriction_surjective_of_globalSectionsConstant [IsAlgClosed K]
    (hSMT : StandardMonomialTheory K)
    (hglobalSections : ∀ w : Equiv.Perm (Fin n), GlobalSectionsConstant K w)
    {S : Finset (Equiv.Perm (Fin n))} (hS : BruhatLower S) (m : ColumnShape n) :
    Function.Surjective (minorRestriction K S m) := by
  intro x
  obtain ⟨⟨t, ht⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨a, ha, hta⟩ := schubertUnion_normality_of_globalSectionsConstant hSMT hglobalSections m hS
      t ht
  refine ⟨⟨a, ha⟩, ?_⟩
  rw [minorRestriction, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.eq,
    semiInvVanishing, Submodule.mem_comap, Submodule.restrictScalars_mem]
  have : (minorToSemiInvSpace K S m ⟨a, ha⟩ - ⟨t, ht⟩ : semiInvSpace (orbitSet K S)
      (shapeWeightZ m)).1 =
      -(t - algebraMap (MatrixEntryPolynomial K n) (GLCoord K n) a) := by
    simp [minorToSemiInvSpace]
  rw [Submodule.coe_subtype, this]
  exact neg_mem hta

/-- **Dimension of the sections**: `dim H⁰(X_S, 𝓛(-λ)) = #chainSet h S`. -/
theorem finrank_sectionSpace_of_globalSectionsConstant [IsAlgClosed K]
    (hSMT : StandardMonomialTheory K)
    (hglobalSections : ∀ w : Equiv.Perm (Fin n), GlobalSectionsConstant K w)
    {S : Finset (Equiv.Perm (Fin n))} (hS : BruhatLower S) {d : ℕ} (h : Fin d → Fin n) :
    Module.finrank K (sectionSpace K S (shapeWeightZ (columnMultiplicity h))) =
      (chainSet h S).card := by
  have hrn := LinearMap.finrank_range_add_finrank_ker (minorRestriction K S (columnMultiplicity h))
  rw [LinearMap.range_eq_top.mpr (minorRestriction_surjective_of_globalSectionsConstant hSMT
      hglobalSections
      hS _), finrank_top,
    ker_minorRestriction] at hrn
  have hk : Module.finrank K ((vanishSpan K (columnMultiplicity h) S).comap
      (minorSpan K (columnMultiplicity h)).subtype) =
      Module.finrank K (vanishSpan K (columnMultiplicity h) S) := by
    rw [(Submodule.equivMapOfInjective _ (minorSpan K (columnMultiplicity h)).injective_subtype
      _).finrank_eq, Submodule.map_comap_subtype, vanishSpan, ← inf_assoc, inf_idem]
  have hadd := hSMT.dim h hS
  rw [← minorSpan_columnMultiplicity] at hadd
  omega

end

end FlagVarieties.PointModel
