import Schubert.FlagVarieties.PointModel.Complex.Main
import Schubert.FlagVarieties.PointModel.Complex.Sections
import Schubert.FlagVarieties.PointModel.Complex.ProjectiveNormality
import Schubert.FlagVarieties.PointModel.Main
import Schubert.FlagVarieties.PointModel.BorelWeil
import Schubert.FlagVarieties.PointModel.ComplexComparison
import Schubert.FlagVarieties.PointModel.Sections
import Schubert.FlagVarieties.PointModel.ProjectiveNormality
import Schubert.FlagVarieties.Plucker.Coordinates
import Schubert.FlagVarieties.Schubert.GlobalSectionsRingForm

/-!
# Projective normality and its corollaries without hypotheses

`FlagVarieties.globalSectionsConstant_of_charZero` proves `Γ(X_w, 𝒪) = K` (ring form,
`GlobalSectionsConstant K w`) over every field of characteristic `0`; over such a field the bundle
`StandardMonomialTheory K` holds as well (`standardMonomialTheory_of_charZero`). This file restates
every endpoint of `PointModel/` and `PointModel/Complex/` (and of `Plucker/Coordinates`) that took
`GlobalSectionsConstant` as a hypothesis, without it.

The hypothesis-free forms carry the plain names, in the namespaces
`FlagVarieties.PointModel.Complex` (over `ℂ`) and `FlagVarieties.PointModel` (over an algebraically
closed field `K` of characteristic `0`; also without `StandardMonomialTheory K`); the
originals with this hypothesis carry the suffix `_of_globalSectionsConstant`
(`OfGlobalSectionsConstant` in the names of definitions).
-/

open Schubert Demazure.FlagModule Demazure.SchubertUnions FinPermutation

/-! ### Over `ℂ` -/

namespace FlagVarieties.PointModel.Complex

variable {n : ℕ}

/-- **Projective normality** (ring form, over `ℂ`): every section on a union of Schubert varieties
of a
Bruhat ideal `S` is the restriction of a polynomial in the flag minors. -/
theorem schubertUnion_normality (m : ColumnShape n) {S : Finset (Equiv.Perm (Fin n))}
    (hS : BruhatLower S) (t : GLCoord ℂ n) (ht : IsSemiInvOn (orbitSet S) (shapeWeightZ m) t) :
    ∃ a ∈ minorSpan m, t - algebraMap (MatrixPolynomial n) (GLCoord ℂ n) a ∈ orbitIdeal S :=
  PointModel.Complex.schubertUnion_normality_of_globalSectionsConstant
      (globalSectionsConstant_complex n) m hS t ht

theorem sectionsGeneratedByMinors_of_bruhatLower :
    ∀ (N : ℕ) (m : ColumnShape n), nonDeterminantColumnCount m = N →
      ∀ S : Finset (Equiv.Perm (Fin n)), BruhatLower S → SectionsGeneratedByMinors m S :=
  PointModel.Complex.sectionsGeneratedByMinors_of_bruhatLower_of_globalSectionsConstant
      (globalSectionsConstant_complex n)

theorem normality_det {m : ColumnShape n} (hm : nonDeterminantColumnCount m = 0)
    {w : Equiv.Perm (Fin n)} :
    SectionsGeneratedByMinors m (lowerSet w) :=
  PointModel.Complex.normality_det_of_globalSectionsConstant hm (globalSectionsConstant_complex n w)

/-- **Borel–Weil** (ring form, over `ℂ`). -/
theorem borelWeil (m : ColumnShape n) {t : GLCoord ℂ n}
    (ht : IsSemiInvOn Set.univ (shapeWeightZ m) t) :
    ∃ a ∈ minorSpan m, t = algebraMap (MatrixPolynomial n) (GLCoord ℂ n) a :=
  PointModel.Complex.borelWeil_of_globalSectionsConstant (globalSectionsConstant_complex n) m ht

theorem semiInvSpace_univ (m : ColumnShape n) :
    semiInvSpace Set.univ (shapeWeightZ m) =
      (minorSpan m).map
        (IsScalarTower.toAlgHom ℂ (MatrixPolynomial n) (GLCoord ℂ n)).toLinearMap :=
  PointModel.Complex.semiInvSpace_univ_of_globalSectionsConstant (globalSectionsConstant_complex n)
      m

theorem finrank_globalSections {d : ℕ} (h : Fin d → Fin n) :
    Module.finrank ℂ (semiInvSpace Set.univ (shapeWeightZ (columnMultiplicity h))) =
      (chainSet h Finset.univ).card :=
  PointModel.Complex.finrank_globalSections_of_globalSectionsConstant
      (globalSectionsConstant_complex n) h

theorem minorRestriction_surjective {S : Finset (Equiv.Perm (Fin n))} (hS : BruhatLower S)
    (m : ColumnShape n) : Function.Surjective (minorRestriction S m) :=
  PointModel.Complex.minorRestriction_surjective_of_globalSectionsConstant
      (globalSectionsConstant_complex n) hS m

theorem finrank_sectionSpace {S : Finset (Equiv.Perm (Fin n))} (hS : BruhatLower S) {d : ℕ}
    (h : Fin d → Fin n) :
    Module.finrank ℂ (sectionSpace S (shapeWeightZ (columnMultiplicity h))) =
      (chainSet h S).card :=
  PointModel.Complex.finrank_sectionSpace_of_globalSectionsConstant
      (globalSectionsConstant_complex n) hS h

/-- The standard-monomial basis of the sections (over `ℂ`). -/
noncomputable def sectionBasis {S : Finset (Equiv.Perm (Fin n))} (hS : BruhatLower S) {d : ℕ}
    (h : Fin d → Fin n) :
    Module.Basis {T // T ∈ chainSet h S} ℂ (sectionSpace S (shapeWeightZ (columnMultiplicity h))) :=
  PointModel.Complex.sectionBasisOfGlobalSectionsConstant (globalSectionsConstant_complex n) hS h

theorem sectionBasis_apply {S : Finset (Equiv.Perm (Fin n))} (hS : BruhatLower S) {d : ℕ}
    (h : Fin d → Fin n) (T : {T // T ∈ chainSet h S}) :
    sectionBasis hS h T = standardSection h S T.1 :=
  PointModel.Complex.sectionBasisOfGlobalSectionsConstant_apply (globalSectionsConstant_complex n)
      hS h T

end FlagVarieties.PointModel.Complex

/-! ### Over an algebraically closed field of characteristic `0` -/

namespace FlagVarieties.PointModel

variable {K : Type*} [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ}

/-- **Projective normality** (ring form) over an algebraically closed field of characteristic `0`.
-/
theorem schubertUnion_normality (m : ColumnShape n) {S : Finset (Equiv.Perm (Fin n))}
    (hS : BruhatLower S) (t : GLCoord K n)
    (ht : IsSemiInvOn (orbitSet K S) (shapeWeightZ m) t) :
    ∃ a ∈ minorSpan K m, t - algebraMap (MatrixEntryPolynomial K n) (GLCoord K n) a ∈
        orbitIdeal K S :=
  PointModel.schubertUnion_normality_of_globalSectionsConstant
      (standardMonomialTheory_of_charZero K)
    (globalSectionsConstant_of_charZero K n) m hS t ht

theorem schubertUnion_normality_charZero (m : ColumnShape n)
    {S : Finset (Equiv.Perm (Fin n))} (hS : BruhatLower S) (t : GLCoord K n)
    (ht : IsSemiInvOn (orbitSet K S) (shapeWeightZ m) t) :
    ∃ a ∈ minorSpan K m, t - algebraMap (MatrixEntryPolynomial K n) (GLCoord K n) a ∈
        orbitIdeal K S :=
  PointModel.schubertUnion_normality_charZero_of_globalSectionsConstant
      (globalSectionsConstant_of_charZero K n) m
    hS t ht

theorem sectionsGeneratedByMinors_of_bruhatLower :
    ∀ (N : ℕ) (m : ColumnShape n), nonDeterminantColumnCount m = N →
      ∀ S : Finset (Equiv.Perm (Fin n)), BruhatLower S → SectionsGeneratedByMinors K m S :=
  PointModel.sectionsGeneratedByMinors_of_bruhatLower_of_globalSectionsConstant
      (standardMonomialTheory_of_charZero K) (globalSectionsConstant_of_charZero K n)

omit [IsAlgClosed K] in
theorem normality_det {m : ColumnShape n} (hm : nonDeterminantColumnCount m = 0)
    {w : Equiv.Perm (Fin n)} :
    SectionsGeneratedByMinors K m (lowerSet w) :=
  PointModel.normality_det_of_globalSectionsConstant hm (globalSectionsConstant_of_charZero K n w)

/-- **Borel–Weil** (ring form) over an algebraically closed field of characteristic `0`. -/
theorem borelWeil (m : ColumnShape n) {t : GLCoord K n}
    (ht : IsSemiInvOn Set.univ (shapeWeightZ m) t) :
    ∃ a ∈ minorSpan K m, t = algebraMap (MatrixEntryPolynomial K n) (GLCoord K n) a :=
  PointModel.borelWeil_of_globalSectionsConstant (standardMonomialTheory_of_charZero K)
      (globalSectionsConstant_of_charZero K n)
    m ht

theorem semiInvSpace_univ (m : ColumnShape n) :
    semiInvSpace Set.univ (shapeWeightZ m) =
      (minorSpan K m).map (IsScalarTower.toAlgHom K (MatrixEntryPolynomial K n)
          (GLCoord K n)).toLinearMap :=
  PointModel.semiInvSpace_univ_of_globalSectionsConstant (standardMonomialTheory_of_charZero K)
    (globalSectionsConstant_of_charZero K n) m

theorem finrank_globalSections {d : ℕ} (h : Fin d → Fin n) :
    Module.finrank K
        (semiInvSpace (Set.univ : Set (GL (Fin n) K)) (shapeWeightZ (columnMultiplicity h))) =
      (chainSet h Finset.univ).card :=
  PointModel.finrank_globalSections_of_globalSectionsConstant (standardMonomialTheory_of_charZero K)
    (globalSectionsConstant_of_charZero K n) h

theorem minorRestriction_surjective {S : Finset (Equiv.Perm (Fin n))} (hS : BruhatLower S)
    (m : ColumnShape n) : Function.Surjective (minorRestriction K S m) :=
  PointModel.minorRestriction_surjective_of_globalSectionsConstant
      (standardMonomialTheory_of_charZero K)
    (globalSectionsConstant_of_charZero K n) hS m

theorem finrank_sectionSpace {S : Finset (Equiv.Perm (Fin n))} (hS : BruhatLower S) {d : ℕ}
    (h : Fin d → Fin n) :
    Module.finrank K (sectionSpace K S (shapeWeightZ (columnMultiplicity h))) =
      (chainSet h S).card :=
  PointModel.finrank_sectionSpace_of_globalSectionsConstant (standardMonomialTheory_of_charZero K)
    (globalSectionsConstant_of_charZero K n) hS h

/-- The standard-monomial basis of the sections. -/
noncomputable def sectionBasis {S : Finset (Equiv.Perm (Fin n))} (hS : BruhatLower S) {d : ℕ}
    (h : Fin d → Fin n) :
    Module.Basis {T // T ∈ chainSet h S} K
      (sectionSpace K S (shapeWeightZ (columnMultiplicity h))) :=
  PointModel.sectionBasisOfGlobalSectionsConstant (globalSectionsConstant_of_charZero K n) hS h

theorem sectionBasis_apply {S : Finset (Equiv.Perm (Fin n))} (hS : BruhatLower S) {d : ℕ}
    (h : Fin d → Fin n) (T : {T // T ∈ chainSet h S}) :
    sectionBasis hS h T = standardSection K h S T.1 :=
  PointModel.sectionBasisOfGlobalSectionsConstant_apply (globalSectionsConstant_of_charZero K n)
      hS
      h T

/-- **The Plücker coordinates of height `k` are the sections of `𝓛(−ϖ_k)`**. -/
noncomputable def pluckerSectionsEquiv (k : Fin n) :
    minorSpan K (Pi.single k 1) ≃ₗ[K]
      sectionSpace K Finset.univ (shapeWeightZ (Pi.single k 1)) :=
  PointModel.pluckerSectionsEquivOfGlobalSectionsConstant (globalSectionsConstant_of_charZero K n)
      k

/-- **The Plücker coordinates are a basis of `H⁰(Fl_n, 𝓛(−ϖ_k))`**. -/
noncomputable def pluckerSectionBasis (k : Fin n) :
    Module.Basis (FlagMinorRowSet k) K
      (sectionSpace K Finset.univ (shapeWeightZ (Pi.single k 1))) :=
  PointModel.pluckerSectionBasisOfGlobalSectionsConstant (globalSectionsConstant_of_charZero K n)
      k

theorem finrank_sections_single (k : Fin n) :
    Module.finrank K (sectionSpace K Finset.univ (shapeWeightZ (Pi.single k 1))) =
      n.choose (k.val + 1) :=
  PointModel.finrank_sections_single_of_globalSectionsConstant
      (globalSectionsConstant_of_charZero K n) k

end FlagVarieties.PointModel
