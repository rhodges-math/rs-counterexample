import RSCounterexample.FlagVarieties.PointModel.Transfer
import RSCounterexample.FlagVarieties.PointModel.ProjectiveNormality

/-!
# The standard-monomial inputs over `ℂ`, and projective normality in characteristic `0`

* `standardMonomialTheory_complex`: over `ℂ` the general objects are those of the `ℂ`-development
  (`PointModel.Complex`, built on the Demazure library), so the standard-monomial inputs are the
  dimension count and the closure relation of the Demazure library on the flag-minor span.
* `standardMonomialTheory_of_charZero`: by `PointModel.StandardMonomialTheory.transfer` they hold
  over every field of characteristic `0`.
* `schubertUnion_normality_charZero` (**projective normality over an algebraically closed field of
  characteristic `0`**).
-/

open Schubert Demazure.FlagModule Demazure.SchubertUnions FinPermutation

namespace FlagVarieties.PointModel

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

/-- **The standard-monomial inputs over `ℂ`**, from the Demazure library. -/
theorem standardMonomialTheory_complex : StandardMonomialTheory ℂ := by
  refine ⟨fun {n d} h {S} hS => ?_, fun {n d} h {v w} hvw p hp hw => ?_⟩
  · have e : vanishSpan ℂ (columnMultiplicity h) S =
        PointModel.Complex.vanishSpan (columnMultiplicity h) S := by
      ext p
      rw [mem_vanishSpan, PointModel.Complex.mem_vanishSpan]
      rfl
    rw [e]
    exact PointModel.Complex.finrank_vanishSpan_add h hS
  · have hz : flagOrbitRestriction w p = 0 := by
      funext z
      exact hw (upperRowMatrix z) ⟨upperRowMatrix_upper z, upperRowMatrix_diag z⟩
    have hz' := flagOrbitRestriction_zero_of_bruhat_columns h hvw p hp hz
    intro u hu
    obtain ⟨z, rfl⟩ := IsUnitriangular.exists_upperRowMatrix hu
    exact congrFun hz' z

/-- The standard-monomial inputs hold over every field of characteristic `0`. -/
theorem standardMonomialTheory_of_charZero (K : Type*) [Field K] [CharZero K] :
    StandardMonomialTheory K :=
  StandardMonomialTheory.transfer ℂ K standardMonomialTheory_complex

/-- **Projective normality over an algebraically closed field of characteristic `0`** (ring form,
with `Γ(X_w, 𝒪) = K` (`GlobalSectionsConstant`) as hypothesis): every `t ∈ 𝒪(GL_n)` semi-invariant
of weight
`λ = shapeWeight m` on `π⁻¹ X_S`, `S` a Bruhat ideal, agrees there with an element of `A_λ`. -/
theorem schubertUnion_normality_charZero_of_globalSectionsConstant {K : Type*} [Field K]
    [IsAlgClosed K] [CharZero K]
    (hglobalSections : ∀ w : Equiv.Perm (Fin n), GlobalSectionsConstant K w) (m : ColumnShape n)
    {S : Finset (Equiv.Perm (Fin n))} (hS : BruhatLower S) (t : GLCoord K n)
    (ht : IsSemiInvOn (orbitSet K S) (shapeWeightZ m) t) :
    ∃ a ∈ minorSpan K m, t - algebraMap (MatrixEntryPolynomial K n) (GLCoord K n) a ∈
        orbitIdeal K S :=
  schubertUnion_normality_of_globalSectionsConstant (standardMonomialTheory_of_charZero K)
      hglobalSections m
      hS t ht

end

end FlagVarieties.PointModel
