import Schubert.RS.WindowKeyCoefficient
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! Count the actual relative-PBW basis vectors in each coefficient degree. -/

namespace Schubert.RS
noncomputable section
open Representation
variable {n : ℕ}

def AscentDegreeFiber (u : Composition n) (d : RootDegree n) :=
  {a : AscentRoot u → ℕ // monomialDegree (extendAscentPowers u a) = d}

theorem extendAscentPowers_injective (u : Composition n) :
    Function.Injective (extendAscentPowers u) := by
  intro a b h
  funext r
  have he := congrFun h r.val
  simpa [extendAscentPowers, r.property] using he

instance ascentDegreeFiber_finite (u : Composition n) (d : RootDegree n) :
    Finite (AscentDegreeFiber u d) := by
  letI : Finite {a : PositiveRoot n → ℕ // monomialDegree a = d} :=
    (monomialDegree_fiber_finite d).to_subtype
  apply Finite.of_injective (fun a : AscentDegreeFiber u d =>
    (⟨extendAscentPowers u a.val, a.property⟩ : {a : PositiveRoot n → ℕ // monomialDegree a = d}))
  intro a b h
  exact Subtype.ext (extendAscentPowers_injective u (congrArg Subtype.val h))

instance ascentDegreeFiber_fintype (u : Composition n) (d : RootDegree n) :
    Fintype (AscentDegreeFiber u d) := Fintype.ofFinite _

theorem linearBasis_cut_eigen (u : Composition n) (hpbw : HasOrderedPBWBasis n)
    (a : AscentRoot u → ℕ) (k : Fin (n-1)) :
    linearTorusRepresentation u (cutTorus k) (linearPresentationBasis u hpbw a) =
      (weightScalar u (cutTorus k) * (2 : ℂ)^monomialDegree (extendAscentPowers u a) k) •
        linearPresentationBasis u hpbw a := by
  rw [linearPresentationBasis_weight, orderedMonomialScalar_cut]

theorem linearDegreePiece_eq_basisSpan (u : Composition n) (hpbw : HasOrderedPBWBasis n)
    (d : RootDegree n) :
    linearDegreePiece u hpbw d = Submodule.span ℂ
      (linearPresentationBasis u hpbw '' {a | monomialDegree (extendAscentPowers u a) = d}) := by
  apply le_antisymm
  · intro x hx
    apply (linearPresentationBasis u hpbw).mem_span_image.mpr
    intro a ha
    have hn := Finsupp.mem_support_iff.mp ha
    ext k
    apply complex_two_pow_injective
    have h := basis_coord_eigenmap (linearPresentationBasis u hpbw)
      (linearTorusRepresentation u (cutTorus k))
      (fun b => weightScalar u (cutTorus k) * (2 : ℂ)^monomialDegree (extendAscentPowers u b) k)
      (fun b => linearBasis_cut_eigen u hpbw b k) a x
    rw [linearDegreePiece_cut_eigen u hpbw d hx k, map_smul,
      Finsupp.smul_apply, smul_eq_mul] at h
    exact (mul_left_cancel₀ (weightScalar_ne_zero u (cutTorus k))
      (mul_right_cancel₀ hn h)).symm
  · apply Submodule.span_le.mpr
    rintro x ⟨a, ha, rfl⟩
    apply (mem_linearDegreePiece_iff_cut_eigen u hpbw d _).mpr
    intro k
    rw [linearBasis_cut_eigen, ha]

/-- Each finite degree piece has exactly one basis vector per ascent-root
exponent function of that degree. This is a proved count, not a character
or PBW-quotient formula assumed as an extra input. -/
theorem linearDegreePiece_finrank (u : Composition n) (hpbw : HasOrderedPBWBasis n)
    (d : RootDegree n) :
    Module.finrank ℂ (linearDegreePiece u hpbw d) = Fintype.card (AscentDegreeFiber u d) := by
  classical
  rw [linearDegreePiece_eq_basisSpan]
  have he : linearPresentationBasis u hpbw '' {a | monomialDegree (extendAscentPowers u a) = d} =
      Set.range (fun a : AscentDegreeFiber u d => linearPresentationBasis u hpbw a.val) := by
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨a.val, a.property, rfl⟩
  rw [he]
  exact finrank_span_eq_card ((linearPresentationBasis u hpbw).linearIndependent.comp
    Subtype.val Subtype.val_injective)

variable {E : Type*} [AddCommGroup E] [Module ℂ E]
  [Module (Enveloping n) E] [IsScalarTower ℂ (Enveloping n) E]

/-- The local coefficient count for a key, with the Joseph-Polo,
Demazure character, and universal PBW hypotheses explicit. -/
theorem key_coefficient_eq_ascent_count (u : Composition n)
    (ρ : DiagonalTorus n →* Module.End ℂ E) (ξ : E)
    (hJP : HasJosephPoloPresentation u ρ ξ) (hDCF : HasDemazureCharacter u ρ)
    (hpbw : HasOrderedPBWBasis n) (β d : RootDegree n) (hd : d ≤ β)
    (hβ : ∀ r : PositiveRoot n, u r.val.1 < u r.val.2 →
      ¬ jpExponent u r • rootDegree r.val.1 r.val.2 ≤ β) :
    (toLaurent (key u)).coeff (weightOfRootDegree u d) =
      (Fintype.card (AscentDegreeFiber u d) : ℤ) := by
  rw [key_coefficient_eq_linear_window_dimension u ρ ξ hJP hDCF hpbw β d hd hβ,
    linearDegreePiece_finrank]

end
end Schubert.RS
