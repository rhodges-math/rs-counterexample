import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Data.Fin.VecNotation

/-!
# Algebra of ordered projective coordinates

The standard grading and the evaluation map used by the `Proj`
construction. A unimodular pair makes the mapped irrelevant ideal the
unit ideal, without requiring either coordinate individually to be a unit.
-/

noncomputable section

namespace FlagVarieties.Foundations.ProjectiveLine

universe u

variable (R : Type u) [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The standard total-degree grading on two ordered variables. -/
abbrev grading : ℕ → Submodule R (MvPolynomial (Fin 2) R) :=
  MvPolynomial.homogeneousSubmodule (Fin 2) R

theorem variable_mem_irrelevant (i : Fin 2) :
    MvPolynomial.X i ∈ (HomogeneousIdeal.irrelevant (grading R)).toIdeal :=
  HomogeneousIdeal.mem_irrelevant_of_mem (grading R) (by decide : 0 < (1 : ℕ))
    (MvPolynomial.isHomogeneous_X R i)

/-- The constants as elements of the degree-zero part. -/
def constants : R →+* grading R 0 where
  toFun r := ⟨MvPolynomial.C r, MvPolynomial.isHomogeneous_C (Fin 2) r⟩
  map_one' := Subtype.ext (map_one MvPolynomial.C)
  map_mul' r s := Subtype.ext (map_mul MvPolynomial.C r s)
  map_zero' := Subtype.ext (map_zero MvPolynomial.C)
  map_add' r s := Subtype.ext (map_add MvPolynomial.C r s)

@[simp] theorem constants_coe (r : R) :
    ((constants R r : grading R 0) : MvPolynomial (Fin 2) R) = MvPolynomial.C r := rfl

/-- The degree-zero component is exactly the coefficient ring. -/
theorem constants_bijective : Function.Bijective (constants R) := by
  constructor
  · intro r s h
    exact MvPolynomial.C_injective (Fin 2) R (congrArg Subtype.val h)
  · intro p
    have hp : (p : MvPolynomial (Fin 2) R).totalDegree = 0 :=
      (MvPolynomial.totalDegree_zero_iff_isHomogeneous (Fin 2)).mpr p.property
    exact ⟨(p : MvPolynomial (Fin 2) R).coeff 0,
      Subtype.ext (MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hp).symm⟩

/-- Explicit identification of the base of the standard grading. -/
def constantsEquiv : R ≃+* grading R 0 :=
  RingEquiv.ofBijective (constants R) (constants_bijective R)

variable {R} {S : Type*} [CommRing S] (φ : R →+* S) (δ ε : S)

/-- Evaluation at the ordered quotient-coordinate pair. -/
def evaluation : MvPolynomial (Fin 2) R →+* S :=
  MvPolynomial.eval₂Hom φ ![δ, ε]

@[simp] theorem evaluation_X (i : Fin 2) :
    evaluation φ δ ε (MvPolynomial.X i) = ![δ, ε] i :=
  MvPolynomial.eval₂Hom_X' _ _ _

@[simp] theorem evaluation_C (r : R) :
    evaluation φ δ ε (MvPolynomial.C r) = φ r :=
  MvPolynomial.eval₂Hom_C _ _ _

/-- Bézout coefficients put one in the image of the irrelevant ideal. -/
theorem map_irrelevant_eq_top (h : IsCoprime δ ε) :
    (HomogeneousIdeal.irrelevant (grading R)).toIdeal.map (evaluation φ δ ε) = ⊤ := by
  let I := (HomogeneousIdeal.irrelevant (grading R)).toIdeal.map (evaluation φ δ ε)
  have hδ : δ ∈ I := by
    simpa only [evaluation_X, Matrix.cons_val_zero] using
      Ideal.mem_map_of_mem (evaluation φ δ ε) (variable_mem_irrelevant R 0)
  have hε : ε ∈ I := by
    simpa only [evaluation_X, Matrix.cons_val_one, Matrix.cons_val_zero] using
      Ideal.mem_map_of_mem (evaluation φ δ ε) (variable_mem_irrelevant R 1)
  obtain ⟨a, b, hab⟩ := h
  apply (Ideal.eq_top_iff_one _).mpr
  change (1 : S) ∈ I
  rw [← hab]
  exact I.add_mem (I.mul_mem_left a hδ) (I.mul_mem_left b hε)

end FlagVarieties.Foundations.ProjectiveLine
