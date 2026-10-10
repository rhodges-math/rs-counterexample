import RSCounterexample.FlagVarieties.Charts.BigCellPoints
import RSCounterexample.FlagVarieties.LineBundle.Model

/-!
# The big cell functions

* `FlagVarieties.glCoord_algHom_ext`: `R`-algebra maps out of `𝒪(GLₙ)` are determined by the
  matrix of the generic point.
* `FlagVarieties.bigCellFunction R v = ∏ⱼ det (bigCellBlock v j X) ∈ 𝒪(GLₙ)`: up to sign the
  product of the leading minors `Δ_{v(0..j-1)}^{0..j-1}` of the generic matrix.
* `FlagVarieties.isUnit_map_bigCellFunction_iff`: a point `g` of `GLₙ` lies over the big cell of
  `v` (i.e. `g · E•` is in the big cell) iff `f_v(g)` is a unit.
-/

noncomputable section

namespace FlagVarieties

open AlgebraicGeometry CategoryTheory
open Foundations Foundations.QuotientCharts
open scoped TensorProduct

universe u

variable (R : Type u) [CommRing R] {n : ℕ}

/-! ### Algebra maps out of `𝒪(GLₙ)` -/

/-- The matrix of an `R`-algebra map out of `𝒪(GLₙ)`. -/
theorem pointMatrix_comp {A B : Type u} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
    (k : GLCoord R n →ₐ[R] A) (φ : A →ₐ[R] B) :
    GLScheme.pointMatrix R n (φ.comp k) = (GLScheme.pointMatrix R n k).map φ := by
  ext i j
  rfl

/-- `R`-algebra maps out of `𝒪(GLₙ)` are determined by the matrix of the generic point. -/
theorem glCoord_algHom_ext {A : Type u} [CommRing A] [Algebra R A] {k k' : GLCoord R n →ₐ[R] A}
    (h : GLScheme.pointMatrix R n k = GLScheme.pointMatrix R n k') : k = k' :=
  genericMatrix_algHom_ext h

theorem pointMatrix_glPointOfMatrix' {A : Type u} [CommRing A] [Algebra R A]
    (g : Matrix (Fin n) (Fin n) A) (hg : IsUnit g.det) :
    (genericMatrix R n).map (glPointOfMatrix R g hg) = g :=
  pointMatrix_glPointOfMatrix R g hg

/-! ### The big cell function -/

variable {R}

theorem bigCellBlock_map {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    (v : Equiv.Perm (Fin n)) (j : ℕ) (g : Matrix (Fin n) (Fin n) A) :
    (bigCellBlock v j g).map f = bigCellBlock v j (g.map f) := by
  ext r c
  simp only [bigCellBlock, Matrix.map_apply, Matrix.of_apply]
  split_ifs
  · rfl
  · simp [Pi.single_apply, apply_ite f]

variable (R) in
/-- `f_v = ∏ⱼ det (bigCellBlock v j X)`: up to sign the product of the leading minors
`Δ_{v(0..j-1)}^{0..j-1}` of the generic matrix. -/
def bigCellFunction (v : Equiv.Perm (Fin n)) : GLCoord R n :=
  ∏ j : Fin (n + 1), (bigCellBlock v j.val (genericMatrix R n)).det

theorem map_bigCellFunction {A : Type u} [CommRing A] [Algebra R A] (v : Equiv.Perm (Fin n))
    (k : GLCoord R n →ₐ[R] A) :
    k (bigCellFunction R v) = ∏ j : Fin (n + 1),
      (bigCellBlock v j.val (GLScheme.pointMatrix R n k)).det := by
  rw [bigCellFunction, map_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← AlgHom.coe_toRingHom, ← det_map_ringHom, bigCellBlock_map]
  rfl

/-- A point of `GLₙ` lies over the big cell iff `f_v` is a unit there. -/
theorem isUnit_map_bigCellFunction_iff {A : Type u} [CommRing A] [Algebra R A]
    (v : Equiv.Perm (Fin n)) (k : GLCoord R n →ₐ[R] A) :
    IsUnit (k (bigCellFunction R v)) ↔
      InBigCell v (matrixFlag (GLScheme.pointMatrix R n k)
        ((Matrix.isUnit_iff_isUnit_det _).mp (generalLinearMatrixAt_isUnit R A n k))) := by
  rw [map_bigCellFunction, IsUnit.prod_univ_iff, inBigCell_matrixFlag_iff]

end FlagVarieties
