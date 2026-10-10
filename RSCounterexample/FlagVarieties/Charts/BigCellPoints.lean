import RSCounterexample.FlagVarieties.Charts.BigCell
import RSCounterexample.FlagVarieties.Charts.Unipotent
import RSCounterexample.FlagVarieties.Flag.Stabilizer

/-!
# Points of the big cells

* `FlagVarieties.matrixFlag g`: the flag `g · E•` of an invertible matrix (its steps are the spans
  of the initial columns of `g`).
* `FlagVarieties.inBigCell_matrixFlag_iff`: `g · E•` lies in the big cell of `v` iff the matrices
  `bigCellBlock v j g` are invertible.
* `FlagVarieties.bigCellMatrix_eq_of_perm_mul`: the matrix `ẇ u` (`u` lower unitriangular) with
  a given flag is unique; it is the adapted matrix `bigCellMatrix`.
* `FlagVarieties.bigCellPoint_unique`: an `R`-algebra map out of the chart ring of the big cell is
  determined by the flag it classifies.
-/

noncomputable section

namespace FlagVarieties

open AlgebraicGeometry CategoryTheory
open Foundations Foundations.QuotientCharts

universe u

variable {R : Type u} [CommRing R] {n : ℕ} {A : Type u} [CommRing A]

/-- The flag `g · E•` of an invertible matrix `g`. -/
def matrixFlag (g : Matrix (Fin n) (Fin n) A) (hg : IsUnit g.det) : CoordinateFlag A n :=
  (FlagScheme.standardRingFlag n A).transport
    (g.toLinearEquiv' ((Matrix.isUnit_iff_isUnit_det g).mpr hg).invertible)

theorem matrixFlag_congr' {g g' : Matrix (Fin n) (Fin n) A} (h : g = g') {hg : IsUnit g.det}
    {hg' : IsUnit g'.det} : matrixFlag g hg = matrixFlag g' hg' := by
  subst h
  rfl

theorem matrixFlag_step (g : Matrix (Fin n) (Fin n) A) (hg : IsUnit g.det) (j : Fin (n + 1)) :
    ((matrixFlag g hg).step j).toSubmodule = (stdSpan A n j.val).map (Matrix.toLin' g) :=
  transport_standardRingFlag_step g _ j

theorem matrixFlag_eq_iff (g h : Matrix (Fin n) (Fin n) A) (hg : IsUnit g.det) (hh : IsUnit h.det) :
    matrixFlag g hg = matrixFlag h hh ↔ (g⁻¹ * h).BlockTriangular id := by
  rw [matrixFlag, matrixFlag, transport_standardRingFlag_eq_iff, Matrix.invOf_eq_nonsing_inv]

theorem inBigCell_matrixFlag_iff (v : Equiv.Perm (Fin n)) (g : Matrix (Fin n) (Fin n) A)
    (hg : IsUnit g.det) :
    InBigCell v (matrixFlag g hg) ↔ ∀ j : Fin (n + 1), IsUnit (bigCellBlock v j.val g).det := by
  refine forall_congr' fun j => ?_
  rw [matrixFlag_step, isCompl_map_stdSpan_iff]

theorem isUnit_det_perm_mul (v : Equiv.Perm (Fin n)) {u : Matrix (Fin n) (Fin n) A}
    (hu : IsLowerUnitriangular u) :
    IsUnit ((v.symm.toPEquiv.toMatrix : Matrix (Fin n) (Fin n) A) * u).det := by
  rw [Matrix.det_mul, hu.det_eq_one, mul_one, Matrix.det_permutation]
  exact (Equiv.Perm.sign v.symm).isUnit.map (Int.castRingHom A)

/-- `ẇ U⁻ · E•` lies in the big cell of `w`. -/
theorem inBigCell_matrixFlag_perm_mul (v : Equiv.Perm (Fin n)) {u : Matrix (Fin n) (Fin n) A}
    (hu : IsLowerUnitriangular u) :
    InBigCell v (matrixFlag _ (isUnit_det_perm_mul v hu)) :=
  (inBigCell_matrixFlag_iff v _ _).mpr fun j => isUnit_det_bigCellBlock_perm_mul v j.val hu

/-- Uniqueness: two matrices `ẇ u₁`, `ẇ u₂` (`uᵢ` lower unitriangular) with the same flag agree. -/
theorem perm_mul_eq_of_matrixFlag_eq (v : Equiv.Perm (Fin n)) {u₁ u₂ : Matrix (Fin n) (Fin n) A}
    (h₁ : IsLowerUnitriangular u₁) (h₂ : IsLowerUnitriangular u₂)
    (h : matrixFlag _ (isUnit_det_perm_mul v h₁) = matrixFlag _ (isUnit_det_perm_mul v h₂)) :
    u₁ = u₂ := by
  have hP : IsUnit (v.symm.toPEquiv.toMatrix : Matrix (Fin n) (Fin n) A).det := by
    rw [Matrix.det_permutation]
    exact (Equiv.Perm.sign v.symm).isUnit.map (Int.castRingHom A)
  rw [matrixFlag_eq_iff, Matrix.mul_inv_rev, Matrix.mul_assoc, ← Matrix.mul_assoc _ _ u₂,
    Matrix.nonsing_inv_mul _ hP, Matrix.one_mul] at h
  exact eq_of_isLowerUnitriangular_of_upper h₁ h₂ h

theorem isLowerUnitriangular_adaptedUnipotent (v : Equiv.Perm (Fin n))
    (V : ℕ → Submodule A (Fin n → A)) (hV : ∀ j, IsCompl (V j) (tailSpan v j)) :
    IsLowerUnitriangular (adaptedUnipotent v V hV) :=
  ⟨adaptedUnipotent_blockTriangular v V hV, adaptedVector_apply_self v V hV⟩

/-- The adapted matrix of a flag in the big cell, written `ẇ u`. -/
theorem bigCellMatrix_eq_perm_mul {v : Equiv.Perm (Fin n)} {P : CoordinateFlag A n}
    (hP : InBigCell v P) :
    ∃ u : Matrix (Fin n) (Fin n) A, IsLowerUnitriangular u ∧
      bigCellMatrix hP = (v.symm.toPEquiv.toMatrix : Matrix (Fin n) (Fin n) A) * u :=
  ⟨_, isLowerUnitriangular_adaptedUnipotent v _ _, adaptedMatrix_eq v _ _⟩

theorem matrixFlag_bigCellMatrix {v : Equiv.Perm (Fin n)} {P : CoordinateFlag A n}
    (hP : InBigCell v P) : matrixFlag (bigCellMatrix hP) (isUnit_det_bigCellMatrix hP) = P := by
  apply RingFlag.ext
  intro j
  rw [matrixFlag_step, stdSpan, Submodule.map_span, Set.image_image]
  have hj : flagSteps P j.val = (P.step j).toSubmodule := by
    unfold flagSteps
    simp only [Nat.lt_succ_iff.mp j.isLt, ↓reduceDIte]
  rw [← hj, ← span_adaptedVector v (isCompl_flagSteps hP) (flagSteps_monotone P) j.val]
  congr 1
  apply Set.image_congr
  intro k _
  funext i
  simp [bigCellMatrix, adaptedMatrix, Matrix.toLin'_apply, Pi.basisFun_apply]

/-- The adapted matrix is the unique `ẇ u` (`u` lower unitriangular) with the given flag. -/
theorem bigCellMatrix_eq_of_perm_mul {v : Equiv.Perm (Fin n)}
    {P : CoordinateFlag A n} (hP : InBigCell v P) {u : Matrix (Fin n) (Fin n) A}
    (hu : IsLowerUnitriangular u)
    (h : matrixFlag _ (isUnit_det_perm_mul v hu) = P) :
    bigCellMatrix hP = (v.symm.toPEquiv.toMatrix : Matrix (Fin n) (Fin n) A) * u := by
  obtain ⟨u₀, hu₀, he⟩ := bigCellMatrix_eq_perm_mul hP
  have hf : matrixFlag _ (isUnit_det_perm_mul v hu₀) = matrixFlag _ (isUnit_det_perm_mul v hu) := by
    rw [h, ← matrixFlag_bigCellMatrix hP]
    congr 1
    exact he.symm
  rw [he, perm_mul_eq_of_matrixFlag_eq v hu₀ hu hf]

/-! ### Generic matrix facts -/

theorem blockTriangular_nonsing_inv {M : Matrix (Fin n) (Fin n) A}
    (hM : M.BlockTriangular id) : M⁻¹.BlockTriangular id := by
  by_cases h : IsUnit M.det
  · let := M.invertibleOfIsUnitDet h
    exact Matrix.blockTriangular_inv_of_blockTriangular hM
  · rw [Matrix.nonsing_inv_apply_not_isUnit _ h]
    intro i j _
    rfl

theorem blockTriangular_map {B : Type*} [CommRing B]
    {M : Matrix (Fin n) (Fin n) A} (hM : M.BlockTriangular id) (f : A →+* B) :
    (M.map f).BlockTriangular id := fun i j h => by
  simp [Matrix.map_apply, hM h]

/-- Right multiplication by an invertible upper triangular matrix does not change the flag. -/
theorem matrixFlag_mul_of_upper (g b : Matrix (Fin n) (Fin n) A) (hg : IsUnit g.det)
    (hgb : IsUnit (g * b).det) (hb : IsUnit b.det) (hup : b.BlockTriangular id) :
    matrixFlag (g * b) hgb = matrixFlag g hg := by
  let : Invertible b := b.invertibleOfIsUnitDet hb
  apply RingFlag.ext
  intro j
  rw [matrixFlag_step, matrixFlag_step, Matrix.toLin'_mul, Submodule.map_comp,
    (map_stdSpan_eq_iff b).mpr hup]

/-- If `ẇ u b = ẇ u' b'` with `u, u'` lower unitriangular and `b, b'` invertible upper triangular,
then `u = u'`. -/
theorem eq_of_perm_mul_mul_eq (v : Equiv.Perm (Fin n)) {u u' b b' : Matrix (Fin n) (Fin n) A}
    (hu : IsLowerUnitriangular u) (hu' : IsLowerUnitriangular u')
    (hb : IsUnit b.det) (hb' : IsUnit b'.det) (hup : b.BlockTriangular id)
    (hup' : b'.BlockTriangular id)
    (h : (v.symm.toPEquiv.toMatrix : Matrix (Fin n) (Fin n) A) * u * b =
      (v.symm.toPEquiv.toMatrix : Matrix (Fin n) (Fin n) A) * u' * b') : u = u' := by
  have hdet : IsUnit ((v.symm.toPEquiv.toMatrix : Matrix (Fin n) (Fin n) A) * u * b).det := by
    rw [Matrix.det_mul]
    exact (isUnit_det_perm_mul v hu).mul hb
  have hdet' : IsUnit ((v.symm.toPEquiv.toMatrix : Matrix (Fin n) (Fin n) A) * u' * b').det := by
    rw [Matrix.det_mul]
    exact (isUnit_det_perm_mul v hu').mul hb'
  apply perm_mul_eq_of_matrixFlag_eq v hu hu'
  exact ((matrixFlag_mul_of_upper _ b _ hdet hb hup).symm.trans (matrixFlag_congr' h)).trans
    (matrixFlag_mul_of_upper _ b' _ hdet' hb' hup')


end FlagVarieties
