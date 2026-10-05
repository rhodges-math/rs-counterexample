import Schubert.FlagVarieties.Charts.Minors

/-!
# Lower unitriangular matrices and the big cell

* `FlagVarieties.IsLowerUnitriangular u`: `u` is lower triangular with ones on the diagonal.
* `FlagVarieties.eq_of_isLowerUnitriangular_of_upper`: if `u₁, u₂` are lower unitriangular and
  `u₁⁻¹ u₂` is upper triangular then `u₁ = u₂` (uniqueness in `U⁻ ∩ B = 1`).
* `FlagVarieties.isUnit_det_bigCellBlock_perm_mul`: the initial column spans of `ẇ u`, for `u`
  lower unitriangular, are complementary to the tail spans of `w`: `ẇ U⁻` lies in the big cell.
-/

noncomputable section

namespace FlagVarieties

open Matrix

variable {A : Type*} [CommRing A] {n : ℕ}

/-- `u` is lower triangular with ones on the diagonal. -/
def IsLowerUnitriangular (u : Matrix (Fin n) (Fin n) A) : Prop :=
  u.BlockTriangular OrderDual.toDual ∧ ∀ i, u i i = 1

theorem IsLowerUnitriangular.det_eq_one {u : Matrix (Fin n) (Fin n) A}
    (hu : IsLowerUnitriangular u) : u.det = 1 := by
  rw [Matrix.det_of_isLowerTriangular _ hu.1]
  exact Finset.prod_eq_one fun i _ => hu.2 i

theorem IsLowerUnitriangular.isUnit_det {u : Matrix (Fin n) (Fin n) A}
    (hu : IsLowerUnitriangular u) : IsUnit u.det := by
  rw [hu.det_eq_one]
  exact isUnit_one

theorem IsLowerUnitriangular.map {B : Type*} [CommRing B] (f : A →+* B)
    {u : Matrix (Fin n) (Fin n) A} (hu : IsLowerUnitriangular u) :
    IsLowerUnitriangular (u.map f) :=
  ⟨fun i j h => by simp [hu.1 h], fun i => by simp [hu.2 i]⟩

/-- The diagonal of a product of lower triangular matrices. -/
theorem mul_apply_self_of_lowerTriangular {u₁ u₂ : Matrix (Fin n) (Fin n) A}
    (h₁ : u₁.BlockTriangular OrderDual.toDual) (h₂ : u₂.BlockTriangular OrderDual.toDual)
    (i : Fin n) : (u₁ * u₂) i i = u₁ i i * u₂ i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro k _ hki
    rcases lt_or_gt_of_ne hki with h | h
    · rw [h₂ (OrderDual.toDual_lt_toDual.mpr h), mul_zero]
    · rw [h₁ (OrderDual.toDual_lt_toDual.mpr h), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem IsLowerUnitriangular.inv {u : Matrix (Fin n) (Fin n) A} (hu : IsLowerUnitriangular u) :
    IsLowerUnitriangular u⁻¹ := by
  have hinv : u⁻¹.BlockTriangular OrderDual.toDual := by
    let : Invertible u := u.invertibleOfIsUnitDet hu.isUnit_det
    exact Matrix.blockTriangular_inv_of_blockTriangular hu.1
  refine ⟨hinv, fun i => ?_⟩
  have h := congrFun (congrFun (Matrix.nonsing_inv_mul u hu.isUnit_det) i) i
  rw [mul_apply_self_of_lowerTriangular hinv hu.1, hu.2 i, mul_one, Matrix.one_apply_eq] at h
  exact h

theorem IsLowerUnitriangular.mul {u₁ u₂ : Matrix (Fin n) (Fin n) A}
    (h₁ : IsLowerUnitriangular u₁) (h₂ : IsLowerUnitriangular u₂) :
    IsLowerUnitriangular (u₁ * u₂) :=
  ⟨h₁.1.mul h₂.1, fun i => by rw [mul_apply_self_of_lowerTriangular h₁.1 h₂.1, h₁.2, h₂.2, one_mul]⟩

/-- A lower unitriangular matrix that is also upper triangular is the identity. -/
theorem IsLowerUnitriangular.eq_one_of_upper {u : Matrix (Fin n) (Fin n) A}
    (hu : IsLowerUnitriangular u) (hup : u.BlockTriangular id) : u = 1 := by
  ext i j
  rcases lt_trichotomy i j with h | rfl | h
  · rw [hu.1 (OrderDual.toDual_lt_toDual.mpr h), Matrix.one_apply_ne h.ne]
  · rw [hu.2, Matrix.one_apply_eq]
  · rw [hup (show id j < id i from h), Matrix.one_apply_ne h.ne']

/-- Uniqueness of the `U⁻`-factor: `u₁⁻¹ u₂` upper triangular forces `u₁ = u₂`. -/
theorem eq_of_isLowerUnitriangular_of_upper {u₁ u₂ : Matrix (Fin n) (Fin n) A}
    (h₁ : IsLowerUnitriangular u₁) (h₂ : IsLowerUnitriangular u₂)
    (h : (u₁⁻¹ * u₂).BlockTriangular id) : u₁ = u₂ := by
  have h1 := (h₁.inv.mul h₂).eq_one_of_upper h
  have h2 := congrArg (u₁ * ·) h1
  rwa [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ h₁.isUnit_det, Matrix.one_mul,
    Matrix.mul_one, eq_comm] at h2

/-! ### Matrices `ẇ u` lie in the big cell of `w` -/

/-- The matrix `[u₀ … u_{j-1} e_j … e_{n-1}]`: the first `j` columns of `u`, then the identity. -/
def truncateColumns (j : ℕ) (u : Matrix (Fin n) (Fin n) A) : Matrix (Fin n) (Fin n) A :=
  Matrix.of fun r c => if c.val < j then u r c else (1 : Matrix (Fin n) (Fin n) A) r c

theorem IsLowerUnitriangular.truncateColumns {u : Matrix (Fin n) (Fin n) A}
    (hu : IsLowerUnitriangular u) (j : ℕ) : IsLowerUnitriangular (truncateColumns j u) := by
  refine ⟨?_, fun i => ?_⟩
  · intro r c h
    have h' : r < c := OrderDual.toDual_lt_toDual.mp h
    simp only [FlagVarieties.truncateColumns, Matrix.of_apply]
    split_ifs
    · exact hu.1 h
    · exact Matrix.one_apply_ne h'.ne
  · simp only [FlagVarieties.truncateColumns, Matrix.of_apply]
    split_ifs
    · exact hu.2 i
    · exact Matrix.one_apply_eq i

theorem bigCellBlock_perm_mul (w : Equiv.Perm (Fin n)) (j : ℕ) (u : Matrix (Fin n) (Fin n) A) :
    bigCellBlock w j ((w.symm.toPEquiv.toMatrix : Matrix (Fin n) (Fin n) A) * u) =
      (w.symm.toPEquiv.toMatrix : Matrix (Fin n) (Fin n) A) * truncateColumns j u := by
  ext r c
  simp only [bigCellBlock, truncateColumns, Matrix.of_apply, PEquiv.toMatrix_toPEquiv_mul,
    Matrix.submatrix_apply, id]
  split_ifs with hc
  · rfl
  · rw [Pi.single_apply, Matrix.one_apply]
    by_cases h1 : r = w c
    · subst h1
      simp
    · have h2 : w.symm r ≠ c := fun h => h1 (by rw [← h, Equiv.apply_symm_apply])
      simp [h1, h2]

/-- `ẇ u` is in the big cell of `w` for every lower unitriangular `u`. -/
theorem isUnit_det_bigCellBlock_perm_mul (w : Equiv.Perm (Fin n)) (j : ℕ)
    {u : Matrix (Fin n) (Fin n) A} (hu : IsLowerUnitriangular u) :
    IsUnit (bigCellBlock w j ((w.symm.toPEquiv.toMatrix : Matrix (Fin n) (Fin n) A) * u)).det := by
  rw [bigCellBlock_perm_mul, Matrix.det_mul, (hu.truncateColumns j).det_eq_one, mul_one,
    Matrix.det_permutation]
  exact (Equiv.Perm.sign w.symm).isUnit.map (Int.castRingHom A)

end FlagVarieties
