import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Data.Matrix.Basis

/-!
# Upper unitriangular matrices are products of elementary matrices

Every upper unitriangular matrix `u` over a commutative ring is a finite product of elementary
matrices `1 + c • E_ij` with `i < j` (`exists_elemList_of_isUnitriangular`). The proof clears, one
at a time, a nonzero entry above the diagonal in the lowest row that has one.
-/

namespace FlagVarieties.PointModel

open Matrix

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The elementary matrix `1 + c • E_ij` attached to `((i, j), c)`. -/
def elemMatrix (x : (Fin n × Fin n) × R) : Matrix (Fin n) (Fin n) R :=
  1 + x.2 • single x.1.1 x.1.2 1

/-- A matrix is **upper unitriangular**: upper triangular with ones on the diagonal. -/
def IsUnitriangular (u : Matrix (Fin n) (Fin n) R) : Prop :=
  u.IsUpperTriangular ∧ ∀ i, u i i = 1

/-- The positions strictly above the diagonal where `u` does not vanish. -/
noncomputable def offDiagSupport (u : Matrix (Fin n) (Fin n) R) : Finset (Fin n × Fin n) := by
  classical exact Finset.univ.filter fun p => p.1 < p.2 ∧ u p.1 p.2 ≠ 0

theorem mem_offDiagSupport {u : Matrix (Fin n) (Fin n) R} {p : Fin n × Fin n} :
    p ∈ offDiagSupport u ↔ p.1 < p.2 ∧ u p.1 p.2 ≠ 0 := by
  classical
  simp [offDiagSupport]

theorem IsUnitriangular.eq_one_of_offDiagSupport_eq_empty {u : Matrix (Fin n) (Fin n) R}
    (hu : IsUnitriangular u) (h : offDiagSupport u = ∅) : u = 1 := by
  ext i j
  rcases lt_trichotomy i j with hij | rfl | hij
  · by_contra hne
    have hmem : (i, j) ∈ offDiagSupport u :=
      mem_offDiagSupport.mpr ⟨hij, by simpa [Matrix.one_apply_ne hij.ne] using hne⟩
    simp [h] at hmem
  · rw [hu.2 i, Matrix.one_apply_eq]
  · rw [hu.1 hij, Matrix.one_apply_ne (ne_of_gt hij)]

/-- One clearing step: if `(i, j)` lies above the diagonal and no row below `i` meets the
support, then left multiplication by `1 - u_ij • E_ij` clears exactly the entry `(i, j)`. -/
theorem clear_apply {u : Matrix (Fin n) (Fin n) R} (hu : IsUnitriangular u) {i j : Fin n}
    (hij : i < j) (hrow : ∀ p ∈ offDiagSupport u, p.1 ≤ i) (r s : Fin n) :
    ((1 + (-u i j) • single i j 1 : Matrix (Fin n) (Fin n) R) * u) r s =
      if r = i ∧ s = j then 0 else u r s := by
  have hrowj : u j s = if s = j then 1 else 0 := by
    rcases lt_trichotomy s j with hsj | rfl | hsj
    · rw [hu.1 hsj, ite_eq_right hsj.ne]
    · rw [hu.2, ite_eq_left rfl]
    · rw [ite_eq_right hsj.ne']
      by_contra hne
      exact absurd hij (not_lt.mpr (hrow (j, s) (mem_offDiagSupport.mpr ⟨hsj, hne⟩)))
  rw [Matrix.add_mul, Matrix.one_mul, Matrix.add_apply, Matrix.smul_mul, Matrix.smul_apply]
  by_cases hr : r = i
  · subst hr
    rw [Matrix.single_mul_apply_same, hrowj, one_mul]
    by_cases hs : s = j
    · subst hs
      simp
    · simp [hs]
  · rw [Matrix.single_mul_apply_of_ne _ _ _ _ _ hr]
    simp [hr]

theorem elemMatrix_mul_clear (u : Matrix (Fin n) (Fin n) R) {i j : Fin n} (hij : i < j) :
    elemMatrix ((i, j), u i j) * ((1 + (-u i j) • single i j 1 : Matrix (Fin n) (Fin n) R) * u) =
      u := by
  have hE : (single i j (1 : R)) * single i j 1 = 0 := single_mul_single_of_ne _ _ _ _ hij.ne' _
  have h1 : (1 + u i j • single i j (1 : R)) * (1 + (-u i j) • single i j 1) = 1 := by
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul, hE, smul_zero, smul_zero, add_zero, add_assoc, ← add_smul,
      neg_add_cancel, zero_smul, add_zero]
  rw [← Matrix.mul_assoc]
  simp only [elemMatrix]
  rw [h1, Matrix.one_mul]

/-- **Upper unitriangular matrices are products of elementary matrices** `1 + c • E_ij`,
`i < j`. -/
theorem exists_elemList_of_isUnitriangular :
    ∀ (k : ℕ) (u : Matrix (Fin n) (Fin n) R), (offDiagSupport u).card = k → IsUnitriangular u →
      ∃ l : List ((Fin n × Fin n) × R), (∀ x ∈ l, x.1.1 < x.1.2) ∧ u = (l.map elemMatrix).prod := by
  intro k
  induction k with
  | zero =>
    intro u hk hu
    exact ⟨[], by simp,
      (by simpa using hu.eq_one_of_offDiagSupport_eq_empty (Finset.card_eq_zero.mp hk))⟩
  | succ k ih =>
    intro u hk hu
    classical
    have hne : (offDiagSupport u).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨⟨i, j⟩, hp, hmaxp⟩ := Finset.exists_max_image (offDiagSupport u) Prod.fst hne
    have hrow : ∀ p ∈ offDiagSupport u, p.1 ≤ i := hmaxp
    have hij : i < j := (mem_offDiagSupport.mp hp).1
    have happ := clear_apply hu hij hrow
    set u' := (1 + (-u i j) • single i j 1 : Matrix (Fin n) (Fin n) R) * u with hu'def
    have hu' : IsUnitriangular u' := by
      refine ⟨fun r s hsr => ?_, fun r => ?_⟩
      · rw [happ, ite_eq_right, hu.1 hsr]
        rintro ⟨rfl, rfl⟩
        exact absurd hij (not_lt.mpr hsr.le)
      · rw [happ, ite_eq_right, hu.2]
        rintro ⟨rfl, h⟩
        exact lt_irrefl _ (h ▸ hij)
    have hsupp : offDiagSupport u' = (offDiagSupport u).erase (i, j) := by
      ext ⟨r, s⟩
      rw [Finset.mem_erase, mem_offDiagSupport, mem_offDiagSupport, happ]
      by_cases hrs : r = i ∧ s = j
      · obtain ⟨rfl, rfl⟩ := hrs
        simp
      · rw [ite_eq_right hrs]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨fun h => hrs (Prod.mk.inj h), h1, h2⟩
        · rintro ⟨-, h1, h2⟩
          exact ⟨h1, h2⟩
    have hcard : (offDiagSupport u').card = k := by
      rw [hsupp, Finset.card_erase_of_mem hp]
      omega
    obtain ⟨l, hl, hprod⟩ := ih u' hcard hu'
    refine ⟨((i, j), u i j) :: l, ?_, ?_⟩
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hij
      · exact hl x hx
    · rw [List.map_cons, List.prod_cons, ← hprod, hu'def, elemMatrix_mul_clear u hij]

theorem IsUnitriangular.exists_elemList {u : Matrix (Fin n) (Fin n) R} (hu : IsUnitriangular u) :
    ∃ l : List ((Fin n × Fin n) × R), (∀ x ∈ l, x.1.1 < x.1.2) ∧ u = (l.map elemMatrix).prod :=
  exists_elemList_of_isUnitriangular _ u rfl hu

end FlagVarieties.PointModel
