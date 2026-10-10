import RSCounterexample.FlagVarieties.Foundations.TypeA.MatrixBruhatDecompositionBottom

/-!
# Clearing a finite set of columns to the right of a pivot

The resulting matrix is an explicit product of upper-triangular
transvections.  Every processed column is kept zero while the pivot
column remains unchanged.
-/

namespace FlagVarieties.Foundations.TypeA

open Matrix

variable {n : ℕ} {K : Type*} [Field K]

theorem exists_upper_right_clear_finset
    (A : Matrix (Fin n) (Fin n) K) (r c : Fin n)
    (hp : A r c ≠ 0) (S : Finset (Fin n)) :
    (∀ j ∈ S, c < j) →
    ∃ R : Matrix (Fin n) (Fin n) K,
      R.IsUpperTriangular ∧ IsUnit R ∧
      (A * R) r c = A r c ∧
      (∀ j ∈ S, (A * R) r j = 0) ∧
      ∀ j ∉ S, (A * R) r j = A r j := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      intro _
      refine ⟨1, Matrix.blockTriangular_one, isUnit_one, by simp, ?_, ?_⟩
      · simp
      · simp
  | @insert j S hj ih =>
      intro hS
      have hSj : c < j := hS j (Finset.mem_insert_self j S)
      have hS' : ∀ t ∈ S, c < t :=
        fun t ht => hS t (Finset.mem_insert_of_mem ht)
      obtain ⟨R, hR, huR, hRp, hRz, hRkeep⟩ := ih hS'
      let M := A * R
      let E := rightPivotEliminator M r c j
      have hMp : M r c ≠ 0 := by simpa [M, hRp] using hp
      refine ⟨R * E, hR.mul (rightPivotEliminator_upper M r c j hSj),
        huR.mul (rightPivotEliminator_isUnit M r c j hSj), ?_, ?_, ?_⟩
      · calc
          (A * (R * E)) r c = (M * E) r c := by simp [M, Matrix.mul_assoc]
          _ = M r c := rightPivotEliminator_other_column M r c j c
            (ne_of_lt hSj) r
          _ = A r c := hRp
      · intro t ht
        rcases Finset.mem_insert.mp ht with rfl | htS
        · simpa [M, E, Matrix.mul_assoc] using
            (rightPivotEliminator_clear M r c t hMp)
        · have htj : t ≠ j := by
            intro he
            apply hj
            exact he ▸ htS
          calc
            (A * (R * E)) r t = (M * E) r t := by simp [M, Matrix.mul_assoc]
            _ = M r t := rightPivotEliminator_other_column M r c j t htj r
            _ = 0 := hRz t htS
      · intro t ht
        have htj : t ≠ j := by
          intro he
          apply ht
          exact Finset.mem_insert.mpr (Or.inl he)
        have htS : t ∉ S := by
          intro hmem
          exact ht (Finset.mem_insert_of_mem hmem)
        calc
          (A * (R * E)) r t = (M * E) r t := by simp [M, Matrix.mul_assoc]
          _ = M r t := rightPivotEliminator_other_column M r c j t htj r
          _ = A r t := hRkeep t htS

/-- If the pivot is the leftmost nonzero entry of a row, an invertible
upper-triangular right factor reduces that entire row to its pivot. -/
theorem exists_upper_right_clear
    (A : Matrix (Fin n) (Fin n) K) (r c : Fin n)
    (hp : A r c ≠ 0)
    (hleft : ∀ j : Fin n, j < c → A r j = 0) :
    ∃ R : Matrix (Fin n) (Fin n) K,
      R.IsUpperTriangular ∧ IsUnit R ∧
      (A * R) r c = A r c ∧
      ∀ j : Fin n, j ≠ c → (A * R) r j = 0 := by
  classical
  let S : Finset (Fin n) := Finset.univ.filter (fun j => c < j)
  have hS : ∀ j ∈ S, c < j := by
    intro j hj
    simpa [S] using hj
  obtain ⟨R, hR, huR, hpR, hz, hkeep⟩ :=
    exists_upper_right_clear_finset A r c hp S hS
  refine ⟨R, hR, huR, hpR, ?_⟩
  intro j hjc
  rcases lt_trichotomy j c with hlt | heq | hgt
  · have hjS : j ∉ S := by simp [S, not_lt_of_ge hlt.le]
    rw [hkeep j hjS, hleft j hlt]
  · exact (hjc heq).elim
  · exact hz j (by simp [S, hgt])

end FlagVarieties.Foundations.TypeA
