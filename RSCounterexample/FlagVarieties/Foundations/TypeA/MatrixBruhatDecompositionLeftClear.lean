import RSCounterexample.FlagVarieties.Foundations.TypeA.MatrixBruhatDecompositionRightClear

/-!
# Clearing entries above an established pivot

The left factor is an explicit finite product of upper-triangular row
transvections.  It fixes the pivot row and all unprocessed rows.
-/

namespace FlagVarieties.Foundations.TypeA

open Matrix

variable {n : ℕ} {K : Type*} [Field K]

theorem exists_upper_left_clear_finset
    (A : Matrix (Fin n) (Fin n) K) (r c : Fin n)
    (hp : A r c ≠ 0) (S : Finset (Fin n)) :
    (∀ i ∈ S, i < r) →
    ∃ L : Matrix (Fin n) (Fin n) K,
      L.IsUpperTriangular ∧ IsUnit L ∧
      (L * A) r c = A r c ∧
      (∀ i ∈ S, (L * A) i c = 0) ∧
      ∀ i ∉ S, ∀ j, (L * A) i j = A i j := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      intro _
      refine ⟨1, Matrix.blockTriangular_one, isUnit_one, by simp, ?_, ?_⟩
      · simp
      · simp
  | @insert i S hi ih =>
      intro hS
      have hir : i < r := hS i (Finset.mem_insert_self i S)
      have hS' : ∀ t ∈ S, t < r :=
        fun t ht => hS t (Finset.mem_insert_of_mem ht)
      obtain ⟨L, hL, huL, hLp, hLz, hLkeep⟩ := ih hS'
      let M := L * A
      let E := leftPivotEliminator M r c i
      have hMp : M r c ≠ 0 := by simpa [M, hLp] using hp
      refine ⟨E * L, (leftPivotEliminator_upper M r c i hir).mul hL,
        (leftPivotEliminator_isUnit M r c i hir).mul huL, ?_, ?_, ?_⟩
      · calc
          ((E * L) * A) r c = (E * M) r c := by simp [M, Matrix.mul_assoc]
          _ = M r c := leftPivotEliminator_other_row M r c i r
            (ne_of_gt hir) c
          _ = A r c := hLp
      · intro t ht
        rcases Finset.mem_insert.mp ht with rfl | htS
        · simpa [M, E, Matrix.mul_assoc] using
            (leftPivotEliminator_clear M r c t hMp)
        · have hti : t ≠ i := by
            intro he
            apply hi
            exact he ▸ htS
          calc
            ((E * L) * A) t c = (E * M) t c := by simp [M, Matrix.mul_assoc]
            _ = M t c := leftPivotEliminator_other_row M r c i t hti c
            _ = 0 := hLz t htS
      · intro t ht
        have hti : t ≠ i := by
          intro he
          apply ht
          exact Finset.mem_insert.mpr (Or.inl he)
        have htS : t ∉ S := by
          intro hmem
          exact ht (Finset.mem_insert_of_mem hmem)
        intro j
        calc
          ((E * L) * A) t j = (E * M) t j := by simp [M, Matrix.mul_assoc]
          _ = M t j := leftPivotEliminator_other_row M r c i t hti j
          _ = A t j := hLkeep t htS j

end FlagVarieties.Foundations.TypeA
