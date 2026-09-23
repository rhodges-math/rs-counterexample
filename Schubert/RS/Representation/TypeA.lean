import Mathlib.Algebra.Lie.Matrix
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Complex.Basic

namespace Schubert.RS.Representation

noncomputable section
open scoped BigOperators
attribute [local instance 100] LieRing.ofAssociativeRing

abbrev Square (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

/-- Matrix support in a prescribed root pattern. -/
def SupportedOn {n : ℕ} (r : Fin n → Fin n → Prop) (A : Square n) : Prop :=
  ∀ i j, ¬ r i j → A i j = 0

theorem supportedOn_mul {n : ℕ} (r : Fin n → Fin n → Prop)
    (hr : Transitive r) {A B : Square n} (hA : SupportedOn r A) (hB : SupportedOn r B) :
    SupportedOn r (A * B) := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hik : r i k
  · have hkj : ¬ r k j := fun h => hij (hr hik h)
    rw [hB k j hkj, mul_zero]
  · rw [hA i k hik, zero_mul]

/-- A transitive matrix support pattern is closed under the actual commutator. -/
def patternLie {n : ℕ} (r : Fin n → Fin n → Prop) (hr : Transitive r) :
    LieSubalgebra ℂ (Square n) where
  carrier := {A | SupportedOn r A}
  zero_mem' := by intro i j _; rfl
  add_mem' := by
    intro A B hA hB i j hij
    change A i j + B i j = 0
    rw [hA i j hij, hB i j hij, zero_add]
  smul_mem' := by
    intro c A hA i j hij
    change c * A i j = 0
    rw [hA i j hij, mul_zero]
  lie_mem' := by
    intro A B hA hB i j hij
    change (A * B) i j - (B * A) i j = 0
    rw [supportedOn_mul r hr hA hB i j hij,
      supportedOn_mul r hr hB hA i j hij, sub_zero]

/-- The strictly upper-triangular matrix Lie algebra, with commutator bracket. -/
def upperNilpotent (n : ℕ) : LieSubalgebra ℂ (Square n) :=
  patternLie (fun i j => i < j) (fun _ _ _ => lt_trans)

/-- Roots killed linearly by the JP presentation at weight `u`. -/
def killingRelation {n : ℕ} (u : Fin n → ℕ) (i j : Fin n) : Prop :=
  i < j ∧ u j ≤ u i

theorem killingRelation_transitive {n : ℕ} (u : Fin n → ℕ) :
    Transitive (killingRelation u) := by
  intro i j k hij hjk
  exact ⟨hij.1.trans hjk.1, hjk.2.trans hij.2⟩

/-- The paper's linear-killing root space is an actual Lie subalgebra. -/
def killingSubalgebra {n : ℕ} (u : Fin n → ℕ) : LieSubalgebra ℂ (Square n) :=
  patternLie (killingRelation u) (killingRelation_transitive u)

theorem killingSubalgebra_le {n : ℕ} (u : Fin n → ℕ) :
    killingSubalgebra u ≤ upperNilpotent n := by
  intro A hA i j hij
  exact hA i j (fun h => hij h.1)

/-- A matrix unit belongs to any support pattern containing its root. -/
theorem single_mem_pattern {n : ℕ} (r : Fin n → Fin n → Prop)
    (hr : Transitive r) {i j : Fin n} (hij : r i j) :
    Matrix.single i j (1 : ℂ) ∈ patternLie r hr := by
  intro p q hpq
  rw [Matrix.single_apply]
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    exact False.elim (hpq hij)
  · rfl

/-- The matrix support description agrees with the ordinary linear span
of the specified matrix-unit roots; no Lie closure is silently added. -/
theorem pattern_eq_span {n : ℕ} (r : Fin n → Fin n → Prop) (hr : Transitive r) :
    (patternLie r hr).toSubmodule = Submodule.span ℂ
      {A | ∃ i j, r i j ∧ A = Matrix.single i j (1 : ℂ)} := by
  classical
  apply le_antisymm
  · intro A hA
    rw [Matrix.matrix_eq_sum_single A]
    apply Submodule.sum_mem
    intro i _
    apply Submodule.sum_mem
    intro j _
    by_cases hij : r i j
    · have hm : Matrix.single i j (1 : ℂ) ∈ Submodule.span ℂ
          {A | ∃ i j, r i j ∧ A = Matrix.single i j (1 : ℂ)} :=
        Submodule.subset_span ⟨i, j, hij, rfl⟩
      simpa using Submodule.smul_mem _ (A i j) hm
    · rw [hA i j hij, Matrix.single_zero]
      exact Submodule.zero_mem _
  · apply Submodule.span_le.mpr
    rintro A ⟨i, j, hij, rfl⟩
    exact single_mem_pattern r hr hij

/-- Positive root positions, retaining both matrix indices. -/
abbrev PositiveRoot (n : ℕ) := {ij : Fin n × Fin n // ij.1 < ij.2}

/-- The root matrix inside the actual nilpotent Lie algebra. -/
def rootVector {n : ℕ} (r : PositiveRoot n) : upperNilpotent n :=
  ⟨Matrix.single r.val.1 r.val.2 1,
    single_mem_pattern (fun i j : Fin n => i < j)
      (fun _ _ _ => lt_trans) r.property⟩

end
end Schubert.RS.Representation
