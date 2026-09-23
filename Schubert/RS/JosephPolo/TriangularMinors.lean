import Schubert.RS.JosephPolo.FlagCoordinateDuality
import Mathlib.LinearAlgebra.Matrix.Block

namespace Schubert.RS.Representation
noncomputable section
open scoped BigOperators

theorem upperRowMatrix_upper {n : ℕ} (z : List (PositiveRoot n × ℂ)) :
    (upperRowMatrix z).IsUpperTriangular := by
  induction z with
  | nil => exact Matrix.blockTriangular_one
  | cons v z ih =>
    obtain ⟨r,t⟩ := v
    change ((1 + t • Matrix.single r.val.1 r.val.2 (1:ℂ)) * _).IsUpperTriangular
    apply Matrix.BlockTriangular.mul _ ih
    rw [Matrix.smul_single,smul_eq_mul,mul_one]
    exact Matrix.blockTriangular_one.add
      (Matrix.blockTriangular_single (b := id) r.property.le t)

theorem upperRowMatrix_diag {n : ℕ} (z : List (PositiveRoot n × ℂ)) (i : Fin n) :
    upperRowMatrix z i i = 1 := by
  induction z with
  | nil => simp [upperRowMatrix]
  | cons v z ih =>
    obtain ⟨r,t⟩ := v
    rw [upperRowMatrix,Matrix.add_mul,Matrix.one_mul,Matrix.smul_mul]
    by_cases hi : i = r.val.1
    · subst i
      simp only [Matrix.add_apply,Matrix.smul_apply,Matrix.single_mul_apply_same,
        one_mul,upperRowMatrix_upper z r.property,smul_zero,add_zero,ih]
    · simp only [Matrix.add_apply,Matrix.smul_apply,
        Matrix.single_mul_apply_of_ne _ _ _ _ _ hi,smul_zero,add_zero,ih]

theorem upperRowMatrix_principal_det {n k : ℕ} (z : List (PositiveRoot n × ℂ))
    (s : Fin k ↪o Fin n) : (upperRowMatrix z |>.submatrix s s).det = 1 := by
  have hu : (upperRowMatrix z |>.submatrix s s).IsUpperTriangular := by
    intro i j hij
    exact upperRowMatrix_upper z (s.strictMono hij)
  rw [Matrix.det_of_isUpperTriangular hu]
  simp only [Matrix.submatrix_apply,upperRowMatrix_diag,Finset.prod_const_one]

/-- A matching between two sorted lists forces coordinatewise dominance.
The pigeonhole argument includes the first coordinate and empty lists. -/
theorem monotone_le_of_permuted_le {α : Type*} [LinearOrder α] {k : ℕ}
    (s t : Fin k → α) (hs : Monotone s) (ht : Monotone t)
    (σ : Equiv.Perm (Fin k)) (h : ∀ j, s (σ j) ≤ t j) : ∀ i, s i ≤ t i := by
  intro i
  by_contra hn
  have hi : t i < s i := lt_of_not_ge hn
  let e : Fin (i.val+1) ↪ Fin k := Fin.castLEEmb (by omega)
  have hsmall (j : Fin (i.val+1)) : (σ (e j)).val < i.val := by
    by_contra hj
    have hs' := hs (show i ≤ σ (e j) from Nat.le_of_not_gt hj)
    have ht' := ht (show e j ≤ i from by exact Nat.le_of_lt_succ j.isLt)
    exact (not_lt_of_ge (hs'.trans ((h _).trans ht'))) hi
  let f : Fin (i.val+1) → Fin i.val := fun j => ⟨(σ (e j)).val,hsmall j⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply e.injective
    apply σ.injective
    exact Fin.ext (congrArg (fun j : Fin i.val => j.val) hab)
  have hc := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_fin] at hc
  omega

/-- A minor of an upper triangular matrix vanishes unless its sorted rows
are coordinatewise at most its sorted columns. No genericity is assumed. -/
theorem upperTriangular_minor_zero {R : Type*} [CommRing R] {n k : ℕ}
    (g : Matrix (Fin n) (Fin n) R) (hg : g.IsUpperTriangular)
    (s t : Fin k ↪o Fin n) (h : ¬ ∀ i, s i ≤ t i) :
    (g.submatrix s t).det = 0 := by
  classical
  rw [Matrix.det_apply]
  apply Finset.sum_eq_zero
  intro σ hσ
  have hz : ∃ i, g (s (σ i)) (t i) = 0 := by
    by_contra hn
    push Not at hn
    apply h
    apply monotone_le_of_permuted_le s t s.monotone t.monotone σ
    intro i
    by_contra hi
    exact hn i (hg (lt_of_not_ge hi))
  obtain ⟨i,hi⟩ := hz
  have hp : (∏ j : Fin k, (g.submatrix s t) (σ j) j) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) hi
  rw [hp,smul_zero]

theorem mul_rowPermutationMatrix {n : ℕ} (g : Square n) (w : Equiv.Perm (Fin n))
    (i j : Fin n) : (g * rowPermutationMatrix w) i j = g i (w j) := by
  classical
  simp [Matrix.mul_apply,rowPermutationMatrix,mul_ite]

end
end Schubert.RS.Representation
