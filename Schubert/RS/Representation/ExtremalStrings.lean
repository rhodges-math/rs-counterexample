import Schubert.RS.Representation.HighestStrings

namespace Schubert.RS.Representation
noncomputable section
open scoped BigOperators

theorem highestFlag_swap_iter {n : ℕ} (m : ColumnShape n) (a b : Fin n) (hba : b<a) :
    ∃ c : ℂ, c ≠ 0 ∧ rowRename (Equiv.swap a b) (highestFlag m) =
      c • derivationIter (matrixUnitDerivation a b) (stringDegree m a b) (highestFlag m) := by
  let d := stringDegree m a b
  have hd : (d.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero d
  have he : derivationIter (matrixUnitDerivation a b) d (highestFlag m) =
      (d.factorial : ℂ) • stringEndpoint m a b := by
    simpa only [Nat.cast_smul_eq_nsmul] using (highestFlag_derivationTop m a b hba).1
  refine ⟨highestSwapScalar m a b hba / (d.factorial : ℂ), div_ne_zero (highestSwapScalar_ne_zero m a b hba) hd, ?_⟩
  rw [he, smul_smul, div_mul_cancel₀ _ hd, swap_highestFlag_endpoint]

theorem matrixUnitDerivation_rowRename {n : ℕ} (a b : Fin n) (w : Equiv.Perm (Fin n))
    (p : MatrixPolynomial n) :
    matrixUnitDerivation a b (rowRename w p) =
      rowRename w (matrixUnitDerivation (w.symm a) (w.symm b) p) := by
  have hx (rc : Fin n × Fin n) : matrixUnitDerivation a b (rowRename w (MvPolynomial.X rc)) =
      rowRename w (matrixUnitDerivation (w.symm a) (w.symm b) (MvPolynomial.X rc)) := by
    obtain ⟨i,j⟩ := rc
    simp only [rowRename, MvPolynomial.rename_X, matrixUnitDerivation_X]
    by_cases hi : i=w.symm b
    · subst i; simp
    · have hw : w i ≠ b := fun h => hi (w.eq_symm_apply.mpr h)
      simp [hi, hw]
  induction p using MvPolynomial.induction_on with
  | C c => simp [rowRename]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p rc hp =>
    simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add, hp, hx]

theorem derivationIter_rowRename {n : ℕ} (a b : Fin n) (w : Equiv.Perm (Fin n))
    (p : MatrixPolynomial n) (d : ℕ) :
    derivationIter (matrixUnitDerivation a b) d (rowRename w p) =
      rowRename w (derivationIter (matrixUnitDerivation (w.symm a) (w.symm b)) d p) := by
  induction d with
  | zero => rfl
  | succ d ih => rw [derivationIter_succ, ih, matrixUnitDerivation_rowRename, derivationIter_succ]

theorem rowRename_swap_conjugate {n : ℕ} (a b : Fin n) (w : Equiv.Perm (Fin n))
    (p : MatrixPolynomial n) :
    rowRename (Equiv.swap a b) (rowRename w p) =
      rowRename w (rowRename (Equiv.swap (w.symm a) (w.symm b)) p) := by
  rw [← rowRename_mul, ← rowRename_mul]
  have he : Equiv.swap a b * w = w * Equiv.swap (w.symm a) (w.symm b) := by
    apply Equiv.ext
    intro i
    simpa only [Equiv.apply_symm_apply, Equiv.Perm.mul_apply] using w.injective.swap_apply (w.symm a) (w.symm b) i
  rw [he]

theorem extremalFlag_swap_iter {n : ℕ} (m : ColumnShape n) (w : Equiv.Perm (Fin n))
    (a b : Fin n) (hu : extremalWeight m w a < extremalWeight m w b) :
    ∃ c : ℂ, c ≠ 0 ∧ rowRename (Equiv.swap a b) (extremalFlag m w) =
      c • derivationIter (matrixUnitDerivation a b) (stringDegree m (w.symm a) (w.symm b)) (extremalFlag m w) := by
  have hba : w.symm b < w.symm a := by
    by_contra h
    exact (not_lt_of_ge (shapeWeight_antitone m (le_of_not_gt h))) hu
  obtain ⟨c, hc, he⟩ := highestFlag_swap_iter m (w.symm a) (w.symm b) hba
  refine ⟨c, hc, ?_⟩
  change rowRename (Equiv.swap a b) (rowRename w (highestFlag m)) = _
  rw [rowRename_swap_conjugate, he, map_smul, ← derivationIter_rowRename]
  rfl

theorem root_derivationIter_mem {n : ℕ} (r : PositiveRoot n) (p : MatrixPolynomial n) (d : ℕ) :
    derivationIter (matrixUnitDerivation r.val.1 r.val.2) d p ∈ upperCyclic p := by
  induction d with
  | zero => exact upperCyclic_seed p
  | succ d ih =>
    rw [derivationIter_succ]
    have h := upperCyclic_stable p (rootOperator r) ih
    rw [polynomialEnveloping_root] at h
    exact h

theorem extremalFlag_swap_mem {n : ℕ} (m : ColumnShape n) (w : Equiv.Perm (Fin n))
    (r : PositiveRoot n) (hu : extremalWeight m w r.val.1 < extremalWeight m w r.val.2) :
    rowRename (Equiv.swap r.val.1 r.val.2) (extremalFlag m w) ∈ flagDemazure m w := by
  obtain ⟨c, hc, he⟩ := extremalFlag_swap_iter m w r.val.1 r.val.2 hu
  rw [he]
  exact (upperCyclic _).smul_mem c (root_derivationIter_mem r _ _)

end
end Schubert.RS.Representation

