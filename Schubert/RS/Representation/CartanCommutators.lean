import Schubert.RS.Representation.CyclicGeneration

namespace Schubert.RS.Representation
noncomputable section
open scoped BigOperators

variable {A : Type*} [CommRing A] [Algebra ℂ A]

theorem derivation_eigen_mul (D : Derivation ℂ A A) (p q : A) (k l : ℕ)
    (hp : D p = k • p) (hq : D q = l • q) : D (p*q) = (k+l) • (p*q) := by
  rw [Derivation.leibniz, hp, hq]
  simp only [smul_eq_mul, nsmul_eq_mul, Nat.cast_add]
  ring

theorem derivation_eigen_pow (D : Derivation ℂ A A) (p : A) (k : ℕ)
    (hp : D p = k • p) (m : ℕ) : D (p^m) = (k*m) • p^m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, derivation_eigen_mul D (p^m) p (k*m) k ih hp, Nat.mul_succ]

theorem derivation_eigen_prod {ι : Type*} (D : Derivation ℂ A A) (s : Finset ι)
    (p : ι → A) (k : ι → ℕ) (h : ∀ i ∈ s, D (p i) = k i • p i) :
    D (∏ i ∈ s, p i) = (∑ i ∈ s, k i) • ∏ i ∈ s, p i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    apply derivation_eigen_mul D _ _ _ _ (h i (Finset.mem_insert_self ..))
    exact ih (fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem diagonalDerivation_minor {n : ℕ} (a k : Fin n) :
    matrixUnitDerivation a a (flagMinor k) = (if a≤k then 1 else 0 : ℕ) • flagMinor k := by
  classical
  by_cases ha : a≤k
  · rw [if_pos ha, one_nsmul]
    let D := matrixUnitDerivation a a
    let M : Matrix (Fin (k.val+1)) (Fin (k.val+1)) (MatrixPolynomial n) :=
      fun i j => MvPolynomial.X (prefixIndex k i,prefixIndex k j)
    let j : Fin (k.val+1) := ⟨a.val, by change a.val ≤ k.val at ha; omega⟩
    have hj : prefixIndex k j = a := Fin.ext rfl
    change D M.det = M.det
    rw [derivation_det_updateRow D M j]
    · have hr : (fun c => D (M j c)) = M j := by
        funext c
        change matrixUnitDerivation a a (MvPolynomial.X (prefixIndex k j,prefixIndex k c)) = MvPolynomial.X (prefixIndex k j,prefixIndex k c)
        rw [hj, matrixUnitDerivation_X, if_pos rfl]
      rw [hr, Matrix.updateRow_eq_self]
    · intro s hs c
      change matrixUnitDerivation a a (MvPolynomial.X (prefixIndex k s,prefixIndex k c)) = 0
      rw [matrixUnitDerivation_X, if_neg]
      intro h
      exact hs (prefixIndex_injective k (h.trans hj.symm))
  · rw [if_neg ha, zero_nsmul]
    exact matrixUnitDerivation_minor_absent a a k (lt_of_not_ge ha)

theorem diagonalDerivation_highestFlag {n : ℕ} (m : ColumnShape n) (a : Fin n) :
    matrixUnitDerivation a a (highestFlag m) = shapeWeight m a • highestFlag m := by
  apply derivation_eigen_prod
  intro k hk
  have h := derivation_eigen_pow (matrixUnitDerivation a a) (flagMinor k)
    (if a≤k then 1 else 0) (diagonalDerivation_minor a k) (m k)
  simpa only [ite_mul, one_mul, zero_mul] using h

theorem diagonalDerivation_extremalFlag {n : ℕ} (m : ColumnShape n) (w : Equiv.Perm (Fin n))
    (a : Fin n) : matrixUnitDerivation a a (extremalFlag m w) = extremalWeight m w a • extremalFlag m w := by
  change matrixUnitDerivation a a (rowRename w (highestFlag m)) = _
  rw [matrixUnitDerivation_rowRename, diagonalDerivation_highestFlag, map_nsmul]
  rfl

/-- The exact matrix-unit commutator on actual polynomials. -/
theorem matrixUnitDerivation_commutator {n : ℕ} (a b c d : Fin n) (p : MatrixPolynomial n) :
    matrixUnitDerivation a b (matrixUnitDerivation c d p) - matrixUnitDerivation c d (matrixUnitDerivation a b p) =
      (if b=c then matrixUnitDerivation a d p else 0) - (if d=a then matrixUnitDerivation c b p else 0) := by
  classical
  have hd : ⁅matrixUnitDerivation a b, matrixUnitDerivation c d⁆ =
      (if b=c then matrixUnitDerivation a d else 0) - (if d=a then matrixUnitDerivation c b else 0) := by
    apply MvPolynomial.derivation_ext
    rintro ⟨i,j⟩
    simp only [Derivation.commutator_apply, Derivation.sub_apply, matrixUnitDerivation_X]
    split_ifs <;> simp_all [matrixUnitDerivation_X, eq_comm]
  have h := congrArg (fun D : Derivation ℂ (MatrixPolynomial n) (MatrixPolynomial n) => D p) hd
  by_cases hbc : b=c <;> by_cases hda : d=a <;>
    simpa [hbc, hda, Derivation.commutator_apply] using h

end
end Schubert.RS.Representation

