import Schubert.RS.Representation.FlagDiagonal

namespace Schubert.RS.Representation
noncomputable section
open scoped BigOperators

theorem flagMinorScalar_eq_prod_if {n : ℕ} (k : Fin n) (t : DiagonalTorus n) :
    flagMinorScalar k t = ∏ i : Fin n, if i ≤ k then (t i : ℂ) else 1 := by
  classical
  have h : (∏ i : Fin (k.val+1), (t (prefixIndex k i) : ℂ)) =
      ∏ i ∈ Finset.univ.filter (fun i : Fin n => i ≤ k), (t i : ℂ) := by
    apply Finset.prod_bij (fun i _ => prefixIndex k i)
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      change i.val ≤ k.val
      omega
    · intro i hi j hj hij
      exact prefixIndex_injective k hij
    · intro j hj
      have hjk := (Finset.mem_filter.mp hj).2
      refine ⟨⟨j.val, by change j.val ≤ k.val at hjk; omega⟩, Finset.mem_univ _, ?_⟩
      exact Fin.ext rfl
    · intro i hi
      rfl
  simpa only [flagMinorScalar, Finset.prod_filter] using h

theorem highestFlagScalar_eq_weightScalar {n : ℕ} (m : ColumnShape n) (t : DiagonalTorus n) :
    highestFlagScalar m t = weightScalar (shapeWeight m) t := by
  classical
  unfold highestFlagScalar weightScalar
  simp_rw [flagMinorScalar_eq_prod_if, ← Finset.prod_pow]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro i hi
  have hp (k : Fin n) : (if i ≤ k then (t i : ℂ) else 1) ^ m k =
      (t i : ℂ) ^ (if i ≤ k then m k else 0) := by split_ifs <;> simp
  simp_rw [hp]
  rw [Finset.prod_pow_eq_pow_sum]
  rfl

theorem highestFlag_weight {n : ℕ} (m : ColumnShape n) (t : DiagonalTorus n) :
    polynomialTorus n t (highestFlag m) =
      integerWeightScalar (fun i => (shapeWeight m i : ℤ)) t • highestFlag m := by
  rw [highestFlag_diagonal, highestFlagScalar_eq_weightScalar, integerWeightScalar_nat]

theorem torus_rowRename {n : ℕ} (w : Equiv.Perm (Fin n)) (t : DiagonalTorus n)
    (p : MatrixPolynomial n) :
    polynomialTorus n t (rowRename w p) =
      rowRename w (polynomialTorus n (fun i => t (w i)) p) := by
  have h : (rowAction (Matrix.diagonal fun i => (t i : ℂ))).comp (rowRename w) =
      (rowRename w).comp (rowAction (Matrix.diagonal fun i => (t (w i) : ℂ))) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨r,c⟩
    simp [rowRename, rowAction_X, Matrix.diagonal_apply]
  exact AlgHom.congr_fun h p

theorem extremalFlag_weight {n : ℕ} (m : ColumnShape n) (w : Equiv.Perm (Fin n))
    (t : DiagonalTorus n) :
    polynomialTorus n t (extremalFlag m w) =
      integerWeightScalar (fun i => (extremalWeight m w i : ℤ)) t • extremalFlag m w := by
  change polynomialTorus n t (rowRename w (highestFlag m)) = _
  rw [torus_rowRename, highestFlag_weight, integerWeightScalar_nat, map_smul, integerWeightScalar_nat]
  congr 1
  unfold weightScalar extremalWeight
  exact Fintype.prod_equiv w _ _ (fun i => by simp)

end
end Schubert.RS.Representation
