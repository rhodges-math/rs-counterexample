import Schubert.RS.Representation.CompositionFlag

namespace Schubert.RS.Representation
noncomputable section
open scoped BigOperators

theorem shapeWeight_strict_cut {n : ℕ} (m : ColumnShape n) (k j : Fin n)
    (hk : 0 < m k) (hkj : k < j) : shapeWeight m j < shapeWeight m k := by
  unfold shapeWeight
  apply Finset.sum_lt_sum
  · intro i hi
    by_cases hj : j ≤ i
    · simp [hj, le_trans hkj.le hj]
    · simp [hj]
  · refine ⟨k, Finset.mem_univ _, ?_⟩
    simpa [not_le.mpr hkj] using hk

theorem stabilizer_preserves_prefix {n : ℕ} (m : ColumnShape n) (w : Equiv.Perm (Fin n))
    (hw : ∀ i, shapeWeight m (w i) = shapeWeight m i) (k : Fin n) (hk : 0 < m k)
    (i : Fin n) (hi : i ≤ k) : w i ≤ k := by
  by_contra h
  have hs := shapeWeight_strict_cut m k (w i) hk (lt_of_not_ge h)
  rw [hw i] at hs
  exact (not_lt_of_ge (shapeWeight_antitone m hi)) hs

def stabilizerPrefixPermutation {n : ℕ} (m : ColumnShape n) (w : Equiv.Perm (Fin n))
    (hw : ∀ i, shapeWeight m (w i) = shapeWeight m i) (k : Fin n) (hk : 0 < m k) :
    Equiv.Perm (Fin (k.val+1)) where
  toFun i := ⟨(w (prefixIndex k i)).val, by
    have h := stabilizer_preserves_prefix m w hw k hk (prefixIndex k i) (by change i.val ≤ k.val; omega)
    change (w (prefixIndex k i)).val ≤ k.val at h
    omega⟩
  invFun i := ⟨(w.symm (prefixIndex k i)).val, by
    have hw' : ∀ i, shapeWeight m (w.symm i) = shapeWeight m i := by
      intro i
      simpa using (hw (w.symm i)).symm
    have h := stabilizer_preserves_prefix m w.symm hw' k hk (prefixIndex k i) (by change i.val ≤ k.val; omega)
    change (w.symm (prefixIndex k i)).val ≤ k.val at h
    omega⟩
  left_inv i := by
    apply Fin.ext
    change (w.symm (w (prefixIndex k i))).val = i.val
    rw [w.symm_apply_apply]
    rfl
  right_inv i := by
    apply Fin.ext
    change (w (w.symm (prefixIndex k i))).val = i.val
    rw [w.apply_symm_apply]
    rfl
theorem stabilizerPrefixPermutation_apply {n : ℕ} (m : ColumnShape n) (w : Equiv.Perm (Fin n))
    (hw : ∀ i, shapeWeight m (w i) = shapeWeight m i) (k : Fin n) (hk : 0 < m k)
    (i : Fin (k.val+1)) :
    prefixIndex k (stabilizerPrefixPermutation m w hw k hk i) = w (prefixIndex k i) := Fin.ext rfl

set_option backward.isDefEq.respectTransparency false in
theorem stabilizer_flagMinor {n : ℕ} (m : ColumnShape n) (w : Equiv.Perm (Fin n))
    (hw : ∀ i, shapeWeight m (w i) = shapeWeight m i) (k : Fin n) (hk : 0 < m k) :
    rowRename w (flagMinor k) =
      ((Equiv.Perm.sign (stabilizerPrefixPermutation m w hw k hk) : ℤ) : ℂ) • flagMinor k := by
  let M : Matrix (Fin (k.val+1)) (Fin (k.val+1)) (MatrixPolynomial n) :=
    fun i j => MvPolynomial.X (prefixIndex k i, prefixIndex k j)
  change rowRename w M.det = _ • M.det
  rw [AlgHom.map_det]
  have hm : (rowRename w).mapMatrix M = M.submatrix (stabilizerPrefixPermutation m w hw k hk) id := by
    apply Matrix.ext
    intro i j
    simp [M, Matrix.submatrix_apply, rowRename, stabilizerPrefixPermutation_apply]
  rw [hm, Matrix.det_permute, MvPolynomial.smul_eq_C_mul]
  simp
def stabilizerSeedScalar {n : ℕ} (m : ColumnShape n) (w : Equiv.Perm (Fin n))
    (hw : ∀ i, shapeWeight m (w i) = shapeWeight m i) : ℂ :=
  ∏ k, (if hk : 0 < m k then
    ((Equiv.Perm.sign (stabilizerPrefixPermutation m w hw k hk) : ℤ) : ℂ) else 1) ^ m k

theorem stabilizerSeedScalar_ne_zero {n : ℕ} (m : ColumnShape n) (w : Equiv.Perm (Fin n))
    (hw : ∀ i, shapeWeight m (w i) = shapeWeight m i) : stabilizerSeedScalar m w hw ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk
  apply pow_ne_zero
  split_ifs
  · exact_mod_cast (Units.ne_zero (Equiv.Perm.sign (stabilizerPrefixPermutation m w hw k ‹_›)))
  · exact one_ne_zero

theorem stabilizer_highestFlag {n : ℕ} (m : ColumnShape n) (w : Equiv.Perm (Fin n))
    (hw : ∀ i, shapeWeight m (w i) = shapeWeight m i) :
    rowRename w (highestFlag m) = stabilizerSeedScalar m w hw • highestFlag m := by
  classical
  unfold highestFlag stabilizerSeedScalar
  rw [map_prod, ← Finset.prod_smul]
  apply Finset.prod_congr rfl
  intro k hk
  rw [map_pow]
  by_cases hm : 0 < m k
  · rw [dif_pos hm, stabilizer_flagMinor m w hw k hm, smul_pow]
  · have hz : m k = 0 := by omega
    simp [hz]



end
end Schubert.RS.Representation

