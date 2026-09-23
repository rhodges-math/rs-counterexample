import Schubert.RS.Representation.FlagTorus

namespace Schubert.RS.Representation
noncomputable section
open scoped BigOperators

theorem derivation_prod_zero {A ι : Type*} [CommRing A] [Algebra ℂ A]
    (D : Derivation ℂ A A) (s : Finset ι) (f : ι → A) (h : ∀ i ∈ s, D (f i) = 0) :
    D (∏ i ∈ s, f i) = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Derivation.leibniz, h a (Finset.mem_insert_self ..),
      ih (fun i hi => h i (Finset.mem_insert_of_mem hi)), smul_zero, smul_zero, add_zero]

theorem derivation_prod_update {A ι : Type*} [CommRing A] [Algebra ℂ A]
    [Fintype ι] [DecidableEq ι] (D : Derivation ℂ A A) (f : ι → A) (j : ι)
    (h : ∀ i, i ≠ j → D (f i) = 0) :
    D (∏ i, f i) = ∏ i, Function.update f j (D (f j)) i := by
  have hz : D (∏ i ∈ Finset.univ.erase j, f i) = 0 :=
    derivation_prod_zero D _ f (fun i hi => h i (Finset.mem_erase.mp hi).1)
  rw [Finset.prod_update_of_mem (Finset.mem_univ j), Finset.sdiff_singleton_eq_erase]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j), Derivation.leibniz, hz]
  simp [smul_eq_mul, mul_comm]

/-- If only one row is differentiated, the determinant derivative is the
determinant with that row replaced. Derived directly from the Leibniz formula. -/
theorem derivation_det_updateRow {A ι : Type*} [CommRing A] [Algebra ℂ A]
    [Fintype ι] [DecidableEq ι] (D : Derivation ℂ A A) (M : Matrix ι ι A) (j : ι)
    (h : ∀ i, i ≠ j → ∀ c, D (M i c) = 0) :
    D M.det = (M.updateRow j (fun c => D (M j c))).det := by
  rw [← Matrix.det_transpose M, Matrix.det_apply', map_sum,
    ← Matrix.det_transpose (M.updateRow j _), Matrix.det_apply']
  apply Finset.sum_congr rfl
  intro w hw
  simp only [Derivation.leibniz, Derivation.map_intCast, smul_eq_mul, mul_zero, add_zero,
    Matrix.transpose_apply]
  congr 1
  rw [derivation_prod_update D (fun i => M i (w i)) j (fun i hi => h i hi (w i))]
  apply Finset.prod_congr rfl
  intro i hi
  by_cases hij : i = j
  · subst i; simp
  · simp only [Function.update_of_ne hij, Matrix.updateRow_apply, if_neg hij]

theorem rootDerivation_X {n : ℕ} (r : PositiveRoot n) (i j : Fin n) :
    rowDerivation (rootVector r).val (MvPolynomial.X (i,j)) =
      if i = r.val.2 then MvPolynomial.X (r.val.1,j) else 0 := by
  classical
  rw [rowDerivation_X]
  by_cases hi : i = r.val.2 <;> simp [rootVector, Matrix.single, ite_smul, hi, eq_comm]

theorem rootDerivation_flagMinor {n : ℕ} (r : PositiveRoot n) (k : Fin n) :
    rowDerivation (rootVector r).val (flagMinor k) = 0 := by
  classical
  let D := rowDerivation (rootVector r).val
  let M : Matrix (Fin (k.val+1)) (Fin (k.val+1)) (MatrixPolynomial n) :=
    fun i j => MvPolynomial.X (prefixIndex k i, prefixIndex k j)
  change D M.det = 0
  by_cases hj : r.val.2.val ≤ k.val
  · let j : Fin (k.val+1) := ⟨r.val.2.val, by omega⟩
    let i : Fin (k.val+1) := ⟨r.val.1.val, by have h := r.property; change r.val.1.val < r.val.2.val at h; omega⟩
    have hjr : prefixIndex k j = r.val.2 := Fin.ext rfl
    have hir : prefixIndex k i = r.val.1 := Fin.ext rfl
    have hij : i ≠ j := by
      intro h
      have := congrArg (prefixIndex k) h
      rw [hir, hjr] at this
      exact ne_of_lt r.property this
    rw [derivation_det_updateRow D M j]
    · have hr : (fun c => D (M j c)) = M i := by
        funext c
        change rowDerivation (rootVector r).val (MvPolynomial.X (prefixIndex k j, prefixIndex k c)) =
          MvPolynomial.X (prefixIndex k i, prefixIndex k c)
        rw [hjr, hir, rootDerivation_X, if_pos rfl]
      rw [hr]
      exact Matrix.det_updateRow_eq_zero (M := M) hij
    · intro s hs c
      change rowDerivation (rootVector r).val (MvPolynomial.X (prefixIndex k s, prefixIndex k c)) = 0
      rw [rootDerivation_X, if_neg]
      intro he
      apply hs
      exact prefixIndex_injective k (he.trans hjr.symm)
  · have hz (i c : Fin (k.val+1)) : D (M i c) = 0 := by
      change rowDerivation (rootVector r).val (MvPolynomial.X (prefixIndex k i, prefixIndex k c)) = 0
      rw [rootDerivation_X, if_neg]
      intro he
      have hv := congrArg Fin.val he
      have hi := i.isLt
      change i.val = r.val.2.val at hv
      omega
    rw [Matrix.det_apply', map_sum]
    apply Finset.sum_eq_zero
    intro w hw
    rw [Derivation.leibniz, Derivation.map_intCast,
      derivation_prod_zero D Finset.univ _ (fun i hi => hz (w i) i)]
    simp

/-- Every positive root kills the concrete highest flag polynomial, with no
JP, PBW, irreducibility, or character premise. -/
theorem rootDerivation_highestFlag {n : ℕ} (r : PositiveRoot n) (m : ColumnShape n) :
    rowDerivation (rootVector r).val (highestFlag m) = 0 := by
  apply derivation_prod_zero
  intro k hk
  rw [Derivation.leibniz_pow, rootDerivation_flagMinor]
  simp

theorem rootOperator_highestFlag {n : ℕ} (r : PositiveRoot n) (m : ColumnShape n) :
    polynomialEnveloping n (rootOperator r) (highestFlag m) = 0 := by
  rw [polynomialEnveloping_root]
  exact rootDerivation_highestFlag r m

end
end Schubert.RS.Representation


