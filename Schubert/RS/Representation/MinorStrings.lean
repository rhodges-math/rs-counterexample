import Schubert.RS.Representation.DerivationStrings

namespace Schubert.RS.Representation
noncomputable section
open scoped BigOperators

def matrixUnitDerivation {n : ℕ} (a b : Fin n) : Derivation ℂ (MatrixPolynomial n) (MatrixPolynomial n) :=
  rowDerivation (Matrix.single a b 1)

theorem matrixUnitDerivation_X {n : ℕ} (a b i j : Fin n) :
    matrixUnitDerivation a b (MvPolynomial.X (i,j)) = if i=b then MvPolynomial.X (a,j) else 0 := by
  classical
  rw [matrixUnitDerivation, rowDerivation_X]
  by_cases hi : i=b
  · subst i; simp [Matrix.single, ite_smul]
  · simp [Matrix.single, ite_smul, hi, Ne.symm hi]

theorem derivation_det_zero {A ι : Type*} [CommRing A] [Algebra ℂ A]
    [Fintype ι] [DecidableEq ι] (D : Derivation ℂ A A) (M : Matrix ι ι A)
    (h : ∀ i j, D (M i j) = 0) : D M.det = 0 := by
  rw [Matrix.det_apply', map_sum]
  apply Finset.sum_eq_zero
  intro w hw
  rw [Derivation.leibniz, Derivation.map_intCast,
    derivation_prod_zero D Finset.univ _ (fun i hi => h (w i) i)]
  simp

theorem matrixUnitDerivation_minor_absent {n : ℕ} (a b k : Fin n) (hb : k < b) :
    matrixUnitDerivation a b (flagMinor k) = 0 := by
  apply derivation_det_zero
  intro i j
  rw [matrixUnitDerivation_X, if_neg]
  intro he
  have h := congrArg Fin.val he
  have hi := i.isLt
  change i.val = b.val at h
  change k.val < b.val at hb
  omega

theorem matrixUnitDerivation_minor_present {n : ℕ} (a b k : Fin n)
    (hab : a ≠ b) (ha : a ≤ k) (hb : b ≤ k) : matrixUnitDerivation a b (flagMinor k) = 0 := by
  classical
  let D := matrixUnitDerivation a b
  let M : Matrix (Fin (k.val+1)) (Fin (k.val+1)) (MatrixPolynomial n) :=
    fun i j => MvPolynomial.X (prefixIndex k i, prefixIndex k j)
  let i : Fin (k.val+1) := ⟨a.val, by change a.val ≤ k.val at ha; omega⟩
  let j : Fin (k.val+1) := ⟨b.val, by change b.val ≤ k.val at hb; omega⟩
  have hi : prefixIndex k i = a := Fin.ext rfl
  have hj : prefixIndex k j = b := Fin.ext rfl
  have hij : i ≠ j := by intro h; exact hab (hi.symm.trans ((congrArg (prefixIndex k) h).trans hj))
  change D M.det = 0
  rw [derivation_det_updateRow D M j]
  · have hr : (fun c => D (M j c)) = M i := by
      funext c
      change matrixUnitDerivation a b (MvPolynomial.X (prefixIndex k j,prefixIndex k c)) = MvPolynomial.X (prefixIndex k i,prefixIndex k c)
      rw [hi, hj, matrixUnitDerivation_X, if_pos rfl]
    rw [hr]
    exact Matrix.det_updateRow_eq_zero (M := M) hij
  · intro s hs c
    change matrixUnitDerivation a b (MvPolynomial.X (prefixIndex k s,prefixIndex k c)) = 0
    rw [matrixUnitDerivation_X, if_neg]
    intro he
    exact hs (prefixIndex_injective k (he.trans hj.symm))

set_option backward.isDefEq.respectTransparency false in
theorem matrixUnitDerivation_minor_active {n : ℕ} (a b k : Fin n)
    (ha : k < a) (hb : b ≤ k) :
    matrixUnitDerivation a b (flagMinor k) = rowRename (Equiv.swap a b) (flagMinor k) := by
  classical
  let D := matrixUnitDerivation a b
  let M : Matrix (Fin (k.val+1)) (Fin (k.val+1)) (MatrixPolynomial n) :=
    fun i j => MvPolynomial.X (prefixIndex k i, prefixIndex k j)
  let j : Fin (k.val+1) := ⟨b.val, by change b.val ≤ k.val at hb; omega⟩
  have hj : prefixIndex k j = b := Fin.ext rfl
  have hna (s : Fin (k.val+1)) : prefixIndex k s ≠ a := by
    intro h
    have h' := congrArg Fin.val h
    have hs := s.isLt
    change s.val = a.val at h'
    change k.val < a.val at ha
    omega
  change D M.det = rowRename (Equiv.swap a b) M.det
  rw [AlgHom.map_det, derivation_det_updateRow D M j]
  · congr 1
    apply Matrix.ext
    intro s c
    by_cases hs : s=j
    · subst s
      simp [Matrix.updateRow_apply, D, M, hj, matrixUnitDerivation_X, rowRename]
    · have hnb : prefixIndex k s ≠ b := fun h => hs (prefixIndex_injective k (h.trans hj.symm))
      simp [Matrix.updateRow_apply, hs, M, rowRename, Equiv.swap_apply_of_ne_of_ne (hna s) hnb]
  · intro s hs c
    change matrixUnitDerivation a b (MvPolynomial.X (prefixIndex k s,prefixIndex k c)) = 0
    rw [matrixUnitDerivation_X, if_neg]
    intro he
    exact hs (prefixIndex_injective k (he.trans hj.symm))

set_option backward.isDefEq.respectTransparency false in
theorem matrixUnitDerivation_minor_active_twice {n : ℕ} (a b k : Fin n)
    (ha : k < a) (hb : b ≤ k) :
    matrixUnitDerivation a b (matrixUnitDerivation a b (flagMinor k)) = 0 := by
  rw [matrixUnitDerivation_minor_active a b k ha hb]
  unfold flagMinor
  rw [AlgHom.map_det]
  apply derivation_det_zero
  intro i j
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, rowRename, MvPolynomial.rename_X]
  rw [matrixUnitDerivation_X, if_neg]
  intro h
  have he : prefixIndex k i = a := by
    have hh := congrArg (Equiv.swap a b) h
    simpa using hh
  have h' := congrArg Fin.val he
  have hi := i.isLt
  change i.val = a.val at h'
  change k.val < a.val at ha
  omega

end
end Schubert.RS.Representation

