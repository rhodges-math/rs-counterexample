import Schubert.RS.Representation.PolynomialCovariance
import Schubert.RS.Representation.MinorStrings
import Schubert.RS.FullWeightWindow
import Mathlib.LinearAlgebra.Eigenspace.Basic

namespace Schubert.RS.Representation
noncomputable section

theorem polynomialTorus_matrixUnit {n : ℕ} (t : DiagonalTorus n) (a b : Fin n)
    (p : MatrixPolynomial n) :
    polynomialTorus n t (matrixUnitDerivation a b p) =
      rootScalar t a b • matrixUnitDerivation a b (polynomialTorus n t p) := by
  have hm : torusMatrix t (Matrix.single a b 1) =
      rootScalar t a b • Matrix.single a b 1 := by
    ext i j
    simp only [torusMatrix, Matrix.single_apply, Matrix.smul_apply, smul_eq_mul]
    split_ifs with h
    · obtain ⟨rfl,rfl⟩ := h
      rfl
    · simp
  change rowAction _ (rowDerivation _ p) = _
  rw [rowDerivation_torus, hm]
  have hd := (rowDerivationLinear n).map_smul (rootScalar t a b) (Matrix.single a b 1)
  change rowDerivation (rootScalar t a b • Matrix.single a b 1) =
    rootScalar t a b • rowDerivation (Matrix.single a b 1) at hd
  rw [hd]
  rfl

theorem matrixUnit_derivationIter_weight {n : ℕ} (a b : Fin n)
    (p : MatrixPolynomial n) (v : Weight n)
    (hp : ∀ t, polynomialTorus n t p = integerWeightScalar v t • p)
    (k : ℕ) (t : DiagonalTorus n) :
    polynomialTorus n t (derivationIter (matrixUnitDerivation a b) k p) =
      integerWeightScalar (v + k • positiveRoot a b) t •
        derivationIter (matrixUnitDerivation a b) k p := by
  induction k with
  | zero => simpa using hp t
  | succ k ih =>
    rw [derivationIter_succ, polynomialTorus_matrixUnit, ih, Derivation.map_smul]
    simp only [succ_nsmul, ← add_assoc, integerWeightScalar_add,
      integerWeightScalar_positiveRoot, smul_smul]
    congr 1
    ring

theorem derivationIter_add_apply {A : Type*} [CommRing A] [Algebra ℂ A]
    (D : Derivation ℂ A A) (j k : ℕ) (p : A) :
    derivationIter D (j+k) p = derivationIter D j (derivationIter D k p) := by
  change (D.toLinearMap^(j+k)) p = (D.toLinearMap^j * D.toLinearMap^k) p
  rw [pow_add]

theorem derivationIter_zero_of_le {A : Type*} [CommRing A] [Algebra ℂ A]
    (D : Derivation ℂ A A) (p : A) {j k : ℕ} (hjk : j ≤ k)
    (hj : derivationIter D j p = 0) : derivationIter D k p = 0 := by
  obtain ⟨l,rfl⟩ := Nat.exists_eq_add_of_le hjk
  rw [Nat.add_comm, derivationIter_add_apply, hj, map_zero]

theorem derivationIter_ne_zero_of_le {A : Type*} [CommRing A] [Algebra ℂ A]
    (D : Derivation ℂ A A) (p : A) {j k : ℕ} (hjk : j ≤ k)
    (hk : derivationIter D k p ≠ 0) : derivationIter D j p ≠ 0 :=
  fun hj => hk (derivationIter_zero_of_le D p hjk hj)

/-- Nonzero iterates of a single matrix unit applied to a torus eigenvector
have distinct eigenvalues already for one coordinate of the torus. -/
theorem matrixUnit_string_independent {n : ℕ} (a b : Fin n) (hab : a ≠ b)
    (p : MatrixPolynomial n) (v : Weight n)
    (hp : ∀ t, polynomialTorus n t p = integerWeightScalar v t • p)
    (d : ℕ) (hd : derivationIter (matrixUnitDerivation a b) d p ≠ 0) :
    LinearIndependent ℂ (fun k : Fin (d+1) => derivationIter (matrixUnitDerivation a b) k.val p) := by
  let μ : Fin (d+1) → ℂ := fun k => (2 : ℂ)^(v a + k.val)
  have hμ : Function.Injective μ := by
    intro j k hjk
    have he : (2 : ℝ)^(v a + j.val) = (2 : ℝ)^(v a + k.val) := by
      apply Complex.ofReal_injective
      simpa only [Complex.ofReal_zpow, Complex.ofReal_ofNat] using hjk
    have he' := zpow_right_injective₀ (by norm_num : (0 : ℝ)<2)
      (by norm_num : (2 : ℝ)≠1) he
    apply Fin.ext
    omega
  apply (polynomialTorus n (coordinateTorus a)).eigenvectors_linearIndependent' μ hμ
  intro k
  refine ⟨?_, derivationIter_ne_zero_of_le _ _ (by omega) hd⟩
  apply Module.End.mem_eigenspace_iff.mpr
  rw [matrixUnit_derivationIter_weight a b p v hp, integerWeightScalar_coordinate]
  congr 1
  simp [μ, positiveRoot, hab]

end
end Schubert.RS.Representation
