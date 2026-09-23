import Schubert.RS.Representation.MinorStrings

namespace Schubert.RS.Representation
noncomputable section
open scoped BigOperators

def activeMinor {n : ℕ} (a b k : Fin n) : Prop := b ≤ k ∧ k < a
instance {n : ℕ} (a b k : Fin n) : Decidable (activeMinor a b k) := inferInstanceAs (Decidable (_ ∧ _))

def stringMinor {n : ℕ} (a b k : Fin n) : MatrixPolynomial n :=
  if activeMinor a b k then rowRename (Equiv.swap a b) (flagMinor k) else flagMinor k

def stringDegree {n : ℕ} (m : ColumnShape n) (a b : Fin n) : ℕ :=
  ∑ k, if activeMinor a b k then m k else 0

def stringEndpoint {n : ℕ} (m : ColumnShape n) (a b : Fin n) : MatrixPolynomial n :=
  ∏ k, stringMinor a b k ^ m k

theorem inactiveMinor_derivation {n : ℕ} (a b k : Fin n) (hba : b<a)
    (h : ¬activeMinor a b k) : matrixUnitDerivation a b (flagMinor k) = 0 := by
  by_cases hb : b ≤ k
  · exact matrixUnitDerivation_minor_present a b k (ne_of_gt hba) (by unfold activeMinor at h; omega) hb
  · exact matrixUnitDerivation_minor_absent a b k (lt_of_not_ge hb)

theorem highestFlag_derivationTop {n : ℕ} (m : ColumnShape n) (a b : Fin n) (hba : b<a) :
    DerivationTop (matrixUnitDerivation a b) (highestFlag m) (stringEndpoint m a b) (stringDegree m a b) := by
  classical
  suffices hs : ∀ s : Finset (Fin n), DerivationTop (matrixUnitDerivation a b)
      (∏ k ∈ s, flagMinor k ^ m k) (∏ k ∈ s, stringMinor a b k ^ m k)
      (∑ k ∈ s, if activeMinor a b k then m k else 0) from hs Finset.univ
  intro s
  induction s using Finset.induction_on with
  | empty => simpa using derivationTop_one (matrixUnitDerivation a b)
  | @insert k s hk ih =>
    simp only [Finset.prod_insert hk, Finset.sum_insert hk]
    by_cases h : activeMinor a b k
    · have ht := ih.linear_pow_mul (flagMinor k)
        (matrixUnitDerivation_minor_active_twice a b k h.2 h.1) (m k)
      rw [matrixUnitDerivation_minor_active a b k h.2 h.1] at ht
      simpa only [stringMinor, if_pos h, Nat.add_comm] using ht
    · have hz : matrixUnitDerivation a b (flagMinor k ^ m k) = 0 := by
        rw [Derivation.leibniz_pow, inactiveMinor_derivation a b k hba h]
        simp
      simpa only [stringMinor, if_neg h, zero_add] using ih.inert_mul (flagMinor k ^ m k) hz

theorem shapeWeight_single {n : ℕ} (k i : Fin n) :
    shapeWeight (Pi.single k 1) i = if i ≤ k then 1 else 0 := by
  classical
  unfold shapeWeight
  rw [Finset.sum_eq_single k]
  · simp
  · intro j hj hjk
    simp [Pi.single_apply, hjk, Ne.symm hjk]
  · simp

theorem inactiveMinor_prefix {n : ℕ} (a b k : Fin n) (hba : b<a)
    (h : ¬activeMinor a b k) : a ≤ k ↔ b ≤ k := by
  unfold activeMinor at h
  omega

def inactiveMinorStabilizer {n : ℕ} (a b k : Fin n) (hba : b<a) (h : ¬activeMinor a b k) :
    ∀ i, shapeWeight (Pi.single k 1) (Equiv.swap a b i) = shapeWeight (Pi.single k 1) i := by
  intro i
  rw [shapeWeight_single, shapeWeight_single]
  have hk := inactiveMinor_prefix a b k hba h
  by_cases ha : i=a
  · subst i; simp [hk]
  by_cases hb : i=b
  · subst i; simp [hk]
  · rw [Equiv.swap_apply_of_ne_of_ne ha hb]

def minorSwapScalar {n : ℕ} (a b : Fin n) (hba : b<a) (k : Fin n) : ℂ :=
  if h : activeMinor a b k then 1 else
    stabilizerSeedScalar (Pi.single k 1) (Equiv.swap a b) (inactiveMinorStabilizer a b k hba h)

theorem minorSwapScalar_ne_zero {n : ℕ} (a b : Fin n) (hba : b<a) (k : Fin n) :
    minorSwapScalar a b hba k ≠ 0 := by
  unfold minorSwapScalar
  split_ifs
  · exact one_ne_zero
  · exact stabilizerSeedScalar_ne_zero _ _ _

theorem swap_flagMinor_stringMinor {n : ℕ} (a b : Fin n) (hba : b<a) (k : Fin n) :
    rowRename (Equiv.swap a b) (flagMinor k) = minorSwapScalar a b hba k • stringMinor a b k := by
  classical
  unfold minorSwapScalar stringMinor
  split_ifs with h
  · simp
  · have hs := stabilizer_highestFlag (Pi.single k 1) (Equiv.swap a b) (inactiveMinorStabilizer a b k hba h)
    have he : highestFlag (Pi.single k 1) = flagMinor k := by
      simp [highestFlag, Pi.single_apply]
    rw [he] at hs
    exact hs

def highestSwapScalar {n : ℕ} (m : ColumnShape n) (a b : Fin n) (hba : b<a) : ℂ :=
  ∏ k, minorSwapScalar a b hba k ^ m k

theorem highestSwapScalar_ne_zero {n : ℕ} (m : ColumnShape n) (a b : Fin n) (hba : b<a) :
    highestSwapScalar m a b hba ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun k _ => pow_ne_zero _ (minorSwapScalar_ne_zero a b hba k))

theorem swap_highestFlag_endpoint {n : ℕ} (m : ColumnShape n) (a b : Fin n) (hba : b<a) :
    rowRename (Equiv.swap a b) (highestFlag m) = highestSwapScalar m a b hba • stringEndpoint m a b := by
  simp only [highestFlag, map_prod, map_pow, swap_flagMinor_stringMinor a b hba,
    smul_pow, Finset.prod_smul, highestSwapScalar, stringEndpoint]

end
end Schubert.RS.Representation
