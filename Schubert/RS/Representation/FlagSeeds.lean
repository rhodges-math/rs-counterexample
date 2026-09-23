import Schubert.RS.Representation.PolynomialAmbient
import Schubert.RS.Representation.FullWeightSpaces
import Mathlib.Algebra.MvPolynomial.Rename

namespace Schubert.RS.Representation
noncomputable section
open scoped BigOperators

/-- Column multiplicities parameterize partitions without choosing an order
among equal rows. The dominant weight is their sequence of suffix sums. -/
abbrev ColumnShape (n : ℕ) := Fin n → ℕ

def shapeWeight {n : ℕ} (m : ColumnShape n) (i : Fin n) : ℕ :=
  ∑ k : Fin n, if i ≤ k then m k else 0

theorem shapeWeight_antitone {n : ℕ} (m : ColumnShape n) : Antitone (shapeWeight m) := by
  intro i j hij
  apply Finset.sum_le_sum
  intro k hk
  by_cases hj : j ≤ k
  · simp [hj, le_trans hij hj]
  · simp [hj]

def prefixIndex {n : ℕ} (k : Fin n) (i : Fin (k.val+1)) : Fin n :=
  ⟨i.val, by omega⟩

theorem prefixIndex_injective {n : ℕ} (k : Fin n) : Function.Injective (prefixIndex k) := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun x : Fin n => x.val) h

def flagMinor {n : ℕ} (k : Fin n) : MatrixPolynomial n :=
  Matrix.det (fun i j : Fin (k.val+1) => MvPolynomial.X (prefixIndex k i, prefixIndex k j))

def highestFlag {n : ℕ} (m : ColumnShape n) : MatrixPolynomial n :=
  ∏ k, flagMinor k ^ m k

def identityEvaluation (n : ℕ) : MatrixPolynomial n →ₐ[ℂ] ℂ :=
  MvPolynomial.aeval (fun rc => if rc.1 = rc.2 then 1 else 0)

theorem identityEvaluation_flagMinor {n : ℕ} (k : Fin n) :
    identityEvaluation n (flagMinor k) = 1 := by
  have hdet := (identityEvaluation n).map_det
    (fun i j : Fin (k.val+1) => (MvPolynomial.X (prefixIndex k i, prefixIndex k j) : MatrixPolynomial n))
  have hm : (identityEvaluation n).mapMatrix
      (fun i j : Fin (k.val+1) => MvPolynomial.X (prefixIndex k i, prefixIndex k j)) = 1 := by
    ext i j
    change identityEvaluation n (MvPolynomial.X (prefixIndex k i, prefixIndex k j)) =
      if i = j then 1 else 0
    simp [identityEvaluation, Matrix.one_apply, (prefixIndex_injective k).eq_iff]
  exact hdet.trans (by rw [hm, Matrix.det_one])

theorem identityEvaluation_highestFlag {n : ℕ} (m : ColumnShape n) :
    identityEvaluation n (highestFlag m) = 1 := by
  simp [highestFlag, map_prod, identityEvaluation_flagMinor]

theorem highestFlag_ne_zero {n : ℕ} (m : ColumnShape n) : highestFlag m ≠ 0 := by
  intro h
  have he := identityEvaluation_highestFlag m
  rw [h, map_zero] at he
  exact zero_ne_one he

def rowRename {n : ℕ} (w : Equiv.Perm (Fin n)) :
    MatrixPolynomial n →ₐ[ℂ] MatrixPolynomial n :=
  MvPolynomial.rename (fun rc => (w rc.1, rc.2))

/-- Concrete extremal candidate obtained by the Weyl permutation of rows.
No polynomial key or presentation quotient enters this definition. -/
def extremalFlag {n : ℕ} (m : ColumnShape n) (w : Equiv.Perm (Fin n)) : MatrixPolynomial n :=
  rowRename w (highestFlag m)

theorem extremalFlag_ne_zero {n : ℕ} (m : ColumnShape n) (w : Equiv.Perm (Fin n)) :
    extremalFlag m w ≠ 0 := by
  have hf : Function.Injective (fun rc : Fin n × Fin n => (w rc.1, rc.2)) := by
    rintro ⟨a,b⟩ ⟨c,d⟩ h
    change (w a,b) = (w c,d) at h
    have hp := Prod.mk.inj h
    exact Prod.ext (w.injective hp.1) hp.2
  intro hz
  change MvPolynomial.rename (fun rc : Fin n × Fin n => (w rc.1, rc.2)) (highestFlag m) = 0 at hz
  apply highestFlag_ne_zero m
  apply MvPolynomial.rename_injective _ hf
  simpa only [map_zero] using hz

def extremalWeight {n : ℕ} (m : ColumnShape n) (w : Equiv.Perm (Fin n)) : Fin n → ℕ :=
  fun i => shapeWeight m (w.symm i)

/-- The group orbit span of the highest flag polynomial. -/
def flagOrbitSpan {n : ℕ} (m : ColumnShape n) : Submodule ℂ (MatrixPolynomial n) :=
  Submodule.span ℂ (Set.range (fun g : (Square n)ˣ => polynomialGL n g (highestFlag m)))

theorem highestFlag_mem_orbitSpan {n : ℕ} (m : ColumnShape n) :
    highestFlag m ∈ flagOrbitSpan m := by
  have h : polynomialGL n 1 (highestFlag m) ∈ flagOrbitSpan m :=
    Submodule.subset_span ⟨1, rfl⟩
  simpa using h

theorem flagOrbitSpan_stable {n : ℕ} (m : ColumnShape n) (g : (Square n)ˣ)
    {p : MatrixPolynomial n} (hp : p ∈ flagOrbitSpan m) :
    polynomialGL n g p ∈ flagOrbitSpan m := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨h, rfl⟩ := hp
    have he : polynomialGL n g (polynomialGL n h (highestFlag m)) =
      polynomialGL n (g*h) (highestFlag m) := by rw [map_mul]; rfl
    rw [he]
    exact Submodule.subset_span ⟨g*h, rfl⟩
  | zero => simp
  | add p q hp hq ip iq => simpa only [map_add] using (flagOrbitSpan m).add_mem ip iq
  | smul c p hp ip => simpa only [map_smul] using (flagOrbitSpan m).smul_mem c ip

end
end Schubert.RS.Representation
