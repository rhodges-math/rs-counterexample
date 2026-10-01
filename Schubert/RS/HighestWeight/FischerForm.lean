import Schubert.RS.Representation.MinorStrings
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Basic.Complex.BigOperators

/-!
# The Fischer inner product (E5)

On `ℂ[X_{rc}]` the Fischer inner product is `⟨f, g⟩ = Σ_d d!·conj(f_d)·g_d`, where
`d! = ∏_{rc} (d_{rc})!`. It is positive definite (`fischer_self_eq_zero`). Multiplication by
`X_i` is adjoint to `∂/∂X_i` (`fischer_X_mul`). Since `E_ab = Σ_c X_{ac} ∂/∂X_{bc}`, the adjoint
of the matrix-unit derivation `E_ab` is `E_ba` (`fischer_matrixUnitDerivation`).
-/

namespace Schubert.RS.HighestWeight

open Schubert.RS.Representation

noncomputable section

variable {n : ℕ}

/-- `d! = ∏_{rc} (d_{rc})!`. -/
def monomialFactorial (d : (Fin n × Fin n) →₀ ℕ) : ℕ := ∏ rc, (d rc).factorial

theorem monomialFactorial_pos (d : (Fin n × Fin n) →₀ ℕ) : 0 < monomialFactorial d :=
  Finset.prod_pos fun _ _ => Nat.factorial_pos _

theorem monomialFactorial_add_single (d : (Fin n × Fin n) →₀ ℕ) (i : Fin n × Fin n) :
    monomialFactorial (d + Finsupp.single i 1) = monomialFactorial d * (d i + 1) := by
  classical
  unfold monomialFactorial
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase _ (fun rc => (d rc).factorial) (Finset.mem_univ i)]
  have h : ∀ rc ∈ Finset.univ.erase i,
      ((d + Finsupp.single i 1 : (Fin n × Fin n) →₀ ℕ) rc).factorial = (d rc).factorial := by
    intro rc hrc
    rw [Finsupp.add_apply, Finsupp.single_apply, ite_eq_right (Finset.ne_of_mem_erase hrc).symm,
      add_zero]
  rw [Finset.prod_congr rfl h, Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorial_succ]
  ring

/-- The Fischer inner product `⟨f, g⟩ = Σ_d d!·conj(f_d)·g_d`, conjugate-linear in `f`. -/
def fischer (f g : MatrixPolynomial n) : ℂ :=
  ∑ d ∈ f.support, (monomialFactorial d : ℂ) * (star (f.coeff d) * g.coeff d)

theorem fischer_eq_sum_of_subset {f : MatrixPolynomial n} {s : Finset ((Fin n × Fin n) →₀ ℕ)}
    (hs : f.support ⊆ s) (g : MatrixPolynomial n) :
    fischer f g = ∑ d ∈ s, (monomialFactorial d : ℂ) * (star (f.coeff d) * g.coeff d) := by
  apply Finset.sum_subset hs
  intro d _ hd
  rw [MvPolynomial.notMem_support_iff.mp hd, star_zero, zero_mul, mul_zero]

@[simp] theorem fischer_zero_left (g : MatrixPolynomial n) : fischer 0 g = 0 := by
  simp [fischer]

theorem fischer_add_left (f₁ f₂ g : MatrixPolynomial n) :
    fischer (f₁ + f₂) g = fischer f₁ g + fischer f₂ g := by
  classical
  rw [fischer_eq_sum_of_subset MvPolynomial.support_add g,
    fischer_eq_sum_of_subset Finset.subset_union_left g,
    fischer_eq_sum_of_subset Finset.subset_union_right g, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, star_add]
  ring

theorem fischer_smul_left (c : ℂ) (f g : MatrixPolynomial n) :
    fischer (c • f) g = star c * fischer f g := by
  rw [fischer_eq_sum_of_subset MvPolynomial.support_smul g, fischer, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul, star_mul']
  ring

theorem fischer_sub_left (f₁ f₂ g : MatrixPolynomial n) :
    fischer (f₁ - f₂) g = fischer f₁ g - fischer f₂ g := by
  have h := fischer_add_left (f₁ - f₂) f₂ g
  rw [sub_add_cancel] at h
  rw [h, add_sub_cancel_right]

theorem fischer_sum_left {ι : Type*} (s : Finset ι) (f : ι → MatrixPolynomial n)
    (g : MatrixPolynomial n) : fischer (∑ i ∈ s, f i) g = ∑ i ∈ s, fischer (f i) g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, fischer_add_left, ih, Finset.sum_insert hi]

/-- `⟨f, ·⟩` as a linear functional. -/
def fischerRight (f : MatrixPolynomial n) : MatrixPolynomial n →ₗ[ℂ] ℂ where
  toFun g := fischer f g
  map_add' g₁ g₂ := by
    simp only [fischer, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, mul_add,
      Finset.sum_add_distrib]
  map_smul' c g := by
    simp only [fischer, MvPolynomial.coeff_smul, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    ring

@[simp] theorem fischerRight_apply (f g : MatrixPolynomial n) : fischerRight f g = fischer f g :=
  rfl

theorem fischer_sum_right {ι : Type*} (s : Finset ι) (f : MatrixPolynomial n)
    (g : ι → MatrixPolynomial n) : fischer f (∑ i ∈ s, g i) = ∑ i ∈ s, fischer f (g i) :=
  map_sum (fischerRight f) g s

/-- Conjugate symmetry. -/
theorem star_fischer (f g : MatrixPolynomial n) : star (fischer f g) = fischer g f := by
  classical
  rw [fischer_eq_sum_of_subset (Finset.subset_union_left (s₂ := g.support)) g,
    fischer_eq_sum_of_subset (Finset.subset_union_right (s₁ := f.support)) f, star_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [star_mul', star_mul', star_star, star_natCast]
  ring

/-- Positive definiteness. -/
theorem fischer_self_eq_zero {f : MatrixPolynomial n} (h : fischer f f = 0) : f = 0 := by
  have hterm : ∀ d, (monomialFactorial d : ℂ) * (star (f.coeff d) * f.coeff d) =
      (((monomialFactorial d : ℝ) * Complex.normSq (f.coeff d) : ℝ) : ℂ) := by
    intro d
    rw [Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self, Complex.star_def]
    push_cast
    ring
  have hreal : (∑ d ∈ f.support, (monomialFactorial d : ℝ) * Complex.normSq (f.coeff d)) = 0 := by
    have h' := h
    rw [fischer, Finset.sum_congr rfl fun d _ => hterm d, ← Complex.ofReal_sum] at h'
    exact_mod_cast h'
  rw [Finset.sum_eq_zero_iff_of_nonneg
    (fun d _ => mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _))] at hreal
  by_contra hf
  obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr hf
  have h1 := hreal d hd
  rcases mul_eq_zero.mp h1 with h2 | h2
  · exact (monomialFactorial_pos d).ne' (by exact_mod_cast h2)
  · exact (MvPolynomial.mem_support_iff.mp hd) (Complex.normSq_eq_zero.mp h2)

/-- Multiplication by `X_i` is adjoint to `∂/∂X_i`. -/
theorem fischer_X_mul (i : Fin n × Fin n) (f g : MatrixPolynomial n) :
    fischer (MvPolynomial.X i * f) g = fischer f (MvPolynomial.pderiv i g) := by
  rw [fischer, MvPolynomial.support_X_mul, Finset.sum_map, fischer]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [addLeftEmbedding_apply, MvPolynomial.coeff_X_mul, MvPolynomial.coeff_pderiv,
    add_comm (Finsupp.single i 1) d, monomialFactorial_add_single]
  push_cast
  ring

/-- `∂/∂X_i` is adjoint to multiplication by `X_i`. -/
theorem fischer_pderiv (i : Fin n × Fin n) (f g : MatrixPolynomial n) :
    fischer (MvPolynomial.pderiv i f) g = fischer f (MvPolynomial.X i * g) := by
  rw [← star_fischer g, ← fischer_X_mul, star_fischer]

/-- `E_ab = Σ_c X_{ac} ∂/∂X_{bc}`. -/
theorem matrixUnitDerivation_eq_sum (a b : Fin n) (p : MatrixPolynomial n) :
    matrixUnitDerivation a b p =
      ∑ c, MvPolynomial.X (a, c) * MvPolynomial.pderiv (b, c) p := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c =>
    rw [← MvPolynomial.algebraMap_eq, Derivation.map_algebraMap]
    simp
  | add p q hp hq =>
    rw [map_add, hp, hq, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_add, mul_add]
  | mul_X p rc hp =>
    obtain ⟨r, c'⟩ := rc
    have hsum : ∑ c, MvPolynomial.X (a, c) *
        (p * (Pi.single (M := fun _ => MatrixPolynomial n) (b, c) 1 (r, c'))) =
        p * (if r = b then MvPolynomial.X (a, c') else 0) := by
      by_cases hrb : r = b
      · subst hrb
        rw [Finset.sum_eq_single c', Pi.single_eq_same, ite_eq_left rfl]
        · ring
        · intro c _ hc
          rw [Pi.single_eq_of_ne (by simpa [eq_comm] using hc), mul_zero, mul_zero]
        · simp
      · rw [ite_eq_right hrb, mul_zero]
        refine Finset.sum_eq_zero fun c _ => ?_
        rw [Pi.single_eq_of_ne (by simp [hrb]), mul_zero, mul_zero]
    rw [Derivation.leibniz, matrixUnitDerivation_X, hp]
    simp only [Derivation.leibniz, smul_eq_mul, MvPolynomial.pderiv_X, mul_add,
      Finset.sum_add_distrib]
    rw [hsum, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    ring

/-- E5: the adjoint of `E_ab` for the Fischer inner product is `E_ba`. -/
theorem fischer_matrixUnitDerivation (a b : Fin n) (f g : MatrixPolynomial n) :
    fischer (matrixUnitDerivation a b f) g = fischer f (matrixUnitDerivation b a g) := by
  rw [matrixUnitDerivation_eq_sum, fischer_sum_left, matrixUnitDerivation_eq_sum,
    fischer_sum_right]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [fischer_X_mul, fischer_pderiv]

end
end Schubert.RS.HighestWeight
