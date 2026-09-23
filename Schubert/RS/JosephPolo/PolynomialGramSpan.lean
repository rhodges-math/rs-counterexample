import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas

namespace Schubert.RS.Representation
noncomputable section
open scoped BigOperators ComplexConjugate

theorem eq_zero_of_sum_conj_mul_self {ι : Type*} [Fintype ι] (a : ι → ℂ)
    (h : ∑ i, conj (a i) * a i = 0) (i : ι) : a i = 0 := by
  have hr := congrArg Complex.reAddGroupHom h
  have hn : ∑ j, Complex.normSq (a j) = 0 := by
    simpa only [map_sum,map_zero,← Complex.normSq_eq_conj_mul_self,
      Complex.coe_reAddGroupHom,Complex.ofReal_re] using hr
  exact Complex.normSq_eq_zero.mp
    ((Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Complex.normSq_nonneg (a j))).mp hn i
      (Finset.mem_univ i))

/-- Real polynomial generators and any linear image give the same span as
the mixed coefficient vectors. Relations among the generators are allowed;
the proof uses a positive Gram pairing, not independence of minor products. -/
theorem real_polynomial_gram_span {σ ι X : Type*} [Fintype ι]
    [AddCommGroup X] [Module ℂ X]
    (p : ι → MvPolynomial σ ℂ)
    (hp : ∀ i m, conj (MvPolynomial.coeff m (p i)) = MvPolynomial.coeff m (p i))
    (φ : MvPolynomial σ ℂ →ₗ[ℂ] X) :
    Submodule.span ℂ (Set.range (fun m : σ →₀ ℕ =>
      ∑ i, MvPolynomial.coeff m (p i) • φ (p i))) =
      Submodule.span ℂ (Set.range (fun i => φ (p i))) := by
  classical
  let S := Submodule.span ℂ (Set.range (fun m : σ →₀ ℕ =>
    ∑ i, MvPolynomial.coeff m (p i) • φ (p i)))
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨m,rfl⟩
    apply Submodule.sum_mem
    intro i hi
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,rfl⟩)
  · apply Submodule.span_le.mpr
    rintro x ⟨j,rfl⟩
    apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff S _).mp
    intro f hf
    have hf' := (S.mem_dualAnnihilator f).mp hf
    have hlin : ∑ i, f (φ (p i)) • p i = 0 := by
      ext m
      have hm := hf' _ (Submodule.subset_span ⟨m,rfl⟩)
      simpa only [MvPolynomial.coeff_sum,MvPolynomial.coeff_smul,MvPolynomial.coeff_zero,
        map_sum,map_smul,smul_eq_mul,mul_comm] using hm
    have hconj : ∑ i, conj (f (φ (p i))) • p i = 0 := by
      ext m
      have hm := congrArg conj (congrArg (MvPolynomial.coeff m) hlin)
      simpa only [MvPolynomial.coeff_sum,MvPolynomial.coeff_smul,MvPolynomial.coeff_zero,
        smul_eq_mul,map_sum,map_mul,hp,map_zero] using hm
    have hs := congrArg (fun q => f (φ q)) hconj
    simp only [map_sum,map_smul,map_zero,smul_eq_mul] at hs
    exact eq_zero_of_sum_conj_mul_self (fun i => f (φ (p i))) hs j

end
end Schubert.RS.Representation
