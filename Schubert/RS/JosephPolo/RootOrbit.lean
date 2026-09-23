import Schubert.RS.JosephPolo.RootSubstitution
import Schubert.RS.Representation.ExtremalStrings

namespace Schubert.RS.Representation
noncomputable section
open scoped BigOperators

theorem rowAction_root_X {n : ℕ} (a b r c : Fin n) (t : ℂ) :
    rowAction (1 + t • Matrix.single a b (1:ℂ)) (MvPolynomial.X (r,c)) =
      MvPolynomial.X (r,c) + if r=b then t • MvPolynomial.X (a,c) else 0 := by
  classical
  by_cases h : r=b
  · subst r
    simp [rowAction_X,Matrix.add_apply,Matrix.single,Matrix.one_apply,
      add_smul,Finset.sum_add_distrib,ite_smul,eq_comm]
  · simp [rowAction_X,Matrix.add_apply,Matrix.single,Matrix.one_apply,
      add_smul,Finset.sum_add_distrib,ite_smul,h,Ne.symm h]

theorem rootSubstitution_eval {n : ℕ} (a b : Fin n) (p : MatrixPolynomial n) (t : ℂ) :
    (rootSubstitution a b p).eval (MvPolynomial.C t) =
      rowAction (1 + t • Matrix.single a b (1:ℂ)) p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [rootSubstitution_C]
  | add p q hp hq => simp [map_add,hp,hq]
  | mul_X p rc hp =>
    obtain ⟨r,c⟩ := rc
    rw [map_mul,Polynomial.eval_mul,hp,rootSubstitution_X,map_mul,rowAction_root_X]
    congr 1
    by_cases h : r=b
    · simp only [if_pos h,Polynomial.eval_add,Polynomial.eval_C,Polynomial.eval_mul,
        Polynomial.eval_X,MvPolynomial.C_mul']
    · simp [h]

theorem rootSubstitution_coeff_mem {n : ℕ} (r : PositiveRoot n)
    (p : MatrixPolynomial n) (k : ℕ) :
    (rootSubstitution r.val.1 r.val.2 p).coeff k ∈ upperCyclic p := by
  apply ((upperCyclic p).smul_mem_iff
    (show (k.factorial : ℂ) ≠ 0 from Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k))).mp
  rw [Nat.cast_smul_eq_nsmul,rootSubstitution_coeff _ _ (ne_of_lt r.property)]
  exact root_derivationIter_mem r p k

/-- Elementary upper row actions preserve the independently defined Lie-cyclic
span. The proof is finite polynomial Taylor expansion, not integration. -/
theorem rowAction_root_mem_upperCyclic {n : ℕ} (r : PositiveRoot n)
    (p : MatrixPolynomial n) (t : ℂ) :
    rowAction (1 + t • Matrix.single r.val.1 r.val.2 (1:ℂ)) p ∈ upperCyclic p := by
  rw [← rootSubstitution_eval,Polynomial.eval_eq_sum,Polynomial.sum_def]
  apply Submodule.sum_mem
  intro k hk
  rw [← map_pow,mul_comm,MvPolynomial.C_mul']
  exact (upperCyclic p).smul_mem _ (rootSubstitution_coeff_mem r p k)

theorem upperCyclic_rowAction_root_stable {n : ℕ} (r : PositiveRoot n)
    (p q : MatrixPolynomial n) (hq : q ∈ upperCyclic p) (t : ℂ) :
    rowAction (1 + t • Matrix.single r.val.1 r.val.2 (1:ℂ)) q ∈ upperCyclic p :=
  upperCyclic_le_of_seed_mem q p hq (rowAction_root_mem_upperCyclic r q t)

end
end Schubert.RS.Representation
