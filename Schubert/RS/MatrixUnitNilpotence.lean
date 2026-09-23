import Schubert.RS.PolynomialWeightFunctional

namespace Schubert.RS.Representation
noncomputable section
open scoped BigOperators

theorem matrixUnit_locally_nilpotent {n : ℕ} (a b : Fin n) (hab : a≠b)
    (p : MatrixPolynomial n) : ∃ k, derivationIter (matrixUnitDerivation a b) k p=0 := by
  let D := matrixUnitDerivation a b
  change ∃ k, derivationIter D k p=0
  induction p using MvPolynomial.induction_on with
  | C c =>
    refine ⟨1,?_⟩
    simp [derivationIter_succ]
  | add p q hp hq =>
    obtain ⟨j,hj⟩ := hp
    obtain ⟨k,hk⟩ := hq
    refine ⟨j+k,?_⟩
    rw [map_add,derivationIter_zero_of_le D p (by omega) hj,
      derivationIter_zero_of_le D q (by omega) hk,add_zero]
  | mul_X p rc hp =>
    obtain ⟨k,hk⟩ := hp
    have hx : D (D (MvPolynomial.X rc))=0 := by
      obtain ⟨i,j⟩ := rc
      simp only [D,matrixUnitDerivation_X]
      split_ifs with h
      · simp [matrixUnitDerivation_X,hab]
      · exact map_zero _
    refine ⟨k+1,?_⟩
    rw [mul_comm,derivationIter_linear_mul D _ _ hx,
      derivationIter_zero_of_le D p (by omega) hk,hk]
    simp

theorem end_pow_apply_zero_of_le {V : Type*} [AddCommGroup V] [Module ℂ V]
    (E : Module.End ℂ V) (v : V) {j k : ℕ} (hjk : j≤k) (hj : (E^j) v=0) :
    (E^k) v=0 := by
  obtain ⟨l,rfl⟩ := Nat.exists_eq_add_of_le hjk
  rw [Nat.add_comm,end_pow_add_apply,hj,map_zero]

theorem end_nilpotent_of_locally_nilpotent {V : Type*} [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] (E : Module.End ℂ V)
    (hE : ∀ v, ∃ k, (E^k) v=0) : IsNilpotent E := by
  classical
  let b := Module.finBasis ℂ V
  choose k hk using fun j => hE (b j)
  refine ⟨∑ j, k j,?_⟩
  apply b.ext
  intro j
  exact end_pow_apply_zero_of_le E (b j)
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)) (hk j)

def matrixUnitOnSubmodule {n : ℕ} (a b : Fin n)
    (S : Submodule ℂ (MatrixPolynomial n))
    (hS : ∀ p∈S, matrixUnitDerivation a b p∈S) : Module.End ℂ S where
  toFun p := ⟨matrixUnitDerivation a b p.val,hS p.val p.property⟩
  map_add' p q := Subtype.ext ((matrixUnitDerivation a b).map_add p.val q.val)
  map_smul' c p := Subtype.ext ((matrixUnitDerivation a b).map_smul c p.val)

theorem matrixUnitOnSubmodule_pow {n : ℕ} (a b : Fin n)
    (S : Submodule ℂ (MatrixPolynomial n))
    (hS : ∀ p∈S, matrixUnitDerivation a b p∈S) (k : ℕ) (p : S) :
    ((matrixUnitOnSubmodule a b S hS^k) p : MatrixPolynomial n)=
      derivationIter (matrixUnitDerivation a b) k p.val := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [end_pow_succ_apply,derivationIter_succ]
    change matrixUnitDerivation a b _ = _
    rw [ih]

/-- Every finite stable polynomial subspace has a uniform root nilpotence
bound. No character formula or semisimplicity assertion is used. -/
theorem matrixUnitOnSubmodule_nilpotent {n : ℕ} (a b : Fin n) (hab : a≠b)
    (S : Submodule ℂ (MatrixPolynomial n)) [FiniteDimensional ℂ S]
    (hS : ∀ p∈S, matrixUnitDerivation a b p∈S) :
    IsNilpotent (matrixUnitOnSubmodule a b S hS) := by
  apply end_nilpotent_of_locally_nilpotent
  intro p
  obtain ⟨k,hk⟩ := matrixUnit_locally_nilpotent a b hab p.val
  refine ⟨k,Subtype.ext ?_⟩
  rw [matrixUnitOnSubmodule_pow]
  exact hk

end
end Schubert.RS.Representation
