import Schubert.RS.PolynomialPrimitiveVector
import Schubert.RS.Sl2TerminalString

namespace Schubert.RS.Representation
noncomputable section
attribute [local instance 100] LieRing.ofAssociativeRing
open scoped BigOperators

theorem polynomial_weight_homogeneous {n : ℕ} (p : MatrixPolynomial n) (v : Weight n)
    (hp : ∀ t, polynomialTorus n t p=integerWeightScalar v t • p) :
    p.IsHomogeneous (∑ i,(v i).toNat) := by
  intro d hd
  have hv := polynomial_support_weight p v hp d hd
  rw [← hv]
  change Finsupp.weight (fun _ : Fin n × Fin n => 1) d=∑ i,(matrixMonomialWeight d i).toNat
  simp only [Finsupp.weight,Finsupp.linearCombination,LinearMap.toAddMonoidHom_coe,Finsupp.coe_lsum,
    LinearMap.coe_smulRight,LinearMap.id_coe,id,smul_eq_mul,mul_one]
  rw [Finsupp.sum_fintype _ _ (fun _ => by simp),Fintype.sum_prod_type]
  simp only [matrixMonomialWeight,Int.toNat_natCast]

theorem homogeneous_raising_iter_val {n : ℕ} (a b : Fin n) (hab : a≠b)
    (D k : ℕ) (p : homogeneousPolynomialRootModule a b hab D) :
    (primitiveStringVector (sl2RaisingElement (polynomialSl2Triple a b hab)) p k).val=
      derivationIter (matrixUnitDerivation a b) k p.val := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [primitiveStringVector_succ,derivationIter_succ]
      change matrixUnitDerivation a b _=matrixUnitDerivation a b _
      rw [ih]

/-- The residual weight of every actual polynomial raising string is
dominant at its root. The bound follows from finite-dimensional integrability,
not from assuming the Demazure character formula. -/
theorem polynomial_string_admissible {n : ℕ} (a b : Fin n) (hab : a≠b)
    (p : MatrixPolynomial n) (v : Weight n)
    (hp : ∀ t, polynomialTorus n t p=integerWeightScalar v t • p)
    (d : ℕ) (htop : derivationIter (matrixUnitDerivation a b) d p≠0)
    (hend : derivationIter (matrixUnitDerivation a b) (d+1) p=0) :
    0≤v a-v b+(d:ℤ) := by
  let D := ∑ i,(v i).toNat
  let p' : homogeneousPolynomialRootModule a b hab D := ⟨p,polynomial_weight_homogeneous p v hp⟩
  let t := polynomialSl2Triple a b hab
  have hH : ⁅sl2CartanElement t,p'⁆=((v a-v b:ℤ):ℂ) • p' := by
    apply Subtype.ext
    exact polynomialRootCartan_weight a b p v hp
  have ht : primitiveStringVector (sl2RaisingElement t) p' d≠0 := by
    intro hz
    apply htop
    have hh := congrArg Subtype.val hz
    rw [homogeneous_raising_iter_val] at hh
    exact hh
  have he : primitiveStringVector (sl2RaisingElement t) p' (d+1)=0 := by
    apply Subtype.ext
    rw [homogeneous_raising_iter_val]
    exact hend
  obtain ⟨q,hq⟩ := terminalString_residual_nat t
    (polynomialHighestVector_primitive a b hab d) p' ((v a-v b:ℤ):ℂ) hH ht he
  have hqi : v a-v b+(d:ℤ)=(q:ℤ) := by exact_mod_cast hq
  rw [hqi]
  exact Int.natCast_nonneg q

end
end Schubert.RS.Representation
