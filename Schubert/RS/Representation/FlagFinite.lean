import Schubert.RS.Representation.HighestAnnihilation
import Schubert.RS.Representation.EnvelopingGrading
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous

namespace Schubert.RS.Representation
noncomputable section
open scoped BigOperators
attribute [local instance 100] LieRing.ofAssociativeRing

def scalarTorus (n : ℕ) (c : ℂˣ) : DiagonalTorus n := fun _ => c

theorem torusEnveloping_scalar {n : ℕ} (c : ℂˣ) :
    torusEnveloping (scalarTorus n c) = AlgHom.id ℂ (Enveloping n) := by
  apply UniversalEnvelopingAlgebra.hom_ext
  apply LieHom.ext
  intro A
  change torusEnveloping _ (UniversalEnvelopingAlgebra.ι ℂ A) = UniversalEnvelopingAlgebra.ι ℂ A
  rw [torusEnveloping_ι]
  congr 1
  apply Subtype.ext
  ext i j
  simp [torusLie, torusMatrix, rootScalar, scalarTorus]

theorem polynomialTorus_scalar_monomial {n : ℕ} (c : ℂˣ)
    (d : (Fin n × Fin n) →₀ ℕ) :
    polynomialTorus n (scalarTorus n c) (MvPolynomial.monomial d 1) =
      (c : ℂ) ^ d.sum (fun _ k => k) • MvPolynomial.monomial d 1 := by
  classical
  change rowAction _ _ = _
  rw [← MvPolynomial.prod_X_pow_eq_monomial, map_prod]
  simp only [map_pow, show ∀ rc : Fin n × Fin n,
      rowAction (Matrix.diagonal (fun i => (scalarTorus n c i : ℂ))) (MvPolynomial.X rc) =
      (c : ℂ) • MvPolynomial.X rc from fun rc => polynomialTorus_X _ _ _,
    smul_pow, Finset.prod_smul, Finset.prod_pow_eq_pow_sum, Finsupp.sum]

def flagDegree {n : ℕ} (m : ColumnShape n) : ℕ := ∑ i, shapeWeight m i

theorem extremalWeight_sum {n : ℕ} (m : ColumnShape n) (w : Equiv.Perm (Fin n)) :
    ∑ i, extremalWeight m w i = flagDegree m := by
  exact Equiv.sum_comp w.symm (shapeWeight m)

theorem flagDemazure_scalar {n : ℕ} (m : ColumnShape n) (w : Equiv.Perm (Fin n))
    (c : ℂˣ) {p : MatrixPolynomial n} (hp : p ∈ flagDemazure m w) :
    polynomialTorus n (scalarTorus n c) p = (c : ℂ) ^ flagDegree m • p := by
  obtain ⟨a, rfl⟩ := hp
  change polynomialTorus n _ (polynomialEnveloping n a (extremalFlag m w)) = _
  rw [polynomialEnveloping_torus, torusEnveloping_scalar, AlgHom.id_apply,
    extremalFlag_weight, integerWeightScalar_nat]
  have hs : weightScalar (extremalWeight m w) (scalarTorus n c) = (c : ℂ)^flagDegree m := by
    simp only [weightScalar, scalarTorus, Finset.prod_pow_eq_pow_sum, extremalWeight_sum]
  rw [hs, map_smul]
  rfl

theorem scalar_eigen_homogeneous {n D : ℕ} (p : MatrixPolynomial n)
    (hp : polynomialTorus n (scalarTorus n (Units.mk0 2 (by norm_num))) p = (2:ℂ)^D • p) :
    p.IsHomogeneous D := by
  intro d hd
  have h := basis_coord_eigenmap (MvPolynomial.basisMonomials (Fin n × Fin n) ℂ)
    (polynomialTorus n (scalarTorus n (Units.mk0 2 (by norm_num))))
    (fun d => (2:ℂ)^d.sum (fun _ k => k))
    (fun d => polynomialTorus_scalar_monomial (Units.mk0 2 (by norm_num)) d) d p
  rw [hp, map_smul] at h
  change (2:ℂ)^D * MvPolynomial.coeff d p = (2:ℂ)^d.sum (fun _ k => k) * MvPolynomial.coeff d p at h
  have he := complex_two_pow_injective (mul_right_cancel₀ hd h)
  simpa [Finsupp.weight, Finsupp.linearCombination] using he.symm

theorem flagDemazure_homogeneous {n : ℕ} (m : ColumnShape n) (w : Equiv.Perm (Fin n))
    {p : MatrixPolynomial n} (hp : p ∈ flagDemazure m w) : p.IsHomogeneous (flagDegree m) :=
  scalar_eigen_homogeneous p (flagDemazure_scalar m w (Units.mk0 2 (by norm_num)) hp)

theorem flagDemazure_le_degree {n : ℕ} (m : ColumnShape n) (w : Equiv.Perm (Fin n)) :
    flagDemazure m w ≤ MvPolynomial.restrictTotalDegree (Fin n × Fin n) ℂ (flagDegree m) := by
  intro p hp
  exact (MvPolynomial.mem_restrictTotalDegree _ _ _).mpr (flagDemazure_homogeneous m w hp).totalDegree_le

instance flagDemazure_finite {n : ℕ} (m : ColumnShape n) (w : Equiv.Perm (Fin n)) :
    FiniteDimensional ℂ (flagDemazure m w) :=
  Module.Finite.of_injective (Submodule.inclusion (flagDemazure_le_degree m w))
    (Submodule.inclusion_injective _)




theorem rowAction_homogeneous {n D : ℕ} (g : Square n) {p : MatrixPolynomial n}
    (hp : p.IsHomogeneous D) : (rowAction g p).IsHomogeneous D := by
  have h := hp.aeval (fun rc : Fin n × Fin n => ∑ i, g i rc.1 • MvPolynomial.X (i,rc.2))
    (n := 1) (fun rc => (MvPolynomial.homogeneousSubmodule (Fin n × Fin n) ℂ 1).sum_mem
      (fun i _ => (MvPolynomial.homogeneousSubmodule (Fin n × Fin n) ℂ 1).smul_mem _
        (MvPolynomial.isHomogeneous_X ℂ (i,rc.2))))
  simpa only [one_mul, rowAction] using h

theorem highestFlag_homogeneous {n : ℕ} (m : ColumnShape n) :
    (highestFlag m).IsHomogeneous (flagDegree m) := by
  have h := flagDemazure_homogeneous m (Equiv.refl _) (upperCyclic_seed (extremalFlag m (Equiv.refl _)))
  change (MvPolynomial.rename id (highestFlag m)).IsHomogeneous (flagDegree m) at h
  rwa [MvPolynomial.rename_id_apply] at h

theorem flagOrbitSpan_le_degree {n : ℕ} (m : ColumnShape n) :
    flagOrbitSpan m ≤ MvPolynomial.restrictTotalDegree (Fin n × Fin n) ℂ (flagDegree m) := by
  apply Submodule.span_le.mpr
  rintro p ⟨g, rfl⟩
  exact (MvPolynomial.mem_restrictTotalDegree _ _ _).mpr
    (rowAction_homogeneous g.val (highestFlag_homogeneous m)).totalDegree_le

instance flagOrbitSpan_finite {n : ℕ} (m : ColumnShape n) :
    FiniteDimensional ℂ (flagOrbitSpan m) :=
  Module.Finite.of_injective (Submodule.inclusion (flagOrbitSpan_le_degree m))
    (Submodule.inclusion_injective _)

theorem flagDemazure_totalDegree {n : ℕ} (m : ColumnShape n) (w : Equiv.Perm (Fin n))
    {p : MatrixPolynomial n} (hp : p ∈ flagDemazure m w) (hp0 : p ≠ 0) :
    p.totalDegree = flagDegree m := (flagDemazure_homogeneous m w hp).totalDegree hp0



end
end Schubert.RS.Representation

