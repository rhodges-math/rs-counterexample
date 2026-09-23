import Schubert.RS.PolynomialStringSplitting

namespace Schubert.RS.Representation
noncomputable section

/-- A finite decomposition into actual homogeneous root strings. The recursive
remainder is a disjoint complementary subspace. This records the decomposition
without imposing an arbitrary enumeration of the strings or their weights. -/
inductive GradedRootDecomposition {n : ℕ} (a b : Fin n) :
    Submodule ℂ (MatrixPolynomial n) → Prop
  | zero : GradedRootDecomposition a b ⊥
  | split (S K : Submodule ℂ (MatrixPolynomial n)) (p : MatrixPolynomial n)
      (v : Weight n) (d : ℕ)
      (hp : p∈S)
      (hw : ∀ t, polynomialTorus n t p=integerWeightScalar v t • p)
      (htop : derivationIter (matrixUnitDerivation a b) d p≠0)
      (hzero : derivationIter (matrixUnitDerivation a b) (d+1) p=0)
      (hdisjoint : Disjoint (matrixUnitStringSpan a b p d) K)
      (hsup : matrixUnitStringSpan a b p d ⊔ K=S)
      (rest : GradedRootDecomposition a b K) : GradedRootDecomposition a b S

/-- Graded Jordan decomposition for every finite-dimensional polynomial
subspace stable under one root operator and the full diagonal torus.
Termination is certified by strict decrease of the actual dimension. -/
theorem gradedRootDecomposition {n : ℕ} (a b : Fin n) (hab : a≠b)
    (S : Submodule ℂ (MatrixPolynomial n)) [FiniteDimensional ℂ S]
    (hE : ∀ p∈S, matrixUnitDerivation a b p∈S)
    (hT : ∀ t p, p∈S → polynomialTorus n t p∈S) : GradedRootDecomposition a b S := by
  by_cases hS : S=⊥
  · rw [hS]
    exact .zero
  obtain ⟨d,p,hp,v,hv,htop,hzero,K,hK,hdis,hsup,hKE,hKT⟩ :=
    exists_weight_string_complement a b hab S hS hE hT
  letI : FiniteDimensional ℂ K := Module.Finite.of_injective (Submodule.inclusion hK.le)
    (Submodule.inclusion_injective hK.le)
  exact .split S K p v d hp hv htop hzero hdis hsup (gradedRootDecomposition a b hab K hKE hKT)
termination_by Module.finrank ℂ S
decreasing_by exact Submodule.finrank_lt_finrank_of_lt hK

theorem matrixUnitStringSpan_root_stable {n : ℕ} (a b : Fin n)
    (p : MatrixPolynomial n) (d : ℕ)
    (hzero : derivationIter (matrixUnitDerivation a b) (d+1) p=0) :
    ∀ x∈matrixUnitStringSpan a b p d,
      matrixUnitDerivation a b x∈matrixUnitStringSpan a b p d := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j,rfl⟩ := hx
    rw [← derivationIter_succ]
    by_cases hj : j.val=d
    · rw [hj,hzero]; exact Submodule.zero_mem _
    · exact Submodule.subset_span ⟨⟨j.val+1,by omega⟩,rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y hx hy ihx ihy => rw [map_add]; exact Submodule.add_mem _ ihx ihy
  | smul c x hx ih => rw [Derivation.map_smul]; exact Submodule.smul_mem _ _ ih

theorem matrixUnitStringSpan_torus_stable {n : ℕ} (a b : Fin n)
    (p : MatrixPolynomial n) (v : Weight n) (d : ℕ)
    (hw : ∀ t, polynomialTorus n t p=integerWeightScalar v t • p) :
    ∀ t x, x∈matrixUnitStringSpan a b p d →
      polynomialTorus n t x∈matrixUnitStringSpan a b p d := by
  intro t x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j,rfl⟩ := hx
    rw [matrixUnit_derivationIter_weight a b p v hw]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j,rfl⟩)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y hx hy ihx ihy => rw [map_add]; exact Submodule.add_mem _ ihx ihy
  | smul c x hx ih => rw [map_smul]; exact Submodule.smul_mem _ _ ih

end
end Schubert.RS.Representation
