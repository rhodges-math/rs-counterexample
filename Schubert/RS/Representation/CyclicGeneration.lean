import Schubert.RS.Representation.LoweringSpan

namespace Schubert.RS.Representation
noncomputable section
open scoped BigOperators
attribute [local instance 100] LieRing.ofAssociativeRing

/-- Algebra generation of the genuine UEA, proved through its tensor quotient.
This uses neither PBW nor a basis of the enveloping algebra. -/
theorem enveloping_induction {n : ℕ} {P : Enveloping n → Prop}
    (hC : ∀ c : ℂ, P (algebraMap ℂ (Enveloping n) c))
    (hι : ∀ A : upperNilpotent n, P (UniversalEnvelopingAlgebra.ι ℂ A))
    (hmul : ∀ a b, P a → P b → P (a*b))
    (hadd : ∀ a b, P a → P b → P (a+b)) (a : Enveloping n) : P a := by
  have hs : Function.Surjective (UniversalEnvelopingAlgebra.mkAlgHom ℂ (upperNilpotent n)) :=
    RingCon.mkₐ_surjective _
  obtain ⟨x, rfl⟩ := hs a
  induction x using TensorAlgebra.induction with
  | algebraMap c => simpa using hC c
  | ι A => exact hι A
  | mul a b ha hb => simpa only [map_mul] using hmul _ _ ha hb
  | add a b ha hb => simpa only [map_add] using hadd _ _ ha hb

/-- Stability under actual positive matrix units implies stability under U(n+). -/
theorem root_stable_enveloping {n : ℕ} (P : Submodule ℂ (MatrixPolynomial n))
    (hP : ∀ r : PositiveRoot n, ∀ p ∈ P, matrixUnitDerivation r.val.1 r.val.2 p ∈ P)
    (a : Enveloping n) {p : MatrixPolynomial n} (hp : p ∈ P) : polynomialEnveloping n a p ∈ P := by
  have hLie (A : upperNilpotent n) (q : MatrixPolynomial n) (hq : q ∈ P) :
      polynomialUpperLie n A q ∈ P := by
    rw [← (rootBasis n).sum_repr A]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
    apply P.sum_mem
    intro r hr
    apply P.smul_mem
    rw [rootBasis_apply]
    exact hP r q hq
  have hall : ∀ a : Enveloping n, ∀ p ∈ P, polynomialEnveloping n a p ∈ P := by
    intro a
    induction a using enveloping_induction with
    | hC c => intro q hq; simpa using P.smul_mem c hq
    | hι A =>
      intro q hq
      change UniversalEnvelopingAlgebra.lift ℂ (polynomialUpperLie n) (UniversalEnvelopingAlgebra.ι ℂ A) q ∈ P
      rw [UniversalEnvelopingAlgebra.lift_ι_apply]
      exact hLie A q hq
    | hmul a b ha hb =>
      intro q hq
      rw [map_mul]
      exact ha _ (hb q hq)
    | hadd a b ha hb =>
      intro q hq
      rw [map_add, LinearMap.add_apply]
      exact P.add_mem (ha q hq) (hb q hq)
  exact hall a p hp

theorem upperCyclic_le_of_root_stable {n : ℕ} (p : MatrixPolynomial n)
    (P : Submodule ℂ (MatrixPolynomial n)) (hp : p ∈ P)
    (hP : ∀ r : PositiveRoot n, ∀ q ∈ P, matrixUnitDerivation r.val.1 r.val.2 q ∈ P) :
    upperCyclic p ≤ P := by
  rintro q ⟨a, rfl⟩
  exact root_stable_enveloping P hP a hp

theorem upperCyclic_root_stable {n : ℕ} (p : MatrixPolynomial n) (r : PositiveRoot n)
    {q : MatrixPolynomial n} (hq : q ∈ upperCyclic p) : matrixUnitDerivation r.val.1 r.val.2 q ∈ upperCyclic p := by
  have h := upperCyclic_stable p (rootOperator r) hq
  rw [polynomialEnveloping_root] at h
  exact h

end
end Schubert.RS.Representation
