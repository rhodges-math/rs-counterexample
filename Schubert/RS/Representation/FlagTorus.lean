import Schubert.RS.Representation.PolynomialCovariance

namespace Schubert.RS.Representation
noncomputable section

theorem flagDemazure_torus_stable {n : ℕ} (m : ColumnShape n) (w : Equiv.Perm (Fin n))
    (t : DiagonalTorus n) {p : MatrixPolynomial n} (hp : p ∈ flagDemazure m w) :
    polynomialTorus n t p ∈ flagDemazure m w := by
  obtain ⟨a, rfl⟩ := hp
  change polynomialTorus n t (polynomialEnveloping n a (extremalFlag m w)) ∈ _
  rw [polynomialEnveloping_torus, extremalFlag_weight, map_smul]
  apply (flagDemazure m w).smul_mem
  exact ⟨torusEnveloping t a, rfl⟩

/-- Restriction of the concrete ambient torus action. No JP isomorphism, PBW,
character statement, or choice of a desired weight decomposition defines it. -/
def flagTorus {n : ℕ} (m : ColumnShape n) (w : Equiv.Perm (Fin n)) :
    DiagonalTorus n →* Module.End ℂ (flagDemazure m w) where
  toFun t :=
    { toFun := fun p => ⟨polynomialTorus n t p.val, flagDemazure_torus_stable m w t p.property⟩
      map_add' p q := Subtype.ext ((polynomialTorus n t).map_add p.val q.val)
      map_smul' c p := Subtype.ext ((polynomialTorus n t).map_smul c p.val) }
  map_one' := by
    apply LinearMap.ext
    intro p
    apply Subtype.ext
    change polynomialTorus n 1 p.val = p.val
    rw [map_one]
    rfl
  map_mul' s t := by
    apply LinearMap.ext
    intro p
    apply Subtype.ext
    change polynomialTorus n (s*t) p.val = polynomialTorus n s (polynomialTorus n t p.val)
    rw [map_mul]
    rfl

@[simp] theorem flagTorus_val {n : ℕ} (m : ColumnShape n) (w : Equiv.Perm (Fin n))
    (t : DiagonalTorus n) (p : flagDemazure m w) :
    (flagTorus m w t p).val = polynomialTorus n t p.val := rfl

def flagGenerator {n : ℕ} (m : ColumnShape n) (w : Equiv.Perm (Fin n)) : flagDemazure m w :=
  ⟨extremalFlag m w, upperCyclic_seed _⟩

theorem flagGenerator_ne_zero {n : ℕ} (m : ColumnShape n) (w : Equiv.Perm (Fin n)) :
    flagGenerator m w ≠ 0 := by
  intro h
  exact extremalFlag_ne_zero m w (congrArg Subtype.val h)

theorem flagGenerator_weight {n : ℕ} (m : ColumnShape n) (w : Equiv.Perm (Fin n))
    (t : DiagonalTorus n) :
    flagTorus m w t (flagGenerator m w) =
      integerWeightScalar (fun i => (extremalWeight m w i : ℤ)) t • flagGenerator m w := by
  apply Subtype.ext
  exact extremalFlag_weight m w t

theorem flagTorus_covariance {n : ℕ} (m : ColumnShape n) (w : Equiv.Perm (Fin n))
    (t : DiagonalTorus n) (a : Enveloping n) (p : flagDemazure m w) :
    flagTorus m w t (a • p) = torusEnveloping t a • flagTorus m w t p := by
  apply Subtype.ext
  exact polynomialEnveloping_torus t a p.val

/-- Naturality follows from U-linearity and the named generator; it need not
be an additional field of the shared JP input. -/
theorem flagPresentation_natural {n : ℕ} (m : ColumnShape n) (w : Equiv.Perm (Fin n))
    (e : PresentationQuotient (extremalWeight m w) ≃ₗ[Enveloping n] flagDemazure m w)
    (he : e (presentationGenerator (extremalWeight m w)) = flagGenerator m w)
    (a : Enveloping n) : e (Submodule.Quotient.mk a) = flagCyclicModuleMap m w a := by
  have ha : (Submodule.Quotient.mk a : PresentationQuotient (extremalWeight m w)) =
      a • presentationGenerator (extremalWeight m w) := by
    change Submodule.Quotient.mk a = Submodule.Quotient.mk (a*1)
    rw [mul_one]
  rw [ha, map_smul, he]
  rfl

end
end Schubert.RS.Representation
