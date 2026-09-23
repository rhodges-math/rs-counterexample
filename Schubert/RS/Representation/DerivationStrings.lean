import Schubert.RS.Representation.FlagChoice

namespace Schubert.RS.Representation
noncomputable section

variable {A : Type*} [CommRing A] [Algebra ℂ A]

def derivationIter (D : Derivation ℂ A A) (k : ℕ) : A →ₗ[ℂ] A := D.toLinearMap ^ k

@[simp] theorem derivationIter_zero (D : Derivation ℂ A A) (p : A) : derivationIter D 0 p = p := rfl

theorem derivationIter_succ (D : Derivation ℂ A A) (k : ℕ) (p : A) :
    derivationIter D (k+1) p = D (derivationIter D k p) := by
  change (D.toLinearMap^(k+1)) p = (D.toLinearMap * D.toLinearMap^k) p
  rw [pow_succ']

theorem derivationIter_linear_mul (D : Derivation ℂ A A) (f g : A)
    (hf : D (D f) = 0) (k : ℕ) :
    derivationIter D (k+1) (f*g) = f * derivationIter D (k+1) g +
      (k+1) • (D f * derivationIter D k g) := by
  induction k with
  | zero => simp [derivationIter_succ, Derivation.leibniz, smul_eq_mul, mul_comm, add_comm]
  | succ k ih =>
    rw [derivationIter_succ D (k+1), ih, map_add, map_nsmul]
    simp only [Derivation.leibniz, smul_eq_mul, hf, mul_zero, add_zero]
    rw [← derivationIter_succ D (k+1), ← derivationIter_succ D k]
    simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    ring

theorem derivationIter_inert_mul (D : Derivation ℂ A A) (f g : A)
    (hf : D f = 0) (k : ℕ) : derivationIter D k (f*g) = f * derivationIter D k g := by
  cases k with
  | zero => rfl
  | succ k => rw [derivationIter_linear_mul D f g (by rw [hf, map_zero]), hf]; simp

/-- A proved top derivative and its next vanishing, with factorial normalization. -/
def DerivationTop (D : Derivation ℂ A A) (p q : A) (d : ℕ) : Prop :=
  derivationIter D d p = d.factorial • q ∧ derivationIter D (d+1) p = 0

theorem derivationTop_one (D : Derivation ℂ A A) : DerivationTop D 1 1 0 := by
  constructor <;> simp [derivationIter_succ]

theorem DerivationTop.inert_mul {D : Derivation ℂ A A} {p q : A} {d : ℕ}
    (h : DerivationTop D p q d) (f : A) (hf : D f = 0) :
    DerivationTop D (f*p) (f*q) d := by
  constructor
  · rw [derivationIter_inert_mul D f p hf, h.1]
    simp only [nsmul_eq_mul]
    ring
  · rw [derivationIter_inert_mul D f p hf, h.2, mul_zero]

theorem DerivationTop.linear_mul {D : Derivation ℂ A A} {p q : A} {d : ℕ}
    (h : DerivationTop D p q d) (f : A) (hf : D (D f) = 0) :
    DerivationTop D (f*p) (D f*q) (d+1) := by
  constructor
  · rw [derivationIter_linear_mul D f p hf, h.1, h.2, mul_zero, zero_add,
      Nat.factorial_succ]
    simp only [nsmul_eq_mul, Nat.cast_mul]
    ring
  · have hz : derivationIter D (d+1+1) p = 0 := by rw [derivationIter_succ, h.2, map_zero]
    rw [derivationIter_linear_mul D f p hf, hz, h.2]
    simp

theorem DerivationTop.linear_pow_mul {D : Derivation ℂ A A} {p q : A} {d : ℕ}
    (h : DerivationTop D p q d) (f : A) (hf : D (D f) = 0) (m : ℕ) :
    DerivationTop D (f^m*p) ((D f)^m*q) (d+m) := by
  induction m with
  | zero => simpa using h
  | succ m ih =>
    simpa only [pow_succ', mul_assoc, Nat.add_assoc] using ih.linear_mul f hf

end
end Schubert.RS.Representation

