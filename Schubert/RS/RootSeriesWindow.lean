import Schubert.RS.RootConeCoordinates
import Schubert.RS.LinearWindowCount
import Schubert.RS.RectangleCoefficient

/-! Multiply the three proved key windows in genuine nonnegative coordinates. -/

namespace Schubert.RS
noncomputable section
open Representation
variable {n : ℕ}

def keyRootSeries (u : Composition n) : MvPowerSeries (Fin (n-1)) ℤ :=
  (rootCoordinates (normalizedKey u) : MvPowerSeries (Fin (n-1)) ℤ)

def ascentRootSeries (u : Composition n) : MvPowerSeries (Fin (n-1)) ℤ :=
  fun d => (Fintype.card (AscentDegreeFiber u d) : ℤ)

def weylRootSeries (n : ℕ) : MvPowerSeries (Fin (n-1)) ℤ :=
  (rootCoordinates (weylFactor n) : MvPowerSeries (Fin (n-1)) ℤ)

theorem keyRootSeries_window {E : Type*} [AddCommGroup E] [Module ℂ E]
    [Module (Enveloping n) E] [IsScalarTower ℂ (Enveloping n) E]
    (u : Composition n) (ρ : DiagonalTorus n →* Module.End ℂ E) (ξ : E)
    (hJP : HasJosephPoloPresentation u ρ ξ) (hDCF : HasDemazureCharacter u ρ)
    (hpbw : HasOrderedPBWBasis n) (β : RootDegree n)
    (hβ : ∀ r : PositiveRoot n, u r.val.1 < u r.val.2 →
      ¬ jpExponent u r • rootDegree r.val.1 r.val.2 ≤ β) :
    WindowEq β (keyRootSeries u) (ascentRootSeries u) := by
  intro d hd
  change MvPolynomial.coeff d (rootCoordinates (normalizedKey u)) = _
  rw [rootCoordinates_coeff, normalizedKey_coeff]
  exact key_coefficient_eq_ascent_count u ρ ξ hJP hDCF hpbw β d hd hβ

theorem key_eq_shift_normalizedKey (u : Composition n) :
    toLaurent (key u) =
      AddMonoidAlgebra.single (fun i => (u i : ℤ)) 1 * normalizedKey u := by
  simp only [normalizedKey, ← mul_assoc, AddMonoidAlgebra.single_mul_single, one_mul, add_neg_cancel]
  exact (one_mul _).symm

theorem three_keys_shift (a b g : Composition n) :
    toLaurent (key a) * toLaurent (key b) * toLaurent (key g) * weylFactor n =
      AddMonoidAlgebra.single (fun i => (a i : ℤ) + b i + g i) 1 *
        (normalizedKey a * normalizedKey b * normalizedKey g * weylFactor n) := by
  rw [key_eq_shift_normalizedKey a, key_eq_shift_normalizedKey b, key_eq_shift_normalizedKey g]
  have h : AddMonoidAlgebra.single (fun i => (a i : ℤ)) (1 : ℤ) *
      AddMonoidAlgebra.single (fun i => (b i : ℤ)) 1 *
      AddMonoidAlgebra.single (fun i => (g i : ℤ)) 1 =
      AddMonoidAlgebra.single (fun i => (a i : ℤ) + b i + g i) 1 := by
    simp only [AddMonoidAlgebra.single_mul_single, one_mul]
    rfl
  rw [← h]
  ring

theorem rootCoordinates_three_keys (a b g : Composition n)
    (ha : RootSupported (normalizedKey a)) (hb : RootSupported (normalizedKey b))
    (hg : RootSupported (normalizedKey g)) (d : RootDegree n) :
    (normalizedKey a * normalizedKey b * normalizedKey g * weylFactor n).coeff (rootWeight d) =
      MvPowerSeries.coeff d (keyRootSeries a * keyRootSeries b * keyRootSeries g * weylRootSeries n) := by
  rw [← rootCoordinates_coeff, rootCoordinates_mul _ _ ((ha.mul hb).mul hg) (weylFactor_rootSupported n),
    rootCoordinates_mul _ _ (ha.mul hb) hg, rootCoordinates_mul _ _ ha hb]
  simp only [keyRootSeries, weylRootSeries, ← MvPolynomial.coe_mul, MvPolynomial.coeff_coe]

variable {E : Composition n → Type*}
  [∀ u, AddCommGroup (E u)] [∀ u, Module ℂ (E u)]
  [∀ u, Module (Enveloping n) (E u)] [∀ u, IsScalarTower ℂ (Enveloping n) (E u)]

theorem three_key_window_coefficient
    (ρ : (u : Composition n) → DiagonalTorus n →* Module.End ℂ (E u))
    (ξ : (u : Composition n) → E u)
    (hJP : ∀ u, HasJosephPoloPresentation u (ρ u) (ξ u))
    (hDCF : ∀ u, HasDemazureCharacter u (ρ u)) (hpbw : HasOrderedPBWBasis n)
    (a b g : Composition n) (β : RootDegree n)
    (ha : ∀ r : PositiveRoot n, a r.val.1 < a r.val.2 →
      ¬ jpExponent a r • rootDegree r.val.1 r.val.2 ≤ β)
    (hb : ∀ r : PositiveRoot n, b r.val.1 < b r.val.2 →
      ¬ jpExponent b r • rootDegree r.val.1 r.val.2 ≤ β)
    (hg : ∀ r : PositiveRoot n, g r.val.1 < g r.val.2 →
      ¬ jpExponent g r • rootDegree r.val.1 r.val.2 ≤ β) :
    (toLaurent (key a) * toLaurent (key b) * toLaurent (key g) * weylFactor n).coeff
        ((fun i => (a i : ℤ) + b i + g i) + rootWeight β) =
      MvPowerSeries.coeff β (ascentRootSeries a * ascentRootSeries b * ascentRootSeries g * weylRootSeries n) := by
  rw [three_keys_shift, laurent_coefficient_shift]
  rw [rootCoordinates_three_keys a b g
    (normalizedKey_rootSupported a (ρ a) (ξ a) (hJP a) (hDCF a) hpbw)
    (normalizedKey_rootSupported b (ρ b) (ξ b) (hJP b) (hDCF b) hpbw)
    (normalizedKey_rootSupported g (ρ g) (ξ g) (hJP g) (hDCF g) hpbw)]
  exact (((keyRootSeries_window a (ρ a) (ξ a) (hJP a) (hDCF a) hpbw β ha).mul
    (keyRootSeries_window b (ρ b) (ξ b) (hJP b) (hDCF b) hpbw β hb)).mul
    (keyRootSeries_window g (ρ g) (ξ g) (hJP g) (hDCF g) hpbw β hg)).mul
    (WindowEq.refl β (weylRootSeries n)) β le_rfl

namespace Counterexample

theorem rectangular_target :
    (fun i => (a i : ℤ) + b i + g i) + rootWeight coefficientBox = (fun _ => (79 : ℤ)) := by
  rw [rootWeight_coefficientBox]
  funext i
  have h := g_add_c i
  change (a i : ℤ) + b i + g i + ((c i : ℤ) - a i - b i) = 79
  omega

end Counterexample
end
end Schubert.RS
