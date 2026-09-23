import Schubert.RS.JosephPolo.CartanLie
import Schubert.RS.JosephPolo.TriangularExtension
import Mathlib.Tactic.NoncommRing

namespace Schubert.RS.Representation
noncomputable section
attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 1200000

def cartanEnvelopingCocycle {n : ℕ} (h : Fin n → ℂ) :
    upperNilpotent n →ₗ[ℂ] Module.End ℂ (Enveloping n) :=
  (regularEnvelopingAction n).toLinearMap.comp
    ((UniversalEnvelopingAlgebra.ι ℂ).toLinearMap.comp (cartanUpper h))

theorem cartanEnvelopingCocycle_lie {n : ℕ} (h : Fin n → ℂ) (A B : upperNilpotent n) :
    cartanEnvelopingCocycle h ⁅A,B⁆ =
      regularEnvelopingAction n (UniversalEnvelopingAlgebra.ι ℂ A) * cartanEnvelopingCocycle h B +
        cartanEnvelopingCocycle h A * regularEnvelopingAction n (UniversalEnvelopingAlgebra.ι ℂ B) -
        regularEnvelopingAction n (UniversalEnvelopingAlgebra.ι ℂ B) * cartanEnvelopingCocycle h A -
        cartanEnvelopingCocycle h B * regularEnvelopingAction n (UniversalEnvelopingAlgebra.ι ℂ A) := by
  let ρ := regularEnvelopingAction n
  have he (C D : upperNilpotent n) : ρ (UniversalEnvelopingAlgebra.ι ℂ ⁅C,D⁆) =
      ρ (UniversalEnvelopingAlgebra.ι ℂ C) * ρ (UniversalEnvelopingAlgebra.ι ℂ D) -
        ρ (UniversalEnvelopingAlgebra.ι ℂ D) * ρ (UniversalEnvelopingAlgebra.ι ℂ C) := by
    rw [LieHom.map_lie]
    change ρ (_*_ - _*_) = _
    rw [map_sub, map_mul, map_mul]
  change ρ (UniversalEnvelopingAlgebra.ι ℂ (cartanUpper h ⁅A,B⁆)) =
    ρ (UniversalEnvelopingAlgebra.ι ℂ A) * ρ (UniversalEnvelopingAlgebra.ι ℂ (cartanUpper h B)) +
      ρ (UniversalEnvelopingAlgebra.ι ℂ (cartanUpper h A)) * ρ (UniversalEnvelopingAlgebra.ι ℂ B) -
      ρ (UniversalEnvelopingAlgebra.ι ℂ B) * ρ (UniversalEnvelopingAlgebra.ι ℂ (cartanUpper h A)) -
      ρ (UniversalEnvelopingAlgebra.ι ℂ (cartanUpper h B)) * ρ (UniversalEnvelopingAlgebra.ι ℂ A)
  rw [cartanUpper_lie, map_add, map_add, he, he]
  abel

/-- The diagonal derivation on the actual UEA, constructed without PBW. -/
def cartanEnveloping {n : ℕ} (h : Fin n → ℂ) : Module.End ℂ (Enveloping n) :=
  envelopingCocycleOperator (cartanEnvelopingCocycle h) (cartanEnvelopingCocycle_lie h)

theorem cartanEnveloping_one {n : ℕ} (h : Fin n → ℂ) : cartanEnveloping h 1=0 :=
  envelopingCocycleOperator_one _ _

theorem cartanEnveloping_generator_mul {n : ℕ} (h : Fin n → ℂ)
    (A : upperNilpotent n) (a : Enveloping n) :
    cartanEnveloping h (UniversalEnvelopingAlgebra.ι ℂ A * a) =
      UniversalEnvelopingAlgebra.ι ℂ A * cartanEnveloping h a +
        UniversalEnvelopingAlgebra.ι ℂ (cartanUpper h A) * a :=
  envelopingCocycleOperator_generator_mul _ _ _ _

theorem cartanEnveloping_generator {n : ℕ} (h : Fin n → ℂ) (A : upperNilpotent n) :
    cartanEnveloping h (UniversalEnvelopingAlgebra.ι ℂ A) =
      UniversalEnvelopingAlgebra.ι ℂ (cartanUpper h A) := by
  simpa only [mul_one, cartanEnveloping_one, mul_zero, zero_add] using
    cartanEnveloping_generator_mul h A 1

theorem cartanEnveloping_mul {n : ℕ} (h : Fin n → ℂ) (a b : Enveloping n) :
    cartanEnveloping h (a*b) = cartanEnveloping h a*b + a*cartanEnveloping h b := by
  induction a using enveloping_induction generalizing b with
  | hC c =>
    simp only [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, map_smul,
      cartanEnveloping_one, smul_zero, zero_mul, zero_add]
  | hι A => rw [cartanEnveloping_generator_mul, cartanEnveloping_generator, add_comm]
  | hmul a c ha hc =>
    rw [mul_assoc, ha, hc, ha]
    noncomm_ring
  | hadd a c ha hc =>
    rw [add_mul, map_add, ha, hc, map_add]
    noncomm_ring

theorem cartanEnveloping_root {n : ℕ} (h : Fin n → ℂ) (r : PositiveRoot n) :
    cartanEnveloping h (rootOperator r) = (h r.val.1-h r.val.2) • rootOperator r := by
  change cartanEnveloping h (UniversalEnvelopingAlgebra.ι ℂ (rootVector r)) = _
  rw [cartanEnveloping_generator, cartanUpper_root, map_smul]
  rfl

theorem cartanEnveloping_root_pow {n : ℕ} (h : Fin n → ℂ) (r : PositiveRoot n) (k : ℕ) :
    cartanEnveloping h (rootOperator r^k) = ((k : ℂ)*(h r.val.1-h r.val.2)) • rootOperator r^k := by
  induction k with
  | zero => simp [cartanEnveloping_one]
  | succ k ih =>
    rw [pow_succ', cartanEnveloping_mul, cartanEnveloping_root, ih,
      smul_mul_assoc, mul_smul_comm, ← pow_succ', ← add_smul]
    congr 1
    push_cast
    ring

theorem cartanEnveloping_mem_jp {n : ℕ} (h : Fin n → ℂ) (u : Composition n)
    {a : Enveloping n} (ha : a ∈ jpLeftIdeal u) : cartanEnveloping h a ∈ jpLeftIdeal u := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨r,rfl⟩ := ha
    rw [cartanEnveloping_root_pow]
    exact ((jpLeftIdeal u).restrictScalars ℂ).smul_mem _ (Submodule.subset_span ⟨r,rfl⟩)
  | zero => simpa using (jpLeftIdeal u).zero_mem
  | add a b ha hb ia ib => simpa using (jpLeftIdeal u).add_mem ia ib
  | smul a b hb ib =>
    change cartanEnveloping h (a*b) ∈ jpLeftIdeal u
    rw [cartanEnveloping_mul]
    exact (jpLeftIdeal u).add_mem ((jpLeftIdeal u).smul_mem _ hb) ((jpLeftIdeal u).smul_mem _ ib)

theorem shiftedCartanEnveloping_commutator {n : ℕ} (h : Fin n → ℂ) (c : ℂ)
    (A : upperNilpotent n) :
    (cartanEnveloping h+c • 1) * regularEnvelopingAction n (UniversalEnvelopingAlgebra.ι ℂ A) -
      regularEnvelopingAction n (UniversalEnvelopingAlgebra.ι ℂ A) * (cartanEnveloping h+c • 1) =
      regularEnvelopingAction n (UniversalEnvelopingAlgebra.ι ℂ (cartanUpper h A)) := by
  apply LinearMap.ext
  intro a
  change cartanEnveloping h (UniversalEnvelopingAlgebra.ι ℂ A*a) +
    c • (UniversalEnvelopingAlgebra.ι ℂ A*a) -
    UniversalEnvelopingAlgebra.ι ℂ A*(cartanEnveloping h a+c • a) =
    UniversalEnvelopingAlgebra.ι ℂ (cartanUpper h A)*a
  rw [cartanEnveloping_generator_mul, mul_add, mul_smul_comm]
  abel

end
end Schubert.RS.Representation
