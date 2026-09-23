import Schubert.RS.BoundedRootProduct
import Mathlib.RingTheory.MvPowerSeries.Inverse

/-! The paper's root-geometric factors as algebraic formal power series. -/

namespace Schubert.RS
noncomputable section
open Representation
variable {σ : Type*}

def rootGeometricSeries (d : σ →₀ ℕ) : MvPowerSeries σ ℤ :=
  MvPowerSeries.invOfUnit (1 - MvPowerSeries.monomial d 1) 1

theorem rootGeometricSeries_mul (d : σ →₀ ℕ) (hd : d ≠ 0) :
    rootGeometricSeries d * (1 - MvPowerSeries.monomial d 1) = 1 := by
  classical
  apply MvPowerSeries.invOfUnit_mul
  rw [map_sub, map_one, Units.val_one]
  suffices MvPowerSeries.constantCoeff (MvPowerSeries.monomial d (1 : ℤ)) = 0 by rw [this, sub_zero]
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_monomial]
  simp [Ne.symm hd]

theorem finite_geometric_identity {R : Type*} [CommRing R] (x : R) (N : ℕ) :
    (1-x) * (∑ k ∈ Finset.range N, x^k) = 1-x^N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, mul_add, ih, pow_succ]
    ring

theorem geometric_truncation_window (d : σ →₀ ℕ) (cut : σ) (hc : d cut = 1)
    (β : σ →₀ ℕ) :
    WindowEq β
      (∑ k : Fin (β cut+1), MvPowerSeries.monomial (k.val • d) 1)
      (rootGeometricSeries d) := by
  classical
  have hd : d ≠ 0 := by intro he; simp [he] at hc
  let x : MvPowerSeries σ ℤ := MvPowerSeries.monomial d 1
  have he : (1-x) * (∑ k : Fin (β cut+1), MvPowerSeries.monomial (k.val • d) 1) =
      1 - MvPowerSeries.monomial ((β cut+1) • d) 1 := by
    have h := finite_geometric_identity x (β cut+1)
    rw [← Fin.sum_univ_eq_sum_range] at h
    simpa only [x, MvPowerSeries.monomial_pow, one_pow] using h
  have hout : ¬(β cut+1) • d ≤ β := by
    intro h
    have hh := h cut
    simp only [Finsupp.smul_apply, smul_eq_mul, hc, mul_one] at hh
    omega
  have hw : WindowEq β ((1-x) * (∑ k : Fin (β cut+1), MvPowerSeries.monomial (k.val • d) 1)) 1 := by
    rw [he]
    intro e heβ
    have hz := monomial_mem_windowIdeal β ((β cut+1) • d) (1 : ℤ) hout e heβ
    simpa only [map_sub, map_zero, sub_zero] using
      congrArg (fun z => MvPowerSeries.coeff e (1 : MvPowerSeries σ ℤ) - z) hz
  have h := (WindowEq.refl β (rootGeometricSeries d)).mul hw
  simpa only [x, ← mul_assoc, rootGeometricSeries_mul d hd, one_mul, mul_one] using h

theorem WindowEq.prod {ι : Type*} (β : σ →₀ ℕ) (s : Finset ι)
    (f g : ι → MvPowerSeries σ ℤ) (h : ∀ i ∈ s, WindowEq β (f i) (g i)) :
    WindowEq β (∏ i ∈ s, f i) (∏ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using WindowEq.refl β (1 : MvPowerSeries σ ℤ)
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).mul
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

theorem boundedRootProduct_window_geometric {ι : Type*} [Fintype ι] [DecidableEq ι]
    (degree : ι → σ →₀ ℕ) (cut : ι → σ) (hc : ∀ r, degree r (cut r) = 1) (β : σ →₀ ℕ) :
    WindowEq β ((boundedRootProduct degree cut β : MvPolynomial σ ℤ) : MvPowerSeries σ ℤ)
      (∏ r, rootGeometricSeries (degree r)) := by
  change WindowEq β (MvPolynomial.coeToMvPowerSeries.ringHom (boundedRootProduct degree cut β)) _
  simp only [boundedRootProduct, map_prod, map_sum, MvPolynomial.coeToMvPowerSeries.ringHom_apply,
    MvPolynomial.coe_monomial]
  exact WindowEq.prod β _ _ _ (fun r hr => geometric_truncation_window (degree r) (cut r) (hc r) β)

variable {n : ℕ}

/-- The ascent-root exponent-counting series is exactly the product of
root-geometric factors. Every coefficient includes every exponent function. -/
theorem ascentRootSeries_eq_geometric (u : Composition n) :
    ascentRootSeries u = ∏ r : AscentRoot u, rootGeometricSeries (rootDegree r.val.val.1 r.val.val.2) := by
  apply MvPowerSeries.ext
  intro d
  exact ((ascentRootSeries_window_product u d).trans
    (boundedRootProduct_window_geometric
      (fun r : AscentRoot u => rootDegree r.val.val.1 r.val.val.2)
      (fun r => rootFirstCut r.val.val.1 r.val.val.2 r.val.property)
      (fun r => rootDegree_first r.val.val.1 r.val.val.2 r.val.property) d)) d le_rfl

end
end Schubert.RS
