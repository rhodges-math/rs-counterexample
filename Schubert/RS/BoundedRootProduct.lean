import Schubert.RS.RootSeriesWindow

/-! Finite geometric products count all nonnegative exponent functions in a root box. -/

namespace Schubert.RS
noncomputable section
open Representation

variable {ι σ : Type*} [Fintype ι] [DecidableEq ι]

def DegreeFiber (degree : ι → σ →₀ ℕ) (d : σ →₀ ℕ) :=
  {a : ι → ℕ // ∑ r, a r • degree r = d}

def boundedRootProduct (degree : ι → σ →₀ ℕ) (cut : ι → σ) (β : σ →₀ ℕ) :
    MvPolynomial σ ℤ :=
  ∏ r, ∑ k : Fin (β (cut r)+1), MvPolynomial.monomial (k.val • degree r) 1

theorem boundedRootProduct_expansion (degree : ι → σ →₀ ℕ) (cut : ι → σ) (β : σ →₀ ℕ) :
    boundedRootProduct degree cut β =
      ∑ a : (r : ι) → Fin (β (cut r)+1), MvPolynomial.monomial (∑ r, (a r).val • degree r) 1 := by
  classical
  rw [boundedRootProduct, Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro a ha
  exact (MvPolynomial.monomial_sum_one _ _).symm

def boundedDegreeFiberEquiv (degree : ι → σ →₀ ℕ) (cut : ι → σ)
    (hcut : ∀ r, degree r (cut r) = 1) (β d : σ →₀ ℕ) (hd : d ≤ β) :
    {a : (r : ι) → Fin (β (cut r)+1) // ∑ r, (a r).val • degree r = d} ≃
      DegreeFiber degree d where
  toFun a := ⟨fun r => (a.val r).val, a.property⟩
  invFun a := ⟨fun r => ⟨a.val r, Nat.lt_succ_of_le
    ((degree_fiber_bound degree cut hcut d a.val a.property r).trans (hd _))⟩, a.property⟩
  left_inv a := by apply Subtype.ext; funext r; rfl
  right_inv a := rfl

theorem boundedRootProduct_coefficient (degree : ι → σ →₀ ℕ) (cut : ι → σ)
    (hcut : ∀ r, degree r (cut r) = 1) (β d : σ →₀ ℕ) (hd : d ≤ β)
    [Fintype (DegreeFiber degree d)] :
    MvPolynomial.coeff d (boundedRootProduct degree cut β) =
      (Fintype.card (DegreeFiber degree d) : ℤ) := by
  classical
  rw [boundedRootProduct_expansion, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [← Fintype.card_congr (boundedDegreeFiberEquiv degree cut hcut β d hd)]
  simp [Fintype.card_subtype]

variable {n : ℕ}

theorem monomialDegree_extendAscent (u : Composition n) (a : AscentRoot u → ℕ) :
    monomialDegree (extendAscentPowers u a) = ascentMonomialDegree u a := by
  classical
  unfold monomialDegree ascentMonomialDegree
  have h := Finset.sum_subtype
    (p := fun r : PositiveRoot n => u r.val.1 < u r.val.2)
    (F := inferInstance)
    (Finset.univ.filter (fun r : PositiveRoot n => u r.val.1 < u r.val.2))
    (by intro r; simp)
    (fun r : PositiveRoot n => extendAscentPowers u a r • rootDegree r.val.1 r.val.2)
  have he (r : AscentRoot u) : extendAscentPowers u a r.val = a r := by
    simp [extendAscentPowers, r.property]
  simp only [he] at h
  rw [← h]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro r hr hn
  have hh : ¬u r.val.1 < u r.val.2 := by simpa using hn
  simp [extendAscentPowers, hh]

def ascentDegreeFiberEquiv (u : Composition n) (d : RootDegree n) :
    DegreeFiber (fun r : AscentRoot u => rootDegree r.val.val.1 r.val.val.2) d ≃
      AscentDegreeFiber u d where
  toFun a := ⟨a.val, (monomialDegree_extendAscent u a.val).trans a.property⟩
  invFun a := ⟨a.val, (monomialDegree_extendAscent u a.val).symm.trans a.property⟩
  left_inv a := rfl
  right_inv a := rfl

theorem ascentRootSeries_window_product (u : Composition n) (β : RootDegree n) :
    WindowEq β (ascentRootSeries u)
      ((boundedRootProduct
        (fun r : AscentRoot u => rootDegree r.val.val.1 r.val.val.2)
        (fun r => rootFirstCut r.val.val.1 r.val.val.2 r.val.property) β :
          MvPolynomial (Fin (n-1)) ℤ) : MvPowerSeries (Fin (n-1)) ℤ) := by
  intro d hd
  letI : Fintype (DegreeFiber (fun r : AscentRoot u => rootDegree r.val.val.1 r.val.val.2) d) :=
    Fintype.ofEquiv (AscentDegreeFiber u d) (ascentDegreeFiberEquiv u d).symm
  rw [MvPolynomial.coeff_coe, boundedRootProduct_coefficient
    (fun r : AscentRoot u => rootDegree r.val.val.1 r.val.val.2)
    (fun r => rootFirstCut r.val.val.1 r.val.val.2 r.val.property)
    (fun r => rootDegree_first r.val.val.1 r.val.val.2 r.val.property) β d hd,
    Fintype.card_congr (ascentDegreeFiberEquiv u d)]
  rfl

end
end Schubert.RS
