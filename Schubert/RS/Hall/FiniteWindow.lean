import Schubert.RS.Window.General
import Schubert.RS.WeylRootSeries

/-!
# The rational extraction formula with truncated geometric series

Proposition 2.13 (`Window.window_rational_extraction`) writes `[𝒜_c](κ_a κ_b)` as the coefficient of
`x^{c−a−b}` in `∏_{i<j} (1 − x_i/x_j)^{−cmp_{ij}}`, each factor `(1 − x_i/x_j)^{−1}` expanded as a
geometric series. Only finitely many terms of each series reach the coefficient of `x^{c−a−b}`:
this file truncates every geometric series in a degree `B` bounding the prefix heights and reads
the coefficient in the Laurent polynomial ring of the positions.

## Main definitions

* `Schubert.RS.Hall.finiteCmpFactor B k i j`: `(1 − x_i/x_j)^{−k}`, the geometric series
  truncated in degree `B`.

## Main results

* `Schubert.RS.Hall.atomCoefficient_eq_finiteCmpFactor`.
-/

namespace Schubert.RS.Hall

noncomputable section

open MvPolynomial Window Representation

variable {n : ℕ}

theorem windowEq_pow {σ : Type*} {β : σ →₀ ℕ} {f g : MvPowerSeries σ ℤ} (h : WindowEq β f g)
    (k : ℕ) : WindowEq β (f ^ k) (g ^ k) := by
  induction k with
  | zero => simpa using WindowEq.refl β (1 : MvPowerSeries σ ℤ)
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact ih.mul h

/-- A geometric series truncated in a degree bounding the window. -/
theorem geometric_truncation_le {σ : Type*} [Fintype σ] [DecidableEq σ] (d : σ →₀ ℕ) (cut : σ)
    (hc : d cut = 1) (β : σ →₀ ℕ) (B : ℕ) (hB : ∀ i, β i ≤ B) :
    WindowEq β (∑ k : Fin (B + 1), MvPowerSeries.monomial (k.val • d) 1)
      (rootGeometricSeries d) := by
  let γ : σ →₀ ℕ := Finsupp.onFinset Finset.univ (fun _ => B) (by intros; simp)
  have hγ (i : σ) : γ i = B := by simp [γ]
  have hw := geometric_truncation_window d cut hc γ
  change WindowEq γ (∑ k : Fin (B + 1), MvPowerSeries.monomial (k.val • d) 1)
    (rootGeometricSeries d) at hw
  intro e he
  apply hw
  intro i
  rw [hγ]
  exact (he i).trans (hB i)

/-- `(1 − X^d)^{−k}` with the geometric series truncated in degree `B`. -/
def finiteCmpPoly {σ : Type*} (B : ℕ) (k : ℤ) (d : σ →₀ ℕ) : MvPolynomial σ ℤ :=
  if 0 ≤ k then (∑ a : Fin (B + 1), monomial (a.val • d) 1) ^ k.toNat
  else (1 - monomial d 1) ^ (-k).toNat

/-- `(1 − x_i/x_j)^{−k}` in the Laurent polynomials of the positions, with the geometric series
`(1 − x_i/x_j)^{−1}` truncated in degree `B`. -/
def finiteCmpFactor (B : ℕ) (k : ℤ) (i j : Fin n) : Laurent n :=
  if 0 ≤ k then (∑ a : Fin (B + 1), AddMonoidAlgebra.single (a.val • positiveRoot i j) 1) ^ k.toNat
  else (1 - AddMonoidAlgebra.single (positiveRoot i j) 1) ^ (-k).toNat

theorem finiteCmpPoly_window (B : ℕ) (k : ℤ) {i j : Fin n} (hij : i < j) (β : RootDegree n)
    (hB : ∀ x, β x ≤ B) :
    WindowEq β (finiteCmpPoly B k (rootDegree i j) : MvPowerSeries (Fin (n - 1)) ℤ)
      (cmpFactor k (rootDegree i j)) := by
  unfold finiteCmpPoly cmpFactor
  split_ifs with hk
  · change WindowEq β (MvPolynomial.coeToMvPowerSeries.ringHom
      ((∑ a : Fin (B + 1), monomial (a.val • rootDegree i j) 1) ^ k.toNat)) _
    simp only [map_pow, map_sum, MvPolynomial.coeToMvPowerSeries.ringHom_apply,
      MvPolynomial.coe_monomial]
    exact windowEq_pow (geometric_truncation_le _ (rootFirstCut i j hij)
      (rootDegree_first i j hij) β B hB) _
  · change WindowEq β (MvPolynomial.coeToMvPowerSeries.ringHom
      ((1 - monomial (rootDegree i j) 1) ^ (-k).toNat)) _
    simp only [map_pow, map_sub, map_one, MvPolynomial.coeToMvPowerSeries.ringHom_apply,
      MvPolynomial.coe_monomial]
    exact WindowEq.refl _ _

theorem rootCoordinateEmbedding_finiteCmpPoly (B : ℕ) (k : ℤ) {i j : Fin n} (hij : i < j) :
    rootCoordinateEmbedding (finiteCmpPoly B k (rootDegree i j)) = finiteCmpFactor B k i j := by
  unfold finiteCmpPoly finiteCmpFactor
  split_ifs <;>
  simp only [map_pow, map_sum, map_sub, map_one, rootCoordinateEmbedding_monomial,
    rootWeight_nsmul, rootWeight_rootDegree i j hij]

theorem coeff_rootCoordinateEmbedding (p : MvPolynomial (Fin (n - 1)) ℤ) (d : RootDegree n) :
    (rootCoordinateEmbedding p).coeff (rootWeight d) = p.coeff d := by
  change Finsupp.mapDomain rootWeight (AddMonoidAlgebra.coeff p) (rootWeight d) = _
  exact Finsupp.mapDomain_apply_of_injective rootWeight_injective _ _

/-- **The rational extraction formula with truncated series.** Under the hypotheses of
Proposition 2.13, for every `B` bounding the prefix heights,
`[𝒜_c](κ_a κ_b) = [x^{c−a−b}] ∏_{i<j} (1 − x_i/x_j)^{−cmp((a_i,b_i,c̄_i),(a_j,b_j,c̄_j))}`, each
geometric series truncated in degree `B`. -/
theorem atomCoefficient_eq_finiteCmpFactor {a b c : Composition n} {N : ℕ}
    (h : Hypotheses a b c N) (B : ℕ) (hB : ∀ x, heightDegree a b c x ≤ B) :
    atomCoefficient (key a * key b) c =
      (∏ r : PositiveRoot n, finiteCmpFactor B
        (cmp (triple a b (complement N c) r.val.1) (triple a b (complement N c) r.val.2))
        r.val.1 r.val.2).coeff (residual a b c) := by
  have hw := WindowEq.prod (heightDegree a b c) Finset.univ
    (fun r : PositiveRoot n => ((finiteCmpPoly B
      (cmp (triple a b (complement N c) r.val.1) (triple a b (complement N c) r.val.2))
      (rootDegree r.val.1 r.val.2) : MvPolynomial (Fin (n - 1)) ℤ) :
        MvPowerSeries (Fin (n - 1)) ℤ))
    (fun r => cmpFactor
      (cmp (triple a b (complement N c) r.val.1) (triple a b (complement N c) r.val.2))
      (rootDegree r.val.1 r.val.2))
    (fun r _ => finiteCmpPoly_window B _ r.property _ hB)
  have hc := hw (heightDegree a b c) le_rfl
  have he : ((∏ r : PositiveRoot n, finiteCmpPoly B
      (cmp (triple a b (complement N c) r.val.1) (triple a b (complement N c) r.val.2))
      (rootDegree r.val.1 r.val.2) : MvPolynomial (Fin (n - 1)) ℤ) :
        MvPowerSeries (Fin (n - 1)) ℤ) =
      ∏ r : PositiveRoot n, ((finiteCmpPoly B
        (cmp (triple a b (complement N c) r.val.1) (triple a b (complement N c) r.val.2))
        (rootDegree r.val.1 r.val.2) : MvPolynomial (Fin (n - 1)) ℤ) :
          MvPowerSeries (Fin (n - 1)) ℤ) :=
    map_prod MvPolynomial.coeToMvPowerSeries.ringHom _ _
  rw [← he, MvPolynomial.coeff_coe] at hc
  rw [window_rational_extraction h, ← hc, ← coeff_rootCoordinateEmbedding,
    rootWeight_heightDegree h.balance h.height_nonneg, map_prod]
  refine congrArg (fun f : Laurent n => f.coeff (residual a b c)) ?_
  exact Finset.prod_congr rfl fun r _ => rootCoordinateEmbedding_finiteCmpPoly B _ r.property

end

end Schubert.RS.Hall
