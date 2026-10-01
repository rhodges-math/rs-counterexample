import Schubert.RS.Quiver.TwoSource

/-!
# The two-source coefficient as a count

The coefficient (5.10) of Proposition 5.8, `[s_{(ν₂, ν₁)}] ∏_j h_{r_j}(x₁, x₂)`, written with the
Weyl projector (5.7), is `[x₁^{ν₁} x₂^{ν₂}] − [x₁^{ν₁−1} x₂^{ν₂+1}]` of `∏_j h_{r_j}(x₁, x₂)`. The
coefficient of `x₁^p x₂^q` (with `p + q = ∑_j r_j`) is the number of vectors `k` with
`0 ≤ k_j ≤ r_j` and `∑ k = p`, computed by the recursion `twoSourceCount` on the list of the
`r_j`. This is the dynamic program of the algorithm in `TwoSourceAlgorithm.lean`.

## Main definitions

* `Schubert.RS.Algorithms.twoSourceCount rs p`: `1` or `0` for the empty list (`p = 0` or not),
  and `∑_{k ≤ min(t, p)} twoSourceCount rs (p − k)` for `t :: rs`.

## Main results

* `Schubert.RS.Algorithms.coeff_hProdTwo`: the coefficients of `∏_j h_{r_j}(x₁, x₂)`.
* `Schubert.RS.Algorithms.twoSource_eq_count`: under the hypotheses of Proposition 5.8,
  `[𝒜_c](κ_a κ_b) = twoSourceCount r ν₁ − twoSourceCount r (ν₁ − 1)` (the second term `0` when
  `ν₁ = 0`).
-/

namespace Schubert.RS.Algorithms

open Quiver MvPolynomial

/-- The dynamic program of the two-source coefficient: `twoSourceCount rs p` is the coefficient of
`x^p` in `∏_{t ∈ rs} (1 + x + ⋯ + x^t)`, by the recursion on the list. -/
def twoSourceCount : List ℕ → ℕ → ℕ
  | [], p => if p = 0 then 1 else 0
  | t :: rs, p => ∑ k ∈ Finset.range (min t p + 1), twoSourceCount rs (p - k)

/-- `twoSourceCount` at an integer argument, `0` at negative arguments. -/
def twoSourceCountZ (rs : List ℕ) (x : ℤ) : ℕ :=
  if 0 ≤ x then twoSourceCount rs x.toNat else 0

theorem twoSourceCount_eq_zero_of_lt : ∀ (rs : List ℕ) {p : ℕ}, rs.sum < p →
    twoSourceCount rs p = 0
  | [], p, h => by simp only [List.sum_nil] at h; simp [twoSourceCount, Nat.pos_iff_ne_zero.mp h]
  | t :: rs, p, h => by
    simp only [List.sum_cons] at h
    rw [twoSourceCount]
    refine Finset.sum_eq_zero fun k hk => twoSourceCount_eq_zero_of_lt rs ?_
    rw [Finset.mem_range] at hk
    omega

theorem twoSourceCount_le : ∀ (rs : List ℕ) (p : ℕ), twoSourceCount rs p ≤ 2 ^ rs.sum
  | [], p => by simp only [twoSourceCount, List.sum_nil, pow_zero]; split_ifs <;> omega
  | t :: rs, p => by
    rw [twoSourceCount, List.sum_cons, pow_add]
    calc ∑ k ∈ Finset.range (min t p + 1), twoSourceCount rs (p - k)
        ≤ ∑ _k ∈ Finset.range (min t p + 1), 2 ^ rs.sum :=
          Finset.sum_le_sum fun k _ => twoSourceCount_le rs (p - k)
      _ = (min t p + 1) * 2 ^ rs.sum := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
      _ ≤ 2 ^ t * 2 ^ rs.sum := by
          have := Nat.lt_two_pow_self (n := t)
          exact Nat.mul_le_mul_right _ (by omega)

theorem sum_twoSourceCountZ (t : ℕ) (rs : List ℕ) (x : ℤ) :
    ∑ k ∈ Finset.range (t + 1), twoSourceCountZ rs (x - k) = twoSourceCountZ (t :: rs) x := by
  unfold twoSourceCountZ
  by_cases hx : 0 ≤ x
  · rw [ite_eq_left hx, twoSourceCount]
    obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hx
    rw [Int.toNat_natCast]
    rw [← Finset.sum_subset (Finset.range_subset_range.mpr (by omega : min t p + 1 ≤ t + 1))]
    · refine Finset.sum_congr rfl fun k hk => ?_
      rw [Finset.mem_range] at hk
      rw [ite_eq_left (by omega)]
      congr 1
      omega
    · intro k hk hk'
      rw [Finset.mem_range] at hk hk'
      rw [ite_eq_right (by omega)]
  · rw [ite_eq_right hx]
    exact Finset.sum_eq_zero fun k _ => ite_eq_right (by omega)

/-! ### The product `∏_j h_{r_j}(x₁, x₂)` -/

/-- `∏_{t ∈ rs} h_t(x₁, x₂)` in `Laurent 2`. -/
noncomputable def hProdTwo (rs : List ℕ) : Laurent 2 :=
  (rs.map fun t => toLaurent (hsymm (Fin 2) ℤ t)).prod

/-- The monomials of `h_t(x₁, x₂)`, indexed by the exponent `k ≤ t` of `x₁`. -/
theorem sum_compositionsOf_two {M : Type*} [AddCommMonoid M] (t : ℕ) (G : Weight 2 → M) :
    ∑ w ∈ Schur.compositionsOf 2 t, G (Schur.liftW w) =
      ∑ k ∈ Finset.range (t + 1), G ![(k : ℤ), ((t - k : ℕ) : ℤ)] := by
  symm
  refine Finset.sum_nbij' (fun k => ![k, t - k]) (fun w => w 0) (fun k hk => ?_)
    (fun w hw => ?_) (fun k _ => ?_) (fun w hw => ?_) (fun k _ => ?_)
  · rw [Finset.mem_range] at hk
    rw [Schur.mem_compositionsOf, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  · rw [Schur.mem_compositionsOf, Fin.sum_univ_two] at hw
    rw [Finset.mem_range]
    omega
  · simp
  · rw [Schur.mem_compositionsOf, Fin.sum_univ_two] at hw
    funext i
    fin_cases i
    · simp
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      omega
  · congr 1
    funext i
    fin_cases i <;> simp [Schur.liftW]

/-- **The coefficients of `∏_j h_{r_j}(x₁, x₂)`**: the coefficient of `x₁^p x₂^q` is
`twoSourceCount rs p` if `p + q = ∑ rs` (and `p ≥ 0`), and `0` otherwise. -/
theorem coeff_hProdTwo : ∀ (rs : List ℕ) (u : Weight 2),
    (hProdTwo rs).coeff u = if u 0 + u 1 = rs.sum then (twoSourceCountZ rs (u 0) : ℤ) else 0
  | [], u => by
    rw [hProdTwo, List.map_nil, List.prod_nil, AddMonoidAlgebra.one_def,
      AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    simp only [List.sum_nil, Nat.cast_zero, twoSourceCountZ, twoSourceCount]
    by_cases hu : u = 0
    · subst hu
      simp
    · rw [ite_eq_right (Ne.symm hu)]
      symm
      split_ifs with h1 h2 h3 <;> try rfl
      exfalso
      apply hu
      funext i
      fin_cases i
      · simp only [Fin.zero_eta, Pi.zero_apply]
        omega
      · simp only [Fin.mk_one, Pi.zero_apply]
        omega
  | t :: rs, u => by
    rw [hProdTwo, List.map_cons, List.prod_cons, ← hProdTwo, Schur.toLaurent_hsymm,
      Finset.sum_mul, AddMonoidAlgebra.coeff_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
    simp only [AddMonoidAlgebra.coeff_single_mul_apply, one_mul, coeff_hProdTwo rs]
    rw [sum_compositionsOf_two t (fun w => if (-w + u) 0 + (-w + u) 1 = rs.sum then
      (twoSourceCountZ rs ((-w + u) 0) : ℤ) else 0)]
    simp only [Pi.add_apply, Pi.neg_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    have hc : (((t :: rs).sum : ℕ) : ℤ) = t + rs.sum := by simp
    by_cases hs : u 0 + u 1 = ((t :: rs).sum : ℕ)
    · rw [ite_eq_left hs, ← sum_twoSourceCountZ, Nat.cast_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Finset.mem_range] at hk
      have hk' : ((t - k : ℕ) : ℤ) = t - k := by rw [Nat.cast_sub (by omega)]
      rw [ite_eq_left (by rw [hk']; omega)]
      congr 2
      ring
    · rw [ite_eq_right hs]
      refine Finset.sum_eq_zero fun k hk => ?_
      rw [Finset.mem_range] at hk
      have hk' : ((t - k : ℕ) : ℤ) = t - k := by rw [Nat.cast_sub (by omega)]
      rw [ite_eq_right (by rw [hk']; omega)]

theorem twoSourceCountZ_natCast (rs : List ℕ) (p : ℕ) :
    twoSourceCountZ rs (p : ℤ) = twoSourceCount rs p := by
  simp [twoSourceCountZ]

/-- **The Weyl projector of `∏_j h_{r_j}(x₁, x₂)` at `(ν₁, ν₂)`**, for `ν₁ + ν₂ = ∑_j r_j`. -/
theorem weylProjector_hProdTwo (rs : List ℕ) {ν₁ ν₂ : ℕ} (h : ν₁ + ν₂ = rs.sum) :
    Schur.weylProjector ![(ν₁ : ℤ), ν₂] (hProdTwo rs) =
      (twoSourceCount rs ν₁ : ℤ) - twoSourceCountZ rs ((ν₁ : ℤ) - 1) := by
  have hW : Schubert.RS.weylFactor 2 = 1 - AddMonoidAlgebra.single (positiveRoot 0 1) 1 := by
    rw [Schubert.RS.weylFactor, Fin.prod_univ_two]
    have h0 : (Finset.univ.filter fun l : Fin 2 => (0 : Fin 2) < l) = {1} := by decide
    have h1 : (Finset.univ.filter fun l : Fin 2 => (1 : Fin 2) < l) = ∅ := by decide
    rw [h0, h1, Finset.prod_singleton, Finset.prod_empty, mul_one]
  rw [Schur.weylProjector, hW, sub_mul, one_mul, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply,
    AddMonoidAlgebra.coeff_single_mul_apply, one_mul, coeff_hProdTwo, coeff_hProdTwo]
  have e0 : (-(positiveRoot (0 : Fin 2) 1) + ![(ν₁ : ℤ), ν₂]) 0 = ν₁ - 1 := by
    simp [positiveRoot]
    ring
  have e1 : (-(positiveRoot (0 : Fin 2) 1) + ![(ν₁ : ℤ), ν₂]) 1 = ν₂ + 1 := by
    simp [positiveRoot]
    ring
  have f0 : (![(ν₁ : ℤ), ν₂] : Weight 2) 0 = ν₁ := rfl
  have f1 : (![(ν₁ : ℤ), ν₂] : Weight 2) 1 = ν₂ := rfl
  rw [e0, e1, f0, f1, ite_eq_left (by omega), ite_eq_left (by omega), twoSourceCountZ_natCast]

/-- **The two-source coefficient as a count.** Under the hypotheses of Proposition 5.8,
`[𝒜_c](κ_a κ_b) = twoSourceCount r ν₁ − twoSourceCount r (ν₁ − 1)`, the second term `0` when
`ν₁ = 0`. -/
theorem twoSource_eq_count {m : ℕ} {a b c : Composition (m + 2)} {N : ℕ} {ν₁ ν₂ : ℕ}
    {r : Fin m → ℕ} (hW : Window.Hypotheses a b c N)
    (hstar : ∀ i j : Fin (m + 2), i < j →
      Window.cmp (Window.triple a b (Window.complement N c) i)
        (Window.triple a b (Window.complement N c) j) = starPattern i j)
    (hν₁ : Window.residual a b c 0 = ν₁) (hν₂ : Window.residual a b c 1 = ν₂)
    (hr : ∀ j, Window.residual a b c (singletonPos j) = -(r j : ℤ)) :
    atomCoefficient (key a * key b) c =
      (twoSourceCount (List.ofFn r) ν₁ : ℤ) - twoSourceCountZ (List.ofFn r) ((ν₁ : ℤ) - 1) := by
  rw [twoSource_eq_weylProjector hW hstar hν₁ hν₂ hr]
  have hprod : toLaurent (∏ j, hsymm (Fin 2) ℤ (r j)) = hProdTwo (List.ofFn r) := by
    rw [map_prod, hProdTwo, List.map_ofFn, List.prod_ofFn]
    rfl
  rw [hprod, weylProjector_hProdTwo]
  rw [List.sum_ofFn, sum_eq_of_twoSource hW hν₁ hν₂ hr]

end Schubert.RS.Algorithms
