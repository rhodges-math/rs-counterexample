import Schubert.RS.Quiver.Schur.Young
import TauCeti.Combinatorics.Young.Partitions

/-!
# The graded Cauchy identity

In the variables `x_0, …, x_{a−1}` and `y_0, …, y_{b−1}`,

  `h_ℓ(x_i y_j) = ∑_{μ} s_μ(x) s_μ(y)`,

the sum over the Young diagrams `μ` with `ℓ` cells and at most `min(a, b)` rows
(`Schubert.RS.Quiver.Schur.hsymm_mul_alphabet`). The identity is stated in `ℤ[x][y]`.

The proof uses no RSK correspondence. Fix an exponent `β` of the `y`-variables with `|β| = ℓ`.
- On the left, the coefficient of `y^β` is `∏_j h_{β_j}(x)` (`coeff_aeval_hsymm`): split a monomial
  of `h_ℓ` in the products `x_i y_j` by the index `j`.
- On the right, it is `∑_μ K_{μβ} s_μ(x)`.
- Both are symmetric in `x`. Their Weyl-projector coefficients agree: on the left by Young's rule
  (`Schubert.RS.Quiver.Schur.weylProjector_hProd`), on the right by the projector property of
  Schur polynomials.

## Main definitions

* `Schubert.RS.Quiver.Schur.shapesOfSize`: the Young diagrams with `ℓ` cells and at most `k` rows.

## Main results

* `Schubert.RS.Quiver.Schur.prod_hsymm_eq_sum`: `∏_j h_{β_j} = ∑_μ K_{μβ} s_μ`.
* `Schubert.RS.Quiver.Schur.hsymm_mul_alphabet`: the graded Cauchy identity.
-/

namespace Schubert.RS.Quiver.Schur

noncomputable section

open MvPolynomial Equiv

/-! ## Shapes of a given size -/

/-- The Young diagrams with `ℓ` cells and at most `k` rows. -/
def shapesOfSize (ℓ k : ℕ) : Finset YoungDiagram :=
  (Finset.univ.map ⟨TauCeti.diagramOf (n := ℓ), TauCeti.diagramOf_injective⟩).filter
    fun μ => μ.colLen 0 ≤ k

theorem mem_shapesOfSize {ℓ k : ℕ} {μ : YoungDiagram} :
    μ ∈ shapesOfSize ℓ k ↔ μ.card = ℓ ∧ μ.colLen 0 ≤ k := by
  simp only [shapesOfSize, Finset.mem_filter, Finset.mem_map, Finset.mem_univ, true_and,
    Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨⟨ν, rfl⟩, h⟩
    exact ⟨TauCeti.card_diagramOf ν, h⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨TauCeti.toPartition μ h1, TauCeti.diagramOf_toPartition μ h1⟩, h2⟩

/-! ## Monomial expansions -/

/-- An exponent vector on a finite type, as a finitely supported function. -/
def efs {K : Type*} [Fintype K] (w : K → ℕ) : K →₀ ℕ := Finsupp.equivFunOnFinite.symm w

@[simp]
theorem coe_efs {K : Type*} [Fintype K] (w : K → ℕ) : ⇑(efs w) = w :=
  Finsupp.coe_equivFunOnFinite_symm w

theorem efs_eq_iff {K : Type*} [Fintype K] (w : K → ℕ) (β : K →₀ ℕ) : efs w = β ↔ w = ⇑β :=
  ⟨fun h => by rw [← h, coe_efs], fun h => by ext k; rw [coe_efs, h]⟩

/-- The exponent vectors of total degree `ℓ` on a finite type. -/
def compositionsOn (K : Type*) [Fintype K] [DecidableEq K] (ℓ : ℕ) : Finset (K → ℕ) :=
  (Fintype.piFinset fun _ => Finset.range (ℓ + 1)).filter fun w => ∑ k, w k = ℓ

theorem mem_compositionsOn {K : Type*} [Fintype K] [DecidableEq K] {ℓ : ℕ} {w : K → ℕ} :
    w ∈ compositionsOn K ℓ ↔ ∑ k, w k = ℓ := by
  simp only [compositionsOn, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range,
    and_iff_right_iff_imp]
  intro h k
  have := Finset.single_le_sum (fun j _ => Nat.zero_le (w j)) (Finset.mem_univ k)
  omega

/-- `h_ℓ` as the sum of the monomials of degree `ℓ`. -/
theorem hsymm_eq_sum_compositionsOn (K : Type*) [Fintype K] [DecidableEq K] (ℓ : ℕ) :
    hsymm K ℤ ℓ = ∑ w ∈ compositionsOn K ℓ, monomial (efs w) 1 := by
  classical
  ext α
  rw [Schubert.RS.Quiver.coeff_hsymm, coeff_sum]
  simp only [coeff_monomial, efs_eq_iff]
  rw [Finset.sum_ite_eq']
  simp [mem_compositionsOn]

theorem prod_X_pow_eq_monomial' {K R : Type*} [Fintype K] [CommSemiring R] (v : K → ℕ) :
    ∏ k, (X k : MvPolynomial K R) ^ v k = monomial (efs v) 1 := by
  rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ fun k => pow_zero _]
  rfl

variable {a b : ℕ}

/-- The ring `ℤ[x_0, …, x_{a−1}][y_0, …, y_{b−1}]`. -/
abbrev XY (a b : ℕ) : Type := MvPolynomial (Fin b) (MvPolynomial (Fin a) ℤ)

/-- The products `x_i y_j`. -/
def xyProd (a b : ℕ) (ij : Fin a × Fin b) : XY a b := C (X ij.1) * X ij.2

theorem aeval_xyProd_monomial (w : Fin a × Fin b → ℕ) :
    aeval (xyProd a b) (monomial (efs w) (1 : ℤ)) =
      C (monomial (efs fun i => ∑ j, w (i, j)) 1) *
        monomial (efs fun j => ∑ i, w (i, j)) 1 := by
  rw [aeval_monomial, Finsupp.prod_fintype _ _ fun _ => pow_zero _, map_one, one_mul]
  simp only [coe_efs, xyProd, mul_pow, Finset.prod_mul_distrib]
  rw [← prod_X_pow_eq_monomial', ← prod_X_pow_eq_monomial', map_prod]
  congr 1
  · rw [Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Finset.prod_pow_eq_pow_sum, map_prod]
    simp only [map_pow]
  · rw [Fintype.prod_prod_type, Finset.prod_comm]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [← Finset.prod_pow_eq_pow_sum]

/-- **The `y^β`-coefficient of `h_ℓ(x_i y_j)`** is `∏_j h_{β_j}(x)` if `|β| = ℓ`, and `0`
otherwise. -/
theorem coeff_aeval_hsymm (ℓ : ℕ) (β : Fin b →₀ ℕ) :
    (aeval (xyProd a b) (hsymm (Fin a × Fin b) ℤ ℓ)).coeff β =
      if ∑ j, β j = ℓ then ∏ j, hsymm (Fin a) ℤ (β j) else 0 := by
  classical
  have hterm : ∀ w : Fin a × Fin b → ℕ,
      (aeval (xyProd a b) (monomial (efs w) (1 : ℤ))).coeff β =
        if (fun j => ∑ i, w (i, j)) = ⇑β then
          monomial (efs fun i => ∑ j, w (i, j)) 1 else 0 := by
    intro w
    rw [aeval_xyProd_monomial, coeff_C_mul, coeff_monomial]
    by_cases h : (fun j => ∑ i, w (i, j)) = ⇑β
    · rw [ite_eq_left ((efs_eq_iff _ _).mpr h), ite_eq_left h, mul_one]
    · rw [ite_eq_right (fun h' => h ((efs_eq_iff _ _).mp h')), ite_eq_right h, mul_zero]
  rw [hsymm_eq_sum_compositionsOn, map_sum, coeff_sum]
  refine (Finset.sum_congr rfl fun w _ => hterm w).trans ?_
  rw [← Finset.sum_filter]
  split_ifs with hβ
  · simp only [hsymm_eq_sum_compositionsOn, Finset.prod_univ_sum]
    simp only [← monomial_sum_one]
    refine Finset.sum_nbij' (fun w j i => w (i, j)) (fun V ij => V ij.2 ij.1) ?_ ?_ ?_ ?_ ?_
    · intro w hw
      rw [Finset.mem_filter, mem_compositionsOn] at hw
      rw [Fintype.mem_piFinset]
      intro j
      rw [mem_compositionsOn]
      exact congrFun hw.2 j
    · intro V hV
      rw [Fintype.mem_piFinset] at hV
      rw [Finset.mem_filter, mem_compositionsOn]
      refine ⟨?_, ?_⟩
      · rw [Fintype.sum_prod_type, Finset.sum_comm, ← hβ]
        exact Finset.sum_congr rfl fun j _ => mem_compositionsOn.mp (hV j)
      · funext j
        exact mem_compositionsOn.mp (hV j)
    · intro w _
      rfl
    · intro V _
      rfl
    · intro w _
      refine congrArg (fun m => monomial m (1 : ℤ)) ?_
      ext i
      simp [Finsupp.coe_finsetSum, Finset.sum_apply]
  · refine Finset.sum_eq_zero fun w hw => ?_
    exfalso
    rw [Finset.mem_filter, mem_compositionsOn] at hw
    apply hβ
    rw [← hw.1, Fintype.sum_prod_type, Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => (congrFun hw.2 j).symm

/-! ## Expanding `∏_j h_{β_j}` in Schur polynomials -/

/-- The coefficient of `y^β` in `s_μ(y)` counts the tableaux of weight `β`. -/
theorem coeff_diagramSchurPoly_eq (μ : YoungDiagram) (β : Fin b →₀ ℕ) :
    (TauCeti.diagramSchurPoly b ℤ μ).coeff β =
      ((Finset.univ.filter fun T : TauCeti.BoundedSSYT b μ => TauCeti.BoundedSSYT.weight T = β).card
        : ℤ) := by
  classical
  rw [TauCeti.diagramSchurPoly_eq_sum, coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_boole]

theorem coeff_diagramSchurPoly_eq_zero (μ : YoungDiagram) (β : Fin b →₀ ℕ)
    (h : ∑ j, β j ≠ μ.card) : (TauCeti.diagramSchurPoly b ℤ μ).coeff β = 0 := by
  rw [coeff_diagramSchurPoly_eq]
  simp only [Nat.cast_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff,
    Finset.mem_univ, true_implies]
  intro T hT
  apply h
  rw [← hT, TauCeti.BoundedSSYT.sum_weight]

theorem contentOf_eq_mapDomain (β : Fin b →₀ ℕ) :
    contentOf (fun j => β j) = ⇑(Finsupp.mapDomain Fin.val β) := by
  funext k
  by_cases hk : k < b
  · rw [contentOf, dite_eq_left hk]
    exact (Finsupp.mapDomain_apply_of_injective Fin.val_injective β ⟨k, hk⟩).symm
  · rw [contentOf, dite_eq_right hk, Finsupp.mapDomain_of_notMem_range]
    rintro ⟨j, rfl⟩
    exact hk j.isLt

theorem toLaurent_diagramSchurPoly_eq_ratSchur (μ : YoungDiagram) (hμ : μ.colLen 0 ≤ a) :
    toLaurent (TauCeti.diagramSchurPoly a ℤ μ) = ratSchur (TauCeti.weightOfShape a μ) := by
  apply eq_ratSchur_of_alternant_mul
  rw [alternant_mul_schur μ hμ]
  rfl

theorem isSymmetric_sum {ι : Type*} (S : Finset ι) (f : ι → Laurent a)
    (hf : ∀ i ∈ S, IsSymmetric (f i)) : IsSymmetric (∑ i ∈ S, f i) := fun σ => by
  rw [map_sum]
  exact Finset.sum_congr rfl fun i hi => hf i hi σ

theorem isSymmetric_intCast_mul (z : ℤ) {f : Laurent a} (hf : IsSymmetric f) :
    IsSymmetric ((z : Laurent a) * f) := fun σ => by
  rw [map_mul, map_intCast, hf σ]

/-- **`∏_j h_{β_j} = ∑_μ K_{μβ} s_μ`** in `a` variables, for an exponent `β` of total degree
`ℓ` in `b` letters: the sum runs over the shapes with `ℓ` cells and at most `min(a, b)` rows, and
`K_{μβ}` is the coefficient of `y^β` in `s_μ(y)`. -/
theorem prod_hsymm_eq_sum (ℓ : ℕ) (β : Fin b →₀ ℕ) (hβ : ∑ j, β j = ℓ) :
    ∏ j, hsymm (Fin a) ℤ (β j) =
      ∑ μ ∈ shapesOfSize ℓ (min a b),
        (TauCeti.diagramSchurPoly b ℤ μ).coeff β • TauCeti.diagramSchurPoly a ℤ μ := by
  classical
  apply toLaurent_injective
  rw [← sub_eq_zero]
  have hL : IsSymmetric (toLaurent (∏ j, hsymm (Fin a) ℤ (β j))) := isSymmetric_hProd fun j => β j
  have hR : IsSymmetric (toLaurent (∑ μ ∈ shapesOfSize ℓ (min a b),
      (TauCeti.diagramSchurPoly b ℤ μ).coeff β • TauCeti.diagramSchurPoly a ℤ μ)) := by
    rw [map_sum]
    refine isSymmetric_sum _ _ fun μ _ => ?_
    rw [zsmul_eq_mul, map_mul, map_intCast]
    exact isSymmetric_intCast_mul _
      (isSymmetric_toLaurent (TauCeti.isSymmetric_diagramSchurPoly a ℤ μ))
  have hD : IsSymmetric (toLaurent (∏ j, hsymm (Fin a) ℤ (β j)) - toLaurent (∑ μ ∈ shapesOfSize ℓ
      (min a b), (TauCeti.diagramSchurPoly b ℤ μ).coeff β • TauCeti.diagramSchurPoly a ℤ μ)) :=
    fun σ => by rw [map_sub, hL σ, hR σ]
  refine eq_zero_of_weylProjector hD fun u hu => ?_
  set lam : TauCeti.DominantWeight a := ⟨u ∘ ⇑(Fin.revPerm : Perm (Fin a)), antitone_comp_rev hu⟩
  have hu' : u = lam.1 ∘ ⇑(Fin.revPerm : Perm (Fin a)) := by
    funext i
    simp [lam]
  rw [weylProjector_sub, hu']
  have h1 := weylProjector_hProd (fun j => β j) lam
  rw [hProd] at h1
  rw [h1, map_sum, weylProjector_sum]
  have hterm : ∀ μ ∈ shapesOfSize ℓ (min a b),
      weylProjector (lam.1 ∘ ⇑(Fin.revPerm : Perm (Fin a)))
        (toLaurent ((TauCeti.diagramSchurPoly b ℤ μ).coeff β • TauCeti.diagramSchurPoly a ℤ μ)) =
        if TauCeti.weightOfShape a μ = lam then (TauCeti.diagramSchurPoly b ℤ μ).coeff β
        else 0 := by
    intro μ hμ
    have hμa : μ.colLen 0 ≤ a := ((mem_shapesOfSize.mp hμ).2).trans (min_le_left a b)
    rw [zsmul_eq_mul, map_mul, map_intCast, weylProjector_intCast_mul,
      toLaurent_diagramSchurPoly_eq_ratSchur μ hμa,
      weylProjector_ratSchur _ (fun x y hxy => by
        simpa using lam.2 (Fin.rev_le_rev.mpr hxy)) (TauCeti.weightOfShape a μ),
      show (lam.1 ∘ ⇑(Fin.revPerm : Perm (Fin a))) ∘ ⇑(Fin.revPerm : Perm (Fin a)) = lam.1 from
        funext fun i => by simp]
    by_cases he : TauCeti.weightOfShape a μ = lam
    · rw [ite_eq_left (congrArg Subtype.val he), ite_eq_left he, mul_one]
    · rw [ite_eq_right (fun e => he (Subtype.ext e)), ite_eq_right he, mul_zero]
  rw [Finset.sum_congr rfl hterm]
  unfold kostkaZ
  by_cases hp : lam.IsPolynomial
  · rw [ite_eq_left hp]
    have hshape : lam.shape.colLen 0 ≤ a := TauCeti.DominantWeight.colLen_zero_shape_le lam
    have huniq : ∀ μ ∈ shapesOfSize ℓ (min a b),
        TauCeti.weightOfShape a μ = lam ↔ μ = lam.shape := by
      intro μ hμ
      have hμa : μ.colLen 0 ≤ a := ((mem_shapesOfSize.mp hμ).2).trans (min_le_left a b)
      constructor
      · intro he
        rw [← he]
        exact (TauCeti.shape_weightOfShape hμa).symm
      · rintro rfl
        exact TauCeti.weightOfShape_shape hp
    rw [Finset.sum_congr rfl fun μ hμ => by rw [if_congr (huniq μ hμ) rfl rfl],
      Finset.sum_ite_eq']
    have hK : (TauCeti.diagramKostkaNumber lam.shape (contentOf fun j => β j) : ℤ) =
        (TauCeti.diagramSchurPoly b ℤ lam.shape).coeff β := by
      rw [TauCeti.coeff_diagramSchurPoly, contentOf_eq_mapDomain]
    split_ifs with hmem
    · rw [hK, sub_self]
    · rw [hK, sub_zero]
      rw [mem_shapesOfSize, not_and_or] at hmem
      rcases hmem with hcard | hcol
      · exact coeff_diagramSchurPoly_eq_zero _ _ (fun h => hcard (by rw [← h, hβ]))
      · have hb : b < lam.shape.colLen 0 := by omega
        rw [coeff_diagramSchurPoly_eq]
        have := TauCeti.BoundedSSYT.isEmpty_of_lt_colLen (n := b) hb
        simp
  · rw [ite_eq_right hp, zero_sub, neg_eq_zero]
    refine Finset.sum_eq_zero fun μ _ => ?_
    refine ite_eq_right fun he => ?_
    exact hp (he ▸ TauCeti.isPolynomial_weightOfShape a μ)

/-! ## The graded Cauchy identity -/

/-- **The graded Cauchy identity**: `h_ℓ(x_i y_j) = ∑_μ s_μ(x) s_μ(y)` in `ℤ[x][y]`, the sum over
the Young diagrams with `ℓ` cells and at most `min(a, b)` rows. -/
theorem hsymm_mul_alphabet (ℓ : ℕ) :
    aeval (xyProd a b) (hsymm (Fin a × Fin b) ℤ ℓ) =
      ∑ μ ∈ shapesOfSize ℓ (min a b), C (TauCeti.diagramSchurPoly a ℤ μ) *
        map (algebraMap ℤ (MvPolynomial (Fin a) ℤ)) (TauCeti.diagramSchurPoly b ℤ μ) := by
  ext β : 1
  rw [coeff_aeval_hsymm, coeff_sum]
  simp only [coeff_C_mul, coeff_map]
  split_ifs with hβ
  · rw [prod_hsymm_eq_sum ℓ β hβ]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [zsmul_eq_mul, mul_comm]
    rfl
  · refine (Finset.sum_eq_zero fun μ hμ => ?_).symm
    rw [coeff_diagramSchurPoly_eq_zero μ β (fun h => hβ (h.trans (mem_shapesOfSize.mp hμ).1)),
      map_zero, mul_zero]

end

end Schubert.RS.Quiver.Schur
