import RSCounterexample.Paper.Quiver.Decomposition

/-!
# Dual factors and the rectangle rule

For a dominant weight `κ` of `GL_d`, a Young diagram `ν` with at most `d` rows and an integer `c`,
the multiplicity of the one-dimensional character `det^c` in `s_κ(x) · s_ν(x⁻¹)` is `1` if
`κ = ν + c · (1, …, 1)` and `0` otherwise (`weylProjector_ratSchur_mul_reverseNeg`). This is the
dual form of the Pieri rule for a rectangle: `V^κ ⊗ (V^ν)^*` contains `det^c` exactly when
`V^κ = V^ν ⊗ det^c`.

Expanding a symmetric Laurent polynomial in rational Schur polynomials, it follows that the
multiplicity of `det^c` in `G · s_ν(x⁻¹)` is the multiplicity of `s_{ν + c}` in `G`
(`weylProjector_mul_reverseNeg`). In the language of LR chains: appending the dual factor of `ν`
to a sequence of vertex factors and asking for the constant weight `c` is the same as asking for
the weight `ν + c` without it (`card_LRChain_snoc_inFactor`).

Here `s_ν(x⁻¹)` is written `J s_ν` with the paper's involution
`J f(x) = f(x_{d−1}^{−1}, …, x_0^{−1})` (`Schubert.RS.reverseNeg`); for symmetric `f` the two
agree.

## Main results

* `Schubert.RS.Quiver.Schur.weylProjector_ratSchur_const`: the multiplicity of `det^c` in `s_κ`.
* `Schubert.RS.Quiver.Schur.weylProjector_ratSchur_mul_reverseNeg`: the rectangle rule.
* `Schubert.RS.Quiver.Schur.weylProjector_mul_reverseNeg`: appending a dual factor.
* `Schubert.RS.Quiver.Schur.card_LRChain_outFactor`: one polynomial factor.
* `Schubert.RS.Quiver.Schur.card_LRChain_snoc_inFactor`: the LR-chain form of the previous
  statement.
-/

namespace Schubert.RS.Quiver.Schur

noncomputable section

open Equiv ForwardQuiver

variable {d : ℕ}

/-! ## Coefficients -/

/-- The coefficients of `J f`: `[x^w] J f = [x^{w'}] f` with `w'_i = −w_{d−1−i}`. -/
theorem coeff_reverseNeg (f : Laurent d) (w : Weight d) :
    (reverseNeg f).coeff w = f.coeff (fun i => -w i.rev) := by
  simp only [reverseNeg, AddMonoidAlgebra.coeff_mapDomainRingEquiv, Finsupp.equivMapDomain_apply]
  rfl

/-- For symmetric `f`, `J f` is `f(x⁻¹)`: `[x^w] J f = [x^{−w}] f`. -/
theorem IsSymmetric.coeff_reverseNeg {f : Laurent d} (hf : IsSymmetric f) (w : Weight d) :
    (reverseNeg f).coeff w = f.coeff (-w) := by
  rw [Schur.coeff_reverseNeg, ← hf.coeff_comp (Fin.revPerm : Perm (Fin d)) (-w)]
  rfl

/-- The coefficients of an alternant times a Laurent polynomial. -/
theorem coeff_alternant_mul (α : Weight d) (g : Laurent d) (β : Weight d) :
    (alternant α * g).coeff β =
      ∑ σ : Perm (Fin d), (Perm.sign σ : ℤ) * g.coeff (β - α ∘ σ.symm) := by
  rw [alternant, Finset.sum_mul, AddMonoidAlgebra.coeff_sum, Finsupp.coe_finsetSum,
    Finset.sum_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [AddMonoidAlgebra.coeff_single_mul_apply, neg_add_eq_sub]

theorem isSymmetric_reverseNeg_schur (ν : YoungDiagram) (hν : ν.colLen 0 ≤ d) :
    IsSymmetric (reverseNeg (toLaurent (TauCeti.diagramSchurPoly d ℤ ν))) := by
  rw [← character_inFactor d ν hν]
  exact isSymmetric_character d _

/-! ## One factor -/

/-- **The multiplicity of `det^c` in `s_κ`** is `1` if `κ = (c, …, c)` and `0` otherwise. -/
theorem weylProjector_ratSchur_const (κ : TauCeti.DominantWeight d) (c : ℤ) :
    weylProjector (fun _ => c) (ratSchur κ) = if κ.1 = fun _ => c then 1 else 0 :=
  weylProjector_ratSchur _ monotone_const κ

/-! ## The rectangle rule -/

/-- **The rectangle rule.** For a dominant weight `κ` of `GL_d`, a Young diagram `ν` with at most
`d` rows and an integer `c`, the multiplicity of `det^c` in `s_κ(x) · s_ν(x⁻¹)` is `1` if
`κ = ν + c · (1, …, 1)` and `0` otherwise. -/
theorem weylProjector_ratSchur_mul_reverseNeg (κ : TauCeti.DominantWeight d) (ν : YoungDiagram)
    (hν : ν.colLen 0 ≤ d) (c : ℤ) :
    weylProjector (fun _ => c)
        (ratSchur κ * reverseNeg (toLaurent (TauCeti.diagramSchurPoly d ℤ ν))) =
      if κ.1 = (TauCeti.weightOfShape d ν).1 + fun _ => c then 1 else 0 := by
  set s := toLaurent (TauCeti.diagramSchurPoly d ℤ ν)
  have hs : IsSymmetric s := isSymmetric_toLaurent (TauCeti.isSymmetric_diagramSchurPoly d ℤ ν)
  set γ : Weight d := κ.1 - (fun _ => c) + staircase d
  -- `[x^{c + δ}] a_{κ + δ} · J s_ν = [x^{κ − c + δ}] a_δ · s_ν`
  have hsum : ∑ σ : Perm (Fin d), (Perm.sign σ : ℤ) *
      (reverseNeg s).coeff (((fun _ => c) ∘ ⇑(Fin.revPerm : Perm (Fin d)) + staircase d) -
        (κ.1 + staircase d) ∘ ⇑σ.symm) = (alternant (staircase d) * s).coeff γ := by
    rw [coeff_alternant_mul]
    refine Fintype.sum_equiv (Equiv.inv _) _ _ fun σ => ?_
    rw [hs.coeff_reverseNeg, ← hs.coeff_comp σ, Equiv.inv_apply, Perm.sign_inv]
    congr 2
    funext i
    simp only [γ, Function.comp_apply, Pi.neg_apply, Pi.sub_apply, Pi.add_apply,
      Equiv.symm_apply_apply, Perm.inv_def, Equiv.symm_symm]
    ring
  rw [weylProjector_eq_alternant ((isSymmetric_ratSchur κ).mul
      (isSymmetric_reverseNeg_schur ν hν)), ← mul_assoc, alternant_mul_ratSchur,
    coeff_alternant_mul, hsum, alternant_mul_schur ν hν]
  have hν' : StrictAnti fun i : Fin d => (ν.rowLen i : ℤ) + staircase d i :=
    strictAnti_add_staircase (TauCeti.weightOfShape d ν).2
  have hγ : StrictAnti γ := strictAnti_add_staircase fun i j hij => by
    simp only [Pi.sub_apply]
    linarith [κ.2 hij]
  rw [coeff_alternant_of_strictAnti hν' hγ]
  have hiff : ((fun i : Fin d => (ν.rowLen i : ℤ) + staircase d i) = γ) ↔
      κ.1 = (TauCeti.weightOfShape d ν).1 + fun _ => c := by
    constructor
    · intro h
      funext i
      have := congrFun h i
      simp only [γ, Pi.add_apply, Pi.sub_apply, TauCeti.weightOfShape_apply] at this ⊢
      linarith
    · intro h
      funext i
      have := congrFun h i
      simp only [γ, Pi.add_apply, Pi.sub_apply, TauCeti.weightOfShape_apply] at this ⊢
      linarith
  exact if_congr hiff rfl rfl

/-! ## Appending a dual factor -/

/-- **Appending a dual factor.** For a symmetric Laurent polynomial `G` in `d` variables, a Young
diagram `ν` with at most `d` rows and an integer `c`, the multiplicity of `det^c` in
`G · s_ν(x⁻¹)` is the multiplicity of `s_{ν + c · (1, …, 1)}` in `G`. -/
theorem weylProjector_mul_reverseNeg {G : Laurent d} (hG : IsSymmetric G) (ν : YoungDiagram)
    (hν : ν.colLen 0 ≤ d) (c : ℤ) :
    weylProjector (fun _ => c) (G * reverseNeg (toLaurent (TauCeti.diagramSchurPoly d ℤ ν))) =
      weylProjector (((TauCeti.weightOfShape d ν).shift c).1 ∘ ⇑(Fin.revPerm : Perm (Fin d)))
        G := by
  classical
  obtain ⟨S, hS⟩ := exists_eq_sum_ratSchur hG
  set lam₀ := (TauCeti.weightOfShape d ν).shift c
  rw [hS, weylProjector_sum_ratSchur, Finset.sum_mul, weylProjector_sum]
  have hterm : ∀ lam : TauCeti.DominantWeight d,
      weylProjector (fun _ => c) ((weylProjector (lam.1 ∘ ⇑(Fin.revPerm : Perm (Fin d))) G :
          Laurent d) * ratSchur lam * reverseNeg (toLaurent (TauCeti.diagramSchurPoly d ℤ ν))) =
        if lam = lam₀ then weylProjector (lam.1 ∘ ⇑(Fin.revPerm : Perm (Fin d))) G else 0 := by
    intro lam
    rw [mul_assoc, weylProjector_intCast_mul, weylProjector_ratSchur_mul_reverseNeg lam ν hν]
    have hiff : lam.1 = (TauCeti.weightOfShape d ν).1 + (fun _ => c) ↔ lam = lam₀ := by
      constructor
      · intro h
        apply Subtype.ext
        funext i
        rw [h, TauCeti.DominantWeight.shift_apply]
        rfl
      · rintro rfl
        funext i
        rw [TauCeti.DominantWeight.shift_apply]
        rfl
    by_cases h : lam = lam₀
    · rw [ite_eq_left (hiff.mpr h), ite_eq_left h, mul_one]
    · rw [ite_eq_right (fun h' => h (hiff.mp h')), ite_eq_right h, mul_zero]
  simp only [hterm]
  rw [Finset.sum_ite_eq']

/-! ## LR chains -/

/-- **One polynomial factor**: there is one LR chain for the single factor `s_μ` ending at `λ` if
`λ = μ`, and none otherwise. -/
theorem card_LRChain_outFactor (μ : YoungDiagram) (hμ : μ.colLen 0 ≤ d)
    (lam : TauCeti.DominantWeight d) :
    Fintype.card (LRChain ![outFactor μ] lam.1) =
      if lam = TauCeti.weightOfShape d μ then 1 else 0 := by
  have h := weylProjector_prod_character ![outFactor μ] lam
  rw [Fin.prod_univ_one, Matrix.cons_val_zero, character_outFactor,
    toLaurent_diagramSchurPoly_eq_ratSchur μ hμ,
    weylProjector_ratSchur _ (monotone_comp_rev lam)] at h
  have hrr : (lam.1 ∘ ⇑(Fin.revPerm : Perm (Fin d))) ∘ ⇑(Fin.revPerm : Perm (Fin d)) = lam.1 := by
    funext i
    simp
  rw [hrr] at h
  by_cases he : lam = TauCeti.weightOfShape d μ
  · rw [ite_eq_left (by rw [he]), eq_comm, Nat.cast_eq_one] at h
    rw [ite_eq_left he, h]
  · rw [ite_eq_right (fun e => he (Subtype.ext e.symm)), eq_comm, Nat.cast_eq_zero] at h
    rw [ite_eq_right he, h]

/-- **Appending a dual factor to an LR chain.** For vertex factors `F` in `d` variables, a Young
diagram `ν` with at most `d` rows and an integer `c`, the LR chains for `F` followed by the
factor `s_ν(x⁻¹)` ending at the constant weight `(c, …, c)` are as many as the LR chains for `F`
ending at `ν + c · (1, …, 1)`. -/
theorem card_LRChain_snoc_inFactor {m : ℕ} (F : Fin m → VertexFactor) (ν : YoungDiagram)
    (hν : ν.colLen 0 ≤ d) (c : ℤ) :
    Fintype.card (LRChain (Fin.snoc (α := fun _ => VertexFactor) F (inFactor d ν))
        (fun _ : Fin d => c)) =
      Fintype.card (LRChain F ((TauCeti.weightOfShape d ν).shift c).1) := by
  have h1 := weylProjector_prod_character (Fin.snoc (α := fun _ => VertexFactor) F (inFactor d ν))
    ⟨fun _ : Fin d => c, antitone_const⟩
  have h2 := weylProjector_prod_character F ((TauCeti.weightOfShape d ν).shift c)
  rw [Fin.prod_univ_castSucc] at h1
  simp only [Fin.snoc_castSucc, Fin.snoc_last, character_inFactor d ν hν] at h1
  rw [show ((fun _ : Fin d => c) ∘ ⇑(Fin.revPerm : Perm (Fin d))) = fun _ => c from rfl,
    weylProjector_mul_reverseNeg (isSymmetric_prod_character F) ν hν c, h2] at h1
  exact_mod_cast h1.symm

end

end Schubert.RS.Quiver.Schur
