import Schubert.RS.Quiver.Schur.Rational
import Schubert.RS.SourceAlternant

/-!
# The Weyl projector

The paper's Weyl factor `Δ_d(x) = ∏_{i<j} (1 − x_i/x_j)` (REL's `weylFactor d`) extracts Schur
coefficients: for a weakly increasing `u` and a symmetric Laurent polynomial `f`, the coefficient
`[x^u] Δ_d f` is the coefficient of `s_{(u_d, …, u_1)}` in the Schur expansion of `f`. This file
proves (5.7) of the paper, `[z^u] Δ_d(z) s_μ(z) = [μ = (u_d, …, u_1)]`, and the existence and
uniqueness of rational-Schur expansions of symmetric Laurent polynomials.

## Main definitions

* `Schubert.RS.Quiver.Schur.weylProjector`: `u ↦ [x^u] Δ_d f`.

## Main results

* `weylFactor_eq_alternant`: `Δ_d = x^{−(0,1,…,d−1)} a_{(0,1,…,d−1)}`.
* `weylProjector_eq_alternant`: for symmetric `f`, `[x^u] Δ_d f = [x^{u ∘ rev + δ}] a_δ f`.
* `weylProjector_ratSchur`: (5.7).
* `eq_zero_of_weylProjector`: a symmetric Laurent polynomial with vanishing projector coefficients
  at all weakly increasing exponents is zero.
* `exists_eq_sum_ratSchur`, `coeff_eq_weylProjector_of_eq_sum`: every symmetric Laurent
  polynomial is a finite integral combination of rational Schur polynomials, uniquely, and the
  coefficients are the projector coefficients.
-/

namespace Schubert.RS.Quiver.Schur

noncomputable section

open Equiv

variable {d : ℕ}

/-- The increasing staircase `(0, 1, …, d − 1)`. -/
def stairUp (d : ℕ) : Weight d := fun i => (i : ℤ)

theorem stairUp_eq : stairUp d = staircase d ∘ ⇑(Fin.revPerm : Perm (Fin d)) := by
  funext i
  simp only [stairUp, staircase, Function.comp_apply, Fin.revPerm_apply, Fin.val_rev]
  have := i.isLt
  omega

/-- A weakly decreasing weight plus the staircase is strictly decreasing. -/
theorem strictAnti_add_staircase {lam : Weight d} (h : Antitone lam) :
    StrictAnti (lam + staircase d) :=
  h.add_strictAnti (staircase_strictAnti d)

theorem antitone_comp_rev {u : Weight d} (hu : Monotone u) :
    Antitone (u ∘ ⇑(Fin.revPerm : Perm (Fin d))) := fun i j hij => by
  simp only [Function.comp_apply, Fin.revPerm_apply]
  exact hu (Fin.rev_le_rev.mpr hij)

/-- A strictly decreasing integer vector minus the staircase is weakly decreasing. -/
theorem antitone_sub_staircase {β : Weight d} (hβ : StrictAnti β) :
    Antitone (β - staircase d) := by
  cases d with
  | zero => exact fun i => i.elim0
  | succ n =>
    rw [Fin.antitone_iff_succ_le]
    intro i
    have h := hβ (Fin.castSucc_lt_succ (i := i))
    simp only [Pi.sub_apply, staircase, Fin.val_succ, Fin.val_castSucc]
    push_cast
    linarith

/-- The coefficient of a monomial multiple. -/
theorem coeff_single_mul (a : Weight d) (g : Laurent d) (w : Weight d) :
    (AddMonoidAlgebra.single a 1 * g).coeff w = g.coeff (w - a) := by
  have h := AddMonoidAlgebra.coeff_single_mul_add g (1 : ℤ) a (w - a)
  rw [add_sub_cancel, one_mul] at h
  exact h

/-- `Δ_d = x^{−(0,1,…,d−1)} a_{(0,1,…,d−1)}`. -/
theorem weylFactor_eq_alternant :
    weylFactor d = AddMonoidAlgebra.single (-stairUp d) 1 * alternant (stairUp d) := by
  have hdet := Matrix.det_apply'
    (Matrix.of fun i j : Fin d => coordinatePower i ((j.val : ℤ) - i.val))
  refine (weylFactor_eq_determinant.trans hdet).trans ?_
  rw [alternant, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hsum : (∑ i : Fin d, (Pi.single (σ i) ((i : ℤ) - (σ i : ℤ)) : Weight d)) =
      stairUp d ∘ σ.symm - stairUp d := by
    funext k
    rw [Finset.sum_apply]
    simp only [Pi.single_apply, Pi.sub_apply, Function.comp_apply, stairUp]
    rw [← Equiv.sum_comp σ.symm]
    simp only [Equiv.apply_symm_apply]
    rw [Finset.sum_ite_eq]
    simp
  have hprod : ∏ i : Fin d, coordinatePower (σ i) ((i : ℤ) - (σ i : ℤ)) =
      AddMonoidAlgebra.single (stairUp d ∘ σ.symm - stairUp d) 1 := by
    simp only [coordinatePower]
    rw [AddMonoidAlgebra.prod_single, hsum, Finset.prod_const_one]
  simp only [Matrix.of_apply]
  rw [hprod, AddMonoidAlgebra.intCast_def, AddMonoidAlgebra.single_mul_single,
    AddMonoidAlgebra.single_mul_single, zero_add, one_mul, mul_one]
  congr 1
  rw [sub_eq_neg_add]

/-- The Weyl projector: the coefficient of `x^u` in `Δ_d f`. -/
def weylProjector (u : Weight d) (f : Laurent d) : ℤ := (weylFactor d * f).coeff u

theorem weylProjector_add (u : Weight d) (f g : Laurent d) :
    weylProjector u (f + g) = weylProjector u f + weylProjector u g := by
  simp [weylProjector, mul_add]

theorem weylProjector_sub (u : Weight d) (f g : Laurent d) :
    weylProjector u (f - g) = weylProjector u f - weylProjector u g := by
  simp [weylProjector, mul_sub]

theorem weylProjector_sum {ι : Type*} (u : Weight d) (s : Finset ι) (f : ι → Laurent d) :
    weylProjector u (∑ i ∈ s, f i) = ∑ i ∈ s, weylProjector u (f i) := by
  simp [weylProjector, Finset.mul_sum, AddMonoidAlgebra.coeff_sum, Finsupp.coe_finsetSum,
    Finset.sum_apply]

theorem weylProjector_intCast_mul (u : Weight d) (k : ℤ) (f : Laurent d) :
    weylProjector u ((k : Laurent d) * f) = k * weylProjector u f := by
  rw [weylProjector, mul_left_comm, AddMonoidAlgebra.intCast_def, coeff_single_zero_mul]
  rfl

/-- For symmetric `f`, the Weyl projector is an alternant coefficient in the standard
orientation: `[x^u] Δ_d f = [x^{u ∘ rev + δ}] a_δ f`. -/
theorem weylProjector_eq_alternant {f : Laurent d} (hf : IsSymmetric f) (u : Weight d) :
    weylProjector u f =
      (alternant (staircase d) * f).coeff (u ∘ ⇑(Fin.revPerm : Perm (Fin d)) + staircase d) := by
  have hanti := isAntisymmetric_alternant_mul (staircase d) hf
  have e1 : weylFactor d * f =
      AddMonoidAlgebra.single (-stairUp d) 1 * (alternant (stairUp d) * f) := by
    rw [weylFactor_eq_alternant, mul_assoc]
  have e2 : alternant (stairUp d) =
      AddMonoidAlgebra.single 0 (Perm.sign (Fin.revPerm : Perm (Fin d)) : ℤ) *
        alternant (staircase d) := by
    rw [stairUp_eq, alternant_comp_perm]
  have e3 : (u ∘ ⇑(Fin.revPerm : Perm (Fin d)) + staircase d) ∘ ⇑(Fin.revPerm : Perm (Fin d)) =
      u - -stairUp d := by
    funext i
    simp only [Function.comp_apply, Pi.add_apply, Fin.revPerm_apply, Fin.rev_rev, staircase,
      Fin.val_rev, Pi.sub_apply, Pi.neg_apply, stairUp, sub_neg_eq_add]
    have := i.isLt
    omega
  have h2 := hanti Fin.revPerm (u ∘ ⇑(Fin.revPerm : Perm (Fin d)) + staircase d)
  rw [e3] at h2
  rw [weylProjector, e1, coeff_single_mul, e2, mul_assoc, coeff_single_zero_mul, h2,
    ← mul_assoc, ← Units.val_mul, Int.units_mul_self, Units.val_one, one_mul]

/-- **The Weyl projector** (5.7): for weakly increasing `u`,
`[z^u] Δ_d(z) s_μ(z) = 1` if `μ = (u_d, …, u_1)` and `0` otherwise. -/
theorem weylProjector_ratSchur (u : Weight d) (hu : Monotone u) (mu : TauCeti.DominantWeight d) :
    weylProjector u (ratSchur mu) = if mu.1 = u ∘ ⇑(Fin.revPerm : Perm (Fin d)) then 1 else 0 := by
  rw [weylProjector_eq_alternant (isSymmetric_ratSchur mu), alternant_mul_ratSchur,
    coeff_alternant_of_strictAnti (strictAnti_add_staircase mu.2)
      (strictAnti_add_staircase (antitone_comp_rev hu))]
  by_cases h : mu.1 = u ∘ ⇑(Fin.revPerm : Perm (Fin d))
  · simp [h]
  · have h' : ¬ mu.1 + staircase d = u ∘ ⇑(Fin.revPerm : Perm (Fin d)) + staircase d :=
      fun e => h (add_right_cancel e)
    simp [h, h']

/-- A symmetric Laurent polynomial all of whose projector coefficients at weakly increasing
exponents vanish is zero. -/
theorem eq_zero_of_weylProjector {f : Laurent d} (hf : IsSymmetric f)
    (h : ∀ u : Weight d, Monotone u → weylProjector u f = 0) : f = 0 := by
  apply eq_zero_of_alternant_mul_eq_zero
  apply eq_zero_of_isAntisymmetric (isAntisymmetric_alternant_mul _ hf)
  intro β hβ
  have hu : Monotone ((β - staircase d) ∘ ⇑(Fin.revPerm : Perm (Fin d))) := fun i j hij => by
    simp only [Function.comp_apply, Fin.revPerm_apply]
    exact antitone_sub_staircase hβ (Fin.rev_le_rev.mpr hij)
  have h1 := h _ hu
  rw [weylProjector_eq_alternant hf] at h1
  convert h1 using 2
  funext i
  simp

/-- The dominant weight `λ` with `λ + δ = β`, for strictly decreasing `β`. -/
def dominantOfStrictAnti (β : Weight d) (hβ : StrictAnti β) : TauCeti.DominantWeight d :=
  ⟨β - staircase d, antitone_sub_staircase hβ⟩

theorem monotone_comp_rev (lam : TauCeti.DominantWeight d) :
    Monotone (lam.1 ∘ ⇑(Fin.revPerm : Perm (Fin d))) := fun i j hij => by
  simp only [Function.comp_apply, Fin.revPerm_apply]
  exact lam.2 (Fin.rev_le_rev.mpr hij)

/-- **Uniqueness of Schur expansions**: the Weyl projector at `λ ∘ rev` reads off the coefficient
of `s_λ` in any finite combination of rational Schur polynomials. -/
theorem weylProjector_sum_ratSchur (S : Finset (TauCeti.DominantWeight d))
    (c : TauCeti.DominantWeight d → ℤ) (lam₀ : TauCeti.DominantWeight d) :
    weylProjector (lam₀.1 ∘ ⇑(Fin.revPerm : Perm (Fin d)))
        (∑ lam ∈ S, (c lam : Laurent d) * ratSchur lam) = if lam₀ ∈ S then c lam₀ else 0 := by
  classical
  rw [weylProjector_sum]
  have hterm : ∀ lam : TauCeti.DominantWeight d,
      weylProjector (lam₀.1 ∘ ⇑(Fin.revPerm : Perm (Fin d))) ((c lam : Laurent d) * ratSchur lam) =
        if lam = lam₀ then c lam else 0 := by
    intro lam
    rw [weylProjector_intCast_mul, weylProjector_ratSchur _ (monotone_comp_rev lam₀)]
    have hrr : (lam₀.1 ∘ ⇑(Fin.revPerm : Perm (Fin d))) ∘ ⇑(Fin.revPerm : Perm (Fin d)) =
        lam₀.1 := by
      funext i
      simp
    by_cases h : lam = lam₀
    · subst h
      simp [hrr]
    · have h' :
          ¬ lam.1 = (lam₀.1 ∘ ⇑(Fin.revPerm : Perm (Fin d))) ∘ ⇑(Fin.revPerm : Perm (Fin d)) := by
        rw [hrr]
        exact fun e => h (Subtype.ext e)
      simp [h, h']
  simp only [hterm]
  rw [Finset.sum_ite_eq']

/-- **Schur expansions** of symmetric Laurent polynomials exist, with the projector
coefficients: `f = ∑_λ c_λ s_λ` with `c_λ = [x^{λ ∘ rev}] Δ_d f`. -/
theorem exists_eq_sum_ratSchur {f : Laurent d} (hf : IsSymmetric f) :
    ∃ S : Finset (TauCeti.DominantWeight d),
      f = ∑ lam ∈ S, (weylProjector (lam.1 ∘ ⇑(Fin.revPerm : Perm (Fin d))) f : Laurent d) *
        ratSchur lam := by
  classical
  let T : Finset (Weight d) := (alternant (staircase d) * f).coeff.support.filter StrictAnti
  let S : Finset (TauCeti.DominantWeight d) :=
    T.attach.image fun β => dominantOfStrictAnti β.1 (Finset.mem_filter.mp β.2).2
  refine ⟨S, ?_⟩
  rw [← sub_eq_zero]
  refine eq_zero_of_weylProjector ?_ fun u hu => ?_
  · intro σ
    rw [map_sub, hf σ, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun lam _ => ?_
    rw [map_mul, map_intCast, isSymmetric_ratSchur lam σ]
  · let lam₀ : TauCeti.DominantWeight d :=
      ⟨u ∘ ⇑(Fin.revPerm : Perm (Fin d)), antitone_comp_rev hu⟩
    have hu₀ : lam₀.1 ∘ ⇑(Fin.revPerm : Perm (Fin d)) = u := by
      funext i
      simp [lam₀]
    rw [weylProjector_sub, ← hu₀, weylProjector_sum_ratSchur]
    split_ifs with hmem
    · exact sub_self _
    · rw [sub_zero, hu₀, weylProjector_eq_alternant hf]
      by_contra hne
      apply hmem
      have hβ : StrictAnti (u ∘ ⇑(Fin.revPerm : Perm (Fin d)) + staircase d) :=
        strictAnti_add_staircase (antitone_comp_rev hu)
      have hT : u ∘ ⇑(Fin.revPerm : Perm (Fin d)) + staircase d ∈ T :=
        Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr hne, hβ⟩
      refine Finset.mem_image.mpr ⟨⟨_, hT⟩, Finset.mem_attach _ _, ?_⟩
      apply Subtype.ext
      simp [dominantOfStrictAnti, lam₀]

end

end Schubert.RS.Quiver.Schur
