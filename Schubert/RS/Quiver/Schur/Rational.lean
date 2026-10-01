import Schubert.RS.Quiver.Schur.Alternant
import Schubert.RS.LaurentSymmetry
import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Bialternant
import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Symmetric
import TauCeti.RepresentationTheory.ClassicalGroups.DominantWeight

/-!
# Rational Schur polynomials

For a dominant weight `λ = (λ_0 ≥ ⋯ ≥ λ_{d−1})` of `GL_d` (integer entries, possibly negative),
the rational Schur polynomial `s_λ = (x_0⋯x_{d−1})^{λ_{d−1}} s_{λ − λ_{d−1}}` in `Laurent d`,
built from Tau Ceti's Schur polynomial of the normalized shape
(`TauCeti.DominantWeight.detShiftShape`).
These are the characters used in Theorem 5.3 of the paper ([Stanley, EC2, Theorem A2.4]).

## Main definitions

* `Schubert.RS.Quiver.Schur.ratSchur`: the rational Schur polynomial `s_λ`.
* `Schubert.RS.Quiver.Schur.shiftedSchur`: `(x_0⋯x_{d−1})^k s_ν` for a Young diagram `ν`.
* `Schubert.RS.Quiver.Schur.dualWeight`: `λ* = (−λ_{d−1}, …, −λ_0)`.

## Main results

* `isSymmetric_ratSchur`, `isSymmetric_shiftedSchur`: they are symmetric.
* `alternant_mul_ratSchur`: the bialternant formula `a_δ s_λ = a_{λ + δ}`.
* `reverseNeg_ratSchur`: `s_λ(x_{d−1}^{−1}, …, x_0^{−1}) = s_{λ*}(x)`.
-/

namespace Schubert.RS.Quiver.Schur

noncomputable section

open Equiv

variable {d : ℕ}

/-! ## Symmetry through `toLaurent` -/

theorem toLaurent_X (i : Fin d) :
    toLaurent (MvPolynomial.X i : Polynomial d) = AddMonoidAlgebra.single (Pi.single i 1) 1 := by
  rw [MvPolynomial.X, toLaurent_monomial]
  congr 1
  funext k
  simp only [exponentWeight, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Finsupp.single_apply,
    Pi.single_apply, eq_comm]
  split_ifs <;> rfl

theorem permute_toLaurent (σ : Perm (Fin d)) (p : Polynomial d) :
    permute σ (toLaurent p) = toLaurent (MvPolynomial.rename σ p) := by
  have h : (permute σ : Laurent d →+* Laurent d).comp toLaurent =
      toLaurent.comp (MvPolynomial.rename σ).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro z
      show permute σ (toLaurent (MvPolynomial.C z)) =
        toLaurent (MvPolynomial.rename σ (MvPolynomial.C z))
      rw [MvPolynomial.rename_C, MvPolynomial.C_apply, toLaurent_monomial, permute_single,
        map_zero]
      rfl
    · intro i
      simp only [RingHom.comp_apply, RingHom.coe_coe, AlgHom.toRingHom_eq_coe,
        MvPolynomial.rename_X, toLaurent_X, permute_single]
      congr 1
      funext k
      simp only [Function.comp_apply, Pi.single_apply, Equiv.symm_apply_eq]
  exact congrArg (fun φ : Polynomial d →+* Laurent d => φ p) h

theorem isSymmetric_toLaurent {p : Polynomial d} (hp : p.IsSymmetric) :
    IsSymmetric (toLaurent p) := fun σ => by rw [permute_toLaurent, hp σ]

theorem isSymmetric_single_const (k : ℤ) :
    IsSymmetric (AddMonoidAlgebra.single (fun _ : Fin d => k) (1 : ℤ)) := fun σ => by
  rw [permute_single]
  rfl

/-! ## Rational Schur polynomials -/

/-- `(x_0⋯x_{d−1})^k s_ν` for a Young diagram `ν`, with Tau Ceti's Schur polynomial `s_ν`. -/
def shiftedSchur (d : ℕ) (ν : YoungDiagram) (k : ℤ) : Laurent d :=
  AddMonoidAlgebra.single (fun _ => k) 1 * toLaurent (TauCeti.diagramSchurPoly d ℤ ν)

/-- The rational Schur polynomial `s_λ` of a dominant weight `λ` of `GL_d`:
`(x_0⋯x_{d−1})^{λ_{d−1}}` times the Schur polynomial of the diagram with rows
`λ_i − λ_{d−1}`. -/
def ratSchur (lam : TauCeti.DominantWeight d) : Laurent d :=
  shiftedSchur d lam.detShiftShape lam.detShift

theorem isSymmetric_shiftedSchur (ν : YoungDiagram) (k : ℤ) :
    IsSymmetric (shiftedSchur d ν k) :=
  (isSymmetric_single_const k).mul
    (isSymmetric_toLaurent (TauCeti.isSymmetric_diagramSchurPoly d ℤ ν))

theorem isSymmetric_ratSchur (lam : TauCeti.DominantWeight d) : IsSymmetric (ratSchur lam) :=
  isSymmetric_shiftedSchur _ _

/-- **Jacobi's bialternant formula** in `Laurent d`: `a_δ s_ν = a_{ν + δ}` for a Young diagram
with at most `d` rows. -/
theorem alternant_mul_schur (ν : YoungDiagram) (hν : ν.colLen 0 ≤ d) :
    alternant (staircase d) * toLaurent (TauCeti.diagramSchurPoly d ℤ ν) =
      alternant (fun i => (ν.rowLen i : ℤ) + staircase d i) := by
  have h := congrArg toLaurent (TauCeti.diagramSchurPoly_mul_alternant (R := ℤ) d ν hν)
  rw [map_mul, toLaurent_alternant, toLaurent_alternant, mul_comm] at h
  have hst : (fun i : Fin d => ((d - 1 - (i : ℕ) : ℕ) : ℤ)) = staircase d := by
    funext i
    simp only [staircase]
    have := i.isLt
    omega
  have hbeta : (fun i : Fin d => ((ν.betaNumber d i : ℕ) : ℤ)) =
      fun i : Fin d => (ν.rowLen i : ℤ) + staircase d i := by
    funext i
    simp only [YoungDiagram.betaNumber_def, staircase]
    have := i.isLt
    omega
  rw [hst, hbeta] at h
  exact h

theorem alternant_mul_shiftedSchur (ν : YoungDiagram) (hν : ν.colLen 0 ≤ d) (k : ℤ) :
    alternant (staircase d) * shiftedSchur d ν k =
      alternant (fun i => (ν.rowLen i : ℤ) + k + staircase d i) := by
  rw [shiftedSchur, mul_left_comm, alternant_mul_schur ν hν, mul_comm,
    alternant_mul_single_const]
  congr 1
  funext i
  simp only [Pi.add_apply]
  ring

/-- The bialternant formula for rational weights: `a_δ s_λ = a_{λ + δ}`. -/
theorem alternant_mul_ratSchur (lam : TauCeti.DominantWeight d) :
    alternant (staircase d) * ratSchur lam = alternant (lam.1 + staircase d) := by
  rw [ratSchur, alternant_mul_shiftedSchur _ (lam.colLen_zero_detShiftShape_le_pred.trans
    (Nat.sub_le d 1))]
  congr 1
  funext i
  simp only [Pi.add_apply, lam.natCast_rowLen_detShiftShape_add_detShift i]

/-- A symmetric Laurent polynomial `f` with `a_δ f = a_{λ + δ}` is `s_λ`. -/
theorem eq_ratSchur_of_alternant_mul {f : Laurent d} (lam : TauCeti.DominantWeight d)
    (h : alternant (staircase d) * f = alternant (lam.1 + staircase d)) : f = ratSchur lam := by
  rw [← sub_eq_zero]
  apply eq_zero_of_alternant_mul_eq_zero
  rw [mul_sub, h, alternant_mul_ratSchur, sub_self]

/-! ## The dual weight -/

/-- The dual dominant weight `λ* = (−λ_{d−1}, …, −λ_0)`: the highest weight of the dual
representation. -/
def dualWeight (lam : TauCeti.DominantWeight d) : TauCeti.DominantWeight d :=
  ⟨fun i => -lam.1 i.rev, fun i j hij => by
    have := lam.2 (Fin.rev_le_rev.mpr hij)
    simp only
    linarith⟩

theorem reverseNeg_single (w : Weight d) (z : ℤ) :
    reverseNeg (AddMonoidAlgebra.single w z) =
      AddMonoidAlgebra.single (fun i => -w i.rev) z :=
  AddMonoidAlgebra.mapDomainRingEquiv_single _ _ _

/-- `J a_α = a_{−α ∘ rev}` for the paper's involution `J f(x) = f(x_{d−1}^{−1}, …, x_0^{−1})`. -/
theorem reverseNeg_alternant (α : Weight d) :
    reverseNeg (alternant α) = alternant (fun i => -α i.rev) := by
  rw [alternant, alternant, map_sum]
  let c : Perm (Fin d) ≃ Perm (Fin d) :=
    { toFun := fun σ => Fin.revPerm * σ * Fin.revPerm
      invFun := fun σ => Fin.revPerm * σ * Fin.revPerm
      left_inv := fun σ => by
        ext i
        simp [Perm.mul_apply]
      right_inv := fun σ => by
        ext i
        simp [Perm.mul_apply] }
  refine Fintype.sum_equiv c _ _ fun σ => ?_
  have hc : ∀ i, (c σ).symm i = (σ.symm i.rev).rev := by
    intro i
    rw [Equiv.symm_apply_eq]
    simp [c, Perm.mul_apply]
  have hsign : Perm.sign (c σ) = Perm.sign σ := by
    simp only [c, Equiv.coe_fn_mk, Perm.sign_mul]
    rw [mul_comm (Perm.sign Fin.revPerm), mul_assoc, Int.units_mul_self, mul_one]
  rw [reverseNeg_single, hsign]
  congr 1
  funext i
  simp [hc]

/-- **Contragredient characters**: `J s_λ = s_{λ*}`, i.e. `s_λ(x^{−1}) = s_{λ*}(x)` since `s_λ`
is symmetric. -/
theorem reverseNeg_ratSchur (lam : TauCeti.DominantWeight d) :
    reverseNeg (ratSchur lam) = ratSchur (dualWeight lam) := by
  apply eq_ratSchur_of_alternant_mul
  -- `J a_δ = a_δ (x_0⋯x_{d−1})^{−(d−1)}`, and `J a_{λ+δ} = a_{λ*+δ} (x_0⋯x_{d−1})^{−(d−1)}`.
  have hδ : reverseNeg (alternant (staircase d)) =
      alternant (staircase d) * AddMonoidAlgebra.single (fun _ => -((d : ℤ) - 1)) 1 := by
    rw [reverseNeg_alternant, alternant_mul_single_const]
    congr 1
    funext i
    simp only [staircase, Fin.val_rev, Pi.add_apply]
    have := i.isLt
    omega
  have hlam : reverseNeg (alternant (lam.1 + staircase d)) =
      alternant ((dualWeight lam).1 + staircase d) *
        AddMonoidAlgebra.single (fun _ => -((d : ℤ) - 1)) 1 := by
    rw [reverseNeg_alternant, alternant_mul_single_const]
    congr 1
    funext i
    simp only [dualWeight, staircase, Fin.val_rev, Pi.add_apply]
    have := i.isLt
    omega
  have h := congrArg reverseNeg (alternant_mul_ratSchur lam)
  rw [map_mul, hδ, hlam, mul_right_comm] at h
  have hne : AddMonoidAlgebra.single (fun _ : Fin d => -((d : ℤ) - 1)) (1 : ℤ) ≠ 0 := by
    simp
  exact mul_right_cancel₀ hne h

end

end Schubert.RS.Quiver.Schur
