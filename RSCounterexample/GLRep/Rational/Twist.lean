import RSCounterexample.GLRep.HighestWeight.WeylModule

/-!
# Twisting by a character

A representation `ρ` of a monoid `G` can be twisted by a linear character `χ : G → Kˣ`:
`g ↦ χ(g) ρ(g)` on the same space (`GLRep.scaledRep`). Twisting does not change the
subrepresentations, hence preserves irreducibility, and it preserves the coefficient algebras
containing `χ`.

For `GL_n(K)` and `χ = det^k`, `k ≥ 0`, the character is multiplied by `(x_0 ⋯ x_{n-1})^k`
(`GLRep.character_scaledRep_detPow`). Since `s_{λ + k} = (x_0 ⋯ x_{n-1})^k s_λ`
(`GLRep.diagramSchurPoly_shift`), the twist of `V(λ)` by `det^k` is `V(λ + k)`
(`GLRep.nonempty_equiv_scaledRep_irrep`).

## Main definitions

* `GLRep.scaledRep ρ χ`: `ρ` twisted by `χ`.
* `GLRep.detPow K n k`: the character `det^k` of `GL_n(K)`.

## Main results

* `GLRep.isIrreducible_scaledRep_iff`, `GLRep.HasCoeffsIn.scaledRep`.
* `GLRep.character_scaledRep_detPow`, `GLRep.alternant_add_const`,
  `GLRep.diagramSchurPoly_shift`, `GLRep.nonempty_equiv_scaledRep_irrep`,
  `GLRep.nonempty_equiv_scaledRep_detShiftShape`.
-/

namespace GLRep

open Module Representation TauCeti MvPolynomial

noncomputable section

/-! ### Twisting by a character -/

section Scaled

variable {K G W : Type*} [Field K] [Monoid G] [AddCommGroup W] [Module K W]

/-- The representation `ρ` **twisted** by the linear character `χ`: `g ↦ χ(g) ρ(g)`. -/
def scaledRep (ρ : Representation K G W) (χ : G →* Kˣ) : Representation K G W where
  toFun g := (χ g : K) • ρ g
  map_one' := by rw [map_one, map_one, Units.val_one, one_smul]
  map_mul' g h := by rw [map_mul, map_mul, Units.val_mul, smul_mul_smul_comm]

@[simp] theorem scaledRep_apply (ρ : Representation K G W) (χ : G →* Kˣ) (g : G) (w : W) :
    scaledRep ρ χ g w = (χ g : K) • ρ g w := rfl

/-- Twisting does not change the subrepresentations. -/
def subrepScaledOrderIso (ρ : Representation K G W) (χ : G →* Kˣ) :
    Subrepresentation ρ ≃o Subrepresentation (scaledRep ρ χ) where
  toFun U := ⟨U.toSubmodule, fun g _ hw => U.toSubmodule.smul_mem _ (U.apply_mem_toSubmodule g hw)⟩
  invFun U := ⟨U.toSubmodule, fun g w hw => by
    have := U.toSubmodule.smul_mem ((χ g : K)⁻¹) (U.apply_mem_toSubmodule g hw)
    rwa [scaledRep_apply, smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul] at this⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

theorem isIrreducible_scaledRep_iff (ρ : Representation K G W) (χ : G →* Kˣ) :
    (scaledRep ρ χ).IsIrreducible ↔ ρ.IsIrreducible :=
  (OrderIso.isSimpleOrder_iff (subrepScaledOrderIso ρ χ)).symm

/-- Twisting by a character with values in `A` preserves coefficients in `A`. -/
theorem HasCoeffsIn.scaledRep {A : Subalgebra K (G → K)} {ρ : Representation K G W}
    (h : HasCoeffsIn A ρ) {χ : G →* Kˣ} (hχ : (fun g => (χ g : K)) ∈ A) :
    HasCoeffsIn A (GLRep.scaledRep ρ χ) := by
  refine ⟨h.finiteDimensional, fun f w => ?_⟩
  have : (fun g => f (GLRep.scaledRep ρ χ g w)) = (fun g => (χ g : K)) * fun g => f (ρ g w) := by
    funext g
    simp
  rw [this]
  exact A.mul_mem hχ (h.coeff_mem f w)

/-- Twisting is compatible with equivalences. -/
def scaledRepEquiv {V : Type*} [AddCommGroup V] [Module K V] {ρ : Representation K G W}
    {σ : Representation K G V} (e : ρ.Equiv σ) (χ : G →* Kˣ) :
    (scaledRep ρ χ).Equiv (scaledRep σ χ) :=
  .mk e.toLinearEquiv fun g => LinearMap.ext fun w => by
    change e.toLinearEquiv ((χ g : K) • ρ g w) = (χ g : K) • σ g (e.toLinearEquiv w)
    rw [map_smul]
    congr 1
    exact LinearMap.congr_fun (e.toIntertwiningMap.isIntertwining' g) w

end Scaled

/-! ### Powers of the determinant -/

section Det

variable {K : Type*} [Field K] {n : ℕ}
variable {W : Type*} [AddCommGroup W] [Module K W] {ρ : Representation K (GL (Fin n) K) W}

variable (K n) in
/-- The character `det^k` of `GL_n(K)`. -/
def detPow (k : ℕ) : GL (Fin n) K →* Kˣ := Matrix.GeneralLinearGroup.det ^ k

theorem detPow_apply (k : ℕ) (g : GL (Fin n) K) :
    (detPow K n k g : K) = (g : Matrix (Fin n) (Fin n) K).det ^ k := by
  simp [detPow, Matrix.GeneralLinearGroup.val_det_apply]

theorem detPow_mem (k : ℕ) : (fun g => (detPow K n k g : K)) ∈ glPolynomialFunctions K n :=
  mem_coordFunctions.mpr ⟨detPoly K n ^ k, fun g => by
    rw [detPow_apply, MvPolynomial.eval_pow, eval_glCoord_detPoly]⟩

theorem IsPolynomialRep.scaledRep_detPow (h : IsPolynomialRep ρ) (k : ℕ) :
    IsPolynomialRep (scaledRep ρ (detPow K n k)) :=
  HasCoeffsIn.scaledRep h (detPow_mem k)

variable [CharZero K]

/-- **The character of a twist by `det^k`** is multiplied by `(x_0 ⋯ x_{n-1})^k`. -/
theorem character_scaledRep_detPow (h : IsPolynomialRep ρ) (k : ℕ) :
    character (scaledRep ρ (detPow K n k)) = (∏ i, X i) ^ k * character ρ := by
  refine (eq_character_of_forall_trace_eq (h.scaledRep_detPow k) _ fun t => ?_).symm
  have hρ : ∀ w, scaledRep ρ (detPow K n k) (diagGL t) w =
      ((∏ i, (t i : K)) ^ k) • ρ (diagGL t) w := fun w => by
    rw [scaledRep_apply, detPow_apply, diagGL_coe, Matrix.det_diagonal]
  rw [show scaledRep ρ (detPow K n k) (diagGL t) = ((∏ i, (t i : K)) ^ k) • ρ (diagGL t) from
    LinearMap.ext hρ, map_smul, trace_diagGL_eq_eval_character h, smul_eq_mul,
    MvPolynomial.eval₂_mul, MvPolynomial.eval₂_pow, MvPolynomial.eval₂_prod]
  simp

end Det

/-! ### Shifting Schur polynomials -/

section Schur

variable {R : Type*} [CommRing R] {n : ℕ}

/-- Shifting all exponents of an alternant by `k` multiplies it by `(x_0 ⋯ x_{n-1})^k`. -/
theorem alternant_add_const (α : Fin n → ℕ) (k : ℕ) :
    alternant (Fin n) R (fun j => α j + k) = (∏ i, X i) ^ k * alternant (Fin n) R α := by
  rw [alternant_def, alternant_def, ← Finset.prod_pow, ← Matrix.det_mul_column]
  congr 1
  ext i j
  simp only [Matrix.of_apply, pow_add, mul_comm]

/-- **`s_{λ + k} = (x_0 ⋯ x_{n-1})^k s_λ`** for a polynomial dominant weight `λ`. -/
theorem diagramSchurPoly_shift [IsDomain R] {l : DominantWeight n} (hl : l.IsPolynomial)
    (k : ℕ) :
    diagramSchurPoly n R (l.shift k).shape = (∏ i, X i) ^ k * diagramSchurPoly n R l.shape := by
  have hl' : (l.shift k).IsPolynomial := fun i => by
    rw [DominantWeight.shift_apply]
    have := hl i
    omega
  have hδ : Function.Injective fun j : Fin n => n - 1 - (j : ℕ) := fun i j hij => by
    have := i.isLt
    have := j.isLt
    simp only at hij
    exact Fin.ext (by omega)
  apply mul_right_cancel₀ (alternant_ne_zero_of_injective (R := R) hδ)
  rw [diagramSchurPoly_mul_alternant n _ (DominantWeight.colLen_zero_shape_le _), mul_assoc,
    diagramSchurPoly_mul_alternant n _ (DominantWeight.colLen_zero_shape_le _),
    ← alternant_add_const]
  congr 1
  funext j
  have h1 := DominantWeight.natCast_rowLen_shape hl' j
  have h2 := DominantWeight.natCast_rowLen_shape hl j
  rw [DominantWeight.shift_apply] at h1
  simp only [YoungDiagram.betaNumber_def]
  omega

end Schur

/-! ### Twisting the irreducible representations -/

variable {K : Type*} [Field K] [CharZero K] {n : ℕ}

/-- **The twist of `V(λ)` by `det^k` is `V(λ + k)`.** -/
theorem nonempty_equiv_scaledRep_irrep {l : DominantWeight n} (hl : l.IsPolynomial) (k : ℕ) :
    Nonempty ((scaledRep (irrep K n l.shape) (detPow K n k)).Equiv
      (irrep K n (l.shift k).shape)) := by
  have h := isPolynomialRep_irrep (K := K) (n := n) l.shape
  refine IsPolynomialRep.nonempty_equiv_of_character_eq (h.scaledRep_detPow k)
    (isPolynomialRep_irrep _)
    ((isIrreducible_scaledRep_iff _ _).mpr (isIrreducible_irrep
      (DominantWeight.colLen_zero_shape_le l)))
    (isIrreducible_irrep (DominantWeight.colLen_zero_shape_le _)) ?_
  rw [character_scaledRep_detPow h, character_irrep (DominantWeight.colLen_zero_shape_le _),
    character_irrep (DominantWeight.colLen_zero_shape_le _), diagramSchurPoly_shift hl]

/-- The twist of `V(λ − λ_n)` by `det^{λ_n}` is `V(λ)`, for a polynomial dominant weight `λ`. -/
theorem nonempty_equiv_scaledRep_detShiftShape {l : DominantWeight n} (hl : l.IsPolynomial) :
    Nonempty ((scaledRep (irrep K n l.detShiftShape) (detPow K n l.detShift.toNat)).Equiv
      (irrep K n l.shape)) := by
  have h := nonempty_equiv_scaledRep_irrep (K := K)
    (DominantWeight.isPolynomial_shift_neg_detShift l) l.detShift.toNat
  have hk := (DominantWeight.isPolynomial_iff_zero_le_detShift l).mp hl
  have hsh : (l.shift (-l.detShift)).shift (l.detShift.toNat : ℤ) = l := by
    rw [DominantWeight.shift_shift, show -l.detShift + (l.detShift.toNat : ℤ) = 0 by omega,
      DominantWeight.shift_zero]
  rw [hsh] at h
  exact h

end

end GLRep
