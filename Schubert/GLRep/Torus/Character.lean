import Schubert.GLRep.Torus.Weights
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Normalizer

/-!
# Characters of polynomial representations of GL_n

The character of a polynomial representation of a split torus (`GLRep.torusCharacter`) is the
only integer polynomial whose values are the traces, in characteristic zero
(`GLRep.eq_torusCharacter_of_forall_trace_eq`). It is additive on products and multiplicative on
tensor products, and it is an invariant of the representation up to equivalence.

The **character** of a polynomial representation of `GL_n(K)` (`GLRep.character`) is the character
of its restriction to the diagonal torus, a polynomial in `x_0, …, x_{n-1}`; it is symmetric
(`GLRep.IsPolynomialRep.character_isSymmetric`).

## Main definitions

* `GLRep.character`: the character of a polynomial representation of `GL_n(K)`.
* `GLRep.weightSpace`: the weight spaces of the diagonal torus.

## Main results

* `GLRep.torusCharacter_eq_of_equiv`, `GLRep.torusCharacter_prod`, `GLRep.torusCharacter_tprod`.
* `GLRep.trace_diagGL_eq_eval_character`: traces on the torus are values of the character.
* `GLRep.eq_character_of_forall_trace_eq`: the character is the only such integer polynomial.
* `GLRep.character_eq_of_equiv`, `GLRep.character_prod`, `GLRep.character_tprod`.
* `GLRep.IsPolynomialRep.character_isSymmetric`: the character of a polynomial representation of
  `GL_n(K)` is a symmetric polynomial.
-/

namespace GLRep

open Module TauCeti

noncomputable section

variable {K : Type*} [Field K]
variable {W : Type*} [AddCommGroup W] [Module K W]
variable {V : Type*} [AddCommGroup V] [Module K V]

/-! ### Characters of the torus -/

section Torus

variable {κ : Type*} [Fintype κ] [Infinite K]
variable {ρ : Representation K (κ → Kˣ) W} {σ : Representation K (κ → Kˣ) V}

/-- **The character is determined by its values**: an integer polynomial whose value at every
point of the torus is the trace of the action is the character. -/
theorem eq_torusCharacter_of_forall_trace_eq [CharZero K]
    (h : HasCoeffsIn (coordFunctions K (torusCoord K κ)) ρ) (χ : MvPolynomial κ ℤ)
    (hχ : ∀ t : κ → Kˣ, MvPolynomial.eval₂ (Int.castRingHom K) (fun i => (t i : K)) χ =
      LinearMap.trace K W (ρ t)) :
    χ = torusCharacter ρ := by
  refine MvPolynomial.map_injective (Int.castRingHom K) Int.cast_injective ?_
  refine (isZariskiDense_torusCoord K κ).eq_of_forall_eval_eq fun t => ?_
  rw [← MvPolynomial.eval₂_eq_eval_map, ← MvPolynomial.eval₂_eq_eval_map]
  exact (hχ t).trans (trace_eq_eval_torusCharacter h t)

/-- Equivalent polynomial representations of the torus have the same character. -/
theorem torusCharacter_eq_of_equiv [CharZero K]
    (hρ : HasCoeffsIn (coordFunctions K (torusCoord K κ)) ρ)
    (hσ : HasCoeffsIn (coordFunctions K (torusCoord K κ)) σ) (e : ρ.Equiv σ) :
    torusCharacter ρ = torusCharacter σ := by
  refine (eq_torusCharacter_of_forall_trace_eq hσ _ fun t => ?_)
  rw [← trace_eq_eval_torusCharacter hρ t]
  have : σ t = e.toLinearEquiv.conj (ρ t) := by
    ext v
    obtain ⟨w, rfl⟩ := e.toLinearEquiv.surjective v
    simp only [LinearEquiv.conj_apply, LinearMap.coe_comp, LinearEquiv.coe_coe,
      Function.comp_apply, LinearEquiv.symm_apply_apply]
    exact (Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap t w).symm
  rw [this, LinearMap.trace_conj']

/-- The character of a product is the sum of the characters. -/
theorem torusCharacter_prod [CharZero K]
    (hρ : HasCoeffsIn (coordFunctions K (torusCoord K κ)) ρ)
    (hσ : HasCoeffsIn (coordFunctions K (torusCoord K κ)) σ) :
    torusCharacter (ρ.prod σ) = torusCharacter ρ + torusCharacter σ := by
  have := hρ.finiteDimensional
  have := hσ.finiteDimensional
  refine (eq_torusCharacter_of_forall_trace_eq (hρ.prod hσ) _ fun t => ?_).symm
  rw [MvPolynomial.eval₂_add, ← trace_eq_eval_torusCharacter hρ t,
    ← trace_eq_eval_torusCharacter hσ t]
  exact (LinearMap.trace_prodMap' (ρ t) (σ t)).symm

/-- The character of a tensor product is the product of the characters. -/
theorem torusCharacter_tprod [CharZero K]
    (hρ : HasCoeffsIn (coordFunctions K (torusCoord K κ)) ρ)
    (hσ : HasCoeffsIn (coordFunctions K (torusCoord K κ)) σ) :
    torusCharacter (ρ.tprod σ) = torusCharacter ρ * torusCharacter σ := by
  have := hρ.finiteDimensional
  have := hσ.finiteDimensional
  refine (eq_torusCharacter_of_forall_trace_eq (hρ.tprod hσ) _ fun t => ?_).symm
  rw [MvPolynomial.eval₂_mul, ← trace_eq_eval_torusCharacter hρ t,
    ← trace_eq_eval_torusCharacter hσ t, Representation.tprod_apply,
    LinearMap.trace_tensorProduct']

end Torus

/-! ### The general linear group -/

section GeneralLinear

variable {n : ℕ}

/-- The matrix entries of a diagonal matrix are polynomial in its diagonal entries. -/
theorem glCoord_diagGL_mem (p : Fin n × Fin n) :
    (fun t : Fin n → Kˣ => glCoord K n (diagGL t) p) ∈
      coordFunctions K (torusCoord K (Fin n)) := by
  by_cases hp : p.1 = p.2
  · have : (fun t : Fin n → Kˣ => glCoord K n (diagGL t) p) =
        fun t => torusCoord K (Fin n) t p.1 := by
      funext t
      simp [glCoord, diagGL_apply, hp]
    rw [this]
    exact coord_mem_coordFunctions _ _
  · have : (fun t : Fin n → Kˣ => glCoord K n (diagGL t) p) = 0 := by
      funext t
      simp [glCoord, diagGL_apply, hp]
    rw [this]
    exact zero_mem _

variable {ρ : Representation K (GL (Fin n) K) W} {σ : Representation K (GL (Fin n) K) V}

/-- The restriction of a polynomial representation of `GL_n(K)` to the diagonal torus is a
polynomial representation of the torus. -/
theorem IsPolynomialRep.comp_diagGL (h : IsPolynomialRep ρ) :
    HasCoeffsIn (coordFunctions K (torusCoord K (Fin n))) (ρ.comp diagGL) :=
  h.comp diagGL fun _ hf => comp_mem_coordFunctions _ glCoord_diagGL_mem hf

variable (ρ) in
/-- The **character** of a representation of `GL_n(K)`: the character of its restriction to the
diagonal torus, `∑_μ dim W_μ · x^μ`. -/
def character : MvPolynomial (Fin n) ℤ := torusCharacter (ρ.comp diagGL)

/-- The weight space of weight `μ` of a representation of `GL_n(K)`. -/
abbrev weightSpace (ρ : Representation K (GL (Fin n) K) W) (μ : Fin n → ℤ) : Submodule K W :=
  torusWeightSpace (ρ.comp diagGL) μ

variable [Infinite K]

theorem coeff_character (h : IsPolynomialRep ρ) (α : Fin n →₀ ℕ) :
    (character ρ).coeff α = finrank K (weightSpace ρ fun i => (α i : ℤ)) := by
  have := h.finiteDimensional
  exact coeff_torusCharacter _ α

/-- **The trace formula** for a polynomial representation of `GL_n(K)`. -/
theorem trace_diagGL_eq_eval_character (h : IsPolynomialRep ρ) (t : Fin n → Kˣ) :
    LinearMap.trace K W (ρ (diagGL t)) =
      MvPolynomial.eval₂ (Int.castRingHom K) (fun i => (t i : K)) (character ρ) :=
  trace_eq_eval_torusCharacter h.comp_diagGL t

/-- The character of a polynomial representation of `GL_n(K)` is the only integer polynomial
whose values on the diagonal torus are the traces. -/
theorem eq_character_of_forall_trace_eq [CharZero K] (h : IsPolynomialRep ρ)
    (χ : MvPolynomial (Fin n) ℤ)
    (hχ : ∀ t : Fin n → Kˣ, MvPolynomial.eval₂ (Int.castRingHom K) (fun i => (t i : K)) χ =
      LinearMap.trace K W (ρ (diagGL t))) :
    χ = character ρ :=
  eq_torusCharacter_of_forall_trace_eq h.comp_diagGL χ hχ

theorem character_eq_of_equiv [CharZero K] (hρ : IsPolynomialRep ρ) (hσ : IsPolynomialRep σ)
    (e : ρ.Equiv σ) : character ρ = character σ :=
  torusCharacter_eq_of_equiv hρ.comp_diagGL hσ.comp_diagGL (equivComp e diagGL)

theorem character_prod [CharZero K] (hρ : IsPolynomialRep ρ) (hσ : IsPolynomialRep σ) :
    character (ρ.prod σ) = character ρ + character σ := by
  rw [character, prod_comp]
  exact torusCharacter_prod hρ.comp_diagGL hσ.comp_diagGL

theorem character_tprod [CharZero K] (hρ : IsPolynomialRep ρ) (hσ : IsPolynomialRep σ) :
    character (ρ.tprod σ) = character ρ * character σ := by
  rw [character, tprod_comp]
  exact torusCharacter_tprod hρ.comp_diagGL hσ.comp_diagGL

/-- **The character of a polynomial representation of `GL_n(K)` is symmetric**: conjugating the
diagonal torus by a permutation matrix permutes the diagonal entries. -/
theorem IsPolynomialRep.character_isSymmetric [CharZero K] (h : IsPolynomialRep ρ) :
    (character ρ).IsSymmetric := by
  intro τ
  refine eq_character_of_forall_trace_eq h _ fun t => ?_
  have key : diagGL (fun i => t (τ i)) =
      permutationGL τ⁻¹ * diagGL t * (permutationGL (k := K) τ⁻¹)⁻¹ := by
    rw [permutationGL_mul_diagGL_mul_inv, inv_inv]
  rw [MvPolynomial.eval₂_rename]
  change MvPolynomial.eval₂ (Int.castRingHom K) (fun i => ((fun i => t (τ i)) i : K))
    (character ρ) = _
  rw [← trace_diagGL_eq_eval_character h, key, map_mul ρ, map_mul ρ, LinearMap.trace_mul_comm,
    ← mul_assoc, ← map_mul ρ, inv_mul_cancel, map_one, one_mul]

end GeneralLinear

end

end GLRep
