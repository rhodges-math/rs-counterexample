import RSCounterexample.GLRep.Borel.Basic

/-!
# Weights and characters of rational representations of the Borel subgroup

Let `B ⊆ GL_n(K)` be the upper-triangular Borel subgroup over a field `K`, with diagonal torus
`T = (Kˣ)ⁿ`. The **weight space** of `μ ∈ ℤⁿ` in a representation of `B` is the weight space of
its restriction to `T` (`GLRep.borelWeightSpace`), and its **character** is the Laurent polynomial
`ch ρ = ∑_μ dim W_μ · x^μ` (`GLRep.borelCharacter`). This file uses the standard convention
`x^μ` for the weight `μ`; the flag-variety library records weights by `x^{-μ}` instead
(`RSCounterexample.FlagVarieties.Modules.Character`).

## Main results

* `GLRep.IsRationalBorelRep.isInternal_borelWeightSpace`: a rational representation of `B` is the
  direct sum of its weight spaces (over an infinite field).
* `GLRep.IsRationalBorelRep.trace_borelTorus_eq`,
  `GLRep.IsRationalBorelRep.eq_borelCharacter_of_forall`: the trace formula and the uniqueness
  of the character.
* `GLRep.borelCharacter_eq_of_equiv`, `GLRep.borelCharacter_prod`, `GLRep.borelCharacter_tprod`.
* `GLRep.IsRationalBorelRep.borelCharacter_eq_add`: characters are additive on a
  subrepresentation and its quotient.
* `GLRep.borelCharacter_scaledRep`: twisting by the character `η` multiplies the character by
  `x^η`; `GLRep.borelCharacter_borelCharRep`: the character of `K_η` is `x^η`.
* `GLRep.borelCharacter_restrictBorel`: the character of the restriction of a representation of
  `GL_n(K)` to `B` is its character as a representation of `GL_n(K)`.
-/

namespace GLRep

open Module TauCeti

noncomputable section

/-! ### Restricting subrepresentations -/

section Restrict

variable {K G H W : Type*} [Field K] [Monoid G] [Monoid H] [AddCommGroup W] [Module K W]
variable {ρ : Representation K G W}

/-- A subrepresentation of `ρ` is a subrepresentation of the restriction `ρ ∘ φ`. -/
def subrepresentationComp (U : Subrepresentation ρ) (φ : H →* G) :
    Subrepresentation (ρ.comp φ) :=
  ⟨U.toSubmodule, fun h _ hv => U.apply_mem_toSubmodule (φ h) hv⟩

@[simp]
theorem toSubmodule_subrepresentationComp (U : Subrepresentation ρ) (φ : H →* G) :
    (subrepresentationComp U φ).toSubmodule = U.toSubmodule :=
  rfl

theorem toRepresentation_subrepresentationComp (U : Subrepresentation ρ) (φ : H →* G) :
    (subrepresentationComp U φ).toRepresentation = U.toRepresentation.comp φ :=
  rfl

theorem quotient_subrepresentationComp (U : Subrepresentation ρ) (φ : H →* G) :
    (subrepresentationComp U φ).quotient = U.quotient.comp φ :=
  rfl

end Restrict

/-! ### Trivial representations of the torus -/

section TrivialTorus

variable {K : Type*} [Field K] {κ : Type*} [Fintype κ]
variable {W : Type*} [AddCommGroup W] [Module K W]

theorem torusWeightSpace_trivial_zero :
    torusWeightSpace (Representation.trivial K (κ → Kˣ) W) 0 = ⊤ := by
  refine top_le_iff.mp fun w _ => mem_torusWeightSpace.mpr fun t => ?_
  rw [Representation.trivial_apply, coe_weightCharHom_zero, Pi.one_apply, one_smul]

theorem torusWeightSpace_trivial_of_ne_zero [Infinite K] {μ : κ → ℤ} (hμ : μ ≠ 0) :
    torusWeightSpace (Representation.trivial K (κ → Kˣ) W) μ = ⊥ := by
  have h := (iSupIndep_torusWeightSpace (Representation.trivial K (κ → Kˣ) W)).pairwiseDisjoint hμ
  rwa [Function.onFun, torusWeightSpace_trivial_zero, disjoint_top] at h

/-- The Laurent character of a trivial representation is its dimension. -/
theorem laurentCharacter_trivial [Infinite K] [FiniteDimensional K W] :
    laurentCharacter (Representation.trivial K (κ → Kˣ) W) =
      AddMonoidAlgebra.single 0 (finrank K W : ℤ) := by
  classical
  refine TorusLaurent.ext fun μ => ?_
  rw [coeff_laurentCharacter, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  by_cases hμ : μ = 0
  · subst hμ
    rw [ite_eq_left rfl, torusWeightSpace_trivial_zero, finrank_top]
  · rw [ite_eq_right (Ne.symm hμ), torusWeightSpace_trivial_of_ne_zero hμ, finrank_bot,
      Nat.cast_zero]

end TrivialTorus

variable {K : Type*} [Field K] {n : ℕ}
variable {W : Type*} [AddCommGroup W] [Module K W] {ρ : Representation K (borel K n) W}
variable {V : Type*} [AddCommGroup V] [Module K V] {σ : Representation K (borel K n) V}

/-! ### Weight spaces -/

section Weights

variable (ρ) in
/-- The **weight space** of weight `μ ∈ ℤⁿ` of a representation of `B`: the vectors on which each
`t ∈ T` acts by `t^μ = ∏ᵢ tᵢ^{μᵢ}`. -/
abbrev borelWeightSpace (μ : Fin n → ℤ) : Submodule K W :=
  torusWeightSpace (ρ.comp (borelTorus K n)) μ

theorem mem_borelWeightSpace {μ : Fin n → ℤ} {w : W} :
    w ∈ borelWeightSpace ρ μ ↔ ∀ t, ρ (borelTorus K n t) w = weightCharHom K μ t • w :=
  mem_torusWeightSpace

/-- An intertwining map sends weight vectors to weight vectors of the same weight. -/
theorem map_mem_borelWeightSpace (φ : ρ.IntertwiningMap σ) {μ : Fin n → ℤ} {w : W}
    (hw : w ∈ borelWeightSpace ρ μ) : φ w ∈ borelWeightSpace σ μ :=
  map_mem_torusWeightSpace ⟨φ.toLinearMap, fun t => φ.isIntertwining' (borelTorus K n t)⟩ hw

theorem finrank_borelWeightSpace_eq_of_equiv (e : ρ.Equiv σ) (μ : Fin n → ℤ) :
    finrank K (borelWeightSpace ρ μ) = finrank K (borelWeightSpace σ μ) :=
  finrank_torusWeightSpace_eq_of_equiv (equivComp e _) μ

variable [Infinite K]

/-- The weight spaces of a representation of `B` are independent. -/
theorem iSupIndep_borelWeightSpace : iSupIndep (borelWeightSpace ρ) :=
  iSupIndep_torusWeightSpace _

/-- **A rational representation of `B` is the direct sum of its weight spaces.** -/
theorem IsRationalBorelRep.isInternal_borelWeightSpace (h : IsRationalBorelRep ρ) :
    DirectSum.IsInternal (borelWeightSpace ρ) :=
  h.isRationalTorusRep.isInternal

theorem IsRationalBorelRep.iSup_borelWeightSpace_eq_top (h : IsRationalBorelRep ρ) :
    ⨆ μ, borelWeightSpace ρ μ = ⊤ :=
  h.isRationalTorusRep.iSup_torusWeightSpace_eq_top

end Weights

/-! ### Characters -/

section Character

variable (ρ) in
/-- The **character** `∑_μ dim W_μ · x^μ` of a representation of `B`, a Laurent polynomial (`0`
for an infinite-dimensional representation). -/
def borelCharacter : TorusLaurent (Fin n) := laurentCharacter (ρ.comp (borelTorus K n))

/-- **Equivalent representations of `B` have the same character.** -/
theorem borelCharacter_eq_of_equiv (e : ρ.Equiv σ) : borelCharacter ρ = borelCharacter σ :=
  laurentCharacter_eq_of_equiv (equivComp e _)

/-- The character of the restriction to `B` of a representation of `GL_n(K)` is its character as
a representation of `GL_n(K)`. -/
theorem borelCharacter_restrictBorel (ρ : Representation K (GL (Fin n) K) W) :
    borelCharacter (ρ.comp (borel K n).subtype) = ratCharacter ρ :=
  congrArg laurentCharacter (MonoidHom.ext fun _ => rfl)

theorem comp_borelTorus_scaledRep (η : Fin n → ℤ) :
    (scaledRep ρ (borelChar K n η)).comp (borelTorus K n) =
      scaledRep (ρ.comp (borelTorus K n)) (weightChar K η) := by
  ext t w
  simp only [MonoidHom.comp_apply, scaledRep_apply, borelChar_borelTorus]

/-- Twisting by the character `η` shifts the weights by `η`. -/
theorem borelWeightSpace_scaledRep (η μ : Fin n → ℤ) :
    borelWeightSpace (scaledRep ρ (borelChar K n η)) (μ + η) = borelWeightSpace ρ μ := by
  rw [borelWeightSpace, comp_borelTorus_scaledRep, torusWeightSpace_scaledRep]

variable [Infinite K]

theorem coeff_borelCharacter [FiniteDimensional K W] (μ : Fin n → ℤ) :
    (borelCharacter ρ).coeff μ = finrank K (borelWeightSpace ρ μ) :=
  coeff_laurentCharacter _ μ

/-- **The trace formula** for a rational representation of `B`. -/
theorem IsRationalBorelRep.trace_borelTorus_eq (h : IsRationalBorelRep ρ) (t : Fin n → Kˣ) :
    LinearMap.trace K W (ρ (borelTorus K n t)) = laurentEval K t (borelCharacter ρ) :=
  h.isRationalTorusRep.trace_eq_laurentEval t

/-- **Twisting by the character `η` multiplies the character by `x^η`.** -/
theorem borelCharacter_scaledRep [FiniteDimensional K W] (η : Fin n → ℤ) :
    borelCharacter (scaledRep ρ (borelChar K n η)) =
      AddMonoidAlgebra.single η 1 * borelCharacter ρ := by
  rw [borelCharacter, comp_borelTorus_scaledRep, laurentCharacter_scaledRep]
  rfl

/-- The character of the trivial representation is its dimension. -/
theorem borelCharacter_trivial [FiniteDimensional K W] :
    borelCharacter (Representation.trivial K (borel K n) W) =
      AddMonoidAlgebra.single 0 (finrank K W : ℤ) :=
  laurentCharacter_trivial

/-- **The character of `K_η` is `x^η`.** -/
theorem borelCharacter_borelCharRep (η : Fin n → ℤ) :
    borelCharacter (borelCharRep K n η) = AddMonoidAlgebra.single η 1 := by
  rw [borelCharRep, borelCharacter_scaledRep, borelCharacter_trivial, finrank_self,
    Nat.cast_one, AddMonoidAlgebra.single_mul_single, add_zero, mul_one]

/-- With a basis of weight vectors, `dim W_μ` is the number of basis vectors of weight `μ`. -/
theorem finrank_borelWeightSpace_of_basis {ι : Type*} [Fintype ι] (b : Module.Basis ι K W)
    (wt : ι → Fin n → ℤ) (hb : ∀ t i, ρ (borelTorus K n t) (b i) = weightCharHom K (wt i) t • b i)
    (μ : Fin n → ℤ) : finrank K (borelWeightSpace ρ μ) = Fintype.card {i // wt i = μ} :=
  finrank_torusWeightSpace_of_basis (π := ρ.comp (borelTorus K n)) b wt hb μ

/-- **The character of a representation of `B` with a basis of weight vectors.** -/
theorem borelCharacter_eq_sum_of_basis {ι : Type*} [Fintype ι] (b : Module.Basis ι K W)
    (wt : ι → Fin n → ℤ) (hb : ∀ t i, ρ (borelTorus K n t) (b i) = weightCharHom K (wt i) t • b i) :
    borelCharacter ρ = ∑ i, AddMonoidAlgebra.single (wt i) 1 :=
  laurentCharacter_eq_sum_of_basis (π := ρ.comp (borelTorus K n)) b wt hb

/-- **Characters are additive on a subrepresentation and its quotient.** -/
theorem IsRationalBorelRep.borelCharacter_eq_add (h : IsRationalBorelRep ρ)
    (U : Subrepresentation ρ) :
    borelCharacter ρ = borelCharacter U.toRepresentation + borelCharacter U.quotient :=
  h.isRationalTorusRep.laurentCharacter_eq_add (subrepresentationComp U (borelTorus K n))

/-- Weight multiplicities are additive on a subrepresentation and its quotient. -/
theorem IsRationalBorelRep.finrank_borelWeightSpace_eq_add (h : IsRationalBorelRep ρ)
    (U : Subrepresentation ρ) (μ : Fin n → ℤ) :
    finrank K (borelWeightSpace ρ μ) =
      finrank K (borelWeightSpace U.toRepresentation μ) +
        finrank K (borelWeightSpace U.quotient μ) :=
  h.isRationalTorusRep.finrank_torusWeightSpace_eq_add (subrepresentationComp U (borelTorus K n)) μ

variable [CharZero K]

/-- **The character of a rational representation of `B` is determined by the traces** on the
torus. -/
theorem IsRationalBorelRep.eq_borelCharacter_of_forall (h : IsRationalBorelRep ρ)
    (f : TorusLaurent (Fin n))
    (hf : ∀ t, laurentEval K t f = LinearMap.trace K W (ρ (borelTorus K n t))) :
    f = borelCharacter ρ :=
  h.isRationalTorusRep.eq_laurentCharacter_of_forall f hf

/-- The character of a product is the sum of the characters. -/
theorem borelCharacter_prod (hρ : IsRationalBorelRep ρ) (hσ : IsRationalBorelRep σ) :
    borelCharacter (ρ.prod σ) = borelCharacter ρ + borelCharacter σ := by
  rw [borelCharacter, prod_comp]
  exact laurentCharacter_prod hρ.isRationalTorusRep hσ.isRationalTorusRep

/-- The character of a tensor product is the product of the characters. -/
theorem borelCharacter_tprod (hρ : IsRationalBorelRep ρ) (hσ : IsRationalBorelRep σ) :
    borelCharacter (ρ.tprod σ) = borelCharacter ρ * borelCharacter σ := by
  rw [borelCharacter, tprod_comp]
  exact laurentCharacter_tprod hρ.isRationalTorusRep hσ.isRationalTorusRep

end Character

end

end GLRep
