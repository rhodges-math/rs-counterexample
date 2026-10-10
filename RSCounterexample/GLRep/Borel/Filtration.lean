import RSCounterexample.GLRep.Borel.Character

/-!
# Finite filtrations of representations

A **filtration** of a representation `ρ` of a monoid `G` is a finite chain
`0 = F₀ ≤ F₁ ≤ ⋯ ≤ F_r = W` of subrepresentations (`GLRep.RepFiltration`). Its **layers** are the
successive quotients `F_{i+1}/F_i` (`GLRep.RepFiltration.layer`), realized as the subquotients
`GLRep.subquotient (F i) (F (i + 1))`. `GLRep.HasFiltrationBy 𝒞 ρ` states that `ρ` has a filtration
all of whose layers satisfy the predicate `𝒞`.

For rational representations of the Borel subgroup `B ⊆ GL_n(K)`, weight multiplicities and
characters are additive along filtrations (`GLRep.RepFiltration.finrank_borelWeightSpace_eq_sum`,
`GLRep.RepFiltration.borelCharacter_eq_sum`).

## Main definitions

* `GLRep.subrepresentationWithin U V`: the subrepresentation `U ∩ V` of `V`;
  `GLRep.subquotient U V`: the representation on `V / (U ∩ V)`.
* `GLRep.RepFiltration ρ`, `GLRep.RepFiltration.layer`, `GLRep.RepFiltration.single`.
* `GLRep.HasFiltrationBy 𝒞 ρ`.
-/

universe u

namespace GLRep

open Module

noncomputable section

variable {K G : Type*} [Field K] [Monoid G]
variable {W : Type u} [AddCommGroup W] [Module K W] {ρ : Representation K G W}

/-! ### Subquotients -/

section Subquotient

/-- The subrepresentation `U ∩ V` of the representation `V`. -/
def subrepresentationWithin (U V : Subrepresentation ρ) : Subrepresentation V.toRepresentation :=
  ⟨U.toSubmodule.comap V.toSubmodule.subtype, fun g _ hv => U.apply_mem_toSubmodule g hv⟩

theorem mem_subrepresentationWithin {U V : Subrepresentation ρ} {v : V.toSubmodule} :
    v ∈ (subrepresentationWithin U V).toSubmodule ↔ (v : W) ∈ U.toSubmodule :=
  Iff.rfl

/-- The **subquotient** `V / (U ∩ V)` of `ρ`; for `U ≤ V` this is `V / U`. -/
abbrev subquotient (U V : Subrepresentation ρ) :
    Representation K G (V.toSubmodule ⧸ (subrepresentationWithin U V).toSubmodule) :=
  (subrepresentationWithin U V).quotient

/-- For `U ≤ V`, the subrepresentation `U ∩ V` of `V` is equivalent to `U`. -/
def subrepresentationWithinEquiv {U V : Subrepresentation ρ} (h : U ≤ V) :
    (subrepresentationWithin U V).toRepresentation.Equiv U.toRepresentation :=
  .mk (Submodule.comapSubtypeEquivOfLe (show U.toSubmodule ≤ V.toSubmodule from h)) fun _ =>
    LinearMap.ext fun _ => Subtype.ext rfl

end Subquotient

/-! ### Filtrations -/

variable (ρ) in
/-- A **filtration** `0 = F₀ ≤ F₁ ≤ ⋯ ≤ F_r = W` of a representation by subrepresentations. The
steps are indexed by `ℕ`; only `F₀, …, F_r` matter, and `F_i = W` for `i ≥ r` by monotonicity. -/
structure RepFiltration where
  /-- The number `r` of layers. -/
  length : ℕ
  /-- The steps `F_i` of the filtration. -/
  step : ℕ → Subrepresentation ρ
  monotone : Monotone step
  step_zero : step 0 = ⊥
  step_length : step length = ⊤

namespace RepFiltration

variable (F : RepFiltration ρ)

/-- The `i`-th **layer** `F_{i+1} / F_i` of a filtration. -/
abbrev layer (i : ℕ) :
    Representation K G ((F.step (i + 1)).toSubmodule ⧸
      (subrepresentationWithin (F.step i) (F.step (i + 1))).toSubmodule) :=
  subquotient (F.step i) (F.step (i + 1))

theorem step_eq_top {i : ℕ} (hi : F.length ≤ i) : F.step i = ⊤ :=
  top_le_iff.mp (F.step_length ▸ F.monotone hi)

variable (ρ) in
/-- The one-step filtration `0 ≤ W`. -/
def single : RepFiltration ρ where
  length := 1
  step k := if k = 0 then ⊥ else ⊤
  monotone := by
    intro i j hij
    by_cases hi : i = 0
    · simp [hi]
    · have hj : j ≠ 0 := by omega
      simp [hi, hj]
  step_zero := by simp
  step_length := by simp

theorem single_length : (single ρ).length = 1 :=
  rfl

/-- The only layer of the one-step filtration is the representation itself. -/
def singleLayerEquiv : ((single ρ).layer 0).Equiv ρ :=
  .mk ((Submodule.quotEquivOfEqBot _ (by
      ext x
      simp only [mem_subrepresentationWithin, Submodule.mem_bot]
      exact ⟨fun hx => Subtype.ext hx, fun hx => by rw [hx]; rfl⟩)).trans
    (LinearEquiv.ofTop _ rfl)) fun _ => by
    ext
    rfl

end RepFiltration

/-- `ρ` **has a filtration by `𝒞`**: a filtration all of whose layers satisfy the predicate
`𝒞` on representations of `G`. -/
def HasFiltrationBy
    (𝒞 : ∀ (V : Type u) [AddCommGroup V] [Module K V], Representation K G V → Prop)
    (ρ : Representation K G W) : Prop :=
  ∃ F : RepFiltration ρ, ∀ i < F.length, 𝒞 _ (F.layer i)

/-- A representation equivalent to a member of `𝒞` has the one-step filtration by `𝒞`. -/
theorem hasFiltrationBy_single
    {𝒞 : ∀ (V : Type u) [AddCommGroup V] [Module K V], Representation K G V → Prop}
    (h : ∀ (V : Type u) [AddCommGroup V] [Module K V] (σ : Representation K G V),
      Nonempty (σ.Equiv ρ) → 𝒞 V σ) :
    HasFiltrationBy 𝒞 ρ :=
  ⟨RepFiltration.single ρ, fun i hi => by
    obtain rfl : i = 0 := by simpa [RepFiltration.single_length] using hi
    exact h _ _ ⟨RepFiltration.singleLayerEquiv⟩⟩

/-! ### Additivity of characters of representations of the Borel subgroup -/

section Borel

variable {n : ℕ} {ρ : Representation K (borel K n) W}

/-- The weight spaces of a subrepresentation are the intersections with the ambient weight
spaces. -/
theorem finrank_borelWeightSpace_subrepresentation (U : Subrepresentation ρ) (μ : Fin n → ℤ) :
    finrank K (borelWeightSpace U.toRepresentation μ) =
      finrank K ↥(borelWeightSpace ρ μ ⊓ U.toSubmodule) :=
  finrank_torusWeightSpace_subrepresentation (subrepresentationComp U (borelTorus K n)) μ

variable [Infinite K]

namespace RepFiltration

variable (F : RepFiltration ρ)

theorem finrank_borelWeightSpace_step (h : IsRationalBorelRep ρ) (μ : Fin n → ℤ) (k : ℕ) :
    finrank K (borelWeightSpace (F.step k).toRepresentation μ) =
      ∑ i ∈ Finset.range k, finrank K (borelWeightSpace (F.layer i) μ) := by
  induction k with
  | zero =>
    rw [Finset.sum_range_zero, finrank_borelWeightSpace_subrepresentation, F.step_zero]
    change finrank K ↥(borelWeightSpace ρ μ ⊓ (⊥ : Submodule K W)) = 0
    rw [inf_bot_eq, finrank_bot]
  | succ k ih =>
    rw [Finset.sum_range_succ, ← ih,
      IsRationalBorelRep.finrank_borelWeightSpace_eq_add (h.subrepresentation (F.step (k + 1)))
        (subrepresentationWithin (F.step k) (F.step (k + 1))) μ,
      finrank_borelWeightSpace_eq_of_equiv
        (subrepresentationWithinEquiv (F.monotone k.le_succ)) μ]

/-- **Weight multiplicities are additive along a filtration.** -/
theorem finrank_borelWeightSpace_eq_sum (h : IsRationalBorelRep ρ) (μ : Fin n → ℤ) :
    finrank K (borelWeightSpace ρ μ) =
      ∑ i ∈ Finset.range F.length, finrank K (borelWeightSpace (F.layer i) μ) := by
  rw [← F.finrank_borelWeightSpace_step h μ F.length, finrank_borelWeightSpace_subrepresentation,
    F.step_length]
  change _ = finrank K ↥(borelWeightSpace ρ μ ⊓ (⊤ : Submodule K W))
  rw [inf_top_eq]

/-- A weight of a layer is a weight of the filtered representation. -/
theorem finrank_layer_borelWeightSpace_le (h : IsRationalBorelRep ρ) (μ : Fin n → ℤ) {i : ℕ}
    (hi : i < F.length) :
    finrank K (borelWeightSpace (F.layer i) μ) ≤ finrank K (borelWeightSpace ρ μ) := by
  rw [F.finrank_borelWeightSpace_eq_sum h μ]
  exact Finset.single_le_sum (f := fun i => finrank K (borelWeightSpace (F.layer i) μ))
    (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hi)

/-- **Characters are additive along a filtration.** -/
theorem borelCharacter_eq_sum (h : IsRationalBorelRep ρ) :
    borelCharacter ρ = ∑ i ∈ Finset.range F.length, borelCharacter (F.layer i) := by
  have := h.finiteDimensional
  refine TorusLaurent.ext fun μ => ?_
  rw [coeff_borelCharacter, F.finrank_borelWeightSpace_eq_sum h μ, AddMonoidAlgebra.coeff_sum,
    Finset.sum_apply', Nat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coeff_borelCharacter]

end RepFiltration

end Borel

end

end GLRep
