import Schubert.RS.BModules.Constructions

/-!
# Finite filtrations of `B`-modules

A filtration of a `B`-module `M` is a finite chain `0 = F₀ ≤ F₁ ≤ ⋯ ≤ F_r = M` of
`B`-submodules. Its layers are the successive quotients `F_{i+1} / F_i`.
`HasFiltrationBy 𝒞 M` states that `M` has a filtration all of whose layers satisfy `𝒞`.

Weight multiplicities, hence characters, are additive along filtrations.
-/

namespace Schubert.RS.BModules

open Representation

noncomputable section

variable {n : ℕ}

/-- A finite filtration `0 = F₀ ≤ F₁ ≤ ⋯ ≤ F_r = M` by `B`-submodules. The steps are indexed
by `ℕ`; only `F₀, …, F_r` matter, and `F_i = M` for `i ≥ r` by monotonicity. -/
structure BFiltration (M : BModule n) where
  /-- The number `r` of layers. -/
  length : ℕ
  /-- The steps of the filtration. -/
  step : ℕ → BSubmodule M
  monotone : Monotone step
  step_zero : step 0 = ⊥
  step_length : step length = ⊤

theorem BSubmodule.within_bot {M : BModule n} (S' : BSubmodule M) :
    ((⊥ : BSubmodule M).within S').toSubmodule = ⊥ := by
  ext x
  simp only [BSubmodule.within, BSubmodule.bot_toSubmodule, Submodule.mem_bot]
  exact ⟨fun h => Subtype.ext h, fun h => by rw [h]; rfl⟩

namespace BFiltration

variable {M : BModule n} (F : BFiltration M)

/-- The `i`-th successive quotient `F_{i+1} / F_i`. -/
def layer (i : ℕ) : BModule n := BSubmodule.subquotient (F.step i) (F.step (i + 1))

theorem finrank_step_weightSpace (μ : Weight n) (k : ℕ) :
    Module.finrank ℂ ((F.step k).toBModule.weightSpace μ) =
      ∑ i ∈ Finset.range k, Module.finrank ℂ ((F.layer i).weightSpace μ) := by
  induction k with
  | zero =>
    rw [BSubmodule.finrank_toBModule_weightSpace, F.step_zero]
    simp
  | succ k ih =>
    rw [BSubmodule.finrank_weightSpace_subquotient (F.monotone (Nat.le_succ k)) μ, ih,
      Finset.sum_range_succ]
    rfl

/-- Weight multiplicities are additive along a filtration. -/
theorem finrank_weightSpace_eq_sum (μ : Weight n) :
    Module.finrank ℂ (M.weightSpace μ) =
      ∑ i ∈ Finset.range F.length, Module.finrank ℂ ((F.layer i).weightSpace μ) := by
  rw [← F.finrank_step_weightSpace μ F.length, BSubmodule.finrank_toBModule_weightSpace,
    F.step_length, BSubmodule.top_toSubmodule, top_inf_eq]

/-- A weight of a layer is a weight of the filtered module. -/
theorem finrank_layer_weightSpace_le (μ : Weight n) {i : ℕ} (hi : i < F.length) :
    Module.finrank ℂ ((F.layer i).weightSpace μ) ≤ Module.finrank ℂ (M.weightSpace μ) := by
  rw [F.finrank_weightSpace_eq_sum μ]
  exact Finset.single_le_sum (f := fun i => Module.finrank ℂ ((F.layer i).weightSpace μ))
    (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hi)

/-- Characters are additive along a filtration. -/
theorem hasCharacter_sum (f : ℕ → Laurent n)
    (hf : ∀ i < F.length, (F.layer i).HasCharacter (f i)) :
    M.HasCharacter (∑ i ∈ Finset.range F.length, f i) := by
  intro μ
  rw [F.finrank_weightSpace_eq_sum μ, Nat.cast_sum, AddMonoidAlgebra.coeff_sum]
  rw [Finset.sum_apply']
  exact Finset.sum_congr rfl fun i hi => hf i (Finset.mem_range.mp hi) μ

/-- The one-step filtration `0 ≤ M`. -/
def single (M : BModule n) : BFiltration M where
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

/-- The only layer of the one-step filtration is `M` itself. -/
def singleLayerIso (M : BModule n) : (single M).layer 0 ≃ᴮ M where
  toLinearEquiv :=
    (Submodule.quotEquivOfEqBot _ (BSubmodule.within_bot (⊤ : BSubmodule M))).trans
      (LinearEquiv.ofTop (⊤ : BSubmodule M).toSubmodule rfl)
  map_nil X v := by
    induction v using Submodule.Quotient.induction_on with
    | H v => rfl
  map_torus t v := by
    induction v using Submodule.Quotient.induction_on with
    | H v => rfl

end BFiltration

/-- `M` has a finite filtration by `B`-submodules whose successive quotients satisfy `𝒞`. -/
def HasFiltrationBy (𝒞 : BModule n → Prop) (M : BModule n) : Prop :=
  ∃ F : BFiltration M, ∀ i < F.length, 𝒞 (F.layer i)

/-- A module isomorphic to a member of `𝒞` has the one-step filtration. -/
theorem hasFiltrationBy_single {𝒞 : BModule n → Prop} {M : BModule n}
    (h : ∀ L : BModule n, Nonempty (L ≃ᴮ M) → 𝒞 L) : HasFiltrationBy 𝒞 M :=
  ⟨BFiltration.single M, fun i hi => by
    have hi0 : i = 0 := by simpa [BFiltration.single] using hi
    subst hi0
    exact h _ ⟨BFiltration.singleLayerIso M⟩⟩

end

end Schubert.RS.BModules
