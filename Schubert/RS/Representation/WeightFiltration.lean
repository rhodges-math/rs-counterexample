import Schubert.RS.Representation.FullWeightSpaces
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions

namespace Schubert.RS.Representation
noncomputable section
open scoped BigOperators

/-- A finite torus-stable filtration with labelled factor bases and exact
coefficient maps on each weight space. Surjectivity and kernel identities
are included in the structure. -/
structure WeightBasisFiltration {n : ℕ} {E : Type*} [AddCommGroup E] [Module ℂ E]
    (ρ : DiagonalTorus n →* Module.End ℂ E) (L : ℕ)
    (I : Fin L → Type*) [∀ k, Fintype (I k)] (label : ∀ k, I k → Weight n) where
  stage : ℕ → Submodule ℂ E
  start : stage 0 = ⊥
  finish : stage L = ⊤
  increasing : ∀ k, stage k ≤ stage (k+1)
  stable : ∀ k t x, x ∈ stage k → ρ t x ∈ stage k
  factor : ∀ (k : Fin L) (w : Weight n),
    ↥(stage (k.val+1) ⊓ torusWeightSpace ρ w) →ₗ[ℂ]
      ({j : I k // label k j = w} → ℂ)
  onto : ∀ k w, Function.Surjective (factor k w)
  kernel : ∀ k w, LinearMap.ker (factor k w) =
    LinearMap.range (Submodule.inclusion
      (show stage k.val ⊓ torusWeightSpace ρ w ≤
        stage (k.val+1) ⊓ torusWeightSpace ρ w from inf_le_inf_right _ (increasing k.val)))

theorem WeightBasisFiltration.finrank {n : ℕ} {E : Type*}
    [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    {ρ : DiagonalTorus n →* Module.End ℂ E} {L : ℕ}
    {I : Fin L → Type*} [∀ k, Fintype (I k)] {label : ∀ k, I k → Weight n}
    (F : WeightBasisFiltration ρ L I label) (w : Weight n) :
    Module.finrank ℂ (torusWeightSpace ρ w) =
      ∑ k, Fintype.card {j : I k // label k j = w} := by
  classical
  have hstep (k : Fin L) :
      Module.finrank ℂ ↥(F.stage (k.val+1) ⊓ torusWeightSpace ρ w) =
      Module.finrank ℂ ↥(F.stage k.val ⊓ torusWeightSpace ρ w) +
        Fintype.card {j : I k // label k j = w} := by
    have h := (F.factor k w).finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr (F.onto k w), finrank_top,
      F.kernel k w, LinearMap.finrank_range_of_inj (Submodule.inclusion_injective _)] at h
    simpa [Module.finrank_pi, add_comm] using h.symm

  have hs : (∑ k : Fin L,
      ((Module.finrank ℂ ↥(F.stage (k.val+1) ⊓ torusWeightSpace ρ w) : ℤ) -
      Module.finrank ℂ ↥(F.stage k.val ⊓ torusWeightSpace ρ w))) =
      (Module.finrank ℂ (torusWeightSpace ρ w) : ℤ) := by
    rw [Fin.sum_univ_eq_sum_range (fun k : ℕ =>
      (Module.finrank ℂ ↥(F.stage (k+1) ⊓ torusWeightSpace ρ w) : ℤ) -
      Module.finrank ℂ ↥(F.stage k ⊓ torusWeightSpace ρ w)), Finset.sum_range_sub (fun k : ℕ =>
      (Module.finrank ℂ ↥(F.stage k ⊓ torusWeightSpace ρ w) : ℤ))]
    rw [F.start, F.finish, top_inf_eq, bot_inf_eq, finrank_bot]
    simp
  have hc : (∑ k : Fin L, (Fintype.card {j : I k // label k j = w} : ℤ)) =
      (Module.finrank ℂ (torusWeightSpace ρ w) : ℤ) := by
    rw [← hs]
    apply Finset.sum_congr rfl
    intro k _
    have hk := hstep k
    have hk' : (Module.finrank ℂ ↥(F.stage (k.val+1) ⊓ torusWeightSpace ρ w) : ℤ) =
      Module.finrank ℂ ↥(F.stage k.val ⊓ torusWeightSpace ρ w) +
        (Fintype.card {j : I k // label k j = w} : ℤ) := by exact_mod_cast hk
    omega
  exact_mod_cast hc.symm

end
end Schubert.RS.Representation





