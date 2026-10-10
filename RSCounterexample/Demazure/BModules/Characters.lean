import RSCounterexample.Demazure.BModules.Basic
import RSCounterexample.Demazure.TorusEigenbasisCharacter

/-!
# Characters of `B`-modules

We record a weight `μ` by the Laurent monomial `x^{-μ}`:
`ch M = Σ_μ (dim M_μ) x^{-μ}`. The predicate `M.HasCharacter f` states that the Laurent
polynomial `f` has these coefficients.

Characters are unique, invariant under isomorphism, additive along `B`-submodules, and
computed by any basis of weight vectors.
-/

open Schubert

namespace Demazure.BModules

open FlagModule

noncomputable section

variable {n : ℕ}

/-- The Laurent polynomial `Σᵢ x^{-wt i}`, the character of a module with a weight basis of
weights `wt`. -/
def labelledLaurent {ι : Type*} [Fintype ι] (wt : ι → Weight n) : Laurent n :=
  ∑ i, AddMonoidAlgebra.single (-wt i) 1

theorem labelledLaurent_coeff {ι : Type*} [Fintype ι] (wt : ι → Weight n) (μ : Weight n) :
    (labelledLaurent wt).coeff (-μ) = (Fintype.card {i // wt i = μ} : ℤ) := by
  classical
  simp [labelledLaurent, AddMonoidAlgebra.coeff_sum, AddMonoidAlgebra.coeff_single,
    Finsupp.single_apply, Fintype.card_subtype]

theorem labelledLaurent_prod {ι κ : Type*} [Fintype ι] [Fintype κ] (wt : ι → Weight n)
    (wt' : κ → Weight n) :
    labelledLaurent (fun x : ι × κ => wt x.1 + wt' x.2) = labelledLaurent wt *
        labelledLaurent wt' := by
  simp only [labelledLaurent, Finset.sum_mul_sum, AddMonoidAlgebra.single_mul_single, mul_one,
    neg_add, Fintype.sum_prod_type]

/-- Two Laurent polynomials with the same coefficients are equal. -/
theorem laurent_ext {f g : Laurent n} (h : ∀ w, f.coeff w = g.coeff w) : f = g := by
  cases f; cases g
  congr 1
  exact Finsupp.ext h

namespace BModule

/-- `f` is the character of `M` in the convention `ch M = Σ_μ (dim M_μ) x^{-μ}`. -/
def HasCharacter (M : BModule n) (f : Laurent n) : Prop :=
  ∀ μ : Weight n, (Module.finrank ℂ (M.weightSpace μ) : ℤ) = f.coeff (-μ)

theorem HasCharacter.unique {M : BModule n} {f g : Laurent n} (hf : M.HasCharacter f)
    (hg : M.HasCharacter g) : f = g :=
  laurent_ext fun w => by simpa using (hf (-w)).symm.trans (hg (-w))

theorem HasCharacter.of_iso {M N : BModule n} {f : Laurent n} (hM : M.HasCharacter f)
    (e : M ≃ᴮ N) : N.HasCharacter f := fun μ => by rw [← e.finrank_weightSpace μ]; exact hM μ

theorem HasCharacter.coeff_nonneg {M : BModule n} {f : Laurent n} (hM : M.HasCharacter f)
    (w : Weight n) : 0 ≤ f.coeff w := by
  have := hM (-w)
  rw [neg_neg] at this
  rw [← this]
  exact Int.natCast_nonneg _

theorem HasCharacter.weightSpace_ne_bot {M : BModule n} {f : Laurent n} (hM : M.HasCharacter f)
    {μ : Weight n} (hμ : M.weightSpace μ ≠ ⊥) : f.coeff (-μ) ≠ 0 := by
  rw [← hM μ]
  exact_mod_cast (Submodule.finrank_eq_zero.not.mpr hμ)

/-- A weight basis computes the character. -/
theorem hasCharacter_of_basis (M : BModule n) {ι : Type*} [Fintype ι] (b : Module.Basis ι ℂ M)
    (wt : ι → Weight n) (hb : ∀ t i, M.torus t (b i) = integerWeightScalar (wt i) t • b i) :
    M.HasCharacter (labelledLaurent wt) := by
  intro μ
  rw [labelledLaurent_coeff]
  exact_mod_cast torusWeightSpace_finrank_of_eigenbasis M.torus b wt hb μ

/-- Every `B`-module has a basis of weight vectors. -/
theorem exists_weightBasis (M : BModule n) :
    ∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℂ M) (wt : ι → Weight n),
      ∀ t i, M.torus t (b i) = integerWeightScalar (wt i) t • b i := by
  classical
  let W := M.weightSpace
  have hind : iSupIndep W := torusWeightSpace_iSupIndep M.torus
  let _ := hind.fintypeNeBotOfFiniteDimensional
  let V : {μ // W μ ≠ ⊥} → Submodule ℂ M := fun μ => W μ.1
  have hV : DirectSum.IsInternal V := by
    rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
    refine ⟨hind.comp Subtype.val_injective, ?_⟩
    change ⨆ μ : {μ // W μ ≠ ⊥}, W μ.1 = ⊤
    rw [iSup_ne_bot_subtype W]
    exact M.weightDiagonal
  let b := hV.collectedBasis fun μ => Module.finBasis ℂ (V μ)
  refine ⟨Σ μ : {μ // W μ ≠ ⊥}, Fin (Module.finrank ℂ (V μ)), inferInstance, b,
    fun x => x.1.1, fun t x => ?_⟩
  exact hV.collectedBasis_mem _ x t

/-- Every `B`-module has a character. -/
theorem exists_hasCharacter (M : BModule n) : ∃ f, M.HasCharacter f := by
  obtain ⟨ι, _, b, wt, hb⟩ := M.exists_weightBasis
  exact ⟨_, M.hasCharacter_of_basis b wt hb⟩

end BModule

namespace BSubmodule

variable {M : BModule n}

/-- Additivity of characters along a `B`-submodule. -/
theorem hasCharacter_of_quotient (S : BSubmodule M) {f g : Laurent n}
    (hf : S.toBModule.HasCharacter f) (hg : S.quotient.HasCharacter g) :
    M.HasCharacter (f + g) := by
  intro μ
  rw [S.finrank_weightSpace_eq_add μ, AddMonoidAlgebra.coeff_add, Nat.cast_add, hf μ, hg μ]
  rfl

end BSubmodule

end

end Demazure.BModules
