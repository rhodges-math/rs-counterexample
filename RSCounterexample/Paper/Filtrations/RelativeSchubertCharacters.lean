import RSCounterexample.Paper.Filtrations.SectionModules
import RSCounterexample.Paper.SchubertUnions.AtomCharacter
import RSCounterexample.Paper.KeyInitialCoefficient

/-!
# Characters of minimal relative Schubert modules

For `ν ∈ ℤⁿ`, write `k = weightShift ν` and `u = weightComplement ν = k·(1,…,1) − ν`. The
restriction `P(ν) → H⁰(∂X_σ, 𝓛(η))` is surjective, its kernel is `Q(ν)`, and the characters of
source and target are `x^{-k·1} κ_u` and `x^{-k·1} (κ_u − 𝒜_u)`. Hence

  `ch Q(ν) = x^{-k·1} 𝒜_u`,  and in particular `ch Q(−u) = 𝒜_u`,

the second identity of (1.7) (`minRelSchubert_hasCharacter`). The weight `ν` occurs in `Q(ν)`
[van der Kallen, Remark 2.3.5] (`minRelSchubert_weightSpace_ne_bot`).

As by-products, every Demazure atom has nonnegative coefficients and contains its own monomial
with coefficient one (`atom_coeff_nonneg`, `atom_coeff_self`).
-/

namespace Schubert.RS

namespace BModules.BModule

open Representation

variable {n : ℕ}

/-- A surjective homomorphism induces an isomorphism from the quotient by its kernel. -/
noncomputable def Hom.quotKerIso {M N : BModule n} (f : M.Hom N) (hf : Function.Surjective f.toLinearMap) :
    f.ker.quotient ≃ᴮ N where
  toLinearEquiv := f.toLinearMap.quotKerEquivOfSurjective hf
  map_nil X v := by
    induction v using Submodule.Quotient.induction_on with
    | H v =>
      change f.toLinearMap.quotKerEquivOfSurjective hf (Submodule.Quotient.mk (M.nil X v)) = _
      rw [LinearMap.quotKerEquivOfSurjective_apply_mk]
      change f.toLinearMap (M.nil X v) = N.nil X (f.toLinearMap.quotKerEquivOfSurjective hf
        (Submodule.Quotient.mk v))
      rw [LinearMap.quotKerEquivOfSurjective_apply_mk, f.map_nil]
  map_torus t v := by
    induction v using Submodule.Quotient.induction_on with
    | H v =>
      change f.toLinearMap.quotKerEquivOfSurjective hf (Submodule.Quotient.mk (M.torus t v)) = _
      rw [LinearMap.quotKerEquivOfSurjective_apply_mk]
      change f.toLinearMap (M.torus t v) = N.torus t (f.toLinearMap.quotKerEquivOfSurjective hf
        (Submodule.Quotient.mk v))
      rw [LinearMap.quotKerEquivOfSurjective_apply_mk, f.map_torus]

/-- Weight multiplicities along a surjective homomorphism. -/
theorem Hom.finrank_weightSpace_of_surjective {M N : BModule n} (f : M.Hom N)
    (hf : Function.Surjective f.toLinearMap) (μ : Weight n) :
    Module.finrank ℂ (M.weightSpace μ) =
      Module.finrank ℂ (f.ker.toBModule.weightSpace μ) + Module.finrank ℂ (N.weightSpace μ) := by
  rw [f.ker.finrank_weightSpace_eq_add μ, (f.quotKerIso hf).finrank_weightSpace μ]

/-- The kernel of a surjective homomorphism has the difference of the characters. -/
theorem Hom.hasCharacter_ker {M N : BModule n} (f : M.Hom N)
    (hf : Function.Surjective f.toLinearMap) {g h : Laurent n} (hM : M.HasCharacter g)
    (hN : N.HasCharacter h) : f.ker.toBModule.HasCharacter (g - h) := by
  intro μ
  have := f.finrank_weightSpace_of_surjective hf μ
  rw [AddMonoidAlgebra.coeff_sub]
  change _ = (g.coeff - h.coeff) (-μ)
  rw [Finsupp.sub_apply, ← hM μ, ← hN μ, this]
  push_cast
  ring

end BModules.BModule

namespace Filtrations

open Representation BModules FinPermutation SchubertUnions

noncomputable section

variable {n : ℕ}

theorem isMinCosetRep_compositionPermutation (u : Composition n) :
    IsMinCosetRep (shapeWeight (compositionShape u)) (compositionPermutation u) := by
  rw [compositionShape_weight]
  exact fun i j hij he => compositionPermutation_ties u i j hij he

/-- The character of `D_{∂σ}` for `σ = compositionPermutation u`: `κ_u − 𝒜_u`. -/
theorem boundary_hasTorusCharacter (u : Composition n) :
    HasTorusCharacter
      (demazureUnionModule (compositionShape u) (schubertBoundary (compositionPermutation u))).torus
      (key u - atom u) := by
  obtain ⟨d, h, hm⟩ := exists_columnMultiplicity (compositionShape u)
  have hW := isMinCosetRep_compositionPermutation u
  rw [← hm] at hW
  have hc := demazureUnion_boundary_hasTorusCharacter h hW
  rw [hm, composition_extremalWeight] at hc
  exact hc

/-- The extremal weight `u` does not occur in `D_{∂σ}`, `σ = compositionPermutation u`. -/
theorem boundary_inf_extremal (u : Composition n) :
    demazureUnion (compositionShape u) (schubertBoundary (compositionPermutation u)) ⊓
      SchubertUnions.ambientWeight (fun i => (u i : ℤ)) = ⊥ := by
  obtain ⟨d, h, hm⟩ := exists_columnMultiplicity (compositionShape u)
  have hW := isMinCosetRep_compositionPermutation u
  rw [← hm] at hW
  have hc := demazureUnion_boundary_inf_extremal h hW
  rw [hm, composition_extremalWeight] at hc
  exact hc

/-- Every Demazure atom contains its own monomial with coefficient one. -/
theorem atom_coeff_self (u : Composition n) :
    (toLaurent (atom u)).coeff (fun i => (u i : ℤ)) = 1 := by
  have hkey := key_initial_coefficient u (compositionFlagTorus u) (compositionFlagGenerator u)
    (compositionFlagJosephPolo u) (compositionFlagDemazureCharacter u) (orderedPBWBasis_exists n)
  have hb := boundary_hasTorusCharacter u (fun i => (u i : ℤ))
  have hzero : torusWeightSpace
      (demazureUnionModule (compositionShape u) (schubertBoundary (compositionPermutation u))).torus
        (fun i => (u i : ℤ)) = ⊥ := by
    change torusWeightSpace (restrictTorus (polynomialTorus n) _ _) _ = ⊥
    rw [torusWeightSpace_restrictTorus]
    rw [Submodule.eq_bot_iff]
    intro x hx
    have hmem : (x : MatrixPolynomial n) ∈ demazureUnion (compositionShape u)
        (schubertBoundary (compositionPermutation u)) ⊓
          SchubertUnions.ambientWeight (fun i => (u i : ℤ)) := ⟨x.2, hx⟩
    rw [boundary_inf_extremal u] at hmem
    exact Subtype.ext ((Submodule.mem_bot ℂ).mp hmem)
  rw [hzero, finrank_bot, map_sub, AddMonoidAlgebra.coeff_sub] at hb
  change (0 : ℤ) = ((toLaurent (key u)).coeff - (toLaurent (atom u)).coeff) _ at hb
  rw [Finsupp.sub_apply, hkey] at hb
  omega

/-- Every Demazure atom has nonnegative coefficients. -/
theorem atom_coeff_nonneg (u : Composition n) (w : Weight n) : 0 ≤ (toLaurent (atom u)).coeff w := by
  obtain ⟨d, h, hm⟩ := exists_columnMultiplicity (compositionShape u)
  have hW := isMinCosetRep_compositionPermutation u
  rw [← hm] at hW
  have he := exactCharacter_eq h (compositionPermutation u)
  rw [ite_eq_left hW, hm, composition_extremalWeight] at he
  rw [← he, exactCharacter, map_sum, AddMonoidAlgebra.coeff_sum, Finset.sum_apply']
  refine Finset.sum_nonneg fun T _ => ?_
  rw [coeff_compositionMonomial_tuple]
  split_ifs <;> norm_num

/-! ### Characters of `P(ν)` and `Q(ν)` -/

theorem restrictToBoundary_surjective (ν : Weight n) :
    Function.Surjective (restrictToBoundary ν).toLinearMap :=
  LinearMap.dualMap_surjective_of_injective
    (Submodule.inclusion_injective (demazureUnion_boundary_le _ _))

/-- `ch P(ν) = x^{-k·1} κ_u`. -/
theorem dualJoseph_hasCharacter_general (ν : Weight n) :
    (dualJoseph ν).HasCharacter (AddMonoidAlgebra.single (-BModule.constWeight (weightShift ν : ℤ)) 1 *
      toLaurent (key (weightComplement ν))) := by
  have hp := demazureUnionModule_singleton_hasTorusCharacter (compositionShape (weightComplement ν))
    (compositionPermutation (weightComplement ν))
    (compositionFlagJP_and_character (weightComplement ν)).2
  exact sectionModuleOf_hasCharacter _ _ _ hp

/-- `ch Q(ν) = x^{-k·1} 𝒜_u`, with `k = weightShift ν` and `u = k·(1,…,1) − ν`. -/
theorem minRelSchubert_hasCharacter_general (ν : Weight n) :
    (minRelSchubert ν).HasCharacter (AddMonoidAlgebra.single (-BModule.constWeight (weightShift ν : ℤ)) 1 *
      toLaurent (atom (weightComplement ν))) := by
  have hN := sectionModuleOf_hasCharacter (weightShift ν)
    (dominantComposition (weightComplement ν)) (schubertBoundary (schubertIndex ν))
    (boundary_hasTorusCharacter (weightComplement ν))
  have h := (restrictToBoundary ν).hasCharacter_ker (restrictToBoundary_surjective ν)
    (dualJoseph_hasCharacter_general ν) hN
  rw [← mul_sub, ← map_sub, sub_sub_cancel] at h
  exact h

/-- The second identity of (1.7): `ch Q(−u) = 𝒜_u`. -/
theorem minRelSchubert_hasCharacter (u : Composition n) :
    (minRelSchubert (negComposition u)).HasCharacter (toLaurent (atom u)) := by
  have h := minRelSchubert_hasCharacter_general (negComposition u)
  rwa [weightShift_negComposition, weightComplement_negComposition, Nat.cast_zero,
    constWeight_zero, neg_zero, ← AddMonoidAlgebra.one_def, one_mul] at h

/-- `Q(ν)` contains the weight `ν` [van der Kallen, Remark 2.3.5]. -/
theorem minRelSchubert_weightSpace_ne_bot (ν : Weight n) :
    (minRelSchubert ν).weightSpace ν ≠ ⊥ := by
  intro h0
  have h := minRelSchubert_hasCharacter_general ν ν
  rw [h0, finrank_bot] at h
  have hw : -ν = -BModule.constWeight (weightShift ν : ℤ) + fun i => (weightComplement ν i : ℤ) := by
    funext i
    simp only [Pi.add_apply, Pi.neg_apply, BModule.constWeight, weightComplement_cast]
    ring
  rw [hw, laurent_coefficient_shift, atom_coeff_self] at h
  exact absurd h (by norm_num)

/-! ### The recurrences quoted in the proof of Corollary 1.2 -/

/-- `ch P(−sᵢu) = πᵢ ch P(−u)` for `uᵢ > u_{i+1}` (the Demazure recurrence). -/
theorem dualJoseph_character_step (u : Composition n) (i : AdjacentPosition n)
    (h : u i.right < u i.left) :
    (dualJoseph (negComposition (swapComposition u i))).HasCharacter
      (toLaurent (isobaric i (key u))) := by
  rw [isobaric_key, ite_eq_left h]
  exact dualJoseph_hasCharacter _

/-- `ch Q(−sᵢu) = π̄ᵢ ch Q(−u)` for `uᵢ > u_{i+1}` [van der Kallen, Lemma 7.2.3]. -/
theorem minRelSchubert_character_step (u : Composition n) (i : AdjacentPosition n)
    (h : u i.right < u i.left) :
    (minRelSchubert (negComposition (swapComposition u i))).HasCharacter
      (toLaurent (atomOperator i (atom u))) := by
  have hb : (swapComposition u i) i.left < (swapComposition u i) i.right := by simpa using h
  have hs := atom_any_ascent (swapComposition u i) i hb
  rw [swapComposition_involutive] at hs
  rw [← hs]
  exact minRelSchubert_hasCharacter _

/-- The point case (lines 1531–1533): for weakly decreasing `λ`, `ch P(−λ) = ch Q(−λ) = x^λ`. -/
theorem dualJoseph_minRelSchubert_antitone (u : Composition n) (hu : Antitone u) :
    (dualJoseph (negComposition u)).HasCharacter (toLaurent (compositionMonomial u)) ∧
      (minRelSchubert (negComposition u)).HasCharacter (toLaurent (compositionMonomial u)) := by
  constructor
  · rw [← key_of_antitone u hu]; exact dualJoseph_hasCharacter u
  · rw [← atom_of_antitone u hu]; exact minRelSchubert_hasCharacter u

end

end Filtrations

end Schubert.RS
