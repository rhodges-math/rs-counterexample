import Schubert.RS.Representation.HighestAnnihilation
import Schubert.RS.Representation.CyclicGeneration
import Schubert.RS.Representation.CompositionFlag
import Schubert.RS.Representation.DominantCharacter

namespace Schubert.RS.Representation
noncomputable section

/-- The concrete highest vector generates just its line under the positive
nilpotent Lie algebra. This uses algebra generation of the UEA, not PBW. -/
theorem upperCyclic_highestFlag {n : ℕ} (m : ColumnShape n) :
    upperCyclic (highestFlag m) = Submodule.span ℂ {highestFlag m} := by
  apply le_antisymm
  · apply upperCyclic_le_of_root_stable _ _ (Submodule.mem_span_singleton_self _)
    intro r q hq
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hq
    have hz : matrixUnitDerivation r.val.1 r.val.2 (highestFlag m) = 0 :=
      rootDerivation_highestFlag r m
    rw [Derivation.map_smul, hz, smul_zero]
    exact Submodule.zero_mem _
  · exact Submodule.span_le.mpr (by
      intro q hq
      rcases Set.mem_singleton_iff.mp hq with rfl
      exact upperCyclic_seed _)

theorem extremalFlag_refl {n : ℕ} (m : ColumnShape n) :
    extremalFlag m (Equiv.refl _) = highestFlag m := by
  change MvPolynomial.rename id (highestFlag m) = highestFlag m
  simp

/-- Every vector in a dominant composition flag module is a multiple of
its flag generator. -/
theorem compositionFlag_dominant_cyclic_line {n : ℕ} (u : Composition n)
    (hu : Antitone u) (p : compositionFlag u) :
    ∃ c : ℂ, c • compositionFlagGenerator u = p := by
  have he : (compositionFlag u : Submodule ℂ (MatrixPolynomial n)) =
      Submodule.span ℂ {(compositionFlagGenerator u).val} := by
    change upperCyclic (extremalFlag (compositionShape u) (compositionPermutation u)) =
      Submodule.span ℂ {extremalFlag (compositionShape u) (compositionPermutation u)}
    rw [compositionPermutation_of_antitone u hu, extremalFlag_refl, upperCyclic_highestFlag]
  have hp : p.val ∈ Submodule.span ℂ {(compositionFlagGenerator u).val} := by
    rw [← he]
    exact p.property
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hp
  exact ⟨c, Subtype.ext hc⟩

theorem compositionFlag_dominant_finrank {n : ℕ} (u : Composition n) (hu : Antitone u) :
    Module.finrank ℂ (compositionFlag u) = 1 :=
  finrank_eq_one (compositionFlagGenerator u) (compositionFlagGenerator_ne_zero u)
    (compositionFlag_dominant_cyclic_line u hu)

theorem compositionFlag_dominant_torus_scalar {n : ℕ} (u : Composition n)
    (hu : Antitone u) (t : DiagonalTorus n) (p : compositionFlag u) :
    compositionFlagTorus u t p = integerWeightScalar (fun i => (u i : ℤ)) t • p := by
  obtain ⟨c, rfl⟩ := compositionFlag_dominant_cyclic_line u hu p
  rw [map_smul, compositionFlagGenerator_weight, smul_comm]

theorem compositionFlag_dominant_weight_finrank {n : ℕ} (u : Composition n)
    (hu : Antitone u) (z : Weight n) :
    Module.finrank ℂ (torusWeightSpace (compositionFlagTorus u) z) =
      if z = (fun i => (u i : ℤ)) then 1 else 0 := by
  classical
  split_ifs with hz
  · subst z
    rw [scalar_torusWeightSpace_eq_top _ _ (compositionFlag_dominant_torus_scalar u hu)]
    simpa using compositionFlag_dominant_finrank u hu
  · rw [scalar_torusWeightSpace_eq_bot _ _ _ hz
      (compositionFlag_dominant_torus_scalar u hu)]
    simp

/-- The Demazure character formula for dominant composition flag modules,
including rank zero and repeated entries. -/
theorem compositionFlagDemazureCharacter_of_antitone {n : ℕ} (u : Composition n)
    (hu : Antitone u) : CompositionFlagDemazureCharacter u := by
  classical
  intro z
  refine ⟨inferInstance, ?_⟩
  rw [compositionFlag_dominant_weight_finrank u hu, key_of_antitone u hu,
    compositionMonomial, toLaurent_monomial]
  have he : exponentWeight (Finsupp.equivFunOnFinite.symm u) = (fun i => (u i : ℤ)) := by
    funext i
    simp [exponentWeight]
  simp only [he, AddMonoidAlgebra.coeff_single]
  change ((if z = (fun i => (u i : ℤ)) then 1 else 0 : ℕ) : ℤ) =
    (Finsupp.single (fun i => (u i : ℤ)) (1 : ℤ)) z
  rw [Finsupp.single_apply]
  by_cases hz : z = (fun i => (u i : ℤ))
  · subst z
    norm_num
  · simp only [if_neg hz, if_neg (Ne.symm hz), Nat.cast_zero]

end
end Schubert.RS.Representation
