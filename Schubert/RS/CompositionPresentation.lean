import Schubert.RS.FlagPresentationRelations

/-! The canonical surjection from the Joseph-Polo presentation to the
composition flag module, together with its enveloping-algebra linearity and
torus equivariance. The presentation property is equivalent to injectivity. -/

namespace Schubert.RS.Representation
noncomputable section

def compositionPresentationMap {n : ℕ} (u : Composition n) :
    PresentationQuotient u →ₗ[Enveloping n] compositionFlag u :=
  (jpLeftIdeal u).liftQ (flagCyclicModuleMap (compositionShape u) (compositionPermutation u)) (by
    simpa only [composition_extremalWeight] using
      jpLeftIdeal_le_flagCyclic_ker (compositionShape u) (compositionPermutation u))

theorem compositionPresentationMap_mk {n : ℕ} (u : Composition n) (a : Enveloping n) :
    compositionPresentationMap u (Submodule.Quotient.mk a) =
      flagCyclicModuleMap (compositionShape u) (compositionPermutation u) a := rfl

theorem compositionPresentationMap_generator {n : ℕ} (u : Composition n) :
    compositionPresentationMap u (presentationGenerator u) = compositionFlagGenerator u := by
  apply Subtype.ext
  change polynomialEnveloping n 1 _ = _
  rw [map_one]
  rfl

theorem compositionPresentationMap_surjective {n : ℕ} (u : Composition n) :
    Function.Surjective (compositionPresentationMap u) := by
  intro p
  obtain ⟨a,ha⟩ := flagCyclicMap_surjective (compositionShape u) (compositionPermutation u) p
  exact ⟨Submodule.Quotient.mk a,ha⟩

theorem compositionPresentationMap_equivariant {n : ℕ} (u : Composition n)
    (t : DiagonalTorus n) (q : PresentationQuotient u) :
    compositionPresentationMap u (jpTorusRepresentation u t q) =
      compositionFlagTorus u t (compositionPresentationMap u q) := by
  obtain ⟨a,rfl⟩ := Submodule.Quotient.mk_surjective (jpLeftIdeal u) q
  change compositionPresentationMap u
    (weightScalar u t • quotientScale (jpLeftIdeal u) _ t (Submodule.Quotient.mk a)) = _
  rw [quotientScale_mk]
  rw [show compositionPresentationMap u
      (weightScalar u t • (Submodule.Quotient.mk (torusEnveloping t a) : PresentationQuotient u)) =
      weightScalar u t • compositionPresentationMap u (Submodule.Quotient.mk (torusEnveloping t a))
    from ((compositionPresentationMap u).restrictScalars ℂ).map_smul _ _]
  apply Subtype.ext
  change weightScalar u t • polynomialEnveloping n (torusEnveloping t a)
      (extremalFlag (compositionShape u) (compositionPermutation u)) =
    polynomialTorus n t (polynomialEnveloping n a
      (extremalFlag (compositionShape u) (compositionPermutation u)))
  rw [polynomialEnveloping_torus,extremalFlag_weight,composition_extremalWeight,
    integerWeightScalar_nat,map_smul]

/-- The Joseph-Polo presentation property is equivalent to injectivity of
the canonical surjection. Neither side assumes a character formula. -/
theorem compositionFlagJosephPolo_iff_injective {n : ℕ} (u : Composition n) :
    CompositionFlagJosephPolo u ↔ Function.Injective (compositionPresentationMap u) := by
  constructor
  · rintro ⟨e,hgen,heq⟩
    have hn : ∀ q, e q = compositionPresentationMap u q := by
      intro q
      obtain ⟨a,rfl⟩ := presentation_is_cyclic u q
      rw [map_smul,map_smul,hgen,compositionPresentationMap_generator]
    intro x y hxy
    apply e.injective
    rw [hn,hn,hxy]
  · intro hi
    let e := LinearEquiv.ofBijective (compositionPresentationMap u)
      ⟨hi,compositionPresentationMap_surjective u⟩
    exact ⟨e,compositionPresentationMap_generator u,compositionPresentationMap_equivariant u⟩

end
end Schubert.RS.Representation
