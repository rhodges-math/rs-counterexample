import RSCounterexample.FlagVarieties.Modules.SectionCharacter
import RSCounterexample.Demazure.Filtrations.RelativeSchubertCharacters

/-!
# Characters of the dual Joseph modules and the minimal relative Schubert modules

For an antidominant weight `η = k·1 − λ` (`k = weightShift η`, `λ = weightComplement η`), the
sections of `𝓛(η)` over a Schubert union are those of `𝓛(−λ)` with the action of `B` twisted by
`det^k` (`FlagVarieties.SectionRep.sectionRepTwist`), so their character is `x^{−k·1}` times a sum
of atoms (`FlagVarieties.SectionRep.ch_sectionRep`). For `ν ∈ ℤⁿ`, with `k = weightShift ν` and
`u = k·1 − ν ∈ ℕⁿ` (`weightComplement ν`):

* `ch P(ν) = x^{−k·1} κ_u` (`FlagVarieties.SectionRep.ch_dualJoseph`); in particular
  `ch P(−u) = κ_u` (`FlagVarieties.SectionRep.ch_dualJoseph_negWeight`), the first identity
  of (1.7);
* restriction from `X_σ` to its boundary is surjective
  (`FlagVarieties.SectionRep.boundaryRestrict_surjective`);
* `ch Q(ν) = x^{−k·1} 𝒜_u` (`FlagVarieties.SectionRep.ch_minimalRelativeSchubert`); in particular
  `ch Q(−u) = 𝒜_u` (`FlagVarieties.SectionRep.ch_minimalRelativeSchubert_negWeight`), the second
  identity of (1.7);
* `Q(ν)` contains the weight `ν` [van der Kallen, Remark 2.3.5]
  (`FlagVarieties.SectionRep.minimalRelativeSchubert_weightSpace_ne_bot`);
* the Demazure recurrences `ch P(−sᵢu) = πᵢ ch P(−u)` and `ch Q(−sᵢu) = π̄ᵢ ch Q(−u)` for
  `uᵢ > u_{i+1}` (`FlagVarieties.SectionRep.ch_dualJoseph_step`,
  `FlagVarieties.SectionRep.ch_minimalRelativeSchubert_step`).

None of these has a hypothesis: `Γ(X_w, 𝒪) = ℂ` is
`FlagVarieties.globalSectionsConstant_complex`.
-/

open Schubert GLRep TauCeti Demazure Demazure.FlagModule Demazure.SchubertUnions
  FinPermutation

namespace FlagVarieties

open PointModel.Complex

noncomputable section

variable {n : ℕ}

/-! ### The weight combinatorics agrees with Demazure's -/

theorem schubertIndex_eq_demazure (ν : Fin n → ℤ) :
    schubertIndex ν = Demazure.Filtrations.schubertIndex ν := by
  refine ((eq_schubertIndex_iff ν _).mpr ⟨fun i j hij => ?_, fun i j hij he => ?_⟩).symm
  · have := Demazure.Filtrations.fibreWeight_monotone ν hij
    rwa [Demazure.Filtrations.fibreWeight_apply, Demazure.Filtrations.fibreWeight_apply] at this
  · refine Demazure.Filtrations.schubertIndex_minimal ν i j hij ?_
    rw [Demazure.Filtrations.fibreWeight_apply, Demazure.Filtrations.fibreWeight_apply]
    exact he

theorem fibreWeight_eq_demazure (ν : Fin n → ℤ) :
    fibreWeight ν = Demazure.Filtrations.fibreWeight ν := by
  funext i
  rw [fibreWeight_apply, Demazure.Filtrations.fibreWeight_apply, schubertIndex_eq_demazure]

theorem weightComplement_eq_demazure (ν : Fin n → ℤ) :
    weightComplement ν = Demazure.Filtrations.weightComplement ν :=
  rfl

theorem weightShift_eq_demazure (ν : Fin n → ℤ) :
    weightShift ν = Demazure.Filtrations.weightShift ν :=
  rfl

theorem schubertIndex_eq_compositionPermutation (ν : Fin n → ℤ) :
    schubertIndex ν = compositionPermutation (weightComplement ν) := by
  rw [schubertIndex_eq_demazure]
  rfl

/-- `η(ν) = k·1 − λ` with `λ` the dominant rearrangement of `u = weightComplement ν`. -/
theorem fibreWeight_eq_sub (ν : Fin n → ℤ) :
    fibreWeight ν = fun i => (weightShift ν : ℤ) - dominantComposition (weightComplement ν) i := by
  rw [fibreWeight_eq_demazure]
  rfl

namespace SectionRep

/-! ### Changing the weight -/

/-- Equal weights give equivalent section modules. -/
def sectionRepEquivOfEq (S : Finset (Equiv.Perm (Fin n))) {η η' : Fin n → ℤ} (h : η = η') :
    (sectionRep S η).Equiv (sectionRep S η') := by
  subst h
  exact .refl _

/-- **Twisting by a power of the determinant**: `𝓛(η + c·1)` is `𝓛(η)` with the action of `B`
twisted by `det^c`. -/
def sectionRepTwist (S : Finset (Equiv.Perm (Fin n))) (η : Fin n → ℤ) (c : ℕ) :
    (scaledRep (sectionRep S η) (borelChar ℂ n fun _ => (c : ℤ))).Equiv
      (sectionRep S (η + fun _ => (c : ℤ))) :=
  borelSemiInvariantDetTwist _ _ _ η c

theorem ch_sectionRep_add_const (S : Finset (Equiv.Perm (Fin n))) (η : Fin n → ℤ) (c : ℕ)
    [FiniteDimensional ℂ (sectionSubrep S η).toSubmodule] :
    ch (sectionRep S (η + fun _ => (c : ℤ))) =
      AddMonoidAlgebra.single (-fun _ => (c : ℤ)) 1 * ch (sectionRep S η) := by
  rw [← ch_eq_of_equiv (sectionRepTwist S η c), ch_scaledRep]

/-- Every antidominant weight is `−λ + c·1` for a column shape of weight `λ`. -/
theorem exists_eq_neg_shapeWeightZ_add {η : Fin n → ℤ} (hη : IsAntidominant η) :
    ∃ (d : ℕ) (h : Fin d → Fin n),
      shapeWeight (columnMultiplicity h) = weightComplement η ∧
        η = -shapeWeightZ (columnMultiplicity h) + fun _ => (weightShift η : ℤ) := by
  obtain ⟨d, h, hm⟩ := exists_columnMultiplicity (columnsOfWeight (weightComplement η))
  have hw : shapeWeight (columnMultiplicity h) = weightComplement η := by
    rw [hm, shapeWeight_columnsOfWeight _ hη.antitone_weightComplement]
  refine ⟨d, h, hw, funext fun i => ?_⟩
  simp only [Pi.add_apply, Pi.neg_apply, shapeWeightZ, hw]
  rw [weightComplement_cast]
  ring

/-! ### Characters of sections for antidominant weights -/

/-- **The character of `H⁰(X_S, 𝓛(η))` for antidominant `η`**:
`x^{−k·1} ∑_{τ ∈ S ∩ W^λ} 𝒜_{τλ}`, `η = k·1 − λ`. -/
theorem ch_sectionRep
    {S : Finset (Equiv.Perm (Fin n))} (hS : BruhatLower S) {η : Fin n → ℤ}
    (hη : IsAntidominant η) :
    ch (sectionRep S η) = AddMonoidAlgebra.single (-fun _ => (weightShift η : ℤ)) 1 *
      toLaurent (∑ τ ∈ S.filter (IsMinCosetRep (weightComplement η)),
        atom (permAct τ (weightComplement η))) := by
  obtain ⟨d, h, hw, hη'⟩ := exists_eq_neg_shapeWeightZ_add hη
  have := finiteDimensional_sectionRep hS h
  rw [ch_eq_of_equiv (sectionRepEquivOfEq S hη'), ch_sectionRep_add_const,
    ch_sectionRep_neg_eq_sum_atom hS h]
  simp only [extremalWeight_eq_permAct, hw]

theorem finiteDimensional_sectionRep_of_isAntidominant {S : Finset (Equiv.Perm (Fin n))}
    (hS : BruhatLower S) {η : Fin n → ℤ} (hη : IsAntidominant η) :
    FiniteDimensional ℂ (sectionSubrep S η).toSubmodule := by
  obtain ⟨d, h, -, hη'⟩ := exists_eq_neg_shapeWeightZ_add hη
  have := finiteDimensional_sectionRep hS h
  exact Module.Finite.equiv ((sectionRepTwist S _ _).toLinearEquiv.trans
    (sectionRepEquivOfEq S hη'.symm).toLinearEquiv)

/-- **The sections over a Schubert union form a rational representation of `B`**, for
antidominant `η`. -/
theorem isRationalBorelRep_sectionRep
    {S : Finset (Equiv.Perm (Fin n))} (hS : BruhatLower S) {η : Fin n → ℤ}
    (hη : IsAntidominant η) : IsRationalBorelRep (sectionRep S η) :=
  have := finiteDimensional_sectionRep_of_isAntidominant hS hη
  isRationalBorelRep_borelSemiInvariantRep _ _ _ η

/-! ### Dual Joseph modules -/

theorem isAntidominant_fibreWeight' (ν : Fin n → ℤ) : IsAntidominant (fibreWeight ν) :=
  isAntidominant_fibreWeight ν

/-- **`ch P(ν) = x^{−k·1} κ_u`**, with `k = weightShift ν` and `u = k·1 − ν`. -/
theorem ch_dualJoseph
    (ν : Fin n → ℤ) :
    ch (dualJoseph ν) = AddMonoidAlgebra.single (-fun _ => (weightShift ν : ℤ)) 1 *
      toLaurent (key (weightComplement ν)) := by
  set u := weightComplement ν
  obtain ⟨d, h, hm⟩ := exists_columnMultiplicity (compositionShape u)
  have hη : fibreWeight ν =
      -shapeWeightZ (columnMultiplicity h) + fun _ => (weightShift ν : ℤ) := by
    rw [fibreWeight_eq_sub]
    funext i
    simp only [Pi.add_apply, Pi.neg_apply, shapeWeightZ, hm, compositionShape_weight]
    ring
  have := finiteDimensional_sectionRep (bruhatLower_lowerSet (schubertIndex ν)) h
  rw [ch_eq_of_equiv (sectionRepEquivOfEq _ hη), ch_sectionRep_add_const,
    ch_sectionRep_lowerSet _ h, hm, schubertIndex_eq_compositionPermutation,
    composition_extremalWeight]

/-- **The first identity of (1.7): `ch P(−u) = κ_u`.** -/
theorem ch_dualJoseph_negWeight
    (u : Fin n → ℕ) : ch (dualJoseph (negWeight u)) = toLaurent (key u) := by
  rw [ch_dualJoseph, weightShift_negWeight, weightComplement_negWeight]
  have : (-fun _ : Fin n => ((0 : ℕ) : ℤ)) = 0 := by
    funext i
    simp
  rw [this, ← AddMonoidAlgebra.one_def, one_mul]

/-! ### Restriction to the boundary is surjective -/

theorem boundarySet_eq_schubertBoundary (σ : Equiv.Perm (Fin n)) :
    boundarySet σ = Demazure.Filtrations.schubertBoundary σ := by
  ext τ
  rw [mem_boundarySet, Demazure.Filtrations.mem_schubertBoundary]

theorem bruhatLower_boundarySet (σ : Equiv.Perm (Fin n)) : BruhatLower (boundarySet σ) := by
  rw [boundarySet_eq_schubertBoundary]
  exact schubertBoundary_bruhatLower σ

/-- Restriction of sections of `𝓛(−λ)` to a smaller Bruhat ideal is surjective (the normality
theorem for the smaller union). -/
theorem sectionRestrict_surjective_neg
    {S S' : Finset (Equiv.Perm (Fin n))} (hSS' : S' ⊆ S) (hS' : BruhatLower S') {d : ℕ}
    (h : Fin d → Fin n) :
    Function.Surjective (sectionRestrict hSS' (-shapeWeightZ (columnMultiplicity h))) := by
  intro x
  obtain ⟨y, rfl⟩ := (sectionSpaceEquiv S' (shapeWeightZ (columnMultiplicity h))).surjective x
  obtain ⟨a, rfl⟩ :=
    minorRestriction_surjective_of_globalSectionsConstant (globalSectionsConstant_complex _) hS'
        (columnMultiplicity h) y
  exact ⟨sectionSpaceEquiv S _ (minorRestriction S (columnMultiplicity h) a), rfl⟩

/-- Restriction commutes with the twist by a power of the determinant. -/
theorem sectionRestrict_twist {S S' : Finset (Equiv.Perm (Fin n))} (hSS' : S' ⊆ S)
    (η : Fin n → ℤ) (c : ℕ) (f : (sectionSubrep S η).toSubmodule) :
    sectionRestrict hSS' (η + fun _ => (c : ℤ)) (sectionRepTwist S η c f) =
      sectionRepTwist S' η c (sectionRestrict hSS' η f) := by
  apply Subtype.ext
  change Ideal.Quotient.factorₐ ℂ (orbitIdeal_antitone hSS')
      (quotDetInv (orbitIdeal S) ^ c * (f : GLCoord ℂ n ⧸ orbitIdeal S)) =
    quotDetInv (orbitIdeal S') ^ c *
      Ideal.Quotient.factorₐ ℂ (orbitIdeal_antitone hSS') (f : GLCoord ℂ n ⧸ orbitIdeal S)
  rw [map_mul, map_pow]
  rfl

theorem sectionRestrict_surjective_add_const {S S' : Finset (Equiv.Perm (Fin n))}
    (hSS' : S' ⊆ S) {η : Fin n → ℤ} (hη : Function.Surjective (sectionRestrict hSS' η)) (c : ℕ) :
    Function.Surjective (sectionRestrict hSS' (η + fun _ => (c : ℤ))) := by
  intro y
  obtain ⟨y', rfl⟩ := (sectionRepTwist S' η c).toLinearEquiv.surjective y
  obtain ⟨x', rfl⟩ := hη y'
  exact ⟨sectionRepTwist S η c x', sectionRestrict_twist hSS' η c x'⟩

/-- **Restriction of sections between Schubert unions is surjective** for antidominant
weights. -/
theorem sectionRestrict_surjective
    {S S' : Finset (Equiv.Perm (Fin n))} (hSS' : S' ⊆ S) (hS' : BruhatLower S')
    {η : Fin n → ℤ} (hη : IsAntidominant η) :
    Function.Surjective (sectionRestrict hSS' η) := by
  obtain ⟨d, h, -, hη'⟩ := exists_eq_neg_shapeWeightZ_add hη
  rw [hη']
  exact sectionRestrict_surjective_add_const hSS'
    (sectionRestrict_surjective_neg hSS' hS' h) _

/-- **Restriction from `X_σ` to its boundary `∂X_σ` is surjective.** -/
theorem boundaryRestrict_surjective
    (ν : Fin n → ℤ) : Function.Surjective (boundaryRestrict ν) :=
  sectionRestrict_surjective _ (bruhatLower_boundarySet _) (isAntidominant_fibreWeight ν)

end SectionRep

/-! ### Characters along surjections -/

section Surjective

variable {K : Type*} [Field K] [Infinite K]
variable {W : Type*} [AddCommGroup W] [Module K W] {ρ : Representation K (borel K n) W}
variable {V : Type*} [AddCommGroup V] [Module K V] {σ : Representation K (borel K n) V}

/-- The quotient by the kernel of a surjective map of representations is the target. -/
def IntertwiningMap.quotKerEquivOfSurjective (φ : ρ.IntertwiningMap σ)
    (hφ : Function.Surjective φ) :
    φ.ker.quotient.Equiv σ :=
  .mk (φ.toLinearMap.quotKerEquivOfSurjective hφ) fun b => by
    refine LinearMap.ext fun x => ?_
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      change φ (ρ b x) = σ b (φ x)
      exact φ.isIntertwining _ _ b x

/-- **Characters along a surjective map**: `ch ρ = ch (ker φ) + ch σ`. -/
theorem ch_eq_ch_ker_add (hρ : IsRationalBorelRep ρ) (φ : ρ.IntertwiningMap σ)
    (hφ : Function.Surjective φ) : ch ρ = ch φ.ker.toRepresentation + ch σ := by
  rw [ch_eq_add hρ φ.ker, ch_eq_of_equiv (IntertwiningMap.quotKerEquivOfSurjective φ hφ)]

end Surjective

namespace SectionRep

/-! ### Minimal relative Schubert modules -/

theorem isRationalBorelRep_dualJoseph
    (ν : Fin n → ℤ) : IsRationalBorelRep (dualJoseph ν) :=
  isRationalBorelRep_sectionRep (bruhatLower_lowerSet _) (isAntidominant_fibreWeight ν)

/-- The character of the sections over the Schubert boundary: `x^{−k·1} (κ_u − 𝒜_u)`. -/
theorem ch_boundarySections
    (ν : Fin n → ℤ) :
    ch (sectionRep (boundarySet (schubertIndex ν)) (fibreWeight ν)) =
      AddMonoidAlgebra.single (-fun _ => (weightShift ν : ℤ)) 1 *
        toLaurent (key (weightComplement ν) - atom (weightComplement ν)) := by
  set u := weightComplement ν
  obtain ⟨d, h, hm⟩ := exists_columnMultiplicity (compositionShape u)
  have hη : fibreWeight ν =
      -shapeWeightZ (columnMultiplicity h) + fun _ => (weightShift ν : ℤ) := by
    rw [fibreWeight_eq_sub]
    funext i
    simp only [Pi.add_apply, Pi.neg_apply, shapeWeightZ, hm, compositionShape_weight]
    ring
  have hW : IsMinCosetRep (shapeWeight (columnMultiplicity h)) (schubertIndex ν) := by
    rw [hm, schubertIndex_eq_compositionPermutation]
    exact Demazure.Filtrations.isMinCosetRep_compositionPermutation u
  have := finiteDimensional_sectionRep (bruhatLower_boundarySet (schubertIndex ν)) h
  rw [ch_eq_of_equiv (sectionRepEquivOfEq _ hη), ch_sectionRep_add_const,
    ch_sectionRep_neg (bruhatLower_boundarySet _) h, boundarySet_eq_schubertBoundary,
    chainCharacter_boundary h hW, hm, schubertIndex_eq_compositionPermutation,
    composition_extremalWeight]

/-- **`ch Q(ν) = x^{−k·1} 𝒜_u`**, with `k = weightShift ν` and `u = k·1 − ν`. -/
theorem ch_minimalRelativeSchubert
    (ν : Fin n → ℤ) :
    ch (minimalRelativeSchubert ν) = AddMonoidAlgebra.single (-fun _ => (weightShift ν : ℤ)) 1 *
      toLaurent (atom (weightComplement ν)) := by
  have h := ch_eq_ch_ker_add (isRationalBorelRep_dualJoseph ν) (boundaryRestrict ν)
    (boundaryRestrict_surjective ν)
  rw [ch_dualJoseph, ch_boundarySections, map_sub, mul_sub] at h
  rw [eq_sub_of_add_eq h.symm]
  abel

/-- **The second identity of (1.7): `ch Q(−u) = 𝒜_u`.** -/
theorem ch_minimalRelativeSchubert_negWeight
    (u : Fin n → ℕ) : ch (minimalRelativeSchubert (negWeight u)) = toLaurent (atom u) := by
  rw [ch_minimalRelativeSchubert, weightShift_negWeight, weightComplement_negWeight]
  have : (-fun _ : Fin n => ((0 : ℕ) : ℤ)) = 0 := by
    funext i
    simp
  rw [this, ← AddMonoidAlgebra.one_def, one_mul]

/-- **`Q(ν)` contains the weight `ν`** [van der Kallen, Remark 2.3.5]. -/
theorem minimalRelativeSchubert_weightSpace_ne_bot
    (ν : Fin n → ℤ) : borelWeightSpace (minimalRelativeSchubert ν) ν ≠ ⊥ := by
  have := (isRationalBorelRep_dualJoseph ν).finiteDimensional
  intro h0
  have h := coeff_ch (ρ := minimalRelativeSchubert ν) ν
  rw [h0, finrank_bot, ch_minimalRelativeSchubert] at h
  have hw : -ν = -(fun _ => (weightShift ν : ℤ)) + fun i => (weightComplement ν i : ℤ) := by
    funext i
    simp only [Pi.add_apply, Pi.neg_apply, weightComplement_cast]
    ring
  rw [hw, AddMonoidAlgebra.coeff_single_mul_apply, one_mul, neg_neg, ← add_assoc,
    add_neg_cancel, zero_add, Demazure.Filtrations.atom_coeff_self] at h
  exact absurd h (by norm_num)

/-! ### The Demazure recurrences -/

/-- `ch P(−sᵢu) = πᵢ ch P(−u)` for `uᵢ > u_{i+1}` (the Demazure recurrence). -/
theorem ch_dualJoseph_step
    (u : Fin n → ℕ) (i : AdjacentPosition n) (h : u i.right < u i.left) :
    ch (dualJoseph (negWeight (swapComposition u i))) = toLaurent (isobaric i (key u)) := by
  rw [isobaric_key, ite_eq_left h]
  exact ch_dualJoseph_negWeight _

/-- `ch Q(−sᵢu) = π̄ᵢ ch Q(−u)` for `uᵢ > u_{i+1}` [van der Kallen, Lemma 7.2.3]. -/
theorem ch_minimalRelativeSchubert_step
    (u : Fin n → ℕ) (i : AdjacentPosition n) (h : u i.right < u i.left) :
    ch (minimalRelativeSchubert (negWeight (swapComposition u i))) =
      toLaurent (atomOperator i (atom u)) := by
  have hb : (swapComposition u i) i.left < (swapComposition u i) i.right := by simpa using h
  have hs := atom_any_ascent (swapComposition u i) i hb
  rw [swapComposition_involutive] at hs
  rw [← hs]
  exact ch_minimalRelativeSchubert_negWeight _

end SectionRep

end

end FlagVarieties
