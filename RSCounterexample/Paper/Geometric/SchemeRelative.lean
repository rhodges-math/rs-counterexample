import RSCounterexample.Paper.Geometric.SchemeCorollary
import RSCounterexample.FlagVarieties.Modules.SectionRestriction

/-!
# Corollary 1.2 at the sheaf level: relative Schubert filtrations, `SL_n`, type `A₂₇`

The statements of `RSCounterexample.Paper.Geometric.Corollary` for the sheaf-theoretic section modules
`H⁰(X, 𝓛(η)) = FlagVarieties.sections ℂ n I η` with the action `FlagVarieties.sectionsRep` of `B`:

* **the geometric minimal relative Schubert module** `Q(ν)`, the kernel of the restriction
  `H⁰(X_σ, 𝓛(η)) → H⁰(∂X_σ, 𝓛(η))` to the Schubert boundary
  (`Schubert.RS.Geometric.geometricMinimalRelativeSchubert`, with the restriction of sections
  `FlagVarieties.sectionsRestrictHom`), is the ring-model `Q(ν)`
  (`Schubert.RS.Geometric.geometricMinimalRelativeSchubertEquiv`); hence `ch Q(−u) = 𝒜_u` and the
  weight `ν` occurs in `Q(ν)`;
* `P(−a) ⊗ P(−b)` admits no relative Schubert filtration
  (`Schubert.RS.Geometric.not_hasGeometricRelativeSchubertFiltration`), and neither filtration
  exists over `SL_n` (`not_hasGeometricSLRelativeSchubertFiltration`,
  `not_hasGeometricSLSchubertFiltration`); together with Polo's form
  (`Schubert.RS.Geometric.not_hasGeometricSchubertFiltration`) this is all of Corollary 1.2
  (`cor:intro-filtrations`), already in type `A₂₇`
  (`Schubert.RS.Geometric.typeA27_geometricFiltration_failure`).

Everything is transferred from the ring model through `sectionsEquivSemiInvariants`. There are
no hypotheses.
-/

open GLRep FlagVarieties FlagVarieties.SectionRep FlagVarieties.PointModel.Complex
    Demazure.SchubertUnions

universe u

/-! ### Kernels of compatible intertwining maps -/

section Helpers

variable {A G : Type*} [CommSemiring A] [Monoid G]
variable {V₁ V₂ W₁ W₂ : Type*} [AddCommMonoid V₁] [Module A V₁] [AddCommMonoid V₂] [Module A V₂]
  [AddCommMonoid W₁] [Module A W₁] [AddCommMonoid W₂] [Module A W₂]
  {ρ₁ : Representation A G V₁} {ρ₂ : Representation A G V₂} {σ₁ : Representation A G W₁}
  {σ₂ : Representation A G W₂}

/-- The square `e₂ ∘ f = f' ∘ e₁` of intertwining maps and equivalences commutes. -/
def Schubert.RS.Geometric.IsSquare (e₁ : ρ₁.Equiv σ₁) (e₂ : ρ₂.Equiv σ₂)
    (f : ρ₁.IntertwiningMap ρ₂) (f' : σ₁.IntertwiningMap σ₂) : Prop :=
  ∀ v, e₂ (f v) = f' (e₁ v)

/-- Equivalences `e₁ : ρ₁ ≅ σ₁`, `e₂ : ρ₂ ≅ σ₂` compatible with intertwining maps `f`, `f'`
(`e₂ ∘ f = f' ∘ e₁`) restrict to an equivalence of the kernels. -/
def Schubert.RS.Geometric.kerEquivOfSquare (e₁ : ρ₁.Equiv σ₁) (e₂ : ρ₂.Equiv σ₂)
    (f : ρ₁.IntertwiningMap ρ₂) (f' : σ₁.IntertwiningMap σ₂)
    (h : Schubert.RS.Geometric.IsSquare e₁ e₂ f f') :
    f.ker.toRepresentation.Equiv f'.ker.toRepresentation :=
  .mk (e₁.toLinearEquiv.ofSubmodules f.ker.toSubmodule f'.ker.toSubmodule (by
      ext w
      constructor
      · rintro ⟨v, hv, rfl⟩
        have hv' : f v = 0 := hv
        change f' (e₁ v) = 0
        rw [← h, hv', map_zero]
      · intro hw
        have hw' : f' w = 0 := hw
        refine ⟨e₁.toLinearEquiv.symm w, ?_, e₁.toLinearEquiv.apply_symm_apply w⟩
        change f (e₁.toLinearEquiv.symm w) = 0
        have h1 := h (e₁.toLinearEquiv.symm w)
        rw [show e₁ (e₁.toLinearEquiv.symm w) = w from e₁.toLinearEquiv.apply_symm_apply w,
          hw'] at h1
        exact e₂.toLinearEquiv.map_eq_zero_iff.mp h1))
    fun g => LinearMap.ext fun v => Subtype.ext (e₁.toIntertwiningMap.isIntertwining _ _ g v.1)

end Helpers

namespace Schubert.RS.Geometric

noncomputable section

variable {n : ℕ}

/-! ### The Schubert boundary -/

theorem schubertBoundary_eq_schubertUnion (σ : Equiv.Perm (Fin n)) :
    schubertBoundary ℂ n σ = schubertUnion ℂ n (boundarySet σ) := by
  classical
  rw [schubertBoundary]
  congr 1
  ext τ
  rw [Finset.mem_filter, mem_boundarySet]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

/-- The ideal of `π⁻¹(∂X_σ)` is the orbit ideal of `{τ | τ < σ}`
(`preimageIdeal_schubertUnion_eq_orbitIdeal`). -/
theorem preimageIdeal_schubertBoundary_eq_orbitIdeal (σ : Equiv.Perm (Fin n)) :
    preimageIdeal ℂ n (schubertBoundary ℂ n σ) = orbitIdeal (boundarySet σ) := by
  have : Infinite ℂ := Infinite.of_injective (Nat.cast : ℕ → ℂ) Nat.cast_injective
  rw [schubertBoundary_eq_schubertUnion]
  exact preimageIdeal_schubertUnion_eq_orbitIdeal ℂ n _

/-- `∂X_σ ⊆ X_σ`. -/
theorem schubertVariety_le_schubertBoundary (σ : Equiv.Perm (Fin n)) :
    schubertVariety ℂ n σ ≤ schubertBoundary ℂ n σ :=
  (preimageIdeal_le_preimageIdeal_iff ℂ n _ _).mp (by
    rw [preimageIdeal_schubertVariety_eq_orbitIdeal, preimageIdeal_schubertBoundary_eq_orbitIdeal]
    exact orbitIdeal_antitone (boundarySet_subset_lowerSet σ))

theorem isLeftTranslStable_schubertBoundary (σ : Equiv.Perm (Fin n)) :
    IsLeftTranslStable (preimageIdeal ℂ n (schubertBoundary ℂ n σ)) :=
  isLeftTranslStable_of_eq (preimageIdeal_schubertBoundary_eq_orbitIdeal σ)

/-! ### Values of the comparison with the ring model -/

theorem coe_semiInvariantsRepEquiv {S : Finset (Equiv.Perm (Fin n))}
    (J : Ideal (FlagVarieties.GLCoord ℂ n))
    (hJS : J = orbitIdeal S) (hJ : IsLeftTranslStable J) (η : Fin n → ℤ)
    (x : FlagVarieties.quotientSemiInvariants ℂ n J η) :
    ((semiInvariantsRepEquiv J hJS hJ η x : (sectionSubrep S η).toSubmodule) :
        FlagVarieties.GLCoord ℂ n ⧸ orbitIdeal S) =
      Ideal.Quotient.factorₐ ℂ hJS.le (x : FlagVarieties.GLCoord ℂ n ⧸ J) := by
  subst hJS
  obtain ⟨x, -⟩ := x
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

theorem coe_geometricSectionEquiv {S : Finset (Equiv.Perm (Fin n))}
    (I : (FlagScheme ℂ n).IdealSheafData) (hI : preimageIdeal ℂ n I = orbitIdeal S)
    (hJ : IsLeftTranslStable (preimageIdeal ℂ n I)) (η : Fin n → ℤ) (s : sections ℂ n I η) :
    ((geometricSectionEquiv I hI hJ η s : (sectionSubrep S η).toSubmodule) :
        FlagVarieties.GLCoord ℂ n ⧸ orbitIdeal S) =
      Ideal.Quotient.factorₐ ℂ hI.le
        (sectionsEquivSemiInvariants ℂ n I η s : FlagVarieties.GLCoord ℂ n ⧸ preimageIdeal ℂ n I) :=
  coe_semiInvariantsRepEquiv _ hI hJ η _

/-! ### The geometric minimal relative Schubert modules -/

variable (ν : Fin n → ℤ)

/-- `H⁰(∂X_σ, 𝓛(η))`, `σ = σ(ν)`, `η = η(ν)`, with the action of `B` (`sectionsRep`). -/
abbrev geometricBoundarySections :
    Representation ℂ (borel ℂ n)
      (sections ℂ n (schubertBoundary ℂ n (schubertIndex ν)) (fibreWeight ν)) :=
  sectionsRep ℂ n _ (fibreWeight ν) (isLeftTranslStable_schubertBoundary _)

/-- The restriction `P(ν) = H⁰(X_σ, 𝓛(η)) → H⁰(∂X_σ, 𝓛(η))` to the Schubert boundary. -/
def geometricBoundaryRestrict :
    (FlagVarieties.dualJoseph ν).IntertwiningMap (geometricBoundarySections ν) :=
  sectionsRestrictHom ℂ n (schubertVariety_le_schubertBoundary _) _ _ _

/-- The sections in `H⁰(X_σ, 𝓛(η))` vanishing on `∂X_σ`. -/
abbrev geometricMinimalRelativeSchubertSubrep : Subrepresentation (FlagVarieties.dualJoseph ν) :=
  (geometricBoundaryRestrict ν).ker

/-- **The geometric minimal relative Schubert module**:
`Q(ν) = ker(H⁰(X_σ, 𝓛(η)) → H⁰(∂X_σ, 𝓛(η)))`, `σ = σ(ν)`, `η = η(ν)`, on the sheaf sections, with
the action of `B` by left translation. -/
abbrev geometricMinimalRelativeSchubert :
    Representation ℂ (borel ℂ n) (geometricMinimalRelativeSchubertSubrep ν).toSubmodule :=
  (geometricMinimalRelativeSchubertSubrep ν).toRepresentation

/-- The restriction to the boundary corresponds to the ring-model restriction. -/
theorem isSquare_geometricBoundaryRestrict :
    IsSquare (dualJosephEquiv ν)
      (geometricSectionEquiv _ (preimageIdeal_schubertBoundary_eq_orbitIdeal (schubertIndex ν))
        (isLeftTranslStable_schubertBoundary _) (fibreWeight ν))
      (geometricBoundaryRestrict ν) (boundaryRestrict ν) := fun s => by
  apply Subtype.ext
  have h1 : ((boundaryRestrict ν (dualJosephEquiv ν s) :
      (sectionSubrep (boundarySet (schubertIndex ν)) (fibreWeight ν)).toSubmodule) :
        FlagVarieties.GLCoord ℂ n ⧸ orbitIdeal (boundarySet (schubertIndex ν))) =
      Ideal.Quotient.factorₐ ℂ (orbitIdeal_antitone (boundarySet_subset_lowerSet (schubertIndex ν)))
        ((dualJosephEquiv ν s :
          (sectionSubrep (lowerSet (schubertIndex ν)) (fibreWeight ν)).toSubmodule) :
            FlagVarieties.GLCoord ℂ n ⧸ orbitIdeal (lowerSet (schubertIndex ν))) :=
    rfl
  have h2 : ((dualJosephEquiv ν s :
      (sectionSubrep (lowerSet (schubertIndex ν)) (fibreWeight ν)).toSubmodule) :
        FlagVarieties.GLCoord ℂ n ⧸ orbitIdeal (lowerSet (schubertIndex ν))) =
      Ideal.Quotient.factorₐ ℂ (preimageIdeal_schubertVariety_eq_orbitIdeal (schubertIndex ν)).le
        (sectionsEquivSemiInvariants ℂ n _ (fibreWeight ν) s :
          FlagVarieties.GLCoord ℂ n ⧸ preimageIdeal ℂ n (schubertVariety ℂ n (schubertIndex ν))) :=
    coe_geometricSectionEquiv _ _ _ _ s
  have h3 : sectionsEquivSemiInvariants ℂ n _ (fibreWeight ν) (geometricBoundaryRestrict ν s) =
      semiInvariantsRestrict (preimageIdeal_mono ℂ n (schubertVariety_le_schubertBoundary _)) _
        (sectionsEquivSemiInvariants ℂ n _ _ s) :=
    sectionsEquivSemiInvariants_sectionsRestrictHom _ _ _ _ s
  rw [coe_geometricSectionEquiv, h1, h2, h3, coe_semiInvariantsRestrict]
  obtain ⟨f, hf⟩ := Ideal.Quotient.mk_surjective
      (sectionsEquivSemiInvariants ℂ n _ (fibreWeight ν) s :
    FlagVarieties.GLCoord ℂ n ⧸ preimageIdeal ℂ n (schubertVariety ℂ n (schubertIndex ν)))
  rw [← hf]
  rfl


/-- **The geometric `Q(ν)` is the ring-model `Q(ν)`.** -/
def geometricMinimalRelativeSchubertEquiv : (geometricMinimalRelativeSchubert ν).Equiv
    (minimalRelativeSchubert ν) :=
  kerEquivOfSquare _ _ _ _ (isSquare_geometricBoundaryRestrict ν)

theorem ch_geometricMinimalRelativeSchubert : ch (geometricMinimalRelativeSchubert ν) = ch
    (minimalRelativeSchubert ν) :=
  ch_eq_of_equiv (geometricMinimalRelativeSchubertEquiv ν)

/-- **`ch Q(−u) = 𝒜_u` for the geometric minimal relative Schubert modules.** -/
theorem ch_geometricMinimalRelativeSchubert_negWeight (u : Fin n → ℕ) :
    ch (geometricMinimalRelativeSchubert (negWeight u)) = Demazure.toLaurent (Demazure.atom u) := by
  rw [ch_geometricMinimalRelativeSchubert, ch_minimalRelativeSchubert_negWeight]

theorem isRationalBorelRep_geometricMinimalRelativeSchubert :
    IsRationalBorelRep (geometricMinimalRelativeSchubert ν) :=
  ((SectionRep.isRationalBorelRep_dualJoseph ν).subrepresentation _).of_equiv
    (geometricMinimalRelativeSchubertEquiv ν).symm

/-- **The weight `ν` occurs in the geometric `Q(ν)`.** -/
theorem geometricMinimalRelativeSchubert_weightSpace_ne_bot :
    borelWeightSpace (geometricMinimalRelativeSchubert ν) ν ≠ ⊥ := by
  obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff _).mp (minimalRelativeSchubert_weightSpace_ne_bot ν)
  refine (Submodule.ne_bot_iff _).mpr ⟨_, map_mem_borelWeightSpace
    (geometricMinimalRelativeSchubertEquiv ν).symm.toIntertwiningMap hw, fun h => hw0 ?_⟩
  exact (geometricMinimalRelativeSchubertEquiv ν).symm.toLinearEquiv.map_eq_zero_iff.mp h

/-! ### Layers and filtrations -/

variable {W : Type u} [AddCommGroup W] [Module ℂ W]

/-- `L` is equivalent to a geometric minimal relative Schubert module `Q(ν)`. -/
def IsGeometricMinimalRelativeSchubertLayer (V : Type u) [AddCommGroup V] [Module ℂ V]
    (L : Representation ℂ (borel ℂ n) V) : Prop :=
  ∃ ν : Fin n → ℤ, Nonempty (L.Equiv (geometricMinimalRelativeSchubert ν))

theorem isGeometricMinimalRelativeSchubertLayer_iff {V : Type u} [AddCommGroup V] [Module ℂ V]
    (L : Representation ℂ (borel ℂ n) V) :
    IsGeometricMinimalRelativeSchubertLayer V L ↔ IsMinimalRelativeSchubertLayer V L :=
  exists_congr fun ν => ⟨fun ⟨e⟩ => ⟨e.trans (geometricMinimalRelativeSchubertEquiv ν)⟩,
    fun ⟨e⟩ => ⟨e.trans (geometricMinimalRelativeSchubertEquiv ν).symm⟩⟩

/-- `L` is equivalent over `B_SL` to the restriction of a geometric `Q(ν)`. -/
def IsGeometricSLMinimalRelativeSchubertLayer (V : Type u) [AddCommGroup V] [Module ℂ V]
    (L : Representation ℂ (borelSL ℂ n) V) : Prop :=
  ∃ ν : Fin n → ℤ,
    Nonempty (L.Equiv ((geometricMinimalRelativeSchubert ν).comp (borelSL ℂ n).subtype))

/-- `L` is equivalent over `B_SL` to the restriction of a sheaf-theoretic section module
`H⁰(X_S, 𝓛(η))` over a nonempty Schubert union, `η` antidominant. -/
def IsGeometricSLSchubertLayer (V : Type u) [AddCommGroup V] [Module ℂ V]
    (L : Representation ℂ (borelSL ℂ n) V) : Prop :=
  ∃ k : SchubertLayerIndex n, Nonempty (L.Equiv ((sectionsRep ℂ n (schubertUnion ℂ n k.1.2) k.1.1
    (isLeftTranslStable_of_eq (preimageIdeal_schubertUnion_eq_orbitIdeal_complex n _ k.2.2.1
        k.2.2.2))).comp
      (borelSL ℂ n).subtype))

theorem isGeometricSLMinimalRelativeSchubertLayer_iff {V : Type u} [AddCommGroup V] [Module ℂ V]
    (L : Representation ℂ (borelSL ℂ n) V) :
    IsGeometricSLMinimalRelativeSchubertLayer V L ↔ IsSLMinimalRelativeSchubertLayer V L :=
  exists_congr fun ν =>
    ⟨fun ⟨e⟩ => ⟨e.trans (equivComp (geometricMinimalRelativeSchubertEquiv ν) _)⟩,
      fun ⟨e⟩ => ⟨e.trans (equivComp (geometricMinimalRelativeSchubertEquiv ν).symm _)⟩⟩

theorem isGeometricSLSchubertLayer_iff {V : Type u} [AddCommGroup V] [Module ℂ V]
    (L : Representation ℂ (borelSL ℂ n) V) :
    IsGeometricSLSchubertLayer V L ↔ IsSLSchubertLayer V L :=
  exists_congr fun k =>
    ⟨fun ⟨e⟩ => ⟨e.trans (equivComp
      (geometricSectionEquiv _ (preimageIdeal_schubertUnion_eq_orbitIdeal_complex n _ k.2.2.1
          k.2.2.2) _ _) _)⟩,
      fun ⟨e⟩ => ⟨e.trans (equivComp
        (geometricSectionEquiv _ (preimageIdeal_schubertUnion_eq_orbitIdeal_complex n _ k.2.2.1
            k.2.2.2) _ _).symm _)⟩⟩

/-- `ρ` admits a **relative Schubert filtration** with sheaf-theoretic layers `Q(ν)`. -/
def HasGeometricRelativeSchubertFiltration (ρ : Representation ℂ (borel ℂ n) W) : Prop :=
  HasFiltrationBy IsGeometricMinimalRelativeSchubertLayer ρ

/-- `ρ` admits a **Schubert filtration in Polo's sense** with sheaf-theoretic layers
`H⁰(X_S, 𝓛(η))`. -/
def HasGeometricSchubertFiltration (ρ : Representation ℂ (borel ℂ n) W) : Prop :=
  HasFiltrationBy IsGeometricSchubertLayer ρ

/-- The `SL_n` form of `HasGeometricRelativeSchubertFiltration`. -/
def HasGeometricSLRelativeSchubertFiltration (ρ : Representation ℂ (borel ℂ n) W) : Prop :=
  HasFiltrationBy IsGeometricSLMinimalRelativeSchubertLayer (ρ.comp (borelSL ℂ n).subtype)

/-- The `SL_n` form of `HasGeometricSchubertFiltration`. -/
def HasGeometricSLSchubertFiltration (ρ : Representation ℂ (borel ℂ n) W) : Prop :=
  HasFiltrationBy IsGeometricSLSchubertLayer (ρ.comp (borelSL ℂ n).subtype)

/-! ### Corollary 1.2 -/

open Family

variable {P : Parameters}

/-- Scalar matrices act on the sheaf-theoretic `P(−a) ⊗ P(−b)` through a single character. -/
theorem geometricFamilyTensor_hasCentralCharacter :
    ∃ d, HasCentralCharacter (geometricFamilyTensor P) d :=
  ⟨_, ((hasCentralCharacter_dualJoseph _).of_equiv (dualJosephEquiv _).symm).tprod
    ((hasCentralCharacter_dualJoseph _).of_equiv (dualJosephEquiv _).symm)⟩

/-- **Corollary 1.2 for the sheaf-theoretic modules, relative Schubert filtrations.** For
`(p − 2)(q − 2) > 2`, `P(−a) ⊗ P(−b)` admits no filtration whose layers are the geometric minimal
relative Schubert modules `Q(ν)`. -/
theorem not_hasGeometricRelativeSchubertFiltration
    (hneg : 2 < ((P.p : ℤ) - 2) * ((P.q : ℤ) - 2)) :
    ¬ HasGeometricRelativeSchubertFiltration (geometricFamilyTensor P) := fun hF =>
  not_atomPositive P hneg <| atomPositive_of_hasFiltrationBy
    (fun _ _ _ _ ⟨ν, ⟨e⟩⟩ =>
        (ch_eq_of_equiv (e.trans (geometricMinimalRelativeSchubertEquiv ν))).symm ▸
      isShiftedAtomSum_ch_minimalRelativeSchubert ν)
    isRationalBorelRep_geometricFamilyTensor hF ch_geometricFamilyTensor

/-- **Corollary 1.2 for the sheaf-theoretic modules over `SL_n`, relative Schubert
filtrations.** -/
theorem not_hasGeometricSLRelativeSchubertFiltration
    (hneg : 2 < ((P.p : ℤ) - 2) * ((P.q : ℤ) - 2)) :
    ¬ HasGeometricSLRelativeSchubertFiltration (geometricFamilyTensor P) := by
  intro hF'
  obtain ⟨F, hF⟩ := hF'
  have hfin : ∀ ν : Fin P.rank → ℤ, FiniteDimensional ℂ
      (minimalRelativeSchubertSubrep ν).toSubmodule :=
    fun ν => ((SectionRep.isRationalBorelRep_dualJoseph ν).subrepresentation _).finiteDimensional
  obtain ⟨d, hd⟩ := geometricFamilyTensor_hasCentralCharacter (P := P)
  exact not_atomPositive P hneg <| atomPositive_of_borelSL_filtration
    (fun ν => minimalRelativeSchubert ν) (fun ν => ∑ i, fibreWeight ν i)
    (fun ν => hasCentralCharacter_minimalRelativeSchubert ν)
    (fun ν => isShiftedAtomSum_ch_minimalRelativeSchubert ν)
    isRationalBorelRep_geometricFamilyTensor hd F
    (fun i hi => (isGeometricSLMinimalRelativeSchubertLayer_iff _).mp (hF i hi))
    ch_geometricFamilyTensor

/-- **Corollary 1.2 for the sheaf-theoretic modules over `SL_n`, Schubert filtrations in Polo's
sense.** -/
theorem not_hasGeometricSLSchubertFiltration
    (hneg : 2 < ((P.p : ℤ) - 2) * ((P.q : ℤ) - 2)) :
    ¬ HasGeometricSLSchubertFiltration (geometricFamilyTensor P) := by
  intro hF'
  obtain ⟨F, hF⟩ := hF'
  have hfin : ∀ k : SchubertLayerIndex P.rank,
      FiniteDimensional ℂ (sectionSubrep k.1.2 k.1.1).toSubmodule :=
    fun k => finiteDimensional_sectionRep_of_isAntidominant k.2.2.2 k.2.1
  obtain ⟨d, hd⟩ := geometricFamilyTensor_hasCentralCharacter (P := P)
  exact not_atomPositive P hneg <| atomPositive_of_borelSL_filtration
    (fun k : SchubertLayerIndex P.rank => sectionRep k.1.2 k.1.1) (fun k => ∑ i, k.1.1 i)
    (fun k => hasCentralCharacter_sectionRep _ _)
    (fun k => isShiftedAtomSum_ch_sectionRep k.2.2.2 k.2.1)
    isRationalBorelRep_geometricFamilyTensor hd F
    (fun i hi => (isGeometricSLSchubertLayer_iff _).mp (hF i hi))
    ch_geometricFamilyTensor

/-- **Corollary 1.2 for the sheaf-theoretic modules in type `A₂₇`.** For `(p, q) = (3, 5)` and
every scale `δ ≥ 8`, the sheaf-theoretic `P(−a) ⊗ P(−b)` lives in type `A₂₇` and admits neither a
relative Schubert filtration nor a Schubert filtration in Polo's sense, over `GL₂₈` or over
`SL₂₈`. -/
theorem typeA27_geometricFiltration_failure (δ : ℕ) (hδ : 8 ≤ δ) :
    (threeFive δ hδ).rank - 1 = 27 ∧
      ¬ HasGeometricRelativeSchubertFiltration (geometricFamilyTensor (threeFive δ hδ)) ∧
      ¬ HasGeometricSchubertFiltration (geometricFamilyTensor (threeFive δ hδ)) ∧
      ¬ HasGeometricSLRelativeSchubertFiltration (geometricFamilyTensor (threeFive δ hδ)) ∧
      ¬ HasGeometricSLSchubertFiltration (geometricFamilyTensor (threeFive δ hδ)) := by
  have hneg : 2 < (((threeFive δ hδ).p : ℕ) - 2 : ℤ) * (((threeFive δ hδ).q : ℕ) - 2 : ℤ) := by
    simp [threeFive]
  exact ⟨by rw [threeFive_rank], not_hasGeometricRelativeSchubertFiltration hneg,
    not_hasGeometricSchubertFiltration hneg, not_hasGeometricSLRelativeSchubertFiltration hneg,
    not_hasGeometricSLSchubertFiltration hneg⟩

end

end Schubert.RS.Geometric
