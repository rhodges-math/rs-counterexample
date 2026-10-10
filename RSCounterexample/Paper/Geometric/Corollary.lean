import RSCounterexample.FlagVarieties.Modules.Filtrations
import RSCounterexample.Paper.Geometric.Obstruction
import RSCounterexample.Paper.Geometric.Identification
import RSCounterexample.Paper.Family.Extras

/-!
# Corollary 1.2 for the geometric modules

For the family of Theorem 1.1 let `P(−a) ⊗ P(−b)` be the tensor product of the dual Joseph modules
`P(ν) = H⁰(X_σ, 𝓛(η))` of the flag-variety library (`Schubert.RS.Geometric.familyTensor`, built
from `FlagVarieties.SectionRep.dualJoseph`). Its character is `κ_a κ_b`
(`Schubert.RS.Geometric.ch_familyTensor`), and each factor has an excellent filtration.

**Corollary 1.2** (`cor:intro-filtrations`): in the negative range `(p − 2)(q − 2) > 2`,
`P(−a) ⊗ P(−b)` admits neither a relative Schubert filtration nor a Schubert filtration in Polo's
sense, over `GL_n` or over `SL_n` (`Schubert.RS.Geometric.not_hasRelativeSchubertFiltration`,
`not_hasSchubertFiltration`, `not_hasSLRelativeSchubertFiltration`, `not_hasSLSchubertFiltration`),
already in type `A₂₇` (`Schubert.RS.Geometric.typeA27_filtration_failure`).

The proof is the paper's: such a filtration would make `κ_a κ_b` a nonnegative integral combination
of atoms (`Schubert.RS.Geometric.atomPositive_of_hasFiltrationBy`, with the layer characters
`ch Q(ν) = x^{−k·1} 𝒜_u` and `ch H⁰(X_S, 𝓛(η)) = x^{−k·1} ∑ 𝒜_{τλ}`), contradicting Theorem 1.1
(`Schubert.RS.Family.not_atomPositive`).

The statements have no hypotheses: the equality `∀ w, GlobalSectionsConstant w` (`Γ(X_w, 𝒪) = ℂ` in
ring form) is `FlagVarieties.globalSectionsConstant_complex`.
-/

open GLRep FlagVarieties FlagVarieties.SectionRep FlagVarieties.PointModel.Complex
    Demazure.SchubertUnions

namespace Schubert.RS.Geometric

noncomputable section

/-! ### Layer characters are shifted sums of atoms -/

section Layers

variable {n : ℕ}

theorem neg_const_eq_constWeight (k : ℤ) :
    (-fun _ : Fin n => k) = BModules.BModule.constWeight (-k) :=
  rfl

/-- The character of `Q(ν)` is a shifted atom. -/
theorem isShiftedAtomSum_ch_minimalRelativeSchubert (ν : Fin n → ℤ) :
    IsShiftedAtomSum (ch (minimalRelativeSchubert ν)) := by
  refine ⟨-(weightShift ν : ℤ), {Equiv.refl _}, fun _ => weightComplement ν, ?_⟩
  rw [ch_minimalRelativeSchubert, Finset.sum_singleton, neg_const_eq_constWeight, atom_eq]
  rfl

/-- The character of a section module over a Schubert union, for an antidominant weight, is a
shifted sum of atoms. -/
theorem isShiftedAtomSum_ch_sectionRep
    {S : Finset (Equiv.Perm (Fin n))} (hS : BruhatLower S) {η : Fin n → ℤ}
    (hη : IsAntidominant η) : IsShiftedAtomSum (ch (sectionRep S η)) := by
  classical
  refine ⟨-(weightShift η : ℤ), S.filter (IsMinCosetRep (weightComplement η)),
    fun τ => permAct τ (weightComplement η), ?_⟩
  rw [ch_sectionRep hS hη, neg_const_eq_constWeight, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [atom_eq]
  rfl

end Layers

/-! ### The family -/

open Family

variable (P : Parameters)

instance : NeZero P.rank :=
  ⟨by have := P.m_pos; unfold Parameters.rank; omega⟩

/-- The tensor product `P(−a) ⊗ P(−b)` of the (geometric) dual Joseph modules of the family. -/
abbrev familyTensor :=
  (SectionRep.dualJoseph (negWeight (a P))).tprod (SectionRep.dualJoseph (negWeight (b P)))

variable {P}

theorem isRationalBorelRep_familyTensor :
    IsRationalBorelRep (familyTensor P) :=
  (SectionRep.isRationalBorelRep_dualJoseph _).tprod (SectionRep.isRationalBorelRep_dualJoseph _)

/-- **`ch (P(−a) ⊗ P(−b)) = κ_a κ_b`.** -/
theorem ch_familyTensor :
    ch (familyTensor P) = toLaurent (key (a P) * key (b P)) := by
  rw [ch_tprod (SectionRep.isRationalBorelRep_dualJoseph _)
      (SectionRep.isRationalBorelRep_dualJoseph _),
    SectionRep.ch_dualJoseph_negWeight, SectionRep.ch_dualJoseph_negWeight, key_eq, key_eq, map_mul]
  rfl

/-- Scalar matrices act on `P(−a) ⊗ P(−b)` through a single character. -/
theorem familyTensor_hasCentralCharacter :
    ∃ d, HasCentralCharacter (familyTensor P) d :=
  ⟨_, (hasCentralCharacter_dualJoseph _).tprod (hasCentralCharacter_dualJoseph _)⟩

/-- Each factor `P(−a)`, `P(−b)` has an excellent filtration (lines 280–283). -/
theorem factors_hasExcellentFiltration :
    HasExcellentFiltration (SectionRep.dualJoseph (negWeight (a P))) ∧
      HasExcellentFiltration (SectionRep.dualJoseph (negWeight (b P))) :=
  ⟨hasExcellentFiltration_dualJoseph _, hasExcellentFiltration_dualJoseph _⟩

/-! ### Corollary 1.2 -/

/-- **Corollary 1.2, relative Schubert filtrations.** For `(p − 2)(q − 2) > 2`, the `B`-module
`P(−a) ⊗ P(−b)` admits no filtration by subrepresentations whose layers are minimal relative
Schubert modules `Q(ν)`. -/
theorem not_hasRelativeSchubertFiltration
    (hneg : 2 < ((P.p : ℤ) - 2) * ((P.q : ℤ) - 2)) :
    ¬ HasRelativeSchubertFiltration (familyTensor P) := fun hF =>
  not_atomPositive P hneg <| atomPositive_of_hasFiltrationBy
    (fun _ _ _ _ ⟨ν, ⟨e⟩⟩ => (ch_eq_of_equiv e).symm ▸ isShiftedAtomSum_ch_minimalRelativeSchubert
                               ν)
    (isRationalBorelRep_familyTensor) hF (ch_familyTensor)

/-- **Corollary 1.2, Schubert filtrations in Polo's sense.** For `(p − 2)(q − 2) > 2`, the
`B`-module `P(−a) ⊗ P(−b)` admits no filtration whose layers are section modules
`H⁰(X_S, 𝓛(η))` over nonempty unions of Schubert varieties, for antidominant `η`. -/
theorem not_hasSchubertFiltration
    (hneg : 2 < ((P.p : ℤ) - 2) * ((P.q : ℤ) - 2)) :
    ¬ HasSchubertFiltration (familyTensor P) := fun hF =>
  not_atomPositive P hneg <| atomPositive_of_hasFiltrationBy
    (fun _ _ _ _ ⟨k, ⟨e⟩⟩ =>
      (ch_eq_of_equiv e).symm ▸ isShiftedAtomSum_ch_sectionRep k.2.2.2 k.2.1)
    (isRationalBorelRep_familyTensor) hF (ch_familyTensor)

/-- **Corollary 1.2 over `SL_n`, relative Schubert filtrations.** -/
theorem not_hasSLRelativeSchubertFiltration
    (hneg : 2 < ((P.p : ℤ) - 2) * ((P.q : ℤ) - 2)) :
    ¬ HasSLRelativeSchubertFiltration (familyTensor P) := by
  intro hF'
  obtain ⟨F, hF⟩ := hF'
  have hfin : ∀ ν : Fin P.rank → ℤ, FiniteDimensional ℂ
      (minimalRelativeSchubertSubrep ν).toSubmodule :=
    fun ν => ((SectionRep.isRationalBorelRep_dualJoseph ν).subrepresentation _).finiteDimensional
  obtain ⟨d, hd⟩ := familyTensor_hasCentralCharacter (P := P)
  exact not_atomPositive P hneg <| atomPositive_of_borelSL_filtration
    (fun ν => minimalRelativeSchubert ν) (fun ν => ∑ i, fibreWeight ν i)
    (fun ν => hasCentralCharacter_minimalRelativeSchubert ν)
    (fun ν => isShiftedAtomSum_ch_minimalRelativeSchubert ν)
    (isRationalBorelRep_familyTensor) hd F hF (ch_familyTensor)

/-- **Corollary 1.2 over `SL_n`, Schubert filtrations in Polo's sense.** -/
theorem not_hasSLSchubertFiltration
    (hneg : 2 < ((P.p : ℤ) - 2) * ((P.q : ℤ) - 2)) :
    ¬ HasSLSchubertFiltration (familyTensor P) := by
  intro hF'
  obtain ⟨F, hF⟩ := hF'
  have hfin : ∀ k : SchubertLayerIndex P.rank,
      FiniteDimensional ℂ (sectionSubrep k.1.2 k.1.1).toSubmodule :=
    fun k => finiteDimensional_sectionRep_of_isAntidominant k.2.2.2 k.2.1
  obtain ⟨d, hd⟩ := familyTensor_hasCentralCharacter (P := P)
  exact not_atomPositive P hneg <| atomPositive_of_borelSL_filtration
    (fun k : SchubertLayerIndex P.rank => sectionRep k.1.2 k.1.1) (fun k => ∑ i, k.1.1 i)
    (fun k => hasCentralCharacter_sectionRep _ _)
    (fun k => isShiftedAtomSum_ch_sectionRep k.2.2.2 k.2.1)
    (isRationalBorelRep_familyTensor) hd F hF (ch_familyTensor)

/-- The family lives in type `A_{4(p+q)−5}`. -/
theorem rank_sub_one : P.rank - 1 = 4 * (P.p + P.q) - 5 := by
  have hp := P.p_pos
  have hq := P.q_pos
  unfold Parameters.rank Parameters.m
  omega

/-- **Corollary 1.2 in type `A₂₇`.** For `(p, q) = (3, 5)` and every scale `δ ≥ 8`, the module
`P(−a) ⊗ P(−b)` lives in type `A₂₇` and admits neither a relative Schubert filtration nor a
Schubert filtration in Polo's sense, over `GL₂₈` or over `SL₂₈`. -/
theorem typeA27_filtration_failure (δ : ℕ) (hδ : 8 ≤ δ) :
    (threeFive δ hδ).rank - 1 = 27 ∧
      ¬ HasRelativeSchubertFiltration (familyTensor (threeFive δ hδ)) ∧
      ¬ HasSchubertFiltration (familyTensor (threeFive δ hδ)) ∧
      ¬ HasSLRelativeSchubertFiltration (familyTensor (threeFive δ hδ)) ∧
      ¬ HasSLSchubertFiltration (familyTensor (threeFive δ hδ)) := by
  have hneg : 2 < (((threeFive δ hδ).p : ℕ) - 2 : ℤ) * (((threeFive δ hδ).q : ℕ) - 2 : ℤ) := by
    simp [threeFive]
  exact ⟨by rw [threeFive_rank], not_hasRelativeSchubertFiltration hneg,
    not_hasSchubertFiltration hneg, not_hasSLRelativeSchubertFiltration hneg,
    not_hasSLSchubertFiltration hneg⟩

end

end Schubert.RS.Geometric
