import Schubert.FlagVarieties.Modules.JosephCharacter

/-!
# Excellent, relative Schubert and Schubert filtrations

A filtration of a representation of `B` is a finite chain `0 = F₀ ≤ F₁ ≤ ⋯ ≤ F_r = M` of
subrepresentations (`GLRep.RepFiltration`); its layers are the successive quotients.

* An **excellent filtration** has layers equivalent to dual Joseph modules `P(ν)` [Polo 1989,
  1.5; van der Kallen 1993] (`FlagVarieties.SectionRep.HasExcellentFiltration`).
* A **relative Schubert filtration** has layers equivalent to minimal relative Schubert modules
  `Q(ν)` [van der Kallen 1993] (`FlagVarieties.SectionRep.HasRelativeSchubertFiltration`).
* A **Schubert filtration in Polo's sense** has layers equivalent to section modules
  `H⁰(X_S, 𝓛(η))` over nonempty unions of Schubert varieties, `S` a Bruhat ideal, `η`
  antidominant [Polo 1989, 2.8] (`FlagVarieties.SectionRep.HasSchubertFiltration`).

The `SL_n` forms ask for a filtration of the restriction to `B_SL = B ∩ SL_n` whose layers are
equivalent, over `B_SL`, to restrictions of the same modules.

The modules are those of the ring model (`Schubert.FlagVarieties.Modules.RingModel`); since the
notions only depend on the layers up to equivalence, they agree with the notions for the sheaf
sections through `FlagVarieties.sectionsEquivSemiInvariants`, which identifies the two models.
-/

universe u

open Schubert GLRep Demazure Demazure.SchubertUnions FinPermutation

namespace FlagVarieties.SectionRep

open PointModel.Complex

noncomputable section

variable {n : ℕ}

/-! ### Layers -/

/-- `L` is equivalent to a dual Joseph module `P(ν)`. -/
def IsDualJosephLayer (V : Type u) [AddCommGroup V] [Module ℂ V]
    (L : Representation ℂ (borel ℂ n) V) : Prop :=
  ∃ ν : Fin n → ℤ, Nonempty (L.Equiv (dualJoseph ν))

/-- `L` is equivalent to a minimal relative Schubert module `Q(ν)`. -/
def IsMinimalRelativeSchubertLayer (V : Type u) [AddCommGroup V] [Module ℂ V]
    (L : Representation ℂ (borel ℂ n) V) : Prop :=
  ∃ ν : Fin n → ℤ, Nonempty (L.Equiv (minimalRelativeSchubert ν))

/-- The data `(η, S)` of a section module over a nonempty Schubert union: `η` antidominant, `S` a
nonempty Bruhat ideal. -/
abbrev SchubertLayerIndex (n : ℕ) :=
  {p : (Fin n → ℤ) × Finset (Equiv.Perm (Fin n)) //
    IsAntidominant p.1 ∧ p.2.Nonempty ∧ BruhatLower p.2}

/-- `L` is equivalent to a section module `H⁰(X_S, 𝓛(η))` over a nonempty Schubert union
(`S` a Bruhat ideal), for an antidominant weight `η`. -/
def IsSchubertLayer (V : Type u) [AddCommGroup V] [Module ℂ V]
    (L : Representation ℂ (borel ℂ n) V) : Prop :=
  ∃ k : SchubertLayerIndex n, Nonempty (L.Equiv (sectionRep k.1.2 k.1.1))

/-- `L` is equivalent over `B_SL` to the restriction of some `Q(ν)`. -/
def IsSLMinimalRelativeSchubertLayer (V : Type u) [AddCommGroup V] [Module ℂ V]
    (L : Representation ℂ (borelSL ℂ n) V) : Prop :=
  ∃ ν : Fin n → ℤ, Nonempty (L.Equiv ((minimalRelativeSchubert ν).comp (borelSL ℂ n).subtype))

/-- `L` is equivalent over `B_SL` to the restriction of a section module over a nonempty
Schubert union, for an antidominant weight. -/
def IsSLSchubertLayer (V : Type u) [AddCommGroup V] [Module ℂ V]
    (L : Representation ℂ (borelSL ℂ n) V) : Prop :=
  ∃ k : SchubertLayerIndex n,
    Nonempty (L.Equiv ((sectionRep k.1.2 k.1.1).comp (borelSL ℂ n).subtype))

/-! ### Filtrations -/

variable {W : Type u} [AddCommGroup W] [Module ℂ W]

/-- `ρ` admits an **excellent filtration**: its layers are dual Joseph modules. -/
def HasExcellentFiltration (ρ : Representation ℂ (borel ℂ n) W) : Prop :=
  HasFiltrationBy IsDualJosephLayer ρ

/-- `ρ` admits a **relative Schubert filtration**: its layers are minimal relative Schubert
modules `Q(ν)`. -/
def HasRelativeSchubertFiltration (ρ : Representation ℂ (borel ℂ n) W) : Prop :=
  HasFiltrationBy IsMinimalRelativeSchubertLayer ρ

/-- `ρ` admits a **Schubert filtration in Polo's sense**: its layers are section modules over
nonempty unions of Schubert varieties, for antidominant weights. -/
def HasSchubertFiltration (ρ : Representation ℂ (borel ℂ n) W) : Prop :=
  HasFiltrationBy IsSchubertLayer ρ

/-- The `SL_n` form: the restriction of `ρ` to `B_SL` has a filtration whose layers are
equivalent over `B_SL` to minimal relative Schubert modules. -/
def HasSLRelativeSchubertFiltration (ρ : Representation ℂ (borel ℂ n) W) : Prop :=
  HasFiltrationBy IsSLMinimalRelativeSchubertLayer (ρ.comp (borelSL ℂ n).subtype)

/-- The `SL_n` form of Polo's Schubert filtrations. -/
def HasSLSchubertFiltration (ρ : Representation ℂ (borel ℂ n) W) : Prop :=
  HasFiltrationBy IsSLSchubertLayer (ρ.comp (borelSL ℂ n).subtype)

/-- A dual Joseph module has the one-step excellent filtration `0 ⊂ P(ν)`. -/
theorem hasExcellentFiltration_dualJoseph (ν : Fin n → ℤ) :
    HasExcellentFiltration (dualJoseph ν) :=
  hasFiltrationBy_single fun _ _ _ _ ⟨e⟩ => ⟨ν, ⟨e⟩⟩

/-- A minimal relative Schubert module has the one-step relative Schubert filtration. -/
theorem hasRelativeSchubertFiltration_minimalRelativeSchubert (ν : Fin n → ℤ) :
    HasRelativeSchubertFiltration (minimalRelativeSchubert ν) :=
  hasFiltrationBy_single fun _ _ _ _ ⟨e⟩ => ⟨ν, ⟨e⟩⟩

end

end FlagVarieties.SectionRep
