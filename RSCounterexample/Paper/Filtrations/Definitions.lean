import RSCounterexample.Paper.Filtrations.SectionModules

/-!
# Excellent, relative Schubert, and Schubert filtrations

A filtration of a `B`-module is a finite chain `0 = F₀ ≤ F₁ ≤ ⋯ ≤ F_r = M` of `B`-submodules
(`BFiltration`); its layers are the successive quotients `F_{i+1} / F_i`.

* An **excellent filtration** has layers isomorphic to dual Joseph modules `P(ν)`
  [Polo 1989, 1.5; van der Kallen 1993].
* A **relative Schubert filtration** has layers isomorphic to minimal relative Schubert modules
  `Q(ν)` [van der Kallen 1993].
* A **Schubert filtration in Polo's sense** has layers isomorphic to section modules
  `H⁰(X_S, 𝓛(η))` over unions of Schubert varieties `X_S = ⋃_{w ∈ S} X_w`, `S ≠ ∅`, for
  antidominant (weakly increasing) `η` [Polo 1989, 2.8]. Polo writes an increasing sequence of
  submodules with union `M`; for finite-dimensional `M` this is a finite chain.
-/

namespace Schubert.RS.Filtrations

open BModules FinPermutation

variable {n : ℕ}

/-- `L` is isomorphic to a dual Joseph module `P(ν)`. -/
def IsDualJosephLayer (L : BModule n) : Prop := ∃ ν : Weight n, Nonempty (L ≃ᴮ dualJoseph ν)

/-- `L` is isomorphic to a minimal relative Schubert module `Q(ν)`. -/
def IsMinRelSchubertLayer (L : BModule n) : Prop :=
  ∃ ν : Weight n, Nonempty (L ≃ᴮ minRelSchubert ν)

/-- `L` is isomorphic to a section module `H⁰(X_S, 𝓛(η))` over a nonempty union of Schubert
varieties, for an antidominant weight `η`. -/
def IsSchubertLayer (L : BModule n) : Prop :=
  ∃ (η : Weight n) (S : Finset (FinPermutation n)), Monotone η ∧ S.Nonempty ∧
    Nonempty (L ≃ᴮ schubertSectionModule η S)

/-- `M` admits an excellent filtration: its layers are dual Joseph modules. -/
def HasExcellentFiltration (M : BModule n) : Prop := HasFiltrationBy IsDualJosephLayer M

/-- `M` admits a relative Schubert filtration: its layers are minimal relative Schubert
modules `Q(ν)`. -/
def HasRelativeSchubertFiltration (M : BModule n) : Prop :=
  HasFiltrationBy IsMinRelSchubertLayer M

/-- `M` admits a Schubert filtration in Polo's sense: its layers are section modules over
unions of Schubert varieties. -/
def HasSchubertFiltration (M : BModule n) : Prop := HasFiltrationBy IsSchubertLayer M

/-- A dual Joseph module has the one-step excellent filtration `0 ⊂ P(ν)`. -/
theorem hasExcellentFiltration_dualJoseph (ν : Weight n) :
    HasExcellentFiltration (dualJoseph ν) :=
  hasFiltrationBy_single fun _ ⟨e⟩ => ⟨ν, ⟨e⟩⟩

end Schubert.RS.Filtrations
