import RSCounterexample.FlagVarieties.PointModel.Complex.Basic
import RSCounterexample.GLRep.Borel.Main
import RSCounterexample.FlagVarieties.Modules.Weights

/-!
# Section modules over Schubert unions: the ring model as representations of `B`

Over `ℂ`, the preimage in `GL_n` of the union `X_S` of the Schubert varieties `X_w`, `w ∈ S`, is
(for a Bruhat ideal `S`, on points) the union `orbitSet S = ⋃_{w ∈ S} B ẇ B`
(`FlagVarieties.PointModel.Complex.orbitSet`); its ideal in `𝒪(GL_n)` is `orbitIdeal S`. In the ring
model, the sections of `𝓛(η)` over `X_S` are the `(B, η)`-semi-invariants of `𝒪(GL_n)/I_S`, on
which `B` acts by left translation (`FlagVarieties.SectionRep.sectionRep S η`, built on
`GLRep.borelSemiInvariantRep`). `FlagVarieties.sectionsEquivSemiInvariants` identifies them linearly
with the sheaf sections
`H⁰(X_S, 𝓛(η))`; the representation of `B` on the latter is transported along it.

The conventions are those of `RSCounterexample.FlagVarieties.Modules.Character`: `f(g b) = η(b)⁻¹ f(g)`,
`(b · f)(g) = f(b⁻¹ g)`. The predicate `PointModel.Complex.IsSemiInvOn Z η t` (`t(g b) = η(b) t(g)`)
is the weight `−η` here.

## Main definitions

* `FlagVarieties.SectionRep.sectionRep S η`: `H⁰(X_S, 𝓛(η))` as a representation of `B`;
  `FlagVarieties.SectionRep.sectionRestrict`: restriction to a smaller union.
* `FlagVarieties.SectionRep.dualJoseph ν`: the dual Joseph module `P(ν) = H⁰(X_σ, 𝓛(η))`, with
  `σ = σ(ν)` the Schubert index and `η = η(ν)` the fibre weight [van der Kallen, Def. 2.3.2].
* `FlagVarieties.SectionRep.minimalRelativeSchubert ν`: the minimal relative Schubert module
  `Q(ν) = ker (P(ν) → H⁰(∂X_σ, 𝓛(η)))` [van der Kallen, Def. 2.3.4], `∂X_σ = ⋃_{τ < σ} X_τ`.

## Main results

* `FlagVarieties.orbitIdeal_eq_vanishingIdeal`: the orbit ideals of the pointwise model are
  vanishing ideals.
* `FlagVarieties.SectionRep.hasCentralCharacter_sectionRep`: scalar matrices act on
  `H⁰(X_S, 𝓛(η))` by `c^{η₁ + ⋯ + ηₙ}`.
-/

open Schubert GLRep

namespace FlagVarieties

open PointModel.Complex

noncomputable section

variable {n : ℕ}

/-! ### The ring model of `PointModel.Complex` in terms of `GLRep` -/

theorem isBorel_iff_mem_borel {b : GL (Fin n) ℂ} : IsBorel b ↔ b ∈ borel ℂ n :=
  Iff.rfl

theorem orbitIdeal_eq_vanishingIdeal (S : Finset (Equiv.Perm (Fin n))) :
    orbitIdeal S = vanishingIdeal (orbitSet S) := by
  ext t
  exact Iff.rfl

theorem borel_mul_mem_orbitSet {S : Finset (Equiv.Perm (Fin n))} {g b : GL (Fin n) ℂ}
    (hg : g ∈ orbitSet S) (hb : b ∈ borel ℂ n) : b * g ∈ orbitSet S := by
  obtain ⟨w, hw, b₁, b₂, h₁, h₂, rfl⟩ := mem_orbitSet.mp hg
  exact mem_orbitSet.mpr ⟨w, hw, b * b₁, b₂, IsBorel.mul hb h₁, h₂, by simp only [mul_assoc]⟩

theorem isLeftBorelStable_orbitIdeal (S : Finset (Equiv.Perm (Fin n))) :
    IsLeftBorelStable (orbitIdeal S) := by
  rw [orbitIdeal_eq_vanishingIdeal]
  exact isLeftBorelStable_vanishingIdeal fun g hg b hb => borel_mul_mem_orbitSet hg hb

theorem isRightBorelStable_orbitIdeal (S : Finset (Equiv.Perm (Fin n))) :
    IsRightBorelStable (orbitIdeal S) := by
  rw [orbitIdeal_eq_vanishingIdeal]
  exact isRightBorelStable_vanishingIdeal fun g hg b hb => orbitSet_mul_borel hg hb

theorem orbitIdeal_antitone {S S' : Finset (Equiv.Perm (Fin n))} (h : S' ⊆ S) :
    orbitIdeal S ≤ orbitIdeal S' := fun _ ht g hg => ht g (orbitSet_mono h hg)

namespace SectionRep

/-! ### Sections as representations of `B` -/

/-- The sections of `𝓛(η)` over the Schubert union `X_S` in the ring model: the
`(B, η)`-semi-invariants of `𝒪(GL_n)/I_S`, a subrepresentation of left translation. -/
abbrev sectionSubrep (S : Finset (Equiv.Perm (Fin n))) (η : Fin n → ℤ) :
    Subrepresentation (quotLeftRep (orbitIdeal S) (isLeftBorelStable_orbitIdeal S)) :=
  borelSemiInvariantSubrep _ (isLeftBorelStable_orbitIdeal S) (isRightBorelStable_orbitIdeal S) η

/-- The spaces of sections are additive groups (a shortcut instance: the generic search through
the nested subtypes is slow). -/
instance (S : Finset (Equiv.Perm (Fin n))) (η : Fin n → ℤ) :
    AddCommGroup (sectionSubrep S η).toSubmodule :=
  Submodule.addCommGroup _

/-- **`H⁰(X_S, 𝓛(η))` as a representation of `B`** (ring model). -/
abbrev sectionRep (S : Finset (Equiv.Perm (Fin n))) (η : Fin n → ℤ) :
    Representation ℂ (borel ℂ n) (sectionSubrep S η).toSubmodule :=
  (sectionSubrep S η).toRepresentation

theorem mk_mem_sectionSubrep_iff (S : Finset (Equiv.Perm (Fin n))) (η : Fin n → ℤ)
    (t : GLCoord ℂ n) :
    Ideal.Quotient.mk _ t ∈ (sectionSubrep S η).toSubmodule ↔
      ∀ g ∈ orbitSet S, ∀ b : borel ℂ n,
        glEval (g * (b : GL (Fin n) ℂ)) t = (((borelChar ℂ n η b)⁻¹ : ℂˣ) : ℂ) * glEval g t := by
  change Ideal.Quotient.mk _ t ∈ borelSemiInvariants (orbitIdeal S) _ η ↔ _
  rw [mem_borelSemiInvariants]
  have key : ∀ b : borel ℂ n,
      quotRightTranslHom (orbitIdeal S) (isRightBorelStable_orbitIdeal S) b
          (Ideal.Quotient.mk _ t) =
          (((borelChar ℂ n η b)⁻¹ : ℂˣ) : ℂ) • Ideal.Quotient.mk (orbitIdeal S) t ↔
        ∀ g ∈ orbitSet S, glEval (g * (b : GL (Fin n) ℂ)) t =
          (((borelChar ℂ n η b)⁻¹ : ℂˣ) : ℂ) * glEval g t := by
    intro b
    change Ideal.Quotient.mk _ (rightTranslHom ℂ n b t) = _ ↔ _
    rw [← Ideal.Quotient.mkₐ_eq_mk ℂ, ← map_smul, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq,
      mem_orbitIdeal]
    refine forall₂_congr fun g _ => ?_
    rw [map_sub, glEval_rightTranslHom, map_smul, smul_eq_mul, sub_eq_zero]
  simp only [key]
  exact ⟨fun h g hg b => h b g hg, fun h b g hg => h g hg b⟩

/-- Restriction of sections from `X_S` to `X_{S'}`, `S' ⊆ S`, a map of representations of `B`. -/
def sectionRestrict {S S' : Finset (Equiv.Perm (Fin n))} (h : S' ⊆ S) (η : Fin n → ℤ) :
    (sectionRep S η).IntertwiningMap (sectionRep S' η) :=
  borelSemiInvariantRestrict (orbitIdeal_antitone h) _ _ _ _ η

/-- Scalar matrices `c·1` act on `H⁰(X_S, 𝓛(η))` by `c^{η₁ + ⋯ + ηₙ}`. -/
theorem hasCentralCharacter_sectionRep (S : Finset (Equiv.Perm (Fin n))) (η : Fin n → ℤ) :
    HasCentralCharacter (sectionRep S η) (∑ i, η i) :=
  hasCentralCharacter_borelSemiInvariantRep _ _ _ η

/-! ### Dual Joseph modules and minimal relative Schubert modules -/

/-- The Schubert boundary `{τ | τ < σ}`. -/
def boundarySet (σ : Equiv.Perm (Fin n)) : Finset (Equiv.Perm (Fin n)) := by
  classical exact Finset.univ.filter fun τ => τ <ᴮ σ

theorem mem_boundarySet {σ τ : Equiv.Perm (Fin n)} : τ ∈ boundarySet σ ↔ τ <ᴮ σ := by
  classical
  unfold boundarySet
  simp

theorem boundarySet_subset_lowerSet (σ : Equiv.Perm (Fin n)) : boundarySet σ ⊆ lowerSet σ :=
  fun _ hτ => mem_lowerSet.mpr (mem_boundarySet.mp hτ).1

/-- The **dual Joseph module** `P(ν) = H⁰(X_σ, 𝓛(η))`, `σ = σ(ν)`, `η = η(ν)` (ring model). -/
abbrev dualJoseph (ν : Fin n → ℤ) :=
  sectionRep (lowerSet (schubertIndex ν)) (fibreWeight ν)

/-- The restriction `P(ν) → H⁰(∂X_σ, 𝓛(η))` to the Schubert boundary. -/
def boundaryRestrict (ν : Fin n → ℤ) :
    (dualJoseph ν).IntertwiningMap (sectionRep (boundarySet (schubertIndex ν)) (fibreWeight ν)) :=
  sectionRestrict (boundarySet_subset_lowerSet _) _

/-- The sections in `P(ν)` vanishing on the Schubert boundary. -/
abbrev minimalRelativeSchubertSubrep (ν : Fin n → ℤ) : Subrepresentation (dualJoseph ν) :=
  (boundaryRestrict ν).ker

/-- The **minimal relative Schubert module** `Q(ν) ⊆ P(ν)`: the kernel of the restriction
`P(ν) → H⁰(∂X_σ, 𝓛(η))` to the Schubert boundary (ring model). -/
abbrev minimalRelativeSchubert (ν : Fin n → ℤ) :
    Representation ℂ (borel ℂ n) (minimalRelativeSchubertSubrep ν).toSubmodule :=
  (minimalRelativeSchubertSubrep ν).toRepresentation

theorem mem_minimalRelativeSchubertSubrep {ν : Fin n → ℤ}
    {f : (sectionSubrep (lowerSet (schubertIndex ν))
    (fibreWeight ν)).toSubmodule} :
    f ∈ (minimalRelativeSchubertSubrep ν).toSubmodule ↔ boundaryRestrict ν f = 0 :=
  Iff.rfl

theorem hasCentralCharacter_dualJoseph (ν : Fin n → ℤ) :
    HasCentralCharacter (dualJoseph ν) (∑ i, fibreWeight ν i) :=
  hasCentralCharacter_sectionRep _ _

theorem hasCentralCharacter_minimalRelativeSchubert (ν : Fin n → ℤ) :
    HasCentralCharacter (minimalRelativeSchubert ν) (∑ i, fibreWeight ν i) :=
  (hasCentralCharacter_dualJoseph ν).subrepresentation _

end SectionRep

end

end FlagVarieties
