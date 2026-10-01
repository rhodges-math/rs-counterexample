import Schubert.RS.Family.Extras
import Schubert.RS.Filtrations.SpecialLinear

/-!
# Corollary 1.2: no relative Schubert filtrations and no Schubert filtrations

For the family of Theorem 1.1, let `P(−a) ⊗ P(−b)` be the tensor product of the dual Joseph
modules (`familyTensor`). Its character is `κ_a κ_b` (`familyTensor_hasCharacter`). Each factor
has an excellent filtration, namely the one-step filtration (`factors_hasExcellentFiltration`).

Corollary 1.2 (`cor:intro-filtrations`) says that in the negative range `(p − 2)(q − 2) > 2`,
the module `P(−a) ⊗ P(−b)`

* does not admit a relative Schubert filtration (`not_hasRelativeSchubertFiltration`);
* does not admit a Schubert filtration in Polo's sense, with layers from unions of Schubert
  varieties (`not_hasSchubertFiltration`);
* and the same holds over `SL_n` (`not_hasSLRelativeSchubertFiltration`,
  `not_hasSLSchubertFiltration`).

The family lives in type `A_{4(p+q)−5}` (`rank_sub_one`). The member `(p, q) = (3, 5)` gives
both failures already in type `A₂₇` (`typeA27_filtration_failure`).

The proof is the paper's. Such a filtration would make `κ_a κ_b` a nonnegative integral
combination of Demazure atoms (`Filtrations.atomPositive_of_hasRelativeSchubertFiltration` and
its variants), contradicting Theorem 1.1 (`not_atomPositive`).
-/

namespace Schubert.RS.Family

open Representation BModules Filtrations

noncomputable section

/-- The tensor product `P(−a) ⊗ P(−b)` of the dual Joseph modules of the family. -/
def familyTensor (P : Parameters) : BModule P.rank :=
  (dualJoseph (negComposition (a P))).tensor (dualJoseph (negComposition (b P)))

/-- `ch (P(−a) ⊗ P(−b)) = κ_a κ_b`. -/
theorem familyTensor_hasCharacter (P : Parameters) :
    (familyTensor P).HasCharacter (toLaurent (key (a P) * key (b P))) := by
  rw [map_mul]
  exact (dualJoseph_hasCharacter (a P)).tensor (dualJoseph_hasCharacter (b P))

/-- Scalar matrices act on `P(−a) ⊗ P(−b)` through a single character. -/
theorem familyTensor_hasCentralCharacter (P : Parameters) :
    ∃ d, (familyTensor P).HasCentralCharacter d := by
  obtain ⟨d, hd⟩ := dualJoseph_hasCentralCharacter (negComposition (a P))
  obtain ⟨e, he⟩ := dualJoseph_hasCentralCharacter (negComposition (b P))
  exact ⟨d + e, hd.tensor he⟩

/-- Each factor `P(−a)`, `P(−b)` has an excellent filtration (lines 280–283). -/
theorem factors_hasExcellentFiltration (P : Parameters) :
    HasExcellentFiltration (dualJoseph (negComposition (a P))) ∧
      HasExcellentFiltration (dualJoseph (negComposition (b P))) :=
  ⟨hasExcellentFiltration_dualJoseph _, hasExcellentFiltration_dualJoseph _⟩

/-- **Corollary 1.2, relative Schubert filtrations.** For `(p − 2)(q − 2) > 2`, the `B`-module
`P(−a) ⊗ P(−b)` does not admit a relative Schubert filtration: there is no filtration by
`B`-submodules whose layers are minimal relative Schubert modules `Q(ν)`. -/
theorem not_hasRelativeSchubertFiltration (P : Parameters)
    (hneg : 2 < ((P.p : ℤ) - 2) * ((P.q : ℤ) - 2)) :
    ¬ HasRelativeSchubertFiltration (familyTensor P) := fun hF =>
  not_atomPositive P hneg
    (atomPositive_of_hasRelativeSchubertFiltration (familyTensor_hasCharacter P) hF)

/-- **Corollary 1.2, Schubert filtrations in Polo's sense.** For `(p − 2)(q − 2) > 2`, the
`B`-module `P(−a) ⊗ P(−b)` does not admit a Schubert filtration in Polo's sense (layers from
unions): there is no filtration by `B`-submodules whose layers are section modules
`H⁰(X_S, 𝓛(η))` over unions `X_S` of Schubert varieties, for antidominant `η`. -/
theorem not_hasSchubertFiltration (P : Parameters)
    (hneg : 2 < ((P.p : ℤ) - 2) * ((P.q : ℤ) - 2)) :
    ¬ HasSchubertFiltration (familyTensor P) := fun hF =>
  not_atomPositive P hneg (atomPositive_of_hasSchubertFiltration (familyTensor_hasCharacter P) hF)

/-- **Corollary 1.2 over `SL_n`, relative Schubert filtrations.** For `(p − 2)(q − 2) > 2`, the
restriction of `P(−a) ⊗ P(−b)` to the Borel subgroup of `SL_n` does not admit a relative Schubert
filtration. -/
theorem not_hasSLRelativeSchubertFiltration (P : Parameters)
    (hneg : 2 < ((P.p : ℤ) - 2) * ((P.q : ℤ) - 2)) :
    ¬ HasSLRelativeSchubertFiltration (familyTensor P) := fun hF => by
  obtain ⟨d, hd⟩ := familyTensor_hasCentralCharacter P
  exact not_atomPositive P hneg
    (atomPositive_of_hasSLRelativeSchubertFiltration (familyTensor_hasCharacter P) hd hF)

/-- **Corollary 1.2 over `SL_n`, Schubert filtrations in Polo's sense.** For
`(p − 2)(q − 2) > 2`, the restriction of `P(−a) ⊗ P(−b)` to the Borel subgroup of `SL_n` does
not admit a Schubert filtration in Polo's sense (layers from unions). -/
theorem not_hasSLSchubertFiltration (P : Parameters)
    (hneg : 2 < ((P.p : ℤ) - 2) * ((P.q : ℤ) - 2)) :
    ¬ HasSLSchubertFiltration (familyTensor P) := fun hF => by
  obtain ⟨d, hd⟩ := familyTensor_hasCentralCharacter P
  exact not_atomPositive P hneg
    (atomPositive_of_hasSLSchubertFiltration (familyTensor_hasCharacter P) hd hF)

/-- The family lives in type `A_{4(p+q)−5}`: `n − 1 = 4(p + q) − 5` for `n = 4(p + q − 1)`. -/
theorem rank_sub_one (P : Parameters) : P.rank - 1 = 4 * (P.p + P.q) - 5 := by
  have hp := P.p_pos
  have hq := P.q_pos
  rw [Parameters.rank_eq]
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
  exact ⟨by rw [threeFive_rank], not_hasRelativeSchubertFiltration _ hneg,
    not_hasSchubertFiltration _ hneg, not_hasSLRelativeSchubertFiltration _ hneg,
    not_hasSLSchubertFiltration _ hneg⟩

end

end Schubert.RS.Family
