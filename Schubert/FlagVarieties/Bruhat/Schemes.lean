import Schubert.FlagVarieties.Bruhat.Cells
import Schubert.FlagVarieties.Normality.OrbitIdealComparison
import Schubert.FlagVarieties.Schubert.PreimageLattice

/-!
# Bruhat cells and Schubert varieties at the scheme level

The Schubert varieties `FlagVarieties.schubertVariety K n w` are ideal sheaves on `Fl_n`; their
preimages in `GL_n` have ideals `preimageIdeal K n (schubertVariety K n w)`. Two results are
used: `preimageIdeal_schubertVariety_eq_schubertOrbitIdeal`,
`preimageIdeal (X_w) = schubertOrbitIdeal w`, and descent (`le_of_preimageIdeal_le`): the preimage
reflects inclusions of ideal sheaves.

Results, over a field of characteristic `0`:

* `preimageIdeal_le_monotone`: the preimage is monotone.
* `mem_zeroLocus_preimageIdeal_iff`: the `K`-points of `π⁻¹(X_w)` are
  `⊔_{v ≤ w} B v̇ B`, a disjoint union (`eq_of_mem_bruhatCell`): **`X_w(K) = ⊔_{v ≤ w} C_v(K)`** on
  `GL_n`.
* `le_of_schubertVariety_le`: `X_v ⊆ X_w → v ≤ w`; `schubertVariety_le_iff`:
  **`X_v ⊆ X_w ⟺ v ≤ w`**.
-/

open Schubert Demazure.FlagModule Demazure.SchubertUnions FinPermutation
open GLRep (glEval)

namespace FlagVarieties.PointModel

noncomputable section

variable {K : Type*} [Field K] {n : ℕ}

/-- The preimage is monotone. -/
theorem preimageIdeal_le_monotone {I J : (FlagVarieties.FlagScheme K n).IdealSheafData}
    (h : I ≤ J) : FlagVarieties.preimageIdeal K n I ≤ FlagVarieties.preimageIdeal K n J :=
  Ideal.comap_mono
    ((AlgebraicGeometry.Scheme.IdealSheafData.le_def.mp
      (AlgebraicGeometry.Scheme.IdealSheafData.comap_mono _ h)) _)

/-- **`X_w(K) = ⊔_{v ≤ w} C_v(K)`** on `GL_n` (by
`preimageIdeal_schubertVariety_eq_schubertOrbitIdeal`): the `K`-points
of the scheme-theoretic preimage `π⁻¹(X_w)` are the union of the cells `B v̇ B`, `v ≤ w`. -/
theorem mem_zeroLocus_preimageIdeal_iff [CharZero K] (w : Equiv.Perm (Fin n)) (g : GL (Fin n) K) :
    (∀ t ∈ FlagVarieties.preimageIdeal K n (FlagVarieties.schubertVariety K n w), glEval g t = 0) ↔
      ∃ v, v ≤ᴮ w ∧ g ∈ bruhatCell K v := by
  have : Infinite K := Infinite.of_injective (Nat.cast : ℕ → K) Nat.cast_injective
  rw [FlagVarieties.preimageIdeal_schubertVariety_eq_schubertOrbitIdeal K n w,
      schubertOrbitIdeal_eq_cellIdeal]
  exact forall_cellIdeal_iff (standardMonomialTheory_of_charZero K) w g

/-- The preimages of Schubert varieties compare like the Bruhat order. -/
theorem preimageIdeal_schubertVariety_le_iff [CharZero K] {v w : Equiv.Perm (Fin n)} :
    FlagVarieties.preimageIdeal K n (FlagVarieties.schubertVariety K n w) ≤
        FlagVarieties.preimageIdeal K n (FlagVarieties.schubertVariety K n v) ↔ v ≤ᴮ w := by
  have : Infinite K := Infinite.of_injective (Nat.cast : ℕ → K) Nat.cast_injective
  rw [FlagVarieties.preimageIdeal_schubertVariety_eq_schubertOrbitIdeal K n w,
    FlagVarieties.preimageIdeal_schubertVariety_eq_schubertOrbitIdeal K n v,
        schubertOrbitIdeal_eq_cellIdeal,
    schubertOrbitIdeal_eq_cellIdeal]
  exact cellIdeal_le_cellIdeal_iff (standardMonomialTheory_of_charZero K)

/-- `X_v ⊆ X_w → v ≤ w`. -/
theorem le_of_schubertVariety_le [CharZero K] {v w : Equiv.Perm (Fin n)}
    (h : FlagVarieties.schubertVariety K n w ≤ FlagVarieties.schubertVariety K n v) : v ≤ᴮ w :=
  preimageIdeal_schubertVariety_le_iff.mp (preimageIdeal_le_monotone h)

/-- **`X_v ⊆ X_w ⟺ v ≤ w`** for the scheme-level Schubert varieties. -/
theorem schubertVariety_le_iff [CharZero K] {v w : Equiv.Perm (Fin n)} :
    FlagVarieties.schubertVariety K n w ≤ FlagVarieties.schubertVariety K n v ↔ v ≤ᴮ w :=
  ⟨le_of_schubertVariety_le, fun h =>
    le_of_preimageIdeal_le K n _ _ (preimageIdeal_schubertVariety_le_iff.mpr h)⟩

end

end FlagVarieties.PointModel
