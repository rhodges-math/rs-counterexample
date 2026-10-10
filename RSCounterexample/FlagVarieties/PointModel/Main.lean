import RSCounterexample.FlagVarieties.PointModel.SectionBasis
import RSCounterexample.FlagVarieties.PointModel.ClosureRelation

/-!
# Projective normality over an arbitrary field

Namespace `FlagVarieties.PointModel`: the ring-theoretic proof of projective normality
over a field `K`.

* The proof uses, about the flag-minor algebra over `K`, only the bundle `StandardMonomialTheory K`
  (`VanishingIdeals`): the Demazure library's dimension count
  `dim (I_S^A ∩ A_h) + #chainSet h S = dim A_h` and the closure relation on `A_h`. With it, and with
  `K` algebraically closed, `schubertUnion_normality` (`ProjectiveNormality`), the section spaces
  (`Sections`), Borel–Weil (`BorelWeil`) and the closure relation in `𝒪(GL_n)` (`ClosureRelation`)
  hold as over `ℂ`.
* `standardMonomialTheory_complex` (`ComplexComparison`): `StandardMonomialTheory ℂ`, from the
  Demazure library.
* `PointModel.StandardMonomialTheory.transfer` (`Transfer`, `RankTransfer`): the inputs pass between
  fields of characteristic `0` (rational coordinates and rank invariance).
* Hence, for `K` algebraically closed of characteristic `0`:
  `schubertUnion_normality_charZero` (**projective normality**), and the standard-monomial basis of
  the sections `sectionBasis` with its torus weights `evalAt_diagonal_mul_colProd` (the characters).

`Γ(X_w, 𝒪) = K` (`GlobalSectionsConstant K w`) is an explicit hypothesis throughout (the
suffix `_of_globalSectionsConstant`); `Normality/Unconditional` gives the hypothesis-free forms
under the plain names.
-/
