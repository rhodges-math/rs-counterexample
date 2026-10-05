import Schubert.FlagVarieties.Foundations.Schemes.QuotientFlagFamilyInitialAffine
import Schubert.FlagVarieties.Foundations.Schemes.QuotientFlagFamily
import Schubert.FlagVarieties.Foundations.Schemes.ModuleSheafOpenCoverEquality

/-!
# The equal-rank first quotient of a sheaf flag

The first quotient is an isomorphism, derived from the existing epi and
pointwise rank-`n` local frames. On each member of an affine open
cover, the quotient of affine sections is a surjection from `A^n` onto a
finite projective module of rank `n`, hence has zero kernel. Local
isomorphisms detect global monicity, and the original epi completes the
argument.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory
universe u

namespace QuotientFlagFamily

variable {X : Scheme.{u}} {n : ℕ} (F : QuotientFlagFamily X n)

/-- The first labelled quotient map is an isomorphism; this is not
an endpoint premise in `QuotientFlagFamily`. -/
theorem initial_quotient_isIso : IsIso (F.quotient 0) := by
  let M := F.target 0
  let q := F.quotient 0
  let : Epi q := F.quotient_epi 0
  have hfree : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Nonempty (M.over U ≅
        SheafOfModules.free (R := X.ringCatSheaf.over U) (CoordinateIndex.{u} n)) := by
    simpa [M] using F.local_frames (0 : Fin (n+1))
  have hlocal (i : X.affineOpenCover.I₀) :
      IsIso ((Scheme.Modules.pullback (X.affineOpenCover.f i)).map q) := by
    let f := X.affineOpenCover.f i
    have hi : IsIso (coordinatePullbackQuotient f q) :=
      coordinateFreeSheaf_epi_isIso_of_local_frames _ n _
        (FlagVarieties.Foundations.ModuleSheafGluing.coordinateLocalFrames_pullback f M n hfree)
    change IsIso ((Scheme.Modules.pullback f).map q)
    change IsIso ((coordinatePullbackFreeIso f n).inv ≫
      (Scheme.Modules.pullback f).map q) at hi
    letI : IsIso ((coordinatePullbackFreeIso f n).inv ≫
      (Scheme.Modules.pullback f).map q) := hi
    exact IsIso.of_isIso_comp_left (coordinatePullbackFreeIso f n).inv _
  haveI : Mono q := by
    constructor
    intro Z f g h
    apply FlagVarieties.Foundations.ModuleSheafGluing.hom_ext_of_pullbackCover
      X.affineOpenCover.openCover f g
    intro i
    have hi := congrArg
      (fun t => (Scheme.Modules.pullback (X.affineOpenCover.f i)).map t) h
    rw [Functor.map_comp, Functor.map_comp] at hi
    letI : IsIso ((Scheme.Modules.pullback (X.affineOpenCover.f i)).map q) := hlocal i
    exact (cancel_mono ((Scheme.Modules.pullback (X.affineOpenCover.f i)).map q)).mp hi
  exact isIso_of_mono_of_epi q

end QuotientFlagFamily
end FlagVarieties.Foundations.QuotientCharts
