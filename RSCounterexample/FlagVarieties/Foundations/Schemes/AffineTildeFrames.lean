import RSCounterexample.FlagVarieties.Foundations.Schemes.AffineTildeTensor
import Mathlib.RingTheory.Grassmannian
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Principal local frames for finite projective associated sheaves

Rank-one frames are derived from finite projectivity and the stalk rank at
the chosen prime. They are frames of sections of the associated
sheaf on a principal neighborhood; no global frame is constructed.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientPair

open AlgebraicGeometry CategoryTheory TensorProduct

universe u

variable {R : CommRingCat.{u}} (M : ModuleCat.{u} R)

/-- Transport a localization frame to sections by the localization universal property. -/
def principalSectionFrame (f : R)
    (frame : LocalizedModule.Away f M ≃ₗ[Localization.Away f] Localization.Away f) :
    PrincipalSections M f ≃ₗ[PrincipalRing f] PrincipalRing f :=
  (((IsLocalizedModule.iso (Submonoid.powers f) (principalToSections M f)).symm ≪≫ₗ
      frame.restrictScalars R) ≪≫ₗ
    (IsLocalization.algEquiv (Submonoid.powers f) (Localization.Away f)
      (PrincipalRing f)).toLinearEquiv).extendScalarsOfIsLocalization
        (Submonoid.powers f) (PrincipalRing f)

/-- Every prime where a finite projective module has rank one has a principal section frame. -/
theorem exists_principal_section_frame [Module.Finite R M] [Module.Projective R M]
    (p : PrimeSpectrum R) (hrank : Module.rankAtStalk M p = 1) :
    ∃ f : R, f ∉ p.asIdeal ∧
      Nonempty (PrincipalSections M f ≃ₗ[PrincipalRing f] PrincipalRing f) := by
  let : Module.FinitePresentation R M := Module.finitePresentation_of_projective R M
  let : Module.Free (Localization.AtPrime p.asIdeal)
      (LocalizedModule p.asIdeal.primeCompl M) := Module.free_of_flat_of_isLocalRing
  obtain ⟨f, hf, hfree, hdim⟩ :=
    Module.FinitePresentation.exists_free_localizedModule_powers p.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M) (Localization.AtPrime p.asIdeal)
  let := hfree
  let toPrime : Localization.Away f →+* Localization.AtPrime p.asIdeal :=
    IsLocalization.map (M := Submonoid.powers f) (T := p.asIdeal.primeCompl) _
      (RingHom.id _) (Submonoid.powers_le.mpr hf)
  let : Nontrivial (Localization.Away f) := toPrime.domain_nontrivial
  have hdim' : Module.finrank (Localization.Away f) (LocalizedModule.Away f M) = 1 :=
    hdim.trans hrank
  obtain ⟨frame⟩ := Module.nonempty_linearEquiv_of_finrank_eq_one hdim'
  exact ⟨f, hf, ⟨principalSectionFrame M f frame.symm⟩⟩

/-- A Grassmannian quotient of rank one supplies the hypotheses automatically. -/
theorem exists_principal_quotient_frame (K : Module.Grassmannian R M 1)
    (p : PrimeSpectrum R) :
    ∃ f : R, f ∉ p.asIdeal ∧
      Nonempty (PrincipalSections (ModuleCat.of R (M ⧸ K.toSubmodule)) f ≃ₗ[PrincipalRing f]
        PrincipalRing f) :=
  exists_principal_section_frame (ModuleCat.of R (M ⧸ K.toSubmodule)) p (K.rankAtStalk_eq p)

end FlagVarieties.Foundations.QuotientPair

