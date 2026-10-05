import Mathlib.RingTheory.Grassmannian
import Mathlib.RingTheory.LocalProperties.FinitePresentation
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Flat.Localization

/-!
# Finite projective quotients from principal-local frames

Let `s : I → A` generate the unit ideal. Isomorphisms from the
localizations `A[s i⁻¹] ⊗[A] M` to the rank-`d` free modules imply that
`M` is finitely presented, flat, projective, and has stalk rank `d`.
Finite presentation and flatness descend along the tensor
localization maps; projectivity follows from these two derived properties.
For a prime of `A`, a member of the principal cover lifts it to a prime
of the corresponding localization, where the given frame computes rank.

Specializing to `M = (Fin n → A) / K` gives a Mathlib
`Module.Grassmannian` whose submodule is definitionally `K`. No global
basis, nontrivial-ring hypothesis, nonempty index type, or rank restriction
is assumed. In particular zero rings and rank zero are retained.

The local frames are intermediate geometric data; they are produced
from an incoming Grassmannian-chart morphism in
`Schemes/SelectedMorphismQuotient.lean`.
Finite projectivity and stalk rank are conclusions here, not input fields.
-/

noncomputable section

namespace FlagVarieties.Foundations.LocalQuotientProjectivity

open TensorProduct

variable {A : Type*} [CommRing A] {I : Type*}
  (M : Type*) [AddCommGroup M] [Module A M] {d : ℕ}
  (s : I → A) (hs : Ideal.span (Set.range s) = ⊤)
  (frame : ∀ i, Localization.Away (s i) ⊗[A] M ≃ₗ[Localization.Away (s i)]
    (Fin d → Localization.Away (s i)))

include hs frame

/-- Finite presentation is derived from the principal-local tensor frames. -/
theorem finitePresentation_of_principal_frames : Module.FinitePresentation A M := by
  apply Module.FinitePresentation.of_localizationSpan' (Set.range s) hs
    (Rₚ := fun g : Set.range s => Localization.Away g.val)
    (fun g : Set.range s => TensorProduct.mk A (Localization.Away g.val) M 1)
  rintro ⟨g, i, rfl⟩
  let := Module.Finite.equiv (frame i).symm
  let := Module.Projective.of_equiv (frame i).symm
  exact Module.finitePresentation_of_projective _ _

/-- The same localization maps descend flatness. -/
theorem flat_of_principal_frames : Module.Flat A M := by
  apply Module.flat_of_isLocalized_span (R := A) A M (Set.range s) hs
    (fun g : Set.range s => Localization.Away g.val ⊗[A] M)
    (fun g : Set.range s => TensorProduct.mk A (Localization.Away g.val) M 1)
  rintro ⟨g, i, rfl⟩
  let := IsLocalization.flat (Localization.Away (s i)) (Submonoid.powers (s i))
  let := Module.Projective.of_equiv (frame i).symm
  exact Module.Flat.trans A (Localization.Away (s i)) _

/-- Projectivity is a consequence of the descended finite presentation and flatness. -/
theorem projective_of_principal_frames : Module.Projective A M := by
  let := finitePresentation_of_principal_frames M s hs frame
  let := flat_of_principal_frames M s hs frame
  exact Module.Flat.projective_of_finitePresentation

theorem finite_of_principal_frames : Module.Finite A M := by
  let := finitePresentation_of_principal_frames M s hs frame
  infer_instance

/-- Stalk rank is computed on a principal neighborhood of each prime.
Only the existence of that prime supplies the local nontriviality instance. -/
theorem rankAtStalk_of_principal_frames (p : PrimeSpectrum A) :
    Module.rankAtStalk M p = d := by
  have hcover : (⨆ i, PrimeSpectrum.basicOpen (s i)) = ⊤ :=
    PrimeSpectrum.iSup_basicOpen_eq_top_iff.mpr hs
  have hp : p ∈ ⨆ i, PrimeSpectrum.basicOpen (s i) := by rw [hcover]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hp
  obtain ⟨p', hp'⟩ : p ∈ Set.range
      (PrimeSpectrum.comap (algebraMap A (Localization.Away (s i)))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away (s i)) (s i)]
    exact hi
  let := finite_of_principal_frames M s hs frame
  let := projective_of_principal_frames M s hs frame
  let : Nontrivial (Localization.Away (s i)) := p'.nontrivial
  rw [← hp', ← Module.rankAtStalk_baseChange, Module.rankAtStalk_eq_of_equiv (frame i),
    Module.rankAtStalk_pi (fun _ : Fin d => Localization.Away (s i)) p']
  simp [finsum_eq_sum_of_fintype]

/-- The complete locally free finite-rank consequence, with no projectivity
or global rank assertion among the hypotheses. -/
theorem finite_projective_rank_of_principal_frames :
    Module.Finite A M ∧ Module.Projective A M ∧ ∀ p : PrimeSpectrum A,
      Module.rankAtStalk M p = d :=
  ⟨finite_of_principal_frames M s hs frame, projective_of_principal_frames M s hs frame,
    rankAtStalk_of_principal_frames M s hs frame⟩

end FlagVarieties.Foundations.LocalQuotientProjectivity

namespace FlagVarieties.Foundations

open TensorProduct

variable {A : Type*} [CommRing A] {I : Type*} {n d : ℕ}
  (K : Submodule A (Fin n → A)) (s : I → A) (hs : Ideal.span (Set.range s) = ⊤)
  (frame : ∀ i, Localization.Away (s i) ⊗[A] ((Fin n → A) ⧸ K) ≃ₗ[Localization.Away (s i)]
    (Fin d → Localization.Away (s i)))

/-- Local quotient frames produce a Grassmannian point with
exactly the specified global submodule, not merely an isomorphic quotient. -/
def grassmannianOfPrincipalQuotientFrames : Module.Grassmannian A (Fin n → A) d where
  toSubmodule := K
  finite_quotient := LocalQuotientProjectivity.finite_of_principal_frames _ s hs frame
  projective_quotient := LocalQuotientProjectivity.projective_of_principal_frames _ s hs frame
  rankAtStalk_eq := LocalQuotientProjectivity.rankAtStalk_of_principal_frames _ s hs frame

@[simp] theorem grassmannianOfPrincipalQuotientFrames_submodule :
    (grassmannianOfPrincipalQuotientFrames K s hs frame).toSubmodule = K := rfl

/-- The resulting Grassmannian point is independent of the local cover and
frames, because its submodule is the given `K`. -/
theorem grassmannianOfPrincipalQuotientFrames_independent {J : Type*}
    (t : J → A) (ht : Ideal.span (Set.range t) = ⊤)
    (frame' : ∀ j, Localization.Away (t j) ⊗[A] ((Fin n → A) ⧸ K) ≃ₗ[Localization.Away (t j)]
      (Fin d → Localization.Away (t j))) :
    grassmannianOfPrincipalQuotientFrames K s hs frame =
      grassmannianOfPrincipalQuotientFrames K t ht frame' :=
  Module.Grassmannian.ext rfl

end FlagVarieties.Foundations

#print axioms FlagVarieties.Foundations.grassmannianOfPrincipalQuotientFrames
