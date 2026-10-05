import Schubert.FlagVarieties.Foundations.Flags.SelectedFlagChartOverlapLift

/-! # The two full-flag determinant overlap rings are isomorphic -/

noncomputable section
namespace FlagVarieties.Foundations.QuotientCharts
universe u
variable (R : Type u) [CommRing R] {n : ℕ}
  (a b : (j : Fin (n+1)) → Fin (n-j.val) ↪ Fin n)

theorem selectedFlagOverlapLift_comp :
    (selectedFlagOverlapLift R a b).comp (selectedFlagOverlapLift R b a) =
      AlgHom.id R (SelectedFlagOverlapRing R a b) := by
  apply AlgHom.toRingHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers (selectedFlagOverlapDeterminant R a b))
  apply RingHom.ext
  intro p
  change selectedFlagOverlapLift R a b (selectedFlagOverlapLift R b a
    (algebraMap _ (SelectedFlagOverlapRing R a b) p)) = _
  rw [selectedFlagOverlapLift_algebraMap]
  exact AlgHom.congr_fun (selectedFlagOverlapLift_coordinates R a b) p

/-- Inverse regular transitions on the localized incidence rings. -/
def selectedFlagOverlapAlgEquiv :
    SelectedFlagOverlapRing R b a ≃ₐ[R] SelectedFlagOverlapRing R a b :=
  AlgEquiv.ofAlgHom (selectedFlagOverlapLift R a b) (selectedFlagOverlapLift R b a)
    (selectedFlagOverlapLift_comp R a b) (selectedFlagOverlapLift_comp R b a)

end FlagVarieties.Foundations.QuotientCharts
