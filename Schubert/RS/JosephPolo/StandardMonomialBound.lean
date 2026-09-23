import Schubert.RS.JosephPolo.StandardMonomialIndependence

namespace Schubert.RS.Representation
noncomputable section
open FinPermutation
attribute [local instance] Classical.propDecidable

/-- The dimension of the polynomial flag module is bounded below by the
number of standard monomials admitting a defining chain. -/
theorem flagDefiningChain_card_le_finrank {n d : ℕ} (h : Fin d → Fin n) (w : FinPermutation n) :
    Fintype.card {T : (j : Fin d) → FlagMinorRowSet (h j) // HasFlagDefiningChain h T w} ≤
      Module.finrank ℂ (flagDemazure (columnMultiplicity h) w) := by
  classical
  let S := Submodule.span ℂ (Set.range (fun T : (j : Fin d) → FlagMinorRowSet (h j) =>
    flagOrbitRestriction w (flagColumnProduct h T)))
  let v : {T : (j : Fin d) → FlagMinorRowSet (h j) // HasFlagDefiningChain h T w} → S :=
    fun T => ⟨flagOrbitRestriction w (flagColumnProduct h T.val),
      Submodule.subset_span ⟨T.val,rfl⟩⟩
  have hv : LinearIndependent ℂ v :=
    LinearIndependent.of_comp S.subtype (flagColumnProduct_linearIndependent h w)
  let e := flagDemazureColumnDuality h w
  have hv' := hv.map' e.symm.toLinearMap (LinearMap.ker_eq_bot.mpr e.symm.injective)
  have hcard := hv'.fintype_card_le_finrank
  simpa only [Subspace.dual_finrank_eq] using hcard

end
end Schubert.RS.Representation
