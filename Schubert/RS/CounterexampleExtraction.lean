import Schubert.RS.CombinedRootFactors
import Schubert.RS.AtomExpansionCertificate
import Schubert.RS.Representation.CompositionFlag

/-! The rank-28 rectangle-coefficient extraction, specialized to the
composition flag modules. The resulting Hall coefficient is evaluated in
the family counting lemmas. -/

namespace Schubert.RS.Counterexample
noncomputable section
open Representation

theorem rank28_rectangle_eq_root_product
    (hJP : ∀ u : Composition 28, CompositionFlagJosephPolo u)
    (hDCF : ∀ u : Composition 28, CompositionFlagDemazureCharacter u) (hpbw : HasOrderedPBWBasis 28) :
    rectangleCoefficient 79 c (key a * key b) =
      MvPowerSeries.coeff coefficientBox (∏ r : PositiveRoot 28, counterexampleRootFactor r) := by
  have h := three_key_window_coefficient compositionFlagTorus compositionFlagGenerator
    hJP hDCF hpbw a b g coefficientBox
    (fun r hr => power_a_outside r.val.1 r.val.2 r.property hr)
    (fun r hr => power_b_outside r.val.1 r.val.2 r.property hr)
    (fun r hr => power_g_outside r.val.1 r.val.2 r.property hr)
  rw [rectangular_target, concrete_root_series_eq_product] at h
  unfold rectangleCoefficient
  rw [map_mul]
  change (toLaurent (key a) * toLaurent (key b) * toLaurent (key g) * weylFactor 28).coeff
    (fun _ => (79 : ℤ)) = _
  exact h

/-- Any actual integral atom expansion of this key product has the
distinguished coefficient given by the complete cancelled root product. -/
theorem rank28_expansion_coefficient
    (hJP : ∀ u : Composition 28, CompositionFlagJosephPolo u)
    (hDCF : ∀ u : Composition 28, CompositionFlagDemazureCharacter u) (hpbw : HasOrderedPBWBasis 28)
    (t : Composition 28 →₀ ℤ) (ht : key a * key b = t.sum (fun u z => z • atom u)) :
    t c = MvPowerSeries.coeff coefficientBox (∏ r : PositiveRoot 28, counterexampleRootFactor r) := by
  rw [← rectangleCoefficient_expansion compositionFlagTorus compositionFlagGenerator
    hJP hDCF hpbw 79 c c_le t, ← ht]
  exact rank28_rectangle_eq_root_product hJP hDCF hpbw

end
end Schubert.RS.Counterexample
