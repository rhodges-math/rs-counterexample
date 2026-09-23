import Schubert.RS.JosephPolo.FlagCoordinateDuality
import Schubert.RS.JosephPolo.GramWitness
import Schubert.RS.Representation.AdjacentInclusion

namespace Schubert.RS.Representation
noncomputable section

/-- Vanishing transfers along actual flag-module inclusions. The common
minor-product span is essential to the statement. -/
theorem flagOrbitRestriction_zero_of_flagDemazure_le {n : ℕ} (m : ColumnShape n)
    (v w : Equiv.Perm (Fin n)) (hle : flagDemazure m v ≤ flagDemazure m w)
    (q : MatrixPolynomial n)
    (hq : q ∈ Submodule.span ℂ (Set.range (flagTableauPolynomial m)))
    (hz : flagOrbitRestriction w q = 0) : flagOrbitRestriction v q = 0 := by
  apply restriction_zero_of_orbitSpan_le (flagTableauPolynomial m) (flagTableauPolynomial_real_coeff m)
    (flagOrbitRestriction w).toLinearMap (fun z => upperRowWord z (extremalFlag m w))
    (upperRowWord_extremalFlag_sum m w)
    (flagOrbitRestriction v).toLinearMap (fun z => upperRowWord z (extremalFlag m v))
    (upperRowWord_extremalFlag_sum m v) _ q hq hz
  change upperRowOrbitSpan (extremalFlag m v) ≤ upperRowOrbitSpan (extremalFlag m w)
  rwa [← flagDemazure_eq_upperRowOrbitSpan,← flagDemazure_eq_upperRowOrbitSpan]

/-- Root-reflection inclusion, including equal-weight reflections. -/
theorem flagDemazure_reflection_le {n : ℕ} (m : ColumnShape n) (w : Equiv.Perm (Fin n))
    (r : PositiveRoot n)
    (h : extremalWeight m w r.val.1 ≤ extremalWeight m w r.val.2) :
    flagDemazure m (Equiv.swap r.val.1 r.val.2 * w) ≤ flagDemazure m w := by
  rcases h.eq_or_lt with he | hlt
  · have hw : extremalWeight m (Equiv.swap r.val.1 r.val.2 * w) = extremalWeight m w := by
      rw [extremalWeight_swap_mul]
      funext j
      exact Equiv.apply_swap_eq_self he j
    rw [flagDemazure_eq_of_weight_eq m _ _ hw]
  · apply upperCyclic_le_of_seed_mem
    change rowRename (Equiv.swap r.val.1 r.val.2 * w) (highestFlag m) ∈ flagDemazure m w
    rw [rowRename_mul]
    exact extremalFlag_swap_mem m w r hlt

theorem flagOrbitRestriction_zero_of_reflection {n : ℕ} (m : ColumnShape n)
    (w : Equiv.Perm (Fin n)) (r : PositiveRoot n)
    (h : extremalWeight m w r.val.1 ≤ extremalWeight m w r.val.2)
    (q : MatrixPolynomial n)
    (hq : q ∈ Submodule.span ℂ (Set.range (flagTableauPolynomial m)))
    (hz : flagOrbitRestriction w q = 0) :
    flagOrbitRestriction (Equiv.swap r.val.1 r.val.2 * w) q = 0 :=
  flagOrbitRestriction_zero_of_flagDemazure_le m _ w (flagDemazure_reflection_le m w r h) q hq hz

end
end Schubert.RS.Representation
