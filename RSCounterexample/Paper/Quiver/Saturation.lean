import RSCounterexample.Paper.Quiver.Flag
import RSCounterexample.Paper.Quiver.SemiInvariant
import RSCounterexample.Paper.Statements.QuiverSaturation
import RSCounterexample.QuiverInvariants.Saturation

/-!
# Saturation of quiver multiplicities

The statement `Schubert.RS.QuiverSaturation` follows from the saturation of semi-invariants of
quivers in the weight (`Schubert.RS.quiverSaturation_of_semiInvariant`):
1. by the flag identity (`ForwardQuiver.multiplicity_flag`), `m_Q(λ)` is the multiplicity of
   the constant weight `σ = Q.flagWeight λ` for the flag quiver, and `σ` is linear in `λ`
   (`ForwardQuiver.flagWeight_nsmul`);
2. multiplicities of constant weights are positive exactly when there are nonzero
   semi-invariants of that weight (`ForwardQuiver.multiplicity_const_pos_iff`);
3. a nonzero semi-invariant of weight `N σ` with `N ≥ 1` gives one of weight `σ`
   (`QuiverInvariants.FQuiver.exists_semiInvariant_of_nsmul`, the saturation of semi-invariants
   from the library `RSCounterexample/QuiverInvariants`).

## Main results

* `Schubert.RS.quiverSaturation_of_semiInvariant`: the reduction to semi-invariants.
* `Schubert.RS.quiverSaturation_holds`: the proof of `Schubert.RS.QuiverSaturation`.
-/

open QuiverInvariants Schubert.RS.Quiver

namespace Schubert.RS

/-- **Reduction of `QuiverSaturation` to semi-invariants.** If, for every forward quiver, every
dimension vector and every weight `σ`, a nonzero semi-invariant of weight `N σ` with `N ≥ 1`
gives a nonzero semi-invariant of weight `σ`, then quiver multiplicities are saturated. -/
theorem quiverSaturation_of_semiInvariant
    (h : ∀ (P : FQuiver) (n : Fin P.s → ℕ) (σ : Fin P.s → ℤ) (N : ℕ), 0 < N →
      (∃ f : MvPolynomial (P.Entry (finFam n)) ℂ, f ≠ 0 ∧ P.IsSemiInvariant (N • σ) f) →
        ∃ f : MvPolynomial (P.Entry (finFam n)) ℂ, f ≠ 0 ∧ P.IsSemiInvariant σ f) :
    QuiverSaturation := by
  intro Q lam hlam N hN hpos
  set σ : Fin Q.flag.s → ℤ := fun v => Q.flagConst lam (Q.flagVertexEquiv v)
  have hF : Q.flag.multiplicity (fun v _ => σ v) = Q.multiplicity lam := Q.multiplicity_flag hlam
  have hFN : Q.flag.multiplicity (fun v _ => (N • σ) v) = Q.multiplicity (N • lam) := by
    rw [← Q.multiplicity_flag (hlam.smul N), Q.flagWeight_nsmul]
    rfl
  rw [← hFN, ForwardQuiver.multiplicity_const_pos_iff] at hpos
  rw [← hF, ForwardQuiver.multiplicity_const_pos_iff]
  exact h Q.flag.toFQuiver Q.flag.dim σ N hN hpos

/-- **Saturation of quiver multiplicities** (Derksen–Weyman): for a forward quiver `Q`, a dominant
weight `λ` and `N ≥ 1`, if the multiplicity of `N λ` in the coordinate ring of the representation
space is positive, then so is the multiplicity of `λ`. -/
theorem quiverSaturation_holds : QuiverSaturation :=
  quiverSaturation_of_semiInvariant fun P _ σ _ hN h => P.exists_semiInvariant_of_nsmul σ hN h

end Schubert.RS
