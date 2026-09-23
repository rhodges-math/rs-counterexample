import Schubert.RS.JosephPolo.ChainIndependence

namespace Schubert.RS.Representation
noncomputable section
open FinPermutation
open scoped BigOperators
universe u

theorem flagColumnProduct_linearIndependent_on_union {n d : ℕ} (h : Fin d → Fin n)
    {ι : Type u} [Fintype ι] (T : ι → (j : Fin d) → FlagMinorRowSet (h j))
    (hT : Function.Injective T) (W : ι → FinPermutation n)
    (hchain : ∀ i, HasFlagDefiningChain h (T i) (W i)) :
    LinearIndependent ℂ (fun i => fun j : ι =>
      flagOrbitRestriction (W j) (flagColumnProduct h (T i))) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hz
  apply flagColumnProduct_relation_zero h T hT W hchain c
  intro i
  simpa only [map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,Pi.zero_apply] using congrFun hz i

/-- Products admitting a defining chain below w are linearly independent
after restriction to the actual upper-word orbit of w. -/
theorem flagColumnProduct_linearIndependent {n d : ℕ} (h : Fin d → Fin n) (w : FinPermutation n) :
    LinearIndependent ℂ (fun T : {T : (j : Fin d) → FlagMinorRowSet (h j) //
      HasFlagDefiningChain h T w} => flagOrbitRestriction w (flagColumnProduct h T.val)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hz
  apply flagColumnProduct_relation_zero h (fun T => T.val) Subtype.val_injective
    (fun _ => w) (fun T => T.property) c
  intro i
  simpa only [map_sum,map_smul] using hz

/-- The coordinate duality with the column order retained for chain indexing. -/
def flagDemazureColumnDuality {n d : ℕ} (h : Fin d → Fin n) (w : FinPermutation n) :
    Module.Dual ℂ (flagDemazure (columnMultiplicity h) w) ≃ₗ[ℂ]
      Submodule.span ℂ (Set.range (fun T : (j : Fin d) → FlagMinorRowSet (h j) =>
        flagOrbitRestriction w (flagColumnProduct h T))) :=
  (LinearEquiv.ofEq _ _ (flagDemazure_eq_upperRowOrbitSpan (columnMultiplicity h) w)).symm.dualMap.trans
    (polynomialOrbitDuality (flagColumnProduct h) (flagColumnProduct_real_coeff h)
      (flagOrbitRestriction w).toLinearMap
      (fun z => upperRowWord z (extremalFlag (columnMultiplicity h) w))
      (upperRowWord_columnProduct_sum h w))

end
end Schubert.RS.Representation
