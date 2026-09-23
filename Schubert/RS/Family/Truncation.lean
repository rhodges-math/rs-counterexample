import Schubert.RS.Family.RootWindow
import Schubert.RS.UniformRootTruncation

/-! Finite truncation before any source substitution. The bound is left
variable so it may also dominate both unequal source sizes in Hall extraction. -/

namespace Schubert.RS.Family
noncomputable section
open Representation

def finiteRootFactor (P : Parameters) (B : ℕ) (r : PositiveRoot P.rank) :
    MvPolynomial (Fin (P.rank-1)) ℤ :=
  if coordinateClass P r.val.1=coordinateClass P r.val.2 then
    1-MvPolynomial.monomial (rootDegree r.val.1 r.val.2) 1
  else if sourceClass P r.val.1 ∧ ¬sourceClass P r.val.2 then
    ∑ k : Fin (B+1),MvPolynomial.monomial (k.val • rootDegree r.val.1 r.val.2) 1
  else 1

theorem finiteRootFactor_window (P : Parameters) (B : ℕ) (hB : P.m+1≤B)
    (r : PositiveRoot P.rank) :
    WindowEq (coefficientBox P) ((finiteRootFactor P B r : MvPolynomial (Fin (P.rank-1)) ℤ) :
      MvPowerSeries (Fin (P.rank-1)) ℤ) (familyRootFactor P r) := by
  classical
  unfold finiteRootFactor familyRootFactor
  split_ifs with hC hS
  · change WindowEq (coefficientBox P)
      (MvPolynomial.coeToMvPowerSeries.ringHom
        (1-MvPolynomial.monomial (rootDegree r.val.1 r.val.2) 1)) _
    simp only [map_sub,map_one,MvPolynomial.coeToMvPowerSeries.ringHom_apply,MvPolynomial.coe_monomial]
    exact WindowEq.refl _ _
  · change WindowEq (coefficientBox P)
      (MvPolynomial.coeToMvPowerSeries.ringHom (∑ k : Fin (B+1),_)) _
    simp only [map_sum,MvPolynomial.coeToMvPowerSeries.ringHom_apply,MvPolynomial.coe_monomial]
    apply geometric_truncation_uniform _ (rootFirstCut r.val.1 r.val.2 r.property)
      (rootDegree_first r.val.1 r.val.2 r.property)
    intro i
    exact (coefficientBox_bound P i).trans hB
  · simp only [MvPolynomial.coe_one]
    exact WindowEq.refl _ _

theorem finite_root_product_coefficient (P : Parameters) (B : ℕ) (hB : P.m+1≤B) :
    MvPolynomial.coeff (coefficientBox P) (∏ r : PositiveRoot P.rank,finiteRootFactor P B r)=
      MvPowerSeries.coeff (coefficientBox P) (∏ r : PositiveRoot P.rank,familyRootFactor P r) := by
  have hw:=WindowEq.prod (coefficientBox P) Finset.univ
    (fun r : PositiveRoot P.rank => ((finiteRootFactor P B r : MvPolynomial (Fin (P.rank-1)) ℤ) :
      MvPowerSeries (Fin (P.rank-1)) ℤ))
    (familyRootFactor P) (fun r _ => finiteRootFactor_window P B hB r)
  have hc:=hw (coefficientBox P) le_rfl
  have he : ((∏ r : PositiveRoot P.rank,finiteRootFactor P B r :
      MvPolynomial (Fin (P.rank-1)) ℤ) : MvPowerSeries (Fin (P.rank-1)) ℤ)=
      ∏ r : PositiveRoot P.rank,((finiteRootFactor P B r : MvPolynomial (Fin (P.rank-1)) ℤ) :
        MvPowerSeries (Fin (P.rank-1)) ℤ) :=
    map_prod MvPolynomial.coeToMvPowerSeries.ringHom _ _
  rw [← he] at hc
  simpa only [MvPolynomial.coeff_coe] using hc

theorem family_rectangle_eq_finite_laurent (P : Parameters)
    (hJP : ∀ u : Composition P.rank,CompositionFlagJosephPolo u)
    (hDCF : ∀ u : Composition P.rank,CompositionFlagDemazureCharacter u) (hpbw : HasOrderedPBWBasis P.rank)
    (B : ℕ) (hB : P.m+1≤B) :
    rectangleCoefficient P.rectangle (c P) (key (a P)*key (b P))=
      (rootCoordinateEmbedding (∏ r : PositiveRoot P.rank,finiteRootFactor P B r)).coeff
        (targetDifference P) := by
  rw [← rootWeight_coefficientBox,rootCoordinateEmbedding_coeff,
    finite_root_product_coefficient P B hB]
  exact family_rectangle_eq_root_product P hJP hDCF hpbw

theorem hall_cutoff_bounds (P : Parameters) :
    P.m+1≤2*P.m ∧ 2*P.p-1≤2*P.m ∧ 2*P.q-1≤2*P.m := by
  have hm:=P.m_pos
  have hp:=P.p_le_m
  have hq:=P.q_le_m
  omega

end
end Schubert.RS.Family
