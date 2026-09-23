import Schubert.RS.Family.WindowData
import Schubert.RS.CombinedRootFactors

/-! Uniform cancellation of the three ascent denominators. The calculation
depends only on the coordinate classes and holds for every ordered pair. -/

namespace Schubert.RS.Family
noncomputable section
set_option maxRecDepth 2048
open Representation

def comparisonWeight (P : Parameters) (i j : Fin P.rank) : ℤ :=
  (if a P i<a P j then 1 else 0)+(if b P i<b P j then 1 else 0)+
  (if g P i<g P j then 1 else 0)-1

theorem class_pattern (P : Parameters) (i j : Fin P.rank) :
    comparisonWeight P i j =
      if coordinateClass P i=coordinateClass P j then -1
      else if sourceClass P i ∧ ¬sourceClass P j then 1 else 0 := by
  have hi := (coordinateClass P i).isLt
  have hj := (coordinateClass P j).isLt
  have hk := P.K_bound
  have hm := P.m_pos
  have hmul : P.K ≤ P.m*P.K := by
    simpa using Nat.mul_le_mul_right P.K (show 1 ≤ P.m by omega)
  have hG : 0 < (P.m+2)*P.K-2 := by rw [Nat.add_mul]; omega
  by_cases hsi : sourceClass P i <;> by_cases hsj : sourceClass P j <;>
    simp only [comparisonWeight,g_value,hsi,hsj,if_true,if_false,a,b,
      Nat.mul_lt_mul_right P.K_pos,Fin.ext_iff,true_and,false_and,not_true_eq_false,not_false_eq_true]
  all_goals simp only [sourceClass] at hsi hsj
  all_goals split_ifs <;> omega

def familyRootFactor (P : Parameters) (r : PositiveRoot P.rank) :
    MvPowerSeries (Fin (P.rank-1)) ℤ :=
  if coordinateClass P r.val.1=coordinateClass P r.val.2 then
    1-MvPowerSeries.monomial (rootDegree r.val.1 r.val.2) 1
  else if sourceClass P r.val.1 ∧ ¬sourceClass P r.val.2 then
    rootGeometricSeries (rootDegree r.val.1 r.val.2)
  else 1

theorem combinedRootFactor_family (P : Parameters) (r : PositiveRoot P.rank) :
    combinedRootFactor (a P) (b P) (g P) r=familyRootFactor P r := by
  classical
  have hp := class_pattern P r.val.1 r.val.2
  have hd : rootDegree r.val.1 r.val.2 ≠ 0 := by
    intro h
    have hc := rootDegree_first r.val.1 r.val.2 r.property
    rw [h] at hc
    simp at hc
  have hi := rootGeometricSeries_mul (rootDegree r.val.1 r.val.2) hd
  by_cases hA : a P r.val.1<a P r.val.2 <;>
    by_cases hB : b P r.val.1<b P r.val.2 <;>
    by_cases hG : g P r.val.1<g P r.val.2 <;>
    by_cases hC : coordinateClass P r.val.1=coordinateClass P r.val.2 <;>
    by_cases hS : sourceClass P r.val.1 ∧ ¬sourceClass P r.val.2 <;>
    simp only [combinedRootFactor,familyRootFactor,comparisonWeight,
      hA,hB,hG,hC,hS,if_true,if_false,mul_one,one_mul,mul_assoc] at hp ⊢ <;>
    norm_num at hp <;> simp [hi]

theorem family_root_series_eq_product (P : Parameters) :
    ascentRootSeries (a P)*ascentRootSeries (b P)*ascentRootSeries (g P)*
      weylRootSeries P.rank = ∏ r : PositiveRoot P.rank, familyRootFactor P r := by
  rw [three_root_series_eq_product]
  exact Finset.prod_congr rfl (fun r _ => combinedRootFactor_family P r)

end
end Schubert.RS.Family







