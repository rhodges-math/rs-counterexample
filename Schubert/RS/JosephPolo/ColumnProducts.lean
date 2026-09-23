import Schubert.RS.JosephPolo.PrefixMinors
import Schubert.RS.JosephPolo.BruhatMonotonicity

namespace Schubert.RS.Representation
noncomputable section
open scoped BigOperators
open FinPermutation
set_option backward.isDefEq.respectTransparency false

/-- Column multiplicities of a finite sequence of column heights. -/
def columnMultiplicity {n d : ℕ} (h : Fin d → Fin n) : ColumnShape n :=
  fun k => Fintype.card {j // h j = k}

/-- A minor product whose columns have a specified order. This order is
retained for defining chains and deletion induction. -/
def flagColumnProduct {n d : ℕ} (h : Fin d → Fin n)
    (T : (j : Fin d) → FlagMinorRowSet (h j)) : MatrixPolynomial n :=
  ∏ j, flagRowMinor (h j) (T j).rows

theorem highestFlag_columnMultiplicity {n d : ℕ} (h : Fin d → Fin n) :
    highestFlag (columnMultiplicity h) = ∏ j, flagMinor (h j) := by
  classical
  unfold highestFlag columnMultiplicity
  simpa only [Finset.prod_const,Finset.card_univ] using Fintype.prod_fiberwise' h flagMinor

theorem flagColumnProduct_real_coeff {n d : ℕ} (h : Fin d → Fin n)
    (T : (j : Fin d) → FlagMinorRowSet (h j)) (a : (Fin n × Fin n) →₀ ℕ) :
    star (MvPolynomial.coeff a (flagColumnProduct h T)) =
      MvPolynomial.coeff a (flagColumnProduct h T) := by
  have he : MvPolynomial.map (starRingEnd ℂ) (flagColumnProduct h T) = flagColumnProduct h T := by
    simp only [flagColumnProduct,map_prod,flagRowMinor_conjugation]
  simpa only [MvPolynomial.coeff_map,starRingEnd_apply] using congrArg (MvPolynomial.coeff a) he

theorem flagOrbitRestriction_columnProduct {n d : ℕ} (h : Fin d → Fin n)
    (T : (j : Fin d) → FlagMinorRowSet (h j)) (w : FinPermutation n)
    (z : List (PositiveRoot n × ℂ)) :
    flagOrbitRestriction w (flagColumnProduct h T) z =
      ∏ j, flagOrbitRestriction w (flagRowMinor (h j) (T j).rows) z := by
  simp only [flagColumnProduct,map_prod,Finset.prod_apply]

theorem upperRowWord_columnProduct_sum {n d : ℕ} (h : Fin d → Fin n)
    (w : FinPermutation n) (z : List (PositiveRoot n × ℂ)) :
    upperRowWord z (extremalFlag (columnMultiplicity h) w) =
      ∑ T : (j : Fin d) → FlagMinorRowSet (h j),
        flagOrbitRestriction w (flagColumnProduct h T) z • flagColumnProduct h T := by
  classical
  rw [upperRowWord_matrix,rowAction_extremalFlag_matrix,highestFlag_columnMultiplicity,map_prod]
  simp_rw [← flagRowMinor_prefix,rowAction_flagRowMinor_sum]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro T hT
  simp only [flagColumnProduct,map_prod,Finset.prod_apply,flagOrbitRestriction_minor,
    Finset.prod_smul]

/-- Bruhat restriction for a fixed ordered sequence of column heights. -/
theorem flagOrbitRestriction_zero_of_bruhat_columns {n d : ℕ} (h : Fin d → Fin n)
    {u v : FinPermutation n} (huv : u ≤ᴮ v) (q : MatrixPolynomial n)
    (hq : q ∈ Submodule.span ℂ (Set.range (flagColumnProduct h)))
    (hz : flagOrbitRestriction v q = 0) : flagOrbitRestriction u q = 0 := by
  apply restriction_zero_of_orbitSpan_le (flagColumnProduct h) (flagColumnProduct_real_coeff h)
    (flagOrbitRestriction v).toLinearMap
    (fun z => upperRowWord z (extremalFlag (columnMultiplicity h) v))
    (upperRowWord_columnProduct_sum h v)
    (flagOrbitRestriction u).toLinearMap
    (fun z => upperRowWord z (extremalFlag (columnMultiplicity h) u))
    (upperRowWord_columnProduct_sum h u) _ q hq hz
  change upperRowOrbitSpan _ ≤ upperRowOrbitSpan _
  rw [← flagDemazure_eq_upperRowOrbitSpan,← flagDemazure_eq_upperRowOrbitSpan]
  exact flagDemazure_mono (columnMultiplicity h) huv

theorem flagColumnProduct_fin_succ {n d : ℕ} (h : Fin (d+1) → Fin n)
    (T : (j : Fin (d+1)) → FlagMinorRowSet (h j)) :
    flagColumnProduct h T = flagColumnProduct (fun j => h j.castSucc) (fun j => T j.castSucc) *
      flagRowMinor (h (Fin.last d)) (T (Fin.last d)).rows :=
  Fin.prod_univ_castSucc _

end
end Schubert.RS.Representation
