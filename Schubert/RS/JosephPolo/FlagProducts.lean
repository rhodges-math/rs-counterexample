import Schubert.RS.JosephPolo.FlagMinorExpansion
import Schubert.RS.JosephPolo.PolynomialGramSpan

namespace Schubert.RS.Representation
noncomputable section
open scoped BigOperators ComplexConjugate
set_option backward.isDefEq.respectTransparency false

abbrev FlagMinorRowSet {n : ℕ} (k : Fin n) :=
  ↥((Finset.univ : Finset (Fin n)).powersetCard (k.val+1))

def FlagMinorRowSet.rows {n : ℕ} {k : Fin n} (S : FlagMinorRowSet k) : Fin (k.val+1) ↪o Fin n :=
  S.val.orderEmbOfFin (Finset.mem_powersetCard.mp S.property).2

theorem rowAction_flagRowMinor_sum {n : ℕ} (g : Square n) (k : Fin n)
    (s : Fin (k.val+1) → Fin n) :
    rowAction g (flagRowMinor k s) =
      ∑ S : FlagMinorRowSet k, (g.submatrix S.rows s).det • flagRowMinor k S.rows := by
  classical
  rw [rowAction_flagRowMinor,← Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro S hS
  rw [dif_pos (Finset.mem_powersetCard.mp S.property).2]
  rfl

abbrev FlagColumns {n : ℕ} (m : ColumnShape n) := Σ k : Fin n, Fin (m k)
abbrev FlagTableauRows {n : ℕ} (m : ColumnShape n) := (c : FlagColumns m) → FlagMinorRowSet c.1

/-- Products of minors indexed by all column choices. No standardness or
independence assertion is built into this definition. -/
def flagTableauPolynomial {n : ℕ} (m : ColumnShape n) (T : FlagTableauRows m) : MatrixPolynomial n :=
  ∏ c : FlagColumns m, flagRowMinor c.1 (T c).rows

theorem highestFlag_eq_prod_columns {n : ℕ} (m : ColumnShape n) :
    highestFlag m = ∏ c : FlagColumns m, flagMinor c.1 := by
  rw [highestFlag,Fintype.prod_sigma]
  simp

/-- Full expansion of the orbit of the flag seed, retaining the dependent
minor products and all their multiplicities. -/
theorem rowAction_highestFlag_sum {n : ℕ} (g : Square n) (m : ColumnShape n) :
    rowAction g (highestFlag m) =
      ∑ T : FlagTableauRows m,
        (∏ c : FlagColumns m, (g.submatrix (T c).rows (prefixIndex c.1)).det) •
          flagTableauPolynomial m T := by
  classical
  rw [highestFlag_eq_prod_columns,map_prod]
  simp_rw [← flagRowMinor_prefix,rowAction_flagRowMinor_sum]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro T hT
  simp only [flagTableauPolynomial,← Finset.prod_smul]

theorem flagRowMinor_conjugation {n : ℕ} (k : Fin n) (s : Fin (k.val+1) → Fin n) :
    MvPolynomial.map (starRingEnd ℂ) (flagRowMinor k s) = flagRowMinor k s := by
  rw [flagRowMinor,RingHom.map_det]
  congr 1
  apply Matrix.ext
  intro i j
  exact MvPolynomial.map_X _ _

theorem flagTableauPolynomial_real_coeff {n : ℕ} (m : ColumnShape n) (T : FlagTableauRows m)
    (d : (Fin n × Fin n) →₀ ℕ) :
    conj (MvPolynomial.coeff d (flagTableauPolynomial m T)) =
      MvPolynomial.coeff d (flagTableauPolynomial m T) := by
  have h : MvPolynomial.map (starRingEnd ℂ) (flagTableauPolynomial m T) =
      flagTableauPolynomial m T := by
    simp only [flagTableauPolynomial,map_prod,flagRowMinor_conjugation]
  have hc := congrArg (MvPolynomial.coeff d) h
  simpa only [MvPolynomial.coeff_map] using hc

end
end Schubert.RS.Representation
