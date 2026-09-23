import Schubert.RS.JosephPolo.FlagProducts
import Schubert.RS.JosephPolo.OrbitSpan
import Schubert.RS.JosephPolo.OrbitDuality

namespace Schubert.RS.Representation
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

def upperRowMatrix {n : ℕ} : List (PositiveRoot n × ℂ) → Square n
  | [] => 1
  | (r,t)::w => (1 + t • Matrix.single r.val.1 r.val.2 (1:ℂ)) * upperRowMatrix w

theorem upperRowWord_matrix {n : ℕ} (z : List (PositiveRoot n × ℂ)) (p : MatrixPolynomial n) :
    upperRowWord z p = rowAction (upperRowMatrix z) p := by
  induction z with
  | nil => rw [upperRowMatrix,rowAction_one]; rfl
  | cons v z ih =>
    obtain ⟨r,t⟩ := v
    rw [upperRowWord,upperRowMatrix,ih,rowAction_mul]
    rfl

/-- Restrict polynomial functions to elementary upper row matrices translated
by the specified Weyl permutation. No coordinate-ring presentation is assumed. -/
def flagOrbitRestriction {n : ℕ} (w : Equiv.Perm (Fin n)) :
    MatrixPolynomial n →ₐ[ℂ] (List (PositiveRoot n × ℂ) → ℂ) :=
  AlgHom.pi fun z => MvPolynomial.aeval fun rc =>
    (upperRowMatrix z * rowPermutationMatrix w) rc.1 rc.2

theorem flagOrbitRestriction_minor {n : ℕ} (w : Equiv.Perm (Fin n))
    (z : List (PositiveRoot n × ℂ)) (k : Fin n) (s : Fin (k.val+1) → Fin n) :
    flagOrbitRestriction w (flagRowMinor k s) z =
      ((upperRowMatrix z * rowPermutationMatrix w).submatrix s (prefixIndex k)).det := by
  change (MvPolynomial.aeval fun rc : Fin n × Fin n =>
    (upperRowMatrix z * rowPermutationMatrix w) rc.1 rc.2) (flagRowMinor k s) = _
  rw [flagRowMinor,AlgHom.map_det]
  congr 1
  apply Matrix.ext
  intro i j
  exact MvPolynomial.aeval_X _ _

theorem flagOrbitRestriction_tableau {n : ℕ} (m : ColumnShape n) (w : Equiv.Perm (Fin n))
    (T : FlagTableauRows m) (z : List (PositiveRoot n × ℂ)) :
    flagOrbitRestriction w (flagTableauPolynomial m T) z =
      ∏ c : FlagColumns m,
        ((upperRowMatrix z * rowPermutationMatrix w).submatrix (T c).rows (prefixIndex c.1)).det := by
  change (MvPolynomial.aeval fun rc : Fin n × Fin n =>
    (upperRowMatrix z * rowPermutationMatrix w) rc.1 rc.2) (∏ c, flagRowMinor c.1 (T c).rows) = _
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro c hc
  exact flagOrbitRestriction_minor w z c.1 (T c).rows

theorem rowAction_extremalFlag_matrix {n : ℕ} (g : Square n) (m : ColumnShape n)
    (w : Equiv.Perm (Fin n)) :
    rowAction g (extremalFlag m w) = rowAction (g * rowPermutationMatrix w) (highestFlag m) := by
  change rowAction g (rowRename w (highestFlag m)) = _
  rw [← rowAction_permutation,rowAction_mul]
  rfl

theorem upperRowWord_extremalFlag_sum {n : ℕ} (m : ColumnShape n) (w : Equiv.Perm (Fin n))
    (z : List (PositiveRoot n × ℂ)) :
    upperRowWord z (extremalFlag m w) =
      ∑ T : FlagTableauRows m,
        flagOrbitRestriction w (flagTableauPolynomial m T) z • flagTableauPolynomial m T := by
  rw [upperRowWord_matrix,rowAction_extremalFlag_matrix,rowAction_highestFlag_sum]
  simp only [flagOrbitRestriction_tableau]

/-- An independent duality with restricted products of flag minors. This
provides the polynomial model needed for a standard-monomial comparison;
it asserts neither standardness of all products nor the character formula. -/
def flagDemazureCoordinateDuality {n : ℕ} (m : ColumnShape n) (w : Equiv.Perm (Fin n)) :
    Module.Dual ℂ (flagDemazure m w) ≃ₗ[ℂ]
      Submodule.span ℂ (Set.range (fun T : FlagTableauRows m =>
        flagOrbitRestriction w (flagTableauPolynomial m T))) :=
  (LinearEquiv.ofEq _ _ (flagDemazure_eq_upperRowOrbitSpan m w)).symm.dualMap.trans
    (polynomialOrbitDuality (flagTableauPolynomial m) (flagTableauPolynomial_real_coeff m)
      (flagOrbitRestriction w).toLinearMap (fun z => upperRowWord z (extremalFlag m w))
      (upperRowWord_extremalFlag_sum m w))

end
end Schubert.RS.Representation
