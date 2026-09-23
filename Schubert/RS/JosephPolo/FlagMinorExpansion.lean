import Schubert.RS.JosephPolo.GrinbergCauchyBinet
import Schubert.RS.Representation.FlagWeyl

namespace Schubert.RS.Representation
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- A flag minor with arbitrary ordered rows and the fixed prefix columns.
Repeated rows are allowed in the definition and give the zero determinant. -/
def flagRowMinor {n : ℕ} (k : Fin n) (s : Fin (k.val+1) → Fin n) : MatrixPolynomial n :=
  Matrix.det (fun i j => MvPolynomial.X (s i,prefixIndex k j))

theorem flagRowMinor_prefix {n : ℕ} (k : Fin n) :
    flagRowMinor k (prefixIndex k) = flagMinor k := rfl

/-- Cauchy-Binet for the actual row action, with its covariant convention. -/
theorem rowAction_flagRowMinor {n : ℕ} (g : Square n) (k : Fin n)
    (s : Fin (k.val+1) → Fin n) :
    rowAction g (flagRowMinor k s) =
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard (k.val+1),
        if h : S.card = k.val+1 then
          (g.submatrix (S.orderEmbOfFin h) s).det • flagRowMinor k (S.orderEmbOfFin h)
        else 0 := by
  classical
  let A : Matrix (Fin (k.val+1)) (Fin n) (MatrixPolynomial n) :=
    fun i j => MvPolynomial.C (g j (s i))
  let D : Matrix (Fin n) (Fin (k.val+1)) (MatrixPolynomial n) :=
    fun i j => MvPolynomial.X (i,prefixIndex k j)
  have hM : (rowAction g).mapMatrix (fun i j => MvPolynomial.X (s i,prefixIndex k j)) = A*D := by
    apply Matrix.ext
    intro i j
    change rowAction g (MvPolynomial.X (s i,prefixIndex k j)) =
      ∑ r, MvPolynomial.C (g r (s i)) * MvPolynomial.X (r,prefixIndex k j)
    simp only [rowAction_X,MvPolynomial.C_mul']
  rw [flagRowMinor,AlgHom.map_det,hM,GrinbergCauchyBinet.cauchyBinet]
  apply Finset.sum_congr rfl
  intro S hS
  split_ifs with h
  · have hA : (GrinbergCauchyBinet.colsSubmatrix A S h).det =
        MvPolynomial.C (g.submatrix (S.orderEmbOfFin h) s).det := by
      change ((g.submatrix (S.orderEmbOfFin h) s).transpose.map MvPolynomial.C).det = _
      exact ((MvPolynomial.C : ℂ →+* MatrixPolynomial n).map_det
        (g.submatrix (S.orderEmbOfFin h) s).transpose).symm.trans
        (congrArg MvPolynomial.C (Matrix.det_transpose _))
    rw [hA,MvPolynomial.C_mul']
    rfl
  · rfl

end
end Schubert.RS.Representation
