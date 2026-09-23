import Schubert.RS.PolynomialRootStringBasis
import Schubert.RS.TorusEigenbasisCharacter
import Schubert.RS.Representation.CyclicGeneration

namespace Schubert.RS.Representation
noncomputable section

/-- Every actual flag module has a full-torus homogeneous basis in strings
for each positive root, without a character-formula assumption. -/
theorem exists_flagRootStringBasis {n : ℕ} (m : ColumnShape n)
    (w : Equiv.Perm (Fin n)) (r : PositiveRoot n) :
    Nonempty (PolynomialRootStringBasis r.val.1 r.val.2 (flagDemazure m w)) :=
  exists_polynomialRootStringBasis r.val.1 r.val.2 (ne_of_lt r.property) _
    (fun p hp => upperCyclic_root_stable _ r hp)
    (fun t p hp => flagDemazure_torus_stable m w t hp)

theorem exists_compositionRootStringBasis {n : ℕ} (u : Composition n)
    (r : PositiveRoot n) : Nonempty (PolynomialRootStringBasis r.val.1 r.val.2 (compositionFlag u)) :=
  exists_flagRootStringBasis (compositionShape u) (compositionPermutation u) r

theorem PolynomialRootStringBasis.flag_basis_weight {n : ℕ} {a b : Fin n}
    {m : ColumnShape n} {w : Equiv.Perm (Fin n)}
    (B : PolynomialRootStringBasis a b (flagDemazure m w))
    (t : DiagonalTorus n) (j : Σ i,Fin (B.length i+1)) :
    flagTorus m w t (B.basis j) =
      integerWeightScalar (B.weight j.1+j.2.val • positiveRoot a b) t • B.basis j := by
  apply Subtype.ext
  change polynomialTorus n t (B.basis j).val =
    integerWeightScalar (B.weight j.1+j.2.val • positiveRoot a b) t • (B.basis j).val
  rw [B.basis_val]
  exact matrixUnit_derivationIter_weight a b (B.seed j.1) (B.weight j.1) (B.seed_weight j.1) j.2.val t

/-- This is an actual weight multiplicity formula in a constructed string
basis. It does not identify that character with the operator-defined key. -/
theorem PolynomialRootStringBasis.flag_weight_finrank {n : ℕ} {a b : Fin n}
    {m : ColumnShape n} {w : Equiv.Perm (Fin n)}
    (B : PolynomialRootStringBasis a b (flagDemazure m w)) (v : Weight n) :
    Module.finrank ℂ (torusWeightSpace (flagTorus m w) v) =
      Fintype.card {j : (Σ i,Fin (B.length i+1)) // B.weight j.1+j.2.val • positiveRoot a b=v} := by
  exact torusWeightSpace_finrank_of_eigenbasis (flagTorus m w) B.basis
    (fun j => B.weight j.1+j.2.val • positiveRoot a b) B.flag_basis_weight v

end
end Schubert.RS.Representation
