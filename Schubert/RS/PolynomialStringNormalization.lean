import Schubert.RS.PolynomialStringAdmissibility
import Mathlib.LinearAlgebra.Basis.SMul

namespace Schubert.RS.Representation
noncomputable section
attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : ℕ} {a b : Fin n} {S : Submodule ℂ (MatrixPolynomial n)}
  (B : PolynomialRootStringBasis a b S)

def PolynomialRootStringBasis.normalizedBasis :
    Module.Basis (Σ i,Fin (B.length i+1)) ℂ S :=
  (B.basis.reindex (Equiv.sigmaCongrRight (fun _ => Fin.revPerm))).unitsSMul
    (fun j => Units.mk0 (terminalStringScale (B.length j.1) j.2.val)
      (terminalStringScale_ne_zero _ _ (by omega)))

theorem PolynomialRootStringBasis.normalizedBasis_val (j : Σ i,Fin (B.length i+1)) :
    (B.normalizedBasis j : MatrixPolynomial n)=terminalStringScale (B.length j.1) j.2.val •
      derivationIter (matrixUnitDerivation a b) (B.length j.1-j.2.val) (B.seed j.1) := by
  rw [PolynomialRootStringBasis.normalizedBasis,Module.Basis.unitsSMul_apply,
    Module.Basis.reindex_apply]
  change terminalStringScale (B.length j.1) j.2.val • (B.basis _ : MatrixPolynomial n)=_
  rw [B.basis_val]
  change terminalStringScale (B.length j.1) j.2.val •
    derivationIter (matrixUnitDerivation a b) j.2.rev.val (B.seed j.1)=_
  rw [Fin.val_rev,Nat.add_sub_add_right]

theorem PolynomialRootStringBasis.normalizedBasis_e_zero (i : B.index) :
    matrixUnitDerivation a b (B.normalizedBasis ⟨i,0⟩ : MatrixPolynomial n)=0 := by
  rw [B.normalizedBasis_val,Derivation.map_smul]
  simpa only [Fin.val_zero,terminalStringScale,one_smul,Nat.sub_zero,
    ← derivationIter_succ] using B.next_zero i

theorem PolynomialRootStringBasis.normalizedBasis_e_succ (i : B.index)
    (k : ℕ) (hk : k+1<B.length i+1) :
    matrixUnitDerivation a b (B.normalizedBasis ⟨i,⟨k+1,hk⟩⟩ : MatrixPolynomial n)=
      ((k+1)*((B.length i:ℂ)-k)) •
        (B.normalizedBasis ⟨i,⟨k,by omega⟩⟩ : MatrixPolynomial n) := by
  rw [B.normalizedBasis_val,B.normalizedBasis_val,Derivation.map_smul,← derivationIter_succ]
  have hdk : B.length i-(k+1)+1=B.length i-k := by omega
  simp only [hdk,terminalStringScale,smul_smul,Nat.cast_add,Nat.cast_one]

theorem PolynomialRootStringBasis.normalizedBasis_h (hab : a≠b)
    (j : Σ i,Fin (B.length i+1)) :
    polynomialRootCartan a b (B.normalizedBasis j : MatrixPolynomial n)=
      (((B.weight j.1 a-B.weight j.1 b:ℤ):ℂ)+2*((B.length j.1:ℂ)-j.2.val)) •
        (B.normalizedBasis j : MatrixPolynomial n) := by
  rw [B.normalizedBasis_val,map_smul]
  rw [polynomialRootCartan_weight a b _ _
    (matrixUnit_derivationIter_weight a b (B.seed j.1) (B.weight j.1)
      (B.seed_weight j.1) (B.length j.1-j.2.val))]
  rw [smul_smul,smul_smul]
  congr 1
  have hk : j.2.val≤B.length j.1 := by omega
  simp only [Pi.add_apply,Pi.smul_apply,positiveRoot,Pi.sub_apply,Pi.single_apply,
    if_pos rfl,if_neg hab,if_neg hab.symm,
    sub_zero,zero_sub,Int.nsmul_eq_mul,Nat.cast_sub hk]
  push_cast
  ring

def PolynomialRootStringBasis.cartan (hab : a≠b) : Module.End ℂ S :=
  B.normalizedBasis.constr ℂ (fun j =>
    (((B.weight j.1 a-B.weight j.1 b:ℤ):ℂ)+2*((B.length j.1:ℂ)-j.2.val)) • B.normalizedBasis j)

theorem PolynomialRootStringBasis.cartan_val (hab : a≠b) (p : S) :
    (B.cartan hab p : MatrixPolynomial n)=polynomialRootCartan a b p.val := by
  have hh : S.subtype.comp (B.cartan hab)=(polynomialRootCartan a b).comp S.subtype := by
    apply B.normalizedBasis.ext
    intro j
    change (B.cartan hab (B.normalizedBasis j) : MatrixPolynomial n)=_
    rw [PolynomialRootStringBasis.cartan,Module.Basis.constr_basis]
    exact (B.normalizedBasis_h hab j).symm
  exact LinearMap.congr_fun hh p

end
end Schubert.RS.Representation
