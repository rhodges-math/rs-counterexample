import Schubert.RS.PolynomialStringModels
import Schubert.RS.Representation.RankOnePiModule

namespace Schubert.RS.Representation
noncomputable section
attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 2000000

variable {n : ℕ} {a b : Fin n} {S : Submodule ℂ (MatrixPolynomial n)}
  (B : PolynomialRootStringBasis a b S) (hab : a≠b)
  (hE : ∀ p∈S, matrixUnitDerivation a b p∈S)

theorem PolynomialRootStringBasis.stringEquiv_e (p : S) :
    B.stringEquiv hab (matrixUnitOnSubmodule a b S hE p)=B.modelE hab (B.stringEquiv hab p) := by
  classical
  have hh : (B.stringEquiv hab).toLinearMap.comp (matrixUnitOnSubmodule a b S hE)=
      (B.modelE hab).comp (B.stringEquiv hab).toLinearMap := by
    apply B.normalizedBasis.ext
    rintro ⟨i,⟨k,hk⟩⟩
    change B.stringEquiv hab (matrixUnitOnSubmodule a b S hE (B.normalizedBasis ⟨i,⟨k,hk⟩⟩))=
      B.modelE hab (B.stringEquiv hab (B.normalizedBasis ⟨i,⟨k,hk⟩⟩))
    cases k with
    | zero =>
        have hk0 : (⟨0,hk⟩ : Fin (B.length i+1))=0 := Fin.ext rfl
        rw [hk0]
        have he : matrixUnitOnSubmodule a b S hE (B.normalizedBasis ⟨i,0⟩)=0 :=
          Subtype.ext (B.normalizedBasis_e_zero i)
        rw [he,map_zero,B.stringEquiv_basis,PolynomialRootStringBasis.modelE,
          piLinearMap_single,polynomialIrreducibleBasis_e_zero,Pi.single_zero]
    | succ k =>
        have he : matrixUnitOnSubmodule a b S hE (B.normalizedBasis ⟨i,⟨k+1,hk⟩⟩)=
            ((k+1)*((B.length i:ℂ)-k)) • B.normalizedBasis ⟨i,⟨k,by omega⟩⟩ :=
          Subtype.ext (B.normalizedBasis_e_succ i k hk)
        rw [he,map_smul,B.stringEquiv_basis,B.stringEquiv_basis,PolynomialRootStringBasis.modelE,
          piLinearMap_single,polynomialIrreducibleBasis_e_succ,Pi.single_smul]
  exact LinearMap.congr_fun hh p

theorem PolynomialRootStringBasis.stringEquiv_h (p : S) :
    B.stringEquiv hab (B.cartan hab p)=B.modelH hab (B.stringEquiv hab p) := by
  classical
  have hh : (B.stringEquiv hab).toLinearMap.comp (B.cartan hab)=
      (B.modelH hab).comp (B.stringEquiv hab).toLinearMap := by
    apply B.normalizedBasis.ext
    intro j
    change B.stringEquiv hab (B.cartan hab (B.normalizedBasis j))=
      B.modelH hab (B.stringEquiv hab (B.normalizedBasis j))
    rw [PolynomialRootStringBasis.cartan,Module.Basis.constr_basis,map_smul,
      B.stringEquiv_basis,PolynomialRootStringBasis.modelH,piLinearMap_single,
      LinearMap.add_apply,LinearMap.smul_apply,LinearMap.id_apply,
      polynomialIrreducibleBasis_h,← add_smul,Pi.single_smul]
    have hc : ((B.weight j.1 a-B.weight j.1 b:ℤ):ℂ)+2*((B.length j.1:ℂ)-j.2.val)=
        (B.length j.1:ℂ)-2*j.2.val+(B.residual j.1:ℂ) := by
      rw [B.residual_cast hab]
      ring
    rw [hc]
  exact LinearMap.congr_fun hh p

end
end Schubert.RS.Representation
