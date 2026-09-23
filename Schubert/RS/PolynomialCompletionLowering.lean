import Schubert.RS.PolynomialCompletionTorus

namespace Schubert.RS.Representation
noncomputable section
open TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000

theorem polynomialIrreducibleBasis_f {n : ℕ} (a b : Fin n) (hab : a≠b)
    (d : ℕ) (k : Fin (d+1)) (hk : k.val<d) :
    ⁅sl2LoweringElement (polynomialSl2Triple a b hab),polynomialIrreducibleBasis a b hab d k⁆=
      polynomialIrreducibleBasis a b hab d ⟨k.val+1,by omega⟩ :=
  primitiveStringBasis_f (polynomialHighestVector_primitive a b hab d) k hk

theorem polynomialIrreducibleBasis_f_last {n : ℕ} (a b : Fin n) (hab : a≠b) (d : ℕ) :
    ⁅sl2LoweringElement (polynomialSl2Triple a b hab),
      polynomialIrreducibleBasis a b hab d ⟨d,by omega⟩⁆=0 :=
  primitiveStringBasis_f_last (polynomialHighestVector_primitive a b hab d)

variable {n : ℕ} {a b : Fin n} {S : Submodule ℂ (MatrixPolynomial n)}
  (B : PolynomialRootStringBasis a b S) (hab : a≠b)

theorem PolynomialRootStringBasis.completionBasis_f (j : B.index)
    (k : Fin (B.length j+1)) (l : Fin (B.residual j+1))
    (hk : k.val<B.length j) (hl : l.val<B.residual j) :
    ⁅sl2LoweringElement (polynomialSl2Triple a b hab),B.completionBasis hab ⟨j,(k,l)⟩⁆=
      B.completionBasis hab ⟨j,(⟨k.val+1,by omega⟩,l)⟩+
      B.completionBasis hab ⟨j,(k,⟨l.val+1,by omega⟩)⟩ := by
  classical
  simp only [PolynomialRootStringBasis.completionBasis,Pi.basis_apply,
    Module.Basis.tensorProduct_apply]
  rw [← piLieSingle_apply (L := (polynomialSl2Triple a b hab).toLieSubalgebra ℂ),
    ← LieModuleHom.map_lie,TensorProduct.LieModule.lie_tmul_right,
    polynomialIrreducibleBasis_f a b hab _ k hk,polynomialIrreducibleBasis_f a b hab _ l hl,map_add]
  rfl

theorem PolynomialRootStringBasis.completionBasis_f_first_last (j : B.index)
    (l : Fin (B.residual j+1)) (hl : l.val<B.residual j) :
    ⁅sl2LoweringElement (polynomialSl2Triple a b hab),
      B.completionBasis hab ⟨j,(⟨B.length j,by omega⟩,l)⟩⁆=
      B.completionBasis hab ⟨j,(⟨B.length j,by omega⟩,⟨l.val+1,by omega⟩)⟩ := by
  classical
  simp only [PolynomialRootStringBasis.completionBasis,Pi.basis_apply,
    Module.Basis.tensorProduct_apply]
  rw [← piLieSingle_apply (L := (polynomialSl2Triple a b hab).toLieSubalgebra ℂ),
    ← LieModuleHom.map_lie,TensorProduct.LieModule.lie_tmul_right,
    polynomialIrreducibleBasis_f_last,polynomialIrreducibleBasis_f a b hab _ l hl,
    zero_tmul,zero_add]
  rfl

end
end Schubert.RS.Representation
