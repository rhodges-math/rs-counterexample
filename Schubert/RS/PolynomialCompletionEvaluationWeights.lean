import Schubert.RS.PolynomialCompletionLowering
import Schubert.RS.PolynomialGridWeights

namespace Schubert.RS.Representation
noncomputable section
attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000

variable {n : ℕ} {a b : Fin n} {S : Submodule ℂ (MatrixPolynomial n)}
  (B : PolynomialRootStringBasis a b S) (hab : a≠b)

theorem PolynomialRootStringBasis.completionWeight_grid (j : B.index)
    (k : Fin (B.length j+1)) (l : Fin (B.residual j+1)) :
    B.completionWeight ⟨j,(k,l)⟩=
      B.weight j+B.length j • positiveRoot a b-(k.val+l.val) • positiveRoot a b := by
  simp only [PolynomialRootStringBasis.completionWeight,← Nat.cast_smul_eq_nsmul ℤ,
    Nat.cast_add,sub_smul,add_smul]
  abel

/-- A polynomial-valued linear comparison preserving the actual boundary
and lowering action preserves every full weight of the exhibited completion. -/
theorem PolynomialRootStringBasis.evaluation_basis_weight
    (f : B.completedModule hab →ₗ[ℂ] MatrixPolynomial n)
    (hb : ∀ p : S, f (B.completionBoundary hab p)=p.val)
    (hf : ∀ x, f ⁅sl2LoweringElement (polynomialSl2Triple a b hab),x⁆=
      matrixUnitDerivation b a (f x))
    (j : B.completionIndex) (t : DiagonalTorus n) :
    polynomialTorus n t (f (B.completionBasis hab j))=
      integerWeightScalar (B.completionWeight j) t • f (B.completionBasis hab j) := by
  obtain ⟨j,k,l⟩ := j
  let p := fun (k : Fin (B.length j+1)) (l : Fin (B.residual j+1)) =>
    f (B.completionBasis hab ⟨j,(k,l)⟩)
  have h0 (k : Fin (B.length j+1)) (t : DiagonalTorus n) :
      polynomialTorus n t (p k 0)=integerWeightScalar
        (B.weight j+B.length j • positiveRoot a b-k.val • positiveRoot a b) t • p k 0 := by
    have hp0 : p k 0=(B.normalizedBasis ⟨j,k⟩ : MatrixPolynomial n) := by
      change f (B.completionBasis hab ⟨j,(k,0)⟩)=_
      rw [← B.completionBoundary_basis hab ⟨j,k⟩,hb]
    rw [hp0,B.normalizedBasis_weight]
    have hw : B.normalizedWeight ⟨j,k⟩=
        B.weight j+B.length j • positiveRoot a b-k.val • positiveRoot a b := by
      simp only [PolynomialRootStringBasis.normalizedWeight,sub_smul,← Nat.cast_smul_eq_nsmul ℤ]
      abel
    rw [hw]
  have hs (k : Fin (B.length j+1)) (l : Fin (B.residual j+1))
      (hk : k.val<B.length j) (hl : l.val<B.residual j) :
      p k ⟨l.val+1,by omega⟩=matrixUnitDerivation b a (p k l)-p ⟨k.val+1,by omega⟩ l := by
    have h := hf (B.completionBasis hab ⟨j,(k,l)⟩)
    rw [B.completionBasis_f hab j k l hk hl,map_add] at h
    apply eq_sub_iff_add_eq.mpr
    exact (add_comm _ _).trans h
  have he (l : Fin (B.residual j+1)) (hl : l.val<B.residual j) :
      p ⟨B.length j,by omega⟩ ⟨l.val+1,by omega⟩=
        matrixUnitDerivation b a (p ⟨B.length j,by omega⟩ l) := by
    have h := hf (B.completionBasis hab ⟨j,(⟨B.length j,by omega⟩,l)⟩)
    rw [B.completionBasis_f_first_last hab j l hl] at h
    exact h
  rw [B.completionWeight_grid]
  exact polynomial_grid_weights a b (B.weight j+B.length j • positiveRoot a b) p h0 hs he k l t

theorem PolynomialRootStringBasis.evaluation_torus
    (f : B.completedModule hab →ₗ[ℂ] MatrixPolynomial n)
    (hb : ∀ p : S, f (B.completionBoundary hab p)=p.val)
    (hf : ∀ x, f ⁅sl2LoweringElement (polynomialSl2Triple a b hab),x⁆=
      matrixUnitDerivation b a (f x))
    (t : DiagonalTorus n) (x : B.completedModule hab) :
    f (B.completionTorus hab t x)=polynomialTorus n t (f x) := by
  have h : f.comp (B.completionTorus hab t)=(polynomialTorus n t).comp f := by
    apply (B.completionBasis hab).ext
    intro j
    change f (basisWeightTorus (B.completionBasis hab) B.completionWeight t
      (B.completionBasis hab j))=polynomialTorus n t (f (B.completionBasis hab j))
    rw [basisWeightTorus_basis,map_smul]
    exact (B.evaluation_basis_weight hab f hb hf j t).symm
  exact LinearMap.congr_fun h x

end
end Schubert.RS.Representation
