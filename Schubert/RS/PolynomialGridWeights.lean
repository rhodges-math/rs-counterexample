import Schubert.RS.MatrixUnitStringWeights

namespace Schubert.RS.Representation
noncomputable section

theorem positiveRoot_reverse {n : ℕ} (a b : Fin n) :
    positiveRoot b a = -positiveRoot a b := by
  unfold positiveRoot
  abel

theorem polynomial_lowering_weight {n : ℕ} (a b : Fin n)
    (p : MatrixPolynomial n) (v : Weight n)
    (hp : ∀ t, polynomialTorus n t p=integerWeightScalar v t • p)
    (t : DiagonalTorus n) :
    polynomialTorus n t (matrixUnitDerivation b a p)=
      integerWeightScalar (v-positiveRoot a b) t • matrixUnitDerivation b a p := by
  have h := matrixUnit_derivationIter_weight b a p v hp 1 t
  simpa [derivationIter_succ,positiveRoot_reverse a b,sub_eq_add_neg] using h

/-- Weights propagate along a rectangular tensor-string grid. The recurrence
is the tensor Leibniz rule for the lowering operator, including the terminal
first-factor column. -/
theorem polynomial_grid_weights {n d q : ℕ} (a b : Fin n) (v : Weight n)
    (p : Fin (d+1) → Fin (q+1) → MatrixPolynomial n)
    (h0 : ∀ k t, polynomialTorus n t (p k 0)=
      integerWeightScalar (v-k.val • positiveRoot a b) t • p k 0)
    (hs : ∀ (k : Fin (d+1)) (l : Fin (q+1)) (hk : k.val<d) (hl : l.val<q),
      p k ⟨l.val+1,by omega⟩=matrixUnitDerivation b a (p k l)-p ⟨k.val+1,by omega⟩ l)
    (he : ∀ (l : Fin (q+1)) (hl : l.val<q),
      p ⟨d,by omega⟩ ⟨l.val+1,by omega⟩=matrixUnitDerivation b a (p ⟨d,by omega⟩ l))
    (k : Fin (d+1)) (l : Fin (q+1)) (t : DiagonalTorus n) :
    polynomialTorus n t (p k l)=
      integerWeightScalar (v-(k.val+l.val) • positiveRoot a b) t • p k l := by
  obtain ⟨l,hl⟩ := l
  induction l generalizing k t with
  | zero => simpa using h0 k t
  | succ l ih =>
    have hlq : l<q := by omega
    have hl' : l<q+1 := by omega
    have hw (k : Fin (d+1)) :
        (v-(k.val+l) • positiveRoot a b)-positiveRoot a b=
          v-(k.val+(l+1)) • positiveRoot a b := by
      rw [← Nat.add_assoc,succ_nsmul]
      abel
    have hd (k : Fin (d+1)) : polynomialTorus n t (matrixUnitDerivation b a (p k ⟨l,hl'⟩))=
        integerWeightScalar (v-(k.val+(l+1)) • positiveRoot a b) t •
          matrixUnitDerivation b a (p k ⟨l,hl'⟩) := by
      simpa only [hw k] using polynomial_lowering_weight a b (p k ⟨l,hl'⟩)
        (v-(k.val+l) • positiveRoot a b) (fun t => ih k t hl') t
    by_cases hk : k.val<d
    · rw [hs k ⟨l,hl'⟩ hk hlq,map_sub,hd k,ih ⟨k.val+1,by omega⟩ t hl']
      have hh : k.val+1+l=k.val+(l+1) := by omega
      simp only [Fin.val_mk,hh,smul_sub]
    · have hk' : k=(⟨d,by omega⟩ : Fin (d+1)) := by
        apply Fin.ext
        change k.val=d
        omega
      rw [hk',he ⟨l,hl'⟩ hlq]
      exact hd _

end
end Schubert.RS.Representation
