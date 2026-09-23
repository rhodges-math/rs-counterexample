import Schubert.RS.GradedRootDecomposition

namespace Schubert.RS.Representation
noncomputable section

structure PolynomialRootStringBasis {n : ℕ} (a b : Fin n)
    (S : Submodule ℂ (MatrixPolynomial n)) where
  index : Type
  finiteIndex : Fintype index
  length : index → ℕ
  seed : index → MatrixPolynomial n
  weight : index → Weight n
  seed_weight : ∀ i t, polynomialTorus n t (seed i)=integerWeightScalar (weight i) t • seed i
  top_ne_zero : ∀ i, derivationIter (matrixUnitDerivation a b) (length i) (seed i)≠0
  next_zero : ∀ i, derivationIter (matrixUnitDerivation a b) (length i+1) (seed i)=0
  independent : LinearIndependent ℂ
    (fun j : (Σ i,Fin (length i+1)) => derivationIter (matrixUnitDerivation a b) j.2.val (seed j.1))
  span_eq : Submodule.span ℂ
    (Set.range (fun j : (Σ i,Fin (length i+1)) => derivationIter (matrixUnitDerivation a b) j.2.val (seed j.1)))=S

attribute [instance] PolynomialRootStringBasis.finiteIndex

def optionStringIndexEquiv (I : Type) (length : I → ℕ) (d : ℕ) :
    (Σ i : Option I,Fin (i.elim d length+1)) ≃ (Fin (d+1) ⊕ (Σ i : I,Fin (length i+1))) where
  toFun
    | ⟨none,j⟩ => Sum.inl j
    | ⟨some i,j⟩ => Sum.inr ⟨i,j⟩
  invFun
    | Sum.inl j => ⟨none,j⟩
    | Sum.inr ⟨i,j⟩ => ⟨some i,j⟩
  left_inv := by rintro ⟨i,j⟩; cases i <;> rfl
  right_inv := by intro j; cases j <;> rfl

def PolynomialRootStringBasis.empty {n : ℕ} (a b : Fin n) : PolynomialRootStringBasis a b ⊥ where
  index := PEmpty
  finiteIndex := inferInstance
  length := PEmpty.elim
  seed := PEmpty.elim
  weight := PEmpty.elim
  seed_weight i := PEmpty.elim i
  top_ne_zero i := PEmpty.elim i
  next_zero i := PEmpty.elim i
  independent := by apply linearIndependent_empty_type
  span_eq := by simp

def PolynomialRootStringBasis.cons {n : ℕ} {a b : Fin n} (hab : a≠b)
    {S K : Submodule ℂ (MatrixPolynomial n)} (B : PolynomialRootStringBasis a b K)
    (p : MatrixPolynomial n) (v : Weight n) (d : ℕ)
    (hw : ∀ t, polynomialTorus n t p=integerWeightScalar v t • p)
    (htop : derivationIter (matrixUnitDerivation a b) d p≠0)
    (hzero : derivationIter (matrixUnitDerivation a b) (d+1) p=0)
    (hdisjoint : Disjoint (matrixUnitStringSpan a b p d) K)
    (hsup : matrixUnitStringSpan a b p d ⊔ K=S) : PolynomialRootStringBasis a b S := by
  let f := fun j : Fin (d+1) => derivationIter (matrixUnitDerivation a b) j.val p
  let g := fun j : (Σ i,Fin (B.length i+1)) => derivationIter (matrixUnitDerivation a b) j.2.val (B.seed j.1)
  let e := optionStringIndexEquiv B.index B.length d
  have hdj : Disjoint (Submodule.span ℂ (Set.range f)) (Submodule.span ℂ (Set.range g)) := by
    rw [B.span_eq]
    exact hdisjoint
  have hli := (matrixUnit_string_independent a b hab p v hw d htop).sum_type B.independent hdj
  have heq : (fun j : (Σ i : Option B.index,Fin (i.elim d B.length+1)) =>
      derivationIter (matrixUnitDerivation a b) j.2.val (j.1.elim p B.seed)) = (Sum.elim f g) ∘ e := by
    funext j
    obtain ⟨i,j⟩ := j
    cases i <;> rfl
  refine { index := Option B.index
           finiteIndex := inferInstance
           length := fun i => i.elim d B.length
           seed := fun i => i.elim p B.seed
           weight := fun i => i.elim v B.weight
           seed_weight := ?_
           top_ne_zero := ?_
           next_zero := ?_
           independent := ?_
           span_eq := ?_ }
  · intro i t
    cases i with
    | none => exact hw t
    | some i => exact B.seed_weight i t
  · intro i
    cases i with
    | none => exact htop
    | some i => exact B.top_ne_zero i
  · intro i
    cases i with
    | none => exact hzero
    | some i => exact B.next_zero i
  · rw [heq]
    exact hli.comp e e.injective
  · rw [heq,e.surjective.range_comp,Set.Sum.elim_range,Submodule.span_union,B.span_eq]
    exact hsup

theorem GradedRootDecomposition.hasStringBasis {n : ℕ} {a b : Fin n} (hab : a≠b)
    {S : Submodule ℂ (MatrixPolynomial n)} (h : GradedRootDecomposition a b S) :
    Nonempty (PolynomialRootStringBasis a b S) := by
  induction h with
  | zero => exact ⟨PolynomialRootStringBasis.empty a b⟩
  | split S K p v d hp hw htop hzero hdis hsup rest ih =>
    obtain ⟨B⟩ := ih
    exact ⟨B.cons hab p v d hw htop hzero hdis hsup⟩

theorem exists_polynomialRootStringBasis {n : ℕ} (a b : Fin n) (hab : a≠b)
    (S : Submodule ℂ (MatrixPolynomial n)) [FiniteDimensional ℂ S]
    (hE : ∀ p∈S, matrixUnitDerivation a b p∈S)
    (hT : ∀ t p, p∈S → polynomialTorus n t p∈S) : Nonempty (PolynomialRootStringBasis a b S) :=
  (gradedRootDecomposition a b hab S hE hT).hasStringBasis hab

def PolynomialRootStringBasis.basis {n : ℕ} {a b : Fin n}
    {S : Submodule ℂ (MatrixPolynomial n)} (B : PolynomialRootStringBasis a b S) :
    Module.Basis (Σ i,Fin (B.length i+1)) ℂ S :=
  (Module.Basis.span B.independent).map (LinearEquiv.ofEq _ _ B.span_eq)

theorem PolynomialRootStringBasis.basis_val {n : ℕ} {a b : Fin n}
    {S : Submodule ℂ (MatrixPolynomial n)} (B : PolynomialRootStringBasis a b S)
    (j : Σ i,Fin (B.length i+1)) :
    (B.basis j : MatrixPolynomial n)=derivationIter (matrixUnitDerivation a b) j.2.val (B.seed j.1) := by
  simp [PolynomialRootStringBasis.basis]

end
end Schubert.RS.Representation
