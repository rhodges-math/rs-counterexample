import Schubert.RS.AtomBox
import Mathlib.Algebra.MvPolynomial.Degrees

/-! Exact coordinates in a finite exponent box over the integers. -/

namespace Schubert.RS
noncomputable section
variable {n w : ℕ}

abbrev BoxIndex (n w : ℕ) := Fin n → Fin (w+1)

def boxComposition (u : BoxIndex n w) : Composition n := fun i => (u i).val

theorem boxComposition_injective : Function.Injective (boxComposition (n:=n) (w:=w)) := by
  intro u v h
  funext i
  exact Fin.ext (congrFun h i)

def boxExponent (u : BoxIndex n w) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (boxComposition u)

theorem boxExponent_eq (u : BoxIndex n w) :
    boxExponent u=Finsupp.equivFunOnFinite.symm (boxComposition u) := rfl

theorem boxExponent_injective : Function.Injective (boxExponent (n:=n) (w:=w)) := by
  intro u v h
  apply boxComposition_injective
  exact congrArg (fun d : Fin n →₀ ℕ => (fun i => d i)) h

theorem boxComposition_bound (u : BoxIndex n w) (i : Fin n) : boxComposition u i≤w :=
  Nat.le_of_lt_succ (u i).isLt

def boxCoordinates (f : Polynomial n) : BoxIndex n w → ℤ := fun u => MvPolynomial.coeff (boxExponent u) f

def boxDecode (v : BoxIndex n w → ℤ) : Polynomial n :=
  ∑ u,v u • compositionMonomial (boxComposition u)

theorem boxCoordinates_decode (v : BoxIndex n w → ℤ) : boxCoordinates (boxDecode v)=v := by
  funext u
  simp only [boxCoordinates,boxDecode,MvPolynomial.coeff_sum,MvPolynomial.coeff_smul,
    compositionMonomial,← boxExponent_eq,MvPolynomial.coeff_monomial,
    boxExponent_injective.eq_iff,smul_eq_mul]
  simp

theorem boxDecode_mem (v : BoxIndex n w → ℤ) : boxDecode v∈exponentBox n w := by
  apply (exponentBox n w).sum_mem
  intro u _
  apply (exponentBox n w).smul_mem
  exact monomial_mem_exponentBox w _ 1 (boxComposition_bound u)

theorem boxDecode_coordinates (f : Polynomial n) (hf : f∈exponentBox n w) :
    boxDecode (boxCoordinates (w:=w) f)=f := by
  apply MvPolynomial.ext
  intro d
  by_cases hd : ∀ i,d i≤w
  · let u : BoxIndex n w:=fun i => ⟨d i,Nat.lt_succ_of_le (hd i)⟩
    have he : boxExponent u=d := by ext i; rfl
    rw [← he]
    exact congrFun (boxCoordinates_decode (boxCoordinates (w:=w) f)) u
  · have hz : MvPolynomial.coeff d f=0 := by
      by_contra h
      exact hd (hf d h)
    have hz' : MvPolynomial.coeff d (boxDecode (boxCoordinates (w:=w) f))=0 := by
      by_contra h
      exact hd (boxDecode_mem (boxCoordinates (w:=w) f) d h)
    rw [hz,hz']

theorem boxCoordinates_injective_on {f g : Polynomial n}
    (hf : f∈exponentBox n w) (hg : g∈exponentBox n w)
    (h : boxCoordinates (w:=w) f=boxCoordinates g) : f=g := by
  rw [← boxDecode_coordinates f hf,← boxDecode_coordinates g hg,h]

theorem polynomial_mem_degree_box (f : Polynomial n) : f∈exponentBox n f.totalDegree := by
  intro d hd i
  exact (MvPolynomial.monomial_le_degreeOf i (MvPolynomial.mem_support_iff.mpr hd)).trans
    (MvPolynomial.degreeOf_le_totalDegree f i)

end
end Schubert.RS

