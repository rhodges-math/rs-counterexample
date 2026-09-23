import Schubert.RS.Representation.AdjacentSaturation

namespace Schubert.RS.Representation
noncomputable section
open FinPermutation
set_option maxHeartbeats 20000

/-- Positive roots in the nilradical of the adjacent minimal parabolic. -/
abbrev RadicalRoot {n : ℕ} (i : AdjacentPosition n) :=
  {r : PositiveRoot n // r.val ≠ (i.left,i.right)}

/-- The smallest subspace containing a seed and stable under given actual operators. -/
def operatorCyclic {E R : Type*} [AddCommGroup E] [Module ℂ E]
    (p : E) (act : R → Module.End ℂ E) : Submodule ℂ E :=
  sInf {P | p ∈ P ∧ ∀ r, ∀ q ∈ P, act r q ∈ P}

theorem operatorCyclic_seed {E R : Type*} [AddCommGroup E] [Module ℂ E]
    (p : E) (act : R → Module.End ℂ E) : p ∈ operatorCyclic p act := by
  apply Submodule.mem_sInf.mpr
  intro P hP
  exact hP.1

theorem operatorCyclic_stable {E R : Type*} [AddCommGroup E] [Module ℂ E]
    (p : E) (act : R → Module.End ℂ E) (r : R) {q : E}
    (hq : q ∈ operatorCyclic p act) : act r q ∈ operatorCyclic p act := by
  apply Submodule.mem_sInf.mpr
  intro P hP
  exact hP.2 r q (Submodule.mem_sInf.mp hq P hP)

theorem operatorCyclic_le {E R : Type*} [AddCommGroup E] [Module ℂ E]
    (p : E) (act : R → Module.End ℂ E) (P : Submodule ℂ E)
    (hp : p ∈ P) (hP : ∀ r, ∀ q ∈ P, act r q ∈ P) : operatorCyclic p act ≤ P :=
  sInf_le ⟨hp,hP⟩

def radicalCyclic {n : ℕ} (i : AdjacentPosition n) (p : MatrixPolynomial n) :=
  operatorCyclic p (fun r : RadicalRoot i =>
    (matrixUnitDerivation r.val.val.1 r.val.val.2).toLinearMap)

theorem adjacent_raising_radical_commutator {n : ℕ} (i : AdjacentPosition n)
    (r : RadicalRoot i) (P : Submodule ℂ (MatrixPolynomial n)) (q : MatrixPolynomial n)
    (hroot : ∀ s : RadicalRoot i, matrixUnitDerivation s.val.val.1 s.val.val.2 q ∈ P) :
    matrixUnitDerivation i.left i.right (matrixUnitDerivation r.val.val.1 r.val.val.2 q) -
      matrixUnitDerivation r.val.val.1 r.val.val.2 (matrixUnitDerivation i.left i.right q) ∈ P := by
  rw [matrixUnitDerivation_commutator]
  apply P.sub_mem
  · split_ifs with h
    · have ht : i.right < r.val.val.2 := by simpa only [h] using r.val.property
      exact hroot ⟨⟨(i.left,r.val.val.2),lt_trans i.left_lt_right ht⟩,
        fun he => (ne_of_gt ht) (congrArg Prod.snd he)⟩
    · exact P.zero_mem
  · split_ifs with h
    · have ht : r.val.val.1 < i.left := by simpa only [h] using r.val.property
      exact hroot ⟨⟨(r.val.val.1,i.right),lt_trans ht i.left_lt_right⟩,
        fun he => (ne_of_lt ht) (congrArg Prod.fst he)⟩
    · exact P.zero_mem

theorem adjacent_lowering_radical_commutator {n : ℕ} (i : AdjacentPosition n)
    (r : RadicalRoot i) (P : Submodule ℂ (MatrixPolynomial n)) (q : MatrixPolynomial n)
    (hroot : ∀ s : RadicalRoot i, matrixUnitDerivation s.val.val.1 s.val.val.2 q ∈ P) :
    matrixUnitDerivation i.right i.left (matrixUnitDerivation r.val.val.1 r.val.val.2 q) -
      matrixUnitDerivation r.val.val.1 r.val.val.2 (matrixUnitDerivation i.right i.left q) ∈ P := by
  rw [matrixUnitDerivation_commutator]
  apply P.sub_mem
  · split_ifs with h
    · have hn : r.val.val.2 ≠ i.right := by
        intro he
        apply r.property
        exact Prod.ext h.symm he
      have ht : i.right < r.val.val.2 := by
        have hr := r.val.property
        have hv := congrArg Fin.val h
        have hi := i.right_val
        have hne : r.val.val.2.val ≠ i.right.val := fun he => hn (Fin.ext he)
        change r.val.val.1.val < r.val.val.2.val at hr
        change i.right.val < r.val.val.2.val
        omega
      exact hroot ⟨⟨(i.right,r.val.val.2),ht⟩,
        fun he => i.left_ne_right (congrArg Prod.fst he).symm⟩
    · exact P.zero_mem
  · split_ifs with h
    · have hn : r.val.val.1 ≠ i.left := by
        intro he
        apply r.property
        exact Prod.ext he h
      have ht : r.val.val.1 < i.left := by
        have hr := r.val.property
        have hv := congrArg Fin.val h
        have hi := i.right_val
        have hne : r.val.val.1.val ≠ i.left.val := fun he => hn (Fin.ext he)
        change r.val.val.1.val < r.val.val.2.val at hr
        change r.val.val.1.val < i.left.val
        omega
      exact hroot ⟨⟨(r.val.val.1,i.left),ht⟩,
        fun he => i.left_ne_right (congrArg Prod.snd he)⟩
    · exact P.zero_mem

/-- Moving E_i past all radical words requires only the matrix commutators.
No PBW or straightening input is used. -/
theorem radicalCyclic_raising_stable {n : ℕ} (i : AdjacentPosition n)
    (p : MatrixPolynomial n) (hp : matrixUnitDerivation i.left i.right p = 0)
    {q : MatrixPolynomial n} (hq : q ∈ radicalCyclic i p) :
    matrixUnitDerivation i.left i.right q ∈ radicalCyclic i p := by
  apply cyclic_core_stability (radicalCyclic i p) p
    (fun r : RadicalRoot i => (matrixUnitDerivation r.val.val.1 r.val.val.2).toLinearMap)
    (matrixUnitDerivation i.left i.right).toLinearMap
    (fun Q hp hQ => operatorCyclic_le p _ Q hp hQ)
    (operatorCyclic_seed p _) (fun r x hx => operatorCyclic_stable p _ r hx) _ _ hq
  · change matrixUnitDerivation i.left i.right p ∈ radicalCyclic i p
    rw [hp]
    exact Submodule.zero_mem _
  · intro r x hx
    exact adjacent_raising_radical_commutator i r _ x
      (fun s => operatorCyclic_stable p _ s hx)

/-- A vector killed by E_i generates its upper cyclic module using only the
other positive roots. This is actual normal ordering, not an assumed PBW fact. -/
theorem upperCyclic_eq_radicalCyclic {n : ℕ} (i : AdjacentPosition n)
    (p : MatrixPolynomial n) (hp : matrixUnitDerivation i.left i.right p = 0) :
    upperCyclic p = radicalCyclic i p := by
  apply le_antisymm
  · apply upperCyclic_le_of_root_stable _ _ (operatorCyclic_seed p _)
    intro r q hq
    by_cases hr : r.val = (i.left,i.right)
    · have h1 := congrArg Prod.fst hr
      have h2 := congrArg Prod.snd hr
      rw [h1,h2]
      exact radicalCyclic_raising_stable i p hp hq
    · exact operatorCyclic_stable p (fun s : RadicalRoot i =>
        (matrixUnitDerivation s.val.val.1 s.val.val.2).toLinearMap) ⟨r,hr⟩ hq
  · apply operatorCyclic_le _ _ _ (upperCyclic_seed p)
    intro r q hq
    exact upperCyclic_root_stable p r.val hq

/-- The sorted-neighbor flag module is generated by the actual parabolic
radical on its distinguished highest endpoint. -/
theorem adjacentFlag_eq_radicalCyclic {n : ℕ} (u : Composition n)
    (i : AdjacentPosition n) (hu : u i.left < u i.right) :
    compositionFlag (swapComposition u i) = radicalCyclic i
      (extremalFlag (compositionShape (swapComposition u i))
        (compositionPermutation (swapComposition u i))) := by
  apply upperCyclic_eq_radicalCyclic
  apply extremalFlag_lowering_zero _ _ i.right i.left
  simpa only [composition_extremalWeight, swapComposition_left, swapComposition_right] using hu

end
end Schubert.RS.Representation

