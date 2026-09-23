import Schubert.RS.PolynomialSl2
import Schubert.RS.Representation.ParabolicRadical

namespace Schubert.RS.Representation
noncomputable section
open FinPermutation
attribute [local instance 100] LieRing.ofAssociativeRing

theorem matrixUnitEnd_commutator {n : ℕ} (a b c d : Fin n) :
    ⁅(matrixUnitDerivation a b).toLinearMap,(matrixUnitDerivation c d).toLinearMap⁆ =
      (if b=c then (matrixUnitDerivation a d).toLinearMap else 0) -
      (if d=a then (matrixUnitDerivation c b).toLinearMap else 0) := by
  classical
  apply LinearMap.ext
  intro p
  have hh := matrixUnitDerivation_commutator a b c d p
  by_cases hbc : b=c <;> by_cases hda : d=a <;> simpa [hbc,hda] using hh

/-- The actual finite span of all positive-root polynomial operators other
than the chosen simple root. -/
def radicalEndSpan {n : ℕ} (i : AdjacentPosition n) :
    Submodule ℂ (Module.End ℂ (MatrixPolynomial n)) :=
  Submodule.span ℂ (Set.range (fun r : RadicalRoot i =>
    (matrixUnitDerivation r.val.val.1 r.val.val.2).toLinearMap))

theorem radicalEndSpan_root_mem {n : ℕ} (i : AdjacentPosition n) (r : RadicalRoot i) :
    (matrixUnitDerivation r.val.val.1 r.val.val.2).toLinearMap ∈ radicalEndSpan i :=
  Submodule.subset_span ⟨r,rfl⟩

private theorem nonadjacent_of_between {n : ℕ} (i : AdjacentPosition n)
    {a b c : Fin n} (hab : a<b) (hbc : b<c) : (a,c) ≠ (i.left,i.right) := by
  intro he
  have ha : a=i.left := congrArg Prod.fst he
  have hc : c=i.right := congrArg Prod.snd he
  rw [ha] at hab
  rw [hc] at hbc
  have hi := i.right_val
  change i.left.val < b.val at hab
  change b.val < i.right.val at hbc
  omega

theorem radicalEndSpan_root_bracket {n : ℕ} (i : AdjacentPosition n) (r s : RadicalRoot i) :
    ⁅(matrixUnitDerivation r.val.val.1 r.val.val.2).toLinearMap,
      (matrixUnitDerivation s.val.val.1 s.val.val.2).toLinearMap⁆ ∈ radicalEndSpan i := by
  classical
  rw [matrixUnitEnd_commutator]
  apply (radicalEndSpan i).sub_mem
  · split_ifs with h
    · have hs : r.val.val.2 < s.val.val.2 := by simpa only [h] using s.val.property
      exact radicalEndSpan_root_mem i
        ⟨⟨(r.val.val.1,s.val.val.2),r.val.property.trans hs⟩,
          nonadjacent_of_between i r.val.property hs⟩
    · exact (radicalEndSpan i).zero_mem
  · split_ifs with h
    · have hs : s.val.val.1 < r.val.val.1 := by simpa only [h] using s.val.property
      exact radicalEndSpan_root_mem i
        ⟨⟨(s.val.val.1,r.val.val.2),hs.trans r.val.property⟩,
          nonadjacent_of_between i hs r.val.property⟩
    · exact (radicalEndSpan i).zero_mem

theorem radicalEndSpan_lie_mem {n : ℕ} (i : AdjacentPosition n)
    {A B : Module.End ℂ (MatrixPolynomial n)} (hA : A∈radicalEndSpan i) (hB : B∈radicalEndSpan i) :
    ⁅A,B⁆ ∈ radicalEndSpan i := by
  induction hA using Submodule.span_induction with
  | mem A hA =>
      obtain ⟨r,rfl⟩ := hA
      induction hB using Submodule.span_induction with
      | mem B hB => obtain ⟨s,rfl⟩ := hB; exact radicalEndSpan_root_bracket i r s
      | zero => simpa only [lie_zero] using (radicalEndSpan i).zero_mem
      | add B C hB hC ihB ihC => rw [lie_add]; exact (radicalEndSpan i).add_mem ihB ihC
      | smul c B hB ihB => rw [lie_smul]; exact (radicalEndSpan i).smul_mem c ihB
  | zero => simpa only [zero_lie] using (radicalEndSpan i).zero_mem
  | add A C hA hC ihA ihC => rw [add_lie]; exact (radicalEndSpan i).add_mem ihA ihC
  | smul c A hA ihA => rw [smul_lie]; exact (radicalEndSpan i).smul_mem c ihA

theorem radicalEndSpan_raising_root {n : ℕ} (i : AdjacentPosition n) (r : RadicalRoot i) :
    ⁅(matrixUnitDerivation i.left i.right).toLinearMap,
      (matrixUnitDerivation r.val.val.1 r.val.val.2).toLinearMap⁆ ∈ radicalEndSpan i := by
  classical
  rw [matrixUnitEnd_commutator]
  apply (radicalEndSpan i).sub_mem
  · split_ifs with h
    · have ht : i.right < r.val.val.2 := by simpa only [h] using r.val.property
      exact radicalEndSpan_root_mem i ⟨⟨(i.left,r.val.val.2),i.left_lt_right.trans ht⟩,
        fun he => (ne_of_gt ht) (congrArg Prod.snd he)⟩
    · exact (radicalEndSpan i).zero_mem
  · split_ifs with h
    · have ht : r.val.val.1 < i.left := by simpa only [h] using r.val.property
      exact radicalEndSpan_root_mem i ⟨⟨(r.val.val.1,i.right),ht.trans i.left_lt_right⟩,
        fun he => (ne_of_lt ht) (congrArg Prod.fst he)⟩
    · exact (radicalEndSpan i).zero_mem

theorem radicalEndSpan_lowering_root {n : ℕ} (i : AdjacentPosition n) (r : RadicalRoot i) :
    ⁅(matrixUnitDerivation i.right i.left).toLinearMap,
      (matrixUnitDerivation r.val.val.1 r.val.val.2).toLinearMap⁆ ∈ radicalEndSpan i := by
  classical
  rw [matrixUnitEnd_commutator]
  apply (radicalEndSpan i).sub_mem
  · split_ifs with h
    · have hn : r.val.val.2 ≠ i.right := by
        intro he
        exact r.property (Prod.ext h.symm he)
      have ht : i.right < r.val.val.2 := by
        have hr := r.val.property
        have hv := congrArg Fin.val h
        have hi := i.right_val
        have hne : r.val.val.2.val ≠ i.right.val := fun he => hn (Fin.ext he)
        change r.val.val.1.val < r.val.val.2.val at hr
        change i.right.val < r.val.val.2.val
        omega
      exact radicalEndSpan_root_mem i ⟨⟨(i.right,r.val.val.2),ht⟩,
        fun he => i.left_ne_right (congrArg Prod.fst he).symm⟩
    · exact (radicalEndSpan i).zero_mem
  · split_ifs with h
    · have hn : r.val.val.1 ≠ i.left := by
        intro he
        exact r.property (Prod.ext he h)
      have ht : r.val.val.1 < i.left := by
        have hr := r.val.property
        have hv := congrArg Fin.val h
        have hi := i.right_val
        have hne : r.val.val.1.val ≠ i.left.val := fun he => hn (Fin.ext he)
        change r.val.val.1.val < r.val.val.2.val at hr
        change r.val.val.1.val < i.left.val
        omega
      exact radicalEndSpan_root_mem i ⟨⟨(r.val.val.1,i.left),ht⟩,
        fun he => i.left_ne_right (congrArg Prod.snd he)⟩
    · exact (radicalEndSpan i).zero_mem

private theorem radicalEndSpan_lie_stable_of_roots {n : ℕ} (i : AdjacentPosition n)
    (D : Module.End ℂ (MatrixPolynomial n))
    (hD : ∀ r : RadicalRoot i,
      ⁅D,(matrixUnitDerivation r.val.val.1 r.val.val.2).toLinearMap⁆ ∈ radicalEndSpan i)
    {A : Module.End ℂ (MatrixPolynomial n)} (hA : A∈radicalEndSpan i) :
    ⁅D,A⁆ ∈ radicalEndSpan i := by
  induction hA using Submodule.span_induction with
  | mem A hA => obtain ⟨r,rfl⟩ := hA; exact hD r
  | zero => simpa only [lie_zero] using (radicalEndSpan i).zero_mem
  | add A B hA hB ihA ihB => rw [lie_add]; exact (radicalEndSpan i).add_mem ihA ihB
  | smul c A hA ihA => rw [lie_smul]; exact (radicalEndSpan i).smul_mem c ihA

theorem radicalEndSpan_raising {n : ℕ} (i : AdjacentPosition n)
    {A : Module.End ℂ (MatrixPolynomial n)} (hA : A∈radicalEndSpan i) :
    ⁅(matrixUnitDerivation i.left i.right).toLinearMap,A⁆ ∈ radicalEndSpan i :=
  radicalEndSpan_lie_stable_of_roots i _ (radicalEndSpan_raising_root i) hA

theorem radicalEndSpan_lowering {n : ℕ} (i : AdjacentPosition n)
    {A : Module.End ℂ (MatrixPolynomial n)} (hA : A∈radicalEndSpan i) :
    ⁅(matrixUnitDerivation i.right i.left).toLinearMap,A⁆ ∈ radicalEndSpan i :=
  radicalEndSpan_lie_stable_of_roots i _ (radicalEndSpan_lowering_root i) hA

theorem radicalEndSpan_cartan {n : ℕ} (i : AdjacentPosition n)
    {A : Module.End ℂ (MatrixPolynomial n)} (hA : A∈radicalEndSpan i) :
    ⁅polynomialRootCartan i.left i.right,A⁆ ∈ radicalEndSpan i := by
  rw [← polynomial_root_e_f i.left i.right,lie_lie]
  exact (radicalEndSpan i).sub_mem
    (radicalEndSpan_raising i (radicalEndSpan_lowering i hA))
    (radicalEndSpan_lowering i (radicalEndSpan_raising i hA))

end
end Schubert.RS.Representation
