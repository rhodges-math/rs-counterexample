import Schubert.RS.CompositionPresentation
import Schubert.RS.Representation.CyclicGeneration

/-! The dominant base case for the Joseph-Polo induction, proved without
assuming the general presentation, PBW, or Demazure character formula. -/

namespace Schubert.RS.Representation
noncomputable section
open scoped BigOperators

theorem presentation_dominant_cyclic_line {n : ℕ} (u : Composition n)
    (hu : Antitone u) (q : PresentationQuotient u) :
    ∃ c : ℂ, c • presentationGenerator u=q := by
  have hroot (r : PositiveRoot n) : rootOperator r • presentationGenerator u=0 :=
    killing_root_kills_generator u r (hu r.property.le)
  have hlie (A : upperNilpotent n) :
      UniversalEnvelopingAlgebra.ι ℂ A • presentationGenerator u=0 := by
    rw [← (rootBasis n).sum_repr A]
    simp only [map_sum,map_smul,Finset.sum_smul,smul_assoc,rootBasis_apply]
    change (∑ r, (rootBasis n).repr A r • (rootOperator r • presentationGenerator u))=0
    simp only [hroot,smul_zero,Finset.sum_const_zero]
  obtain ⟨a,rfl⟩ := presentation_is_cyclic u q
  induction a using enveloping_induction with
  | hC c => exact ⟨c,by simp⟩
  | hι A => exact ⟨0,by rw [hlie,zero_smul]⟩
  | hmul a b ha hb =>
      obtain ⟨c,hc⟩ := ha
      obtain ⟨d,hd⟩ := hb
      refine ⟨d*c,?_⟩
      calc
        (d*c) • presentationGenerator u = d • (c • presentationGenerator u) := mul_smul _ _ _
        _ = d • (a • presentationGenerator u) := congrArg (d • ·) hc
        _ = a • (d • presentationGenerator u) := smul_comm _ _ _
        _ = a • (b • presentationGenerator u) := congrArg (a • ·) hd
        _ = (a*b) • presentationGenerator u := (mul_smul _ _ _).symm
  | hadd a b ha hb =>
      obtain ⟨c,hc⟩ := ha
      obtain ⟨d,hd⟩ := hb
      exact ⟨c+d,by rw [add_smul,add_smul,hc,hd]⟩

/-- The Joseph-Polo presentation property for every dominant composition,
including ties and rank zero. -/
theorem compositionFlagJosephPolo_of_antitone {n : ℕ} (u : Composition n)
    (hu : Antitone u) : CompositionFlagJosephPolo u := by
  apply (compositionFlagJosephPolo_iff_injective u).mpr
  intro x y hxy
  obtain ⟨c,hc⟩ := presentation_dominant_cyclic_line u hu x
  obtain ⟨d,hd⟩ := presentation_dominant_cyclic_line u hu y
  let f := (compositionPresentationMap u).restrictScalars ℂ
  have hf : f (presentationGenerator u)=compositionFlagGenerator u :=
    compositionPresentationMap_generator u
  have hcd : c=d := by
    apply smul_left_injective ℂ (compositionFlagGenerator_ne_zero u)
    change f x=f y at hxy
    rw [← hc,← hd,map_smul,map_smul,hf] at hxy
    exact hxy
  rw [← hc,← hd,hcd]

end
end Schubert.RS.Representation
