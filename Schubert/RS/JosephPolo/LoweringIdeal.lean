import Schubert.RS.JosephPolo.LoweringPowers

namespace Schubert.RS.Representation
noncomputable section
open FinPermutation
set_option maxHeartbeats 1600000

theorem jp_mem_iff_generator_zero {n : ℕ} (u : Composition n) (a : Enveloping n) :
    a ∈ jpLeftIdeal u ↔ a • presentationGenerator u=0 := by
  have he : a • presentationGenerator u = (Submodule.Quotient.mk a : PresentationQuotient u) := by
    change a • (Submodule.Quotient.mk 1 : PresentationQuotient u) = _
    rw [← Submodule.Quotient.mk_smul]
    simp
  rw [he, Submodule.Quotient.mk_eq_zero]

theorem loweringEnveloping_root_relation_mem {n : ℕ} (u : Composition n)
    (i : AdjacentPosition n) (hu : u i.left ≤ u i.right) (r : PositiveRoot n) :
    loweringEnveloping i (-((u i.right-u i.left : ℕ) : ℂ)) (rootOperator r^jpExponent u r) ∈ jpLeftIdeal u := by
  rcases r with ⟨⟨a,b⟩,hab⟩
  by_cases hal : a=i.left
  · subst a
    by_cases hbr : b=i.right
    · subst b
      change loweringEnveloping i (-((u i.right-u i.left : ℕ) : ℂ))
        (rootOperator (adjacentPositiveRoot i)^(u i.right-u i.left+1)) ∈ _
      rw [loweringEnveloping_simple_relation]
      exact (jpLeftIdeal u).zero_mem
    · have hb : i.right < b := by
        have hv := i.right_val
        have hn : b.val≠i.right.val := fun h => hbr (Fin.ext h)
        change i.left.val < b.val at hab
        change i.right.val < b.val
        omega
      let r : PositiveRoot n := ⟨(i.left,b),hab⟩
      let s : PositiveRoot n := ⟨(i.right,b),hb⟩
      have hr : r≠adjacentPositiveRoot i := fun h => hbr (congrArg (fun t : PositiveRoot n => t.val.2) h)
      have hs : UniversalEnvelopingAlgebra.ι ℂ (loweringUpper i (rootVector r)) = rootOperator s := by
        rw [show loweringUpper i (rootVector r)=rootVector s from loweringUpper_outgoing i b hb]
        rfl
      have hc : Commute (rootOperator r) (UniversalEnvelopingAlgebra.ι ℂ (loweringUpper i (rootVector r))) := by
        rw [hs]
        exact rootOperator_commute r s (ne_of_gt hb) (ne_of_gt hab)
      change loweringEnveloping i _ (rootOperator r^(u b-u i.left+1)) ∈ _
      rw [loweringEnveloping_nonsimple_pow i _ r hr hc, hs, nsmul_eq_mul]
      apply (jpLeftIdeal u).smul_mem
      apply (jp_mem_iff_generator_zero u _).mpr
      rw [mul_smul]
      exact jp_outgoing_lowering_relation u i hu b hb
  · by_cases hbr : b=i.right
    · subst b
      have ha : a < i.left := by
        have hv := i.right_val
        have hn : a.val≠i.left.val := fun h => hal (Fin.ext h)
        change a.val < i.right.val at hab
        change a.val < i.left.val
        omega
      let r : PositiveRoot n := ⟨(a,i.right),hab⟩
      let s : PositiveRoot n := ⟨(a,i.left),ha⟩
      have hr : r≠adjacentPositiveRoot i := fun h => hal (congrArg (fun t : PositiveRoot n => t.val.1) h)
      have hs : UniversalEnvelopingAlgebra.ι ℂ (loweringUpper i (rootVector r)) = -rootOperator s := by
        rw [show loweringUpper i (rootVector r) = -rootVector s from loweringUpper_incoming i a ha, map_neg]
        rfl
      have hc : Commute (rootOperator r) (UniversalEnvelopingAlgebra.ι ℂ (loweringUpper i (rootVector r))) := by
        rw [hs]
        exact (rootOperator_commute r s (ne_of_gt hab) (ne_of_gt ha)).neg_right
      change loweringEnveloping i _ (rootOperator r^(u i.right-u a+1)) ∈ _
      rw [loweringEnveloping_nonsimple_pow i _ r hr hc, hs, mul_neg, nsmul_eq_mul]
      apply (jpLeftIdeal u).smul_mem
      apply (jpLeftIdeal u).neg_mem
      apply (jp_mem_iff_generator_zero u _).mpr
      rw [mul_smul]
      exact jp_incoming_lowering_relation u i hu a ha
    · let r : PositiveRoot n := ⟨(a,b),hab⟩
      have hr : r≠adjacentPositiveRoot i := fun h => hal (congrArg (fun t : PositiveRoot n => t.val.1) h)
      have hs : UniversalEnvelopingAlgebra.ι ℂ (loweringUpper i (rootVector r)) = 0 := by
        rw [loweringUpper_other i r hal hbr, map_zero]
      have hc : Commute (rootOperator r) (UniversalEnvelopingAlgebra.ι ℂ (loweringUpper i (rootVector r))) := by
        rw [hs]
        exact Commute.zero_right _
      change loweringEnveloping i _ (rootOperator r^(u b-u a+1)) ∈ _
      rw [loweringEnveloping_nonsimple_pow i _ r hr hc, hs, mul_zero, smul_zero]
      exact (jpLeftIdeal u).zero_mem

theorem loweringEnveloping_left_factor_mem {n : ℕ} (u : Composition n)
    (i : AdjacentPosition n) (w : ℂ) (a b : Enveloping n)
    (hb : b ∈ jpLeftIdeal u) (hFb : loweringEnveloping i w b ∈ jpLeftIdeal u) :
    loweringEnveloping i w (a*b) ∈ jpLeftIdeal u := by
  induction a using enveloping_induction generalizing b with
  | hC c =>
    rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, map_smul]
    exact ((jpLeftIdeal u).restrictScalars ℂ).smul_mem c hFb
  | hι A =>
    rw [loweringEnveloping_generator_mul]
    apply (jpLeftIdeal u).add_mem ((jpLeftIdeal u).smul_mem _ hFb)
    apply (jpLeftIdeal u).sub_mem ((jpLeftIdeal u).smul_mem _ hb)
    apply ((jpLeftIdeal u).restrictScalars ℂ).smul_mem
    exact (jpLeftIdeal u).add_mem (cartanEnveloping_mem_jp _ u hb)
      (((jpLeftIdeal u).restrictScalars ℂ).smul_mem w hb)
  | hmul a c ha hc =>
    rw [mul_assoc]
    exact ha _ ((jpLeftIdeal u).smul_mem c hb) (hc _ hb hFb)
  | hadd a c ha hc =>
    rw [add_mul, map_add]
    exact (jpLeftIdeal u).add_mem (ha _ hb hFb) (hc _ hb hFb)

/-- The constructed lowering operator preserves the complete JP LEFT
ideal, so it descends to the actual universal quotient. -/
theorem loweringEnveloping_mem_jp {n : ℕ} (u : Composition n) (i : AdjacentPosition n)
    (hu : u i.left ≤ u i.right) {a : Enveloping n} (ha : a ∈ jpLeftIdeal u) :
    loweringEnveloping i (-((u i.right-u i.left : ℕ) : ℂ)) a ∈ jpLeftIdeal u := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨r,rfl⟩ := ha
    exact loweringEnveloping_root_relation_mem u i hu r
  | zero => simpa using (jpLeftIdeal u).zero_mem
  | add a b ha hb ia ib => simpa using (jpLeftIdeal u).add_mem ia ib
  | smul a b hb ib => exact loweringEnveloping_left_factor_mem u i _ a b hb ib

def presentationLowering {n : ℕ} (u : Composition n) (i : AdjacentPosition n)
    (hu : u i.left ≤ u i.right) : Module.End ℂ (PresentationQuotient u) :=
  ((jpLeftIdeal u).restrictScalars ℂ).mapQ ((jpLeftIdeal u).restrictScalars ℂ)
    (loweringEnveloping i (-((u i.right-u i.left : ℕ) : ℂ)))
    (fun a ha => loweringEnveloping_mem_jp u i hu ha)

theorem presentationLowering_mk {n : ℕ} (u : Composition n) (i : AdjacentPosition n)
    (hu : u i.left ≤ u i.right) (a : Enveloping n) :
    presentationLowering u i hu (Submodule.Quotient.mk a) =
      Submodule.Quotient.mk (loweringEnveloping i (-((u i.right-u i.left : ℕ) : ℂ)) a) := rfl

theorem presentationLowering_generator {n : ℕ} (u : Composition n) (i : AdjacentPosition n)
    (hu : u i.left ≤ u i.right) : presentationLowering u i hu (presentationGenerator u)=0 := by
  change presentationLowering u i hu (Submodule.Quotient.mk 1)=0
  rw [presentationLowering_mk, loweringEnveloping_one]
  rfl

end
end Schubert.RS.Representation
