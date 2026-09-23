import Schubert.RS.Representation.KillingStraightening
import Schubert.RS.EnvelopingOrbit
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! Finite spanning of the actual JP presentation in every rank, with no
JP, DCF or PBW assumption. Sorting root words lowers the length of the
commutator error. Moving an excessive root count to the right kills the
cyclic generator. This proves spanning, not independence or JP. -/

namespace Schubert.RS.Representation
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 1000000

abbrev BoundedJPPowers {n : ℕ} (u : Composition n) :=
  (r : PositiveRoot n) → Fin (jpExponent u r)

def boundedJPSpan {n : ℕ} (u : Composition n) (order : RootOrdering n) :
    Submodule ℂ (PresentationQuotient u) :=
  Submodule.span ℂ (Set.range fun powers : BoundedJPPowers u =>
    orderedRootMonomial order (fun r => (powers r).val) • presentationGenerator u)

theorem jp_root_power_kills_of_le {n : ℕ} (u : Composition n) (r : PositiveRoot n)
    (k : ℕ) (hk : jpExponent u r ≤ k) :
    rootOperator r ^ k • presentationGenerator u = 0 := by
  conv_lhs => rw [← Nat.sub_add_cancel hk]
  rw [pow_add, mul_smul, jp_relation_kills_generator, smul_zero]

private theorem filter_root_eq_replicate {n : ℕ} (r : PositiveRoot n)
    (roots : List (PositiveRoot n)) :
    roots.filter (fun s => !(decide (s ≠ r))) = List.replicate (roots.count r) r := by
  classical
  simp only [decide_not, Bool.not_not]
  induction roots with
  | nil => simp
  | cons s roots ih =>
    by_cases hs : s = r
    · subst s; simp [ih, List.replicate_succ]
    · simp [hs, ih]

private theorem shorter_word_smul_mem {n : ℕ} (u : Composition n)
    (S : Submodule ℂ (PresentationQuotient u)) (d : ℕ)
    (hshort : ∀ roots : List (PositiveRoot n), roots.length < d →
      rootWord roots • presentationGenerator u ∈ S)
    {a : Enveloping n} (ha : a ∈ shorterKillingSpan (fun _ : Fin n => 0) d) :
    a • presentationGenerator u ∈ S := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨roots, _, _, hd, rfl⟩ := ha
    exact hshort roots hd
  | zero => simpa using S.zero_mem
  | add a b ha hb ia ib => simpa only [add_smul] using S.add_mem ia ib
  | smul c a ha ia => simpa only [smul_assoc] using S.smul_mem c ia

theorem rootWord_mem_boundedJPSpan {n : ℕ} (u : Composition n) (order : RootOrdering n)
    (roots : List (PositiveRoot n)) :
    rootWord roots • presentationGenerator u ∈ boundedJPSpan u order := by
  classical
  have hk : IsKillingWord (fun _ : Fin n => 0) roots := by intro r hr; exact le_rfl
  have hshort (other : List (PositiveRoot n)) (hother : other.length < roots.length) :
      rootWord other • presentationGenerator u ∈ boundedJPSpan u order :=
    rootWord_mem_boundedJPSpan u order other
  by_cases hb : ∀ r : PositiveRoot n, roots.count r < jpExponent u r
  · let powers : BoundedJPPowers u := fun r => ⟨roots.count r, hb r⟩
    have hc : rootWord (countWord order roots) • presentationGenerator u ∈ boundedJPSpan u order := by
      rw [rootWord_countWord]
      exact Submodule.subset_span ⟨powers, rfl⟩
    have hd := shorter_word_smul_mem u (boundedJPSpan u order) roots.length hshort
      (killingWord_perm_difference (fun _ : Fin n => 0) (countWord_perm order roots) hk)
    rw [sub_smul] at hd
    simpa only [sub_add_cancel] using (boundedJPSpan u order).add_mem hd hc
  · push Not at hb
    obtain ⟨r, hr⟩ := hb
    let other := roots.filter (fun s => decide (s ≠ r)) ++ List.replicate (roots.count r) r
    have hp : roots.Perm other := by
      have h := (List.filter_append_perm (fun s => decide (s ≠ r)) roots).symm
      rwa [filter_root_eq_replicate] at h
    have hz : rootWord other • presentationGenerator u = 0 := by
      simp only [other, rootWord, List.map_append, List.prod_append,
        List.map_replicate, List.prod_replicate, mul_smul]
      rw [jp_root_power_kills_of_le u r _ hr, smul_zero]
    have hd := shorter_word_smul_mem u (boundedJPSpan u order) roots.length hshort
      (killingWord_perm_difference (fun _ : Fin n => 0) hp hk)
    simpa only [sub_smul, hz, sub_zero] using hd
termination_by roots.length

theorem rootWord_presentation_span {n : ℕ} (u : Composition n) :
    Submodule.span ℂ (Set.range fun roots : List (PositiveRoot n) =>
      rootWord roots • presentationGenerator u) = ⊤ := by
  let S := Submodule.span ℂ (Set.range fun roots : List (PositiveRoot n) =>
    rootWord roots • presentationGenerator u)
  let ρ : Enveloping n →ₐ[ℂ] Module.End ℂ (PresentationQuotient u) :=
    Algebra.lsmul ℂ ℂ (PresentationQuotient u)
  have hroot (r : PositiveRoot n) (x : PresentationQuotient u) (hx : x ∈ S) :
      rootOperator r • x ∈ S := by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨roots, rfl⟩ := hx
      exact Submodule.subset_span ⟨r :: roots, by simp only [rootWord_cons, mul_smul]⟩
    | zero => simpa using S.zero_mem
    | add x y hx hy ix iy => simpa only [smul_add] using S.add_mem ix iy
    | smul c x hx ix => rw [smul_comm]; exact S.smul_mem c ix
  have hLie (A : upperNilpotent n) (x : PresentationQuotient u) (hx : x ∈ S) :
      ρ (UniversalEnvelopingAlgebra.ι ℂ A) x ∈ S := by
    rw [← (rootBasis n).sum_repr A]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, rootBasis_apply]
    apply S.sum_mem
    intro r hr
    exact S.smul_mem _ (hroot r x hx)
  apply top_unique
  intro x _
  obtain ⟨a, rfl⟩ := presentation_is_cyclic u x
  apply enveloping_stable ρ S hLie a
  exact Submodule.subset_span ⟨[], by simp⟩

theorem boundedJPSpan_eq_top {n : ℕ} (u : Composition n) (order : RootOrdering n) :
    boundedJPSpan u order = ⊤ := by
  apply top_unique
  rw [← rootWord_presentation_span u]
  apply Submodule.span_le.mpr
  rintro x ⟨roots, rfl⟩
  exact rootWord_mem_boundedJPSpan u order roots

theorem presentation_finite {n : ℕ} (u : Composition n) :
    FiniteDimensional ℂ (PresentationQuotient u) := by
  let order := defaultRootOrdering n
  let v := fun powers : BoundedJPPowers u =>
    orderedRootMonomial order (fun r => (powers r).val) • presentationGenerator u
  letI := FiniteDimensional.span_of_finite ℂ (Set.finite_range v)
  have h : Submodule.span ℂ (Set.range v) = ⊤ := boundedJPSpan_eq_top u order
  exact Module.Finite.of_surjective (Submodule.subtype (Submodule.span ℂ (Set.range v)))
    (by intro x; exact ⟨⟨x, by rw [h]; trivial⟩, rfl⟩)

theorem presentation_finrank_le {n : ℕ} (u : Composition n) :
    Module.finrank ℂ (PresentationQuotient u) ≤ ∏ r : PositiveRoot n, jpExponent u r := by
  have h := finrank_le_of_span_eq_top (boundedJPSpan_eq_top u (defaultRootOrdering n))
  simpa only [Fintype.card_pi, Fintype.card_fin] using h

end
end Schubert.RS.Representation
