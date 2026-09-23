import Schubert.RS.Representation.KillingStraightening
import Schubert.RS.EnvelopingOrbit

/-! Ordered-root spanning in the actual enveloping algebra. No PBW input. -/
namespace Schubert.RS.Representation
noncomputable section
open scoped BigOperators

theorem rootWord_span_eq_top (n : ℕ) :
    Submodule.span ℂ (Set.range (rootWord (n := n))) = ⊤ := by
  let S := Submodule.span ℂ (Set.range (rootWord (n := n)))
  let ρ : Enveloping n →ₐ[ℂ] Module.End ℂ (Enveloping n) :=
    Algebra.lsmul ℂ ℂ (Enveloping n)
  have hroot (r : PositiveRoot n) (x : Enveloping n) (hx : x ∈ S) :
      rootOperator r * x ∈ S := by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨roots, rfl⟩ := hx
      exact Submodule.subset_span ⟨r :: roots, rootWord_cons r roots⟩
    | zero => simpa using S.zero_mem
    | add x y hx hy ix iy => simpa only [mul_add] using S.add_mem ix iy
    | smul c x hx ix => rw [mul_smul_comm]; exact S.smul_mem c ix
  have hLie (A : upperNilpotent n) (x : Enveloping n) (hx : x ∈ S) :
      ρ (UniversalEnvelopingAlgebra.ι ℂ A) x ∈ S := by
    rw [← (rootBasis n).sum_repr A]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      rootBasis_apply]
    apply S.sum_mem
    intro r hr
    exact S.smul_mem _ (hroot r x hx)
  apply top_unique
  intro x _
  have h := enveloping_stable ρ S hLie x
    (Submodule.subset_span ⟨[], rootWord_nil⟩ : (1 : Enveloping n) ∈ S)
  change x * 1 ∈ S at h
  simpa using h

theorem orderedRootMonomial_span_eq_top {n : ℕ} (order : RootOrdering n) :
    Submodule.span ℂ (Set.range (orderedRootMonomial order)) = ⊤ := by
  let S := Submodule.span ℂ (Set.range (orderedRootMonomial order))
  have hk : orderedKillingSpan (fun _ : Fin n => 0) order ≤ S := by
    apply Submodule.span_le.mpr
    rintro x ⟨powers, _, _, rfl⟩
    exact Submodule.subset_span ⟨powers, rfl⟩
  apply top_unique
  rw [← rootWord_span_eq_top n]
  apply Submodule.span_le.mpr
  rintro x ⟨roots, rfl⟩
  cases roots with
  | nil =>
    have h : orderedRootMonomial order (fun _ => 0) = 1 := by
      simp [orderedRootMonomial]
    exact Submodule.subset_span ⟨fun _ => 0, h⟩
  | cons r roots =>
    exact hk (killingWord_mem_orderedSpan (fun _ : Fin n => 0) order (r :: roots)
      (by intro s hs; exact le_rfl) (by simp))

end
end Schubert.RS.Representation
