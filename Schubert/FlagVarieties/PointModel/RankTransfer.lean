import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
import Mathlib.Algebra.Algebra.Rat
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Ranks of rational vectors do not depend on the field

For finitely many vectors `v i : ι' → ℚ` with finite coordinates, and a field `E` of characteristic
`0`, the `E`-span of the images `algebraMap ℚ E ∘ v i` has the same dimension as the `ℚ`-span of the
`v i` (`finrank_span_algebraMap_comp`). Consequently:

* the kernel of `c ↦ ∑ᵢ cᵢ (v i)` has the same dimension over every such field
  (`finrank_ker_linearCombination_algebraMap_comp`);
* an inclusion of such kernels that holds over one field of characteristic `0` holds over all
  (`ker_le_of_ker_le`).

This is how the standard-monomial facts proved over `ℂ` are transferred to other fields.
-/

open Module

namespace FlagVarieties.PointModel

noncomputable section

variable {ι ι' : Type*} [Fintype ι] [Fintype ι']

/-- The coordinatewise image of a rational vector in `E`. -/
abbrev ratVec (E : Type*) [Field E] [CharZero E] (x : ι' → ℚ) : ι' → E := algebraMap ℚ E ∘ x

theorem faithfulSMul_rat (E : Type*) [Field E] [CharZero E] : FaithfulSMul ℚ E :=
  (faithfulSMul_iff_algebraMap_injective ℚ E).mpr (algebraMap ℚ E).injective

/-- **Rank invariance.** -/
theorem finrank_span_algebraMap_comp (E : Type*) [Field E] [CharZero E] (v : ι → ι' → ℚ) :
    finrank E (Submodule.span E (Set.range fun i => ratVec E (v i))) =
      finrank ℚ (Submodule.span ℚ (Set.range v)) := by
  classical
  have := faithfulSMul_rat E
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' ℚ v
  have : Finite κ := Finite.of_injective a ha
  let : Fintype κ := Fintype.ofFinite κ
  have hliE : LinearIndependent E (fun k => ratVec E (v (a k))) :=
    (linearIndependent_algebraMap_comp_iff (v := v ∘ a)).mpr hli
  have hspanE : Submodule.span E (Set.range fun i => ratVec E (v i)) =
      Submodule.span E (Set.range fun k => ratVec E (v (a k))) := by
    refine le_antisymm (Submodule.span_le.mpr ?_)
      (Submodule.span_mono (Set.range_comp_subset_range a fun i => ratVec E (v i)))
    rintro _ ⟨i, rfl⟩
    have hmem : v i ∈ Submodule.span ℚ (Set.range (v ∘ a)) := by
      rw [hspan]
      exact Submodule.subset_span ⟨i, rfl⟩
    -- the coordinatewise map is `ℚ`-linear, so it sends the `ℚ`-span into the `E`-span
    refine Submodule.span_induction (p := fun x _ =>
      ratVec E x ∈ Submodule.span E (Set.range fun k => ratVec E (v (a k)))) ?_ ?_ ?_ ?_ hmem
    · rintro _ ⟨k, rfl⟩
      exact Submodule.subset_span ⟨k, rfl⟩
    · have : ratVec E (0 : ι' → ℚ) = 0 := by
        funext x
        simp
      rw [this]
      exact Submodule.zero_mem _
    · intro x y _ _ hx hy
      have : ratVec E (x + y) = ratVec E x + ratVec E y := by
        funext z
        simp
      rw [this]
      exact Submodule.add_mem _ hx hy
    · intro q x _ hx
      have : ratVec E (q • x) = algebraMap ℚ E q • ratVec E x := by
        funext z
        simp [Algebra.smul_def]
      rw [this]
      exact Submodule.smul_mem _ _ hx
  rw [hspanE, finrank_span_eq_card hliE, ← hspan, finrank_span_eq_card hli]

omit [Fintype ι'] in
theorem finrank_ker_linearCombination (E : Type*) [Field E] (v : ι → ι' → E) :
    finrank E (LinearMap.ker (Fintype.linearCombination E v)) +
      finrank E (Submodule.span E (Set.range v)) = Fintype.card ι := by
  have h := LinearMap.finrank_range_add_finrank_ker (Fintype.linearCombination E v)
  rw [Fintype.range_linearCombination, Module.finrank_pi] at h
  omega

/-- The kernel of `c ↦ ∑ cᵢ vᵢ` has the same dimension over every field of characteristic `0`. -/
theorem finrank_ker_linearCombination_algebraMap_comp (E : Type*) [Field E] [CharZero E]
    (v : ι → ι' → ℚ) :
    finrank E (LinearMap.ker (Fintype.linearCombination E fun i => ratVec E (v i))) +
      finrank ℚ (Submodule.span ℚ (Set.range v)) = Fintype.card ι := by
  rw [← finrank_span_algebraMap_comp E v]
  exact finrank_ker_linearCombination E _

/-- The vector `(aᵢ, bᵢ)` of coordinates on `ι₁ ⊕ ι₂`. -/
def sumVec {ι₁ ι₂ : Type*} (a : ι → ι₁ → ℚ) (b : ι → ι₂ → ℚ) (i : ι) : ι₁ ⊕ ι₂ → ℚ :=
  Sum.elim (a i) (b i)

theorem sum_sumVec_eq_zero_iff {ι₁ ι₂ : Type*} (G : Type*) [Field G]
    [CharZero G] (a : ι → ι₁ → ℚ) (b : ι → ι₂ → ℚ) (c : ι → G) :
    ∑ i, c i • ratVec G (sumVec a b i) = 0 ↔
      (∑ i, c i • ratVec G (a i) = 0 ∧ ∑ i, c i • ratVec G (b i) = 0) := by
  constructor
  · intro h
    constructor
    · funext x
      have := congrFun h (Sum.inl x)
      simpa [sumVec, Finset.sum_apply] using this
    · funext x
      have := congrFun h (Sum.inr x)
      simpa [sumVec, Finset.sum_apply] using this
  · rintro ⟨h1, h2⟩
    funext x
    rcases x with x | x
    · have := congrFun h1 x
      simpa [sumVec, Finset.sum_apply] using this
    · have := congrFun h2 x
      simpa [sumVec, Finset.sum_apply] using this

theorem ker_sumVec_le {ι₁ ι₂ : Type*} (G : Type*) [Field G]
    [CharZero G] (a : ι → ι₁ → ℚ) (b : ι → ι₂ → ℚ) :
    LinearMap.ker (Fintype.linearCombination G fun i => ratVec G (sumVec a b i)) ≤
      LinearMap.ker (Fintype.linearCombination G fun i => ratVec G (a i)) := by
  intro c hc
  rw [LinearMap.mem_ker, Fintype.linearCombination_apply] at hc ⊢
  exact ((sum_sumVec_eq_zero_iff G a b c).mp hc).1

/-- **Transfer of kernel inclusions.** For rational vectors `a i`, `b i`: if every relation
`∑ cᵢ aᵢ = 0` implies `∑ cᵢ bᵢ = 0` over one field `E` of characteristic `0`, then over every field
`F` of characteristic `0`. -/
theorem ker_le_of_ker_le {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] (E F : Type*) [Field E]
    [CharZero E] [Field F] [CharZero F] (a : ι → ι₁ → ℚ) (b : ι → ι₂ → ℚ)
    (hE : ∀ c : ι → E, ∑ i, c i • ratVec E (a i) = 0 → ∑ i, c i • ratVec E (b i) = 0)
    (c : ι → F) (hc : ∑ i, c i • ratVec F (a i) = 0) : ∑ i, c i • ratVec F (b i) = 0 := by
  classical
  -- over `E` the two kernels agree, hence the rational ranks agree
  have hEeq : LinearMap.ker (Fintype.linearCombination E fun i => ratVec E (sumVec a b i)) =
      LinearMap.ker (Fintype.linearCombination E fun i => ratVec E (a i)) := by
    refine le_antisymm (ker_sumVec_le E a b) fun c hc => ?_
    rw [LinearMap.mem_ker, Fintype.linearCombination_apply] at hc ⊢
    exact (sum_sumVec_eq_zero_iff E a b c).mpr ⟨hc, hE c hc⟩
  have h1 := finrank_ker_linearCombination_algebraMap_comp E (sumVec a b)
  have h2 := finrank_ker_linearCombination_algebraMap_comp E a
  rw [hEeq] at h1
  -- over `F` the kernel of `(a, b)` has the dimension of the kernel of `a`, hence they agree
  have h3 := finrank_ker_linearCombination_algebraMap_comp F (sumVec a b)
  have h4 := finrank_ker_linearCombination_algebraMap_comp F a
  have hFeq : LinearMap.ker (Fintype.linearCombination F fun i => ratVec F (sumVec a b i)) =
      LinearMap.ker (Fintype.linearCombination F fun i => ratVec F (a i)) :=
    Submodule.eq_of_le_of_finrank_eq (ker_sumVec_le F a b) (by omega)
  have hcmem : c ∈ LinearMap.ker (Fintype.linearCombination F fun i => ratVec F (a i)) := by
    rw [LinearMap.mem_ker, Fintype.linearCombination_apply]
    exact hc
  rw [← hFeq, LinearMap.mem_ker, Fintype.linearCombination_apply] at hcmem
  exact ((sum_sumVec_eq_zero_iff F a b c).mp hcmem).2

end

end FlagVarieties.PointModel
