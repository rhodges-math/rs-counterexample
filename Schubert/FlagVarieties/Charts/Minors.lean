import Schubert.FlagVarieties.Charts.AdaptedBasis
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Big cell minors

For a permutation `v`, an invertible matrix `g` over a commutative ring `A` and `j ≤ n`, the
initial column span `g · ⟨e₀, …, e_{j-1}⟩` is complementary to `tailSpan v j` iff the matrix
`bigCellBlock v j g`, whose columns are `g e₀, …, g e_{j-1}, e_{v(j)}, …, e_{v(n-1)}`, is
invertible (`isCompl_map_stdSpan_iff`). Its determinant is `±` the minor of `g` on the rows
`v(0), …, v(j-1)` and the first `j` columns.
-/

noncomputable section

namespace FlagVarieties

open Matrix

variable {A : Type*} [CommRing A] {n : ℕ}

/-- The matrix with columns `g e₀, …, g e_{j-1}, e_{v(j)}, …, e_{v(n-1)}`. -/
def bigCellBlock (v : Equiv.Perm (Fin n)) (j : ℕ) (g : Matrix (Fin n) (Fin n) A) :
    Matrix (Fin n) (Fin n) A :=
  Matrix.of fun r c => if c.val < j then g r c else (Pi.single (v c) (1 : A) : Fin n → A) r

theorem bigCellBlock_mulVec_single_of_lt (v : Equiv.Perm (Fin n)) {j : ℕ}
    (g : Matrix (Fin n) (Fin n) A) {c : Fin n} (hc : c.val < j) :
    bigCellBlock v j g *ᵥ Pi.single c 1 = g *ᵥ Pi.single c 1 := by
  funext r
  rw [Matrix.mulVec_single_one, Matrix.mulVec_single_one]
  simp [bigCellBlock, hc]

theorem bigCellBlock_mulVec_single_of_le (v : Equiv.Perm (Fin n)) {j : ℕ}
    (g : Matrix (Fin n) (Fin n) A) {c : Fin n} (hc : j ≤ c.val) :
    bigCellBlock v j g *ᵥ Pi.single c 1 = Pi.single (v c) 1 := by
  funext r
  rw [Matrix.mulVec_single_one]
  simp [bigCellBlock, not_lt.mpr hc]

/-- The span of the standard basis vectors from `j` on. -/
def stdTail (A : Type*) [CommRing A] (n j : ℕ) : Submodule A (Fin n → A) :=
  Submodule.span A (Pi.basisFun A (Fin n) '' {i | j ≤ i.val})

theorem isCompl_stdSpan_stdTail (j : ℕ) : IsCompl (stdSpan A n j) (stdTail A n j) := by
  have htail : stdTail A n j = tailSpan (Equiv.refl (Fin n)) j := by
    simp [stdTail, tailSpan, Pi.basisFun_apply]
  constructor
  · rw [Submodule.disjoint_def]
    intro x hx hx'
    rw [mem_stdSpan_iff] at hx
    rw [htail, mem_tailSpan_iff] at hx'
    funext i
    by_cases hi : i.val < j
    · simpa using hx' i hi
    · exact hx i (not_lt.mp hi)
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    have hx : x = ∑ i, x i • Pi.basisFun A (Fin n) i := by
      simpa using ((Pi.basisFun A (Fin n)).sum_repr x).symm
    rw [hx]
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases hi : i.val < j
    · exact Submodule.mem_sup_left (Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩))
    · exact Submodule.mem_sup_right
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, not_lt.mp hi, rfl⟩))

theorem map_bigCellBlock_stdSpan (v : Equiv.Perm (Fin n)) (j : ℕ)
    (g : Matrix (Fin n) (Fin n) A) :
    (stdSpan A n j).map (Matrix.toLin' (bigCellBlock v j g)) =
      (stdSpan A n j).map (Matrix.toLin' g) := by
  rw [stdSpan, Submodule.map_span, Submodule.map_span]
  congr 1
  apply Set.image_congr
  rintro _ ⟨c, hc, rfl⟩
  simp only [Pi.basisFun_apply, Matrix.toLin'_apply]
  exact bigCellBlock_mulVec_single_of_lt v g hc

theorem map_bigCellBlock_stdTail (v : Equiv.Perm (Fin n)) (j : ℕ)
    (g : Matrix (Fin n) (Fin n) A) :
    (stdTail A n j).map (Matrix.toLin' (bigCellBlock v j g)) = tailSpan v j := by
  rw [stdTail, Submodule.map_span, tailSpan, ← Set.image_comp]
  congr 1
  apply Set.image_congr
  intro c hc
  simp only [Function.comp_apply, Pi.basisFun_apply, Matrix.toLin'_apply]
  exact bigCellBlock_mulVec_single_of_le v g hc

/-- The initial column span of `g` is complementary to `tailSpan v j` iff `bigCellBlock v j g`
is invertible. -/
theorem isCompl_map_stdSpan_iff (v : Equiv.Perm (Fin n)) (j : ℕ)
    (g : Matrix (Fin n) (Fin n) A) :
    IsCompl ((stdSpan A n j).map (Matrix.toLin' g)) (tailSpan v j) ↔
      IsUnit (bigCellBlock v j g).det := by
  rw [← map_bigCellBlock_stdSpan v j g, ← map_bigCellBlock_stdTail v j g,
    ← Matrix.isUnit_iff_isUnit_det]
  generalize bigCellBlock v j g = M
  have hrange : (stdSpan A n j).map (Matrix.toLin' M) ⊔ (stdTail A n j).map (Matrix.toLin' M) =
      LinearMap.range (Matrix.toLin' M) := by
    rw [← Submodule.map_sup, (isCompl_stdSpan_stdTail j).sup_eq_top, Submodule.map_top]
  constructor
  · intro h
    rw [← Matrix.mulVec_surjective_iff_isUnit]
    intro y
    have hy : y ∈ LinearMap.range (Matrix.toLin' M) := by
      rw [← hrange, h.sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨x, rfl⟩ := hy
    exact ⟨x, rfl⟩
  · intro hM
    have hinj : Function.Injective (Matrix.toLin' M) := by
      intro a b hab
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply] at hab
      exact Matrix.mulVec_injective_of_isUnit hM hab
    constructor
    · rw [Submodule.disjoint_def]
      rintro x ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
      have : b = a := hinj hab
      subst this
      have h0 := (isCompl_stdSpan_stdTail (A := A) (n := n) j).disjoint
      rw [Submodule.disjoint_def] at h0
      rw [h0 b ha hb, map_zero]
    · rw [codisjoint_iff, hrange, LinearMap.range_eq_top]
      intro y
      obtain ⟨x, hx⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr hM y
      exact ⟨x, hx⟩

end FlagVarieties
