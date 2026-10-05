import Schubert.FlagVarieties.PointModel.BorelWeil
import Schubert.FlagVarieties.PointModel.Complex.SectionBasis

/-!
# The standard-monomial basis of the sections over a field of characteristic `0`

For an algebraically closed field `K` of characteristic `0`, a Bruhat ideal `S` and a column
sequence `h`, the restrictions of the standard products `colProd K h T`, `T ∈ chainSet h S`, form a
basis of `H⁰(X_S, 𝓛(-λ))` (`sectionBasis`); each is a weight vector of the left torus, of weight
the row content `flagTupleWeight h T` (`evalAt_diagonal_mul_colProd`). Independence is the
standard-monomial independence of the Demazure library over `ℂ`, transferred through rational
coordinates.
-/

open Schubert Demazure.FlagModule Demazure.SchubertUnions FinPermutation Module

namespace FlagVarieties.PointModel

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {K : Type*} [Field K] {n : ℕ}

/-- Over `ℂ`, the coordinate vectors of the standard monomials of `chainSet h S` are independent. -/
theorem linearIndependent_ratCoords_complex {d : ℕ} (h : Fin d → Fin n)
    (S : Finset (Equiv.Perm (Fin n))) :
    LinearIndependent ℂ (fun T : {T // T ∈ chainSet h S} => ratVec ℂ (ratCoords h S T.1)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hmem : ∑ T : {T // T ∈ chainSet h S}, c T • colProd ℂ h T.1 ∈ flagSpan ℂ h :=
    Submodule.sum_mem _ fun T _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨T.1, rfl⟩)
  have hcoord : coordMap ℂ h S (∑ T : {T // T ∈ chainSet h S}, c T • colProd ℂ h T.1) = 0 := by
    rw [map_sum]
    simp only [map_smul, coordMap_colProd]
    exact hc
  rw [coordMap_eq_zero_iff ℂ h S hmem] at hcoord
  have hz :
      unionRestriction S (∑ T : {T // T ∈ chainSet h S}, c T • flagColumnProduct h T.1) = 0 := by
    funext x
    obtain ⟨⟨w, hw⟩, z⟩ := x
    change flagOrbitRestriction w _ z = 0
    have := (orbitPoly_eq_zero_iff (K := ℂ) w _).mp (hcoord w hw) (upperRowMatrix z)
      ⟨upperRowMatrix_upper z, upperRowMatrix_diag z⟩
    exact this
  rw [map_sum] at hz
  simp only [map_smul] at hz
  exact (Fintype.linearIndependent_iff.mp
      (PointModel.Complex.linearIndependent_unionRestriction h S)) c hz

/-- The coordinate vectors of the standard monomials of `chainSet h S` are independent over every
field of characteristic `0`. -/
theorem linearIndependent_ratCoords [CharZero K] {d : ℕ} (h : Fin d → Fin n)
    (S : Finset (Equiv.Perm (Fin n))) :
    LinearIndependent K (fun T : {T // T ∈ chainSet h S} => ratVec K (ratCoords h S T.1)) := by
  have := faithfulSMul_rat K
  have := faithfulSMul_rat ℂ
  have hQ : LinearIndependent ℚ (fun T : {T // T ∈ chainSet h S} => ratCoords h S T.1) :=
    (linearIndependent_algebraMap_comp_iff (S := ℂ)
      (v := fun T : {T // T ∈ chainSet h S} => ratCoords h S T.1)).mp
      (linearIndependent_ratCoords_complex h S)
  exact (linearIndependent_algebraMap_comp_iff (S := K)
    (v := fun T : {T // T ∈ chainSet h S} => ratCoords h S T.1)).mpr hQ

/-- The section of `𝓛(-λ)` over `X_S` given by a standard product. -/
def standardSection (K : Type*) [Field K] {d : ℕ} (h : Fin d → Fin n)
    (S : Finset (Equiv.Perm (Fin n))) (T : (j : Fin d) → FlagMinorRowSet (h j)) :
    sectionSpace K S (shapeWeightZ (columnMultiplicity h)) :=
  minorRestriction K S (columnMultiplicity h) ⟨colProd K h T, colProd_mem_minorSpan h T⟩

theorem linearIndependent_standardSection [CharZero K] {d : ℕ} (h : Fin d → Fin n)
    (S : Finset (Equiv.Perm (Fin n))) :
    LinearIndependent K (fun T : {T // T ∈ chainSet h S} => standardSection K h S T.1) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hmem : ∑ T : {T // T ∈ chainSet h S}, c T • colProd K h T.1 ∈ flagSpan K h :=
    Submodule.sum_mem _ fun T _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨T.1, rfl⟩)
  have hmem' : ∑ T : {T // T ∈ chainSet h S}, c T • colProd K h T.1 ∈
      minorSpan K (columnMultiplicity h) := by
    rw [minorSpan_columnMultiplicity]
    exact hmem
  have heq : (⟨_, hmem'⟩ : minorSpan K (columnMultiplicity h)) =
      ∑ T : {T // T ∈ chainSet h S}, c T • (⟨colProd K h T.1, colProd_mem_minorSpan h T.1⟩ :
        minorSpan K (columnMultiplicity h)) := by
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul]
  have hzero : minorRestriction K S (columnMultiplicity h) ⟨_, hmem'⟩ = 0 := by
    rw [heq, map_sum]
    simp only [map_smul]
    exact hc
  have hv : ∑ T : {T // T ∈ chainSet h S}, c T • colProd K h T.1 ∈
      vanishSpan K (columnMultiplicity h) S :=
    (minorRestriction_eq_zero_iff (S := S) ⟨_, hmem'⟩).mp hzero
  have hcoord : coordMap K h S (∑ T : {T // T ∈ chainSet h S}, c T • colProd K h T.1) = 0 :=
    (mem_vanishSpan_iff_coordMap K h S hmem).mp hv
  have hsum : ∑ T : {T // T ∈ chainSet h S}, c T • ratVec K (ratCoords h S T.1) = 0 := by
    rw [← hcoord, map_sum]
    simp only [map_smul, coordMap_colProd]
  exact (Fintype.linearIndependent_iff.mp (linearIndependent_ratCoords (K := K) h S)) c hsum

/-- **The standard-monomial basis of `H⁰(X_S, 𝓛(-λ))`** over an algebraically closed field of
characteristic `0`. -/
def sectionBasisOfGlobalSectionsConstant [IsAlgClosed K] [CharZero K]
    (hglobalSections : ∀ w : Equiv.Perm (Fin n), GlobalSectionsConstant K w)
    {S : Finset (Equiv.Perm (Fin n))} (hS : BruhatLower S) {d : ℕ} (h : Fin d → Fin n) :
    Basis {T // T ∈ chainSet h S} K (sectionSpace K S (shapeWeightZ (columnMultiplicity h))) :=
  haveI : FiniteDimensional K (sectionSpace K S (shapeWeightZ (columnMultiplicity h))) :=
    Module.Finite.of_surjective _ (minorRestriction_surjective_of_globalSectionsConstant
        (standardMonomialTheory_of_charZero K) hglobalSections hS _)
  basisOfLinearIndependentOfCardEqFinrank' _ (linearIndependent_standardSection h S) (by
    rw [Fintype.card_coe, finrank_sectionSpace_of_globalSectionsConstant
        (standardMonomialTheory_of_charZero K) hglobalSections hS h])

theorem sectionBasisOfGlobalSectionsConstant_apply [IsAlgClosed K] [CharZero K]
    (hglobalSections : ∀ w : Equiv.Perm (Fin n), GlobalSectionsConstant K w)
    {S : Finset (Equiv.Perm (Fin n))} (hS : BruhatLower S) {d : ℕ} (h : Fin d → Fin n)
    (T : {T // T ∈ chainSet h S}) :
    sectionBasisOfGlobalSectionsConstant hglobalSections hS h T = standardSection K h S T.1 := by
  simp [sectionBasisOfGlobalSectionsConstant]

/-! ### Left torus weights -/

theorem evalAt_diagonal_mul_rowMinor (s : Fin n → K) (g : Matrix (Fin n) (Fin n) K) (k : Fin n)
    (R : FlagMinorRowSet k) :
    evalAt (Matrix.diagonal s * g) (rowMinor K k R.rows) =
      (∏ i, s i ^ (if i ∈ R.val then 1 else 0)) * evalAt g (rowMinor K k R.rows) := by
  classical
  rw [evalAt_rowMinor, evalAt_rowMinor]
  have hsub : (Matrix.diagonal s * g).submatrix R.rows (prefixIndex k) =
      Matrix.diagonal (s ∘ R.rows) * g.submatrix R.rows (prefixIndex k) := by
    ext a b
    simp [Matrix.diagonal_mul]
  rw [hsub, Matrix.det_mul, Matrix.det_diagonal]
  congr 1
  have h1 : ∏ a : Fin (k.val + 1), (s ∘ R.rows) a = ∏ i ∈ R.val, s i := by
    rw [← Finset.image_orderEmbOfFin_univ R.val (Finset.mem_powersetCard.mp R.property).2,
      Finset.prod_image fun a _ b _ hab => (R.val.orderEmbOfFin _).injective hab]
    rfl
  have h2 : ∏ i, s i ^ (if i ∈ R.val then 1 else 0) = ∏ i ∈ R.val, s i := by
    rw [← Finset.prod_subset (Finset.subset_univ R.val) fun i _ hi => by simp [hi]]
    exact Finset.prod_congr rfl fun i hi => by simp [hi]
  rw [h1, h2]

/-- **Left torus weights**: a standard product has weight its row content. -/
theorem evalAt_diagonal_mul_colProd {d : ℕ} (h : Fin d → Fin n)
    (T : (j : Fin d) → FlagMinorRowSet (h j)) (s : Fin n → K) (g : Matrix (Fin n) (Fin n) K) :
    evalAt (Matrix.diagonal s * g) (colProd K h T) =
      (∏ i, s i ^ flagTupleWeight h T i) * evalAt g (colProd K h T) := by
  simp only [colProd, map_prod, evalAt_diagonal_mul_rowMinor, Finset.prod_mul_distrib]
  congr 1
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Finset.prod_pow_eq_pow_sum]
  rfl

end

end FlagVarieties.PointModel
