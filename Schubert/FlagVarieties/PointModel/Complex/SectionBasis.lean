import Schubert.FlagVarieties.PointModel.Complex.Sections

/-!
# The standard-monomial basis of the sections

For a Bruhat ideal `S` and a column sequence `h` (shape `m`, weight `λ = shapeWeight m`), the
restrictions of the standard products `flagColumnProduct h T`, `T ∈ chainSet h S`, form a basis of
`sectionSpace S λ = H⁰(X_S, 𝓛(-λ))` (`sectionBasis`, given `GlobalSectionsConstant`). Each basis
vector is an eigenvector of the left torus action, of weight the row content `flagTupleWeight h T`
(`evalAt_diagonal_mul_flagColumnProduct`). This gives the characters of the section modules.
-/

open Schubert Demazure.FlagModule Demazure.SchubertUnions FinPermutation

namespace FlagVarieties.PointModel.Complex

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

/-- The Demazure library's standard-monomial independence on the union of the orbits of `S`, indexed
by `chainSet`. -/
theorem linearIndependent_unionRestriction {d : ℕ} (h : Fin d → Fin n)
    (S : Finset (Equiv.Perm (Fin n))) :
    LinearIndependent ℂ (fun T : {T // T ∈ chainSet h S} =>
      unionRestriction S (flagColumnProduct h T.1)) := by
  classical
  have hW : ∀ T : {T // T ∈ chainSet h S}, ∃ w ∈ S, HasFlagDefiningChain h T.1 w :=
    fun T => mem_chainSet.mp T.2
  choose W hWS hWc using hW
  have hind := flagColumnProduct_linearIndependent_on_union h (fun T => T.1)
    Subtype.val_injective W hWc
  let Ψ : (UnionOrbit S → ℂ) →ₗ[ℂ] ({T // T ∈ chainSet h S} → List (PositiveRoot n × ℂ) → ℂ) :=
    { toFun := fun F j z => F ⟨⟨W j, hWS j⟩, z⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact LinearIndependent.of_comp Ψ hind

/-- The section of `𝓛(-λ)` over `X_S` given by a standard product. -/
def standardSection {d : ℕ} (h : Fin d → Fin n) (S : Finset (Equiv.Perm (Fin n)))
    (T : (j : Fin d) → FlagMinorRowSet (h j)) :
    sectionSpace S (shapeWeightZ (columnMultiplicity h)) :=
  minorRestriction S (columnMultiplicity h) ⟨flagColumnProduct h T, by
    rw [minorSpan_columnMultiplicity]
    exact Submodule.subset_span ⟨T, rfl⟩⟩

theorem linearIndependent_standardSection {d : ℕ} (h : Fin d → Fin n)
    (S : Finset (Equiv.Perm (Fin n))) :
    LinearIndependent ℂ (fun T : {T // T ∈ chainSet h S} => standardSection h S T.1) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc T
  have hsum : ∑ T : {T // T ∈ chainSet h S}, c T • (flagColumnProduct h T.1) ∈
      vanishSpan (columnMultiplicity h) S := by
    have hmem : ∀ T : {T // T ∈ chainSet h S},
        flagColumnProduct h T.1 ∈ minorSpan (columnMultiplicity h) := fun T => by
      rw [minorSpan_columnMultiplicity]
      exact Submodule.subset_span ⟨T.1, rfl⟩
    have hsm : ∑ T : {T // T ∈ chainSet h S}, c T • (flagColumnProduct h T.1) ∈
        minorSpan (columnMultiplicity h) :=
      Submodule.sum_mem _ fun T _ => Submodule.smul_mem _ _ (hmem T)
    have heq : (⟨_, hsm⟩ : minorSpan (columnMultiplicity h)) =
        ∑ T : {T // T ∈ chainSet h S}, c T • (⟨flagColumnProduct h T.1, hmem T⟩ :
          minorSpan (columnMultiplicity h)) := by
      ext
      simp
    exact (minorRestriction_eq_zero_iff (S := S) ⟨_, hsm⟩).mp (by
      rw [heq, map_sum]
      simp only [map_smul]
      exact hc)
  have hz := LinearMap.mem_ker.mp (Submodule.mem_inf.mp hsum).2
  rw [map_sum] at hz
  simp only [map_smul] at hz
  exact (Fintype.linearIndependent_iff.mp (linearIndependent_unionRestriction h S)) c hz T

/-- **The standard-monomial basis of `H⁰(X_S, 𝓛(-λ))`.** -/
def sectionBasisOfGlobalSectionsConstant (hglobalSections : ∀ w : Equiv.Perm (Fin n),
    GlobalSectionsConstant w)
    {S : Finset (Equiv.Perm (Fin n))} (hS : BruhatLower S) {d : ℕ} (h : Fin d → Fin n) :
    Module.Basis {T // T ∈ chainSet h S} ℂ (sectionSpace S (shapeWeightZ (columnMultiplicity h))) :=
  haveI : FiniteDimensional ℂ (sectionSpace S (shapeWeightZ (columnMultiplicity h))) :=
    Module.Finite.of_surjective _ (minorRestriction_surjective_of_globalSectionsConstant
        hglobalSections hS
        _)
  basisOfLinearIndependentOfCardEqFinrank' _ (linearIndependent_standardSection h S) (by
    rw [Fintype.card_coe, finrank_sectionSpace_of_globalSectionsConstant hglobalSections hS h])

theorem sectionBasisOfGlobalSectionsConstant_apply
    (hglobalSections : ∀ w : Equiv.Perm (Fin n), GlobalSectionsConstant w)
    {S : Finset (Equiv.Perm (Fin n))} (hS : BruhatLower S) {d : ℕ} (h : Fin d → Fin n)
    (T : {T // T ∈ chainSet h S}) :
    sectionBasisOfGlobalSectionsConstant hglobalSections hS h T = standardSection h S T.1 := by
  simp [sectionBasisOfGlobalSectionsConstant]

/-! ### Left torus weights -/

theorem evalAt_diagonal_mul_flagRowMinor (s : Fin n → ℂ) (g : Matrix (Fin n) (Fin n) ℂ) (k : Fin n)
    (R : FlagMinorRowSet k) :
    evalAt (Matrix.diagonal s * g) (flagRowMinor k R.rows) =
      (∏ i, s i ^ (if i ∈ R.val then 1 else 0)) * evalAt g (flagRowMinor k R.rows) := by
  classical
  rw [evalAt_flagRowMinor, evalAt_flagRowMinor]
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
theorem evalAt_diagonal_mul_flagColumnProduct {d : ℕ} (h : Fin d → Fin n)
    (T : (j : Fin d) → FlagMinorRowSet (h j)) (s : Fin n → ℂ) (g : Matrix (Fin n) (Fin n) ℂ) :
    evalAt (Matrix.diagonal s * g) (flagColumnProduct h T) =
      (∏ i, s i ^ flagTupleWeight h T i) * evalAt g (flagColumnProduct h T) := by
  simp only [flagColumnProduct, map_prod, evalAt_diagonal_mul_flagRowMinor, Finset.prod_mul_distrib]
  congr 1
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Finset.prod_pow_eq_pow_sum]
  rfl

end

end FlagVarieties.PointModel.Complex
