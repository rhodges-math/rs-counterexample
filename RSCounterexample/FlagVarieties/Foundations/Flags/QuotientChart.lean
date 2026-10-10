import RSCounterexample.FlagVarieties.Foundations.Flags.Ring

/-!
# Normalized quotient charts

For a decomposition `U × V`, the chart condition says that the selected
coordinates `U` map isomorphically onto the quotient. Such a kernel
has a unique normalized presentation `[id C]`, with coefficient map `V → U`.
This is the module calculation for Grassmannian charts. Open chart coverage
is `Flags/CoordinateChartCover.lean`; scheme gluing and representability are
`Schemes/SelectedChartGlueData.lean` and `Schemes/SelectedAffineClassification.lean`.
-/

namespace FlagVarieties.Foundations.QuotientCharts

variable {R U V : Type*} [CommRing R]
  [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]

/-- The normalized quotient matrix `[id C]`. -/
def normalizedMap (C : V →ₗ[R] U) : (U × V) →ₗ[R] U :=
  LinearMap.fst R U V + C.comp (LinearMap.snd R U V)

@[simp] theorem normalizedMap_apply (C : V →ₗ[R] U) (x : U × V) :
    normalizedMap C x = x.1 + C x.2 := rfl

theorem normalizedMap_inl (C : V →ₗ[R] U) (u : U) :
    normalizedMap C (u, 0) = u := by simp

theorem normalizedMap_surjective (C : V →ₗ[R] U) : Function.Surjective (normalizedMap C) :=
  fun u => ⟨(u, 0), normalizedMap_inl C u⟩

theorem mem_normalizedMap_ker (C : V →ₗ[R] U) (x : U × V) :
    x ∈ LinearMap.ker (normalizedMap C) ↔ x.1 = -C x.2 := by
  change x.1 + C x.2 = 0 ↔ _
  exact eq_neg_iff_add_eq_zero.symm

/-- The canonical equivalence sends the class of `(u,v)` to `u+C(v)`. -/
noncomputable def normalizedQuotientEquiv (C : V →ₗ[R] U) :
    ((U × V) ⧸ LinearMap.ker (normalizedMap C)) ≃ₗ[R] U :=
  (normalizedMap C).quotKerEquivOfSurjective (normalizedMap_surjective C)

@[simp] theorem normalizedQuotientEquiv_mk (C : V →ₗ[R] U) (x : U × V) :
    normalizedQuotientEquiv C (Submodule.Quotient.mk x) = x.1 + C x.2 := by
  simp [normalizedQuotientEquiv]

/-- The selected-coordinate map into the quotient. -/
def firstCoordinates (P : Submodule R (U × V)) : U →ₗ[R] ((U × V) ⧸ P) :=
  P.mkQ.comp (LinearMap.inl R U V)

@[simp] theorem firstCoordinates_apply (P : Submodule R (U × V)) (u : U) :
    firstCoordinates P u = P.mkQ (u, 0) := rfl

/-- This predicate concerns the quotient map, not a chosen abstract frame. -/
def ChartCondition (P : Submodule R (U × V)) : Prop :=
  Function.Bijective (firstCoordinates P)

theorem normalizedMap_chartCondition (C : V →ₗ[R] U) :
    ChartCondition (LinearMap.ker (normalizedMap C)) := by
  have he : firstCoordinates (LinearMap.ker (normalizedMap C)) =
      (normalizedQuotientEquiv C).symm.toLinearMap := by
    ext u
    apply (normalizedQuotientEquiv C).injective
    simp [firstCoordinates]
  rw [ChartCondition, he]
  exact (normalizedQuotientEquiv C).symm.bijective

/-- The selected coordinate images themselves determine the quotient frame. -/
noncomputable def frame (P : Submodule R (U × V)) (h : ChartCondition P) :
    U ≃ₗ[R] ((U × V) ⧸ P) := LinearEquiv.ofBijective (firstCoordinates P) h

@[simp] theorem frame_apply (P : Submodule R (U × V)) (h : ChartCondition P) (u : U) :
    frame P h u = P.mkQ (u, 0) := rfl

/-- The remaining coordinate images, normalized by the selected coordinates. -/
noncomputable def coefficients (P : Submodule R (U × V)) (h : ChartCondition P) :
    V →ₗ[R] U := (frame P h).symm.toLinearMap.comp (P.mkQ.comp (LinearMap.inr R U V))

@[simp] theorem coefficients_apply (P : Submodule R (U × V)) (h : ChartCondition P) (v : V) :
    coefficients P h v = (frame P h).symm (P.mkQ (0, v)) := rfl

theorem normalizedMap_coefficients (P : Submodule R (U × V)) (h : ChartCondition P) :
    normalizedMap (coefficients P h) = (frame P h).symm.toLinearMap.comp P.mkQ := by
  apply LinearMap.ext
  rintro ⟨u, v⟩
  change u + (frame P h).symm (P.mkQ (0, v)) = (frame P h).symm (P.mkQ (u, v))
  have he : (u, v) = (u, (0 : V)) + ((0 : U), v) := by simp
  rw [he, map_add, map_add]
  congr 1
  exact ((frame P h).symm_apply_apply u).symm

theorem normalizedMap_coefficients_ker (P : Submodule R (U × V)) (h : ChartCondition P) :
    LinearMap.ker (normalizedMap (coefficients P h)) = P := by
  rw [normalizedMap_coefficients]
  ext x
  change (frame P h).symm (P.mkQ x) = 0 ↔ x ∈ P
  rw [map_eq_zero_iff _ (frame P h).symm.injective, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero]

/-- Equal normalized kernels force equal coefficient maps, over any ring. -/
theorem normalizedMap_ker_injective :
    Function.Injective (fun C : V →ₗ[R] U => LinearMap.ker (normalizedMap C)) := by
  intro C D h
  change LinearMap.ker (normalizedMap C) = LinearMap.ker (normalizedMap D) at h
  ext v
  have hv : (-C v, v) ∈ LinearMap.ker (normalizedMap C) := by
    rw [mem_normalizedMap_ker]
  rw [h, mem_normalizedMap_ker] at hv
  exact neg_injective hv

@[simp] theorem coefficients_normalizedMap (C : V →ₗ[R] U)
    (h : ChartCondition (LinearMap.ker (normalizedMap C))) :
    coefficients (LinearMap.ker (normalizedMap C)) h = C :=
  normalizedMap_ker_injective (normalizedMap_coefficients_ker _ h)

/-- Unique normalized presentation of every quotient in the chart. -/
theorem existsUnique_normalizedMap (P : Submodule R (U × V)) (h : ChartCondition P) :
    ∃! C : V →ₗ[R] U, LinearMap.ker (normalizedMap C) = P := by
  refine ⟨coefficients P h, normalizedMap_coefficients_ker P h, ?_⟩
  intro C hC
  exact normalizedMap_ker_injective (hC.trans (normalizedMap_coefficients_ker P h).symm)

/-- The chart is parametrized by coefficient maps. -/
noncomputable def chartEquiv :
    (V →ₗ[R] U) ≃ {P : Submodule R (U × V) // ChartCondition P} where
  toFun C := ⟨LinearMap.ker (normalizedMap C), normalizedMap_chartCondition C⟩
  invFun P := coefficients P.val P.property
  left_inv C := coefficients_normalizedMap C _
  right_inv P := Subtype.ext (normalizedMap_coefficients_ker P.val P.property)

end FlagVarieties.Foundations.QuotientCharts
