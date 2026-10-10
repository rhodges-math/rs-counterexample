import RSCounterexample.FlagVarieties.Bruhat.Dimension.Algebra
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.Topology.KrullDimension
import Mathlib.AlgebraicGeometry.Properties

/-!
# Dimension of integral schemes of finite type over a field

* `topologicalKrullDim_le_of_forall`: the topological Krull dimension is local: if every point
  has an open neighbourhood of dimension `≤ d`, the space has dimension `≤ d`.
* `topologicalKrullDim_isAffineOpen`: an affine open `U` has dimension `dim Γ(X, U)`.
* `ringKrullDim_eq_of_isAffineOpen`: on an integral scheme locally of finite type over a field,
  all nonempty affine opens have coordinate rings of the same Krull dimension (they share a common
  basic open; `ringKrullDim_localization_eq`).
* **`topologicalKrullDim_eq_ringKrullDim`**: hence **`dim X = dim Γ(X, U)` for every nonempty
  affine open `U`**.
-/

namespace FlagVarieties.Dimension

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

/-! ### Topological dimension is local -/

section Topology

variable {X : Type*} [TopologicalSpace X]

/-- The trace on an open `U ∋ x` of an irreducible closed set containing `x`. -/
def restrictIrreducibleCloseds (U : Opens X) {x : X} (hxU : x ∈ U) (Z : IrreducibleCloseds X)
    (hxZ : x ∈ Z) : IrreducibleCloseds U :=
  ⟨Subtype.val ⁻¹' (Z : Set X),
    Z.isIrreducible.preimage U.isOpen.isOpenEmbedding_subtypeVal ⟨x, hxZ, ⟨x, hxU⟩, rfl⟩,
    Z.isClosed.preimage continuous_subtype_val⟩

theorem restrictIrreducibleCloseds_lt (U : Opens X) {x : X} (hxU : x ∈ U)
    {Z Z' : IrreducibleCloseds X} (hxZ : x ∈ Z) (hxZ' : x ∈ Z') (h : Z < Z') :
    restrictIrreducibleCloseds U hxU Z hxZ < restrictIrreducibleCloseds U hxU Z' hxZ' := by
  refine lt_of_le_of_ne (fun y hy => h.le hy) fun heq => h.not_ge ?_
  have hsub : (Z' : Set X) ⊆ closure ((Z' : Set X) ∩ U) :=
    subset_closure_inter_of_isPreirreducible_of_isOpen Z'.isIrreducible.2 U.isOpen ⟨x, hxZ', hxU⟩
  have hin : (Z' : Set X) ∩ U ⊆ Z := by
    rintro y ⟨hyZ', hyU⟩
    have : (⟨y, hyU⟩ : U) ∈ restrictIrreducibleCloseds U hxU Z' hxZ' := hyZ'
    rw [← heq] at this
    exact this
  exact hsub.trans (closure_minimal hin Z.isClosed)

/-- **The topological Krull dimension is local.** -/
theorem topologicalKrullDim_le_of_forall {d : WithBot ℕ∞}
    (h : ∀ x : X, ∃ U : Opens X, x ∈ U ∧ topologicalKrullDim U ≤ d) :
    topologicalKrullDim X ≤ d := by
  refine iSup_le fun p => ?_
  obtain ⟨x, hx⟩ := p.head.isIrreducible.nonempty
  obtain ⟨U, hxU, hU⟩ := h x
  have hmem : ∀ i, x ∈ p i := fun i => p.head_le i hx
  let q : LTSeries (IrreducibleCloseds U) :=
    { length := p.length
      toFun := fun i => restrictIrreducibleCloseds U hxU (p i) (hmem i)
      step := fun i => restrictIrreducibleCloseds_lt U hxU _ _ (p.step i) }
  exact (Order.LTSeries.length_le_krullDim q).trans hU

end Topology

/-! ### Schemes of finite type over a field -/

section Scheme

variable {K : Type u} [Field K] {X : Scheme.{u}} (π : X ⟶ Spec (CommRingCat.of K))

theorem le_preimage_top (U : X.Opens) : U ≤ π ⁻¹ᵁ ⊤ := by
  rw [Scheme.Hom.preimage_top]
  exact le_top

/-- The `K`-algebra structure on the sections of a scheme over `Spec K`. -/
noncomputable abbrev sectionsAlgebra (U : X.Opens) : Algebra K Γ(X, U) :=
  ((π.appLE ⊤ U (le_preimage_top π U)).hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom).toAlgebra

theorem sectionsFiniteType [LocallyOfFiniteType π] {U : X.Opens} (hU : IsAffineOpen U) :
    @Algebra.FiniteType K Γ(X, U) _ _ (sectionsAlgebra π U) := by
  have h1 : (π.appLE ⊤ U (le_preimage_top π U)).hom.FiniteType :=
    HasRingHomProperty.appLE (P := @LocallyOfFiniteType) π inferInstance
      ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ _
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom.FiniteType :=
    RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).2
  exact h1.comp h2

/-- An affine open `U` has topological dimension `dim Γ(X, U)`. -/
theorem topologicalKrullDim_isAffineOpen {U : X.Opens} (hU : IsAffineOpen U) :
    topologicalKrullDim U = ringKrullDim Γ(X, U) := by
  rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso hU.isoSpec).isHomeomorph

variable [IsIntegral X] [LocallyOfFiniteType π]

include π in
theorem ringKrullDim_basicOpen_eq {U : X.Opens} (hU : IsAffineOpen U) (f : Γ(X, U))
    (hf : (X.basicOpen f : Set X).Nonempty) :
    ringKrullDim Γ(X, X.basicOpen f) = ringKrullDim Γ(X, U) := by
  obtain ⟨x, hx⟩ := hf
  have _ : Nonempty U := ⟨⟨x, X.basicOpen_le f hx⟩⟩
  let _ := sectionsAlgebra π U
  have _ := sectionsFiniteType π hU
  have _ := hU.isLocalization_basicOpen f
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [Scheme.basicOpen_zero] at hx
    exact hx
  exact ringKrullDim_localization_eq K Γ(X, U) hf0 Γ(X, X.basicOpen f)

include π in
/-- **On an integral scheme locally of finite type over a field, all nonempty affine opens have
coordinate rings of the same dimension.** -/
theorem ringKrullDim_eq_of_isAffineOpen {U V : X.Opens} (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (hUne : (U : Set X).Nonempty) (hVne : (V : Set X).Nonempty) :
    ringKrullDim Γ(X, U) = ringKrullDim Γ(X, V) := by
  obtain ⟨x, hxU, hxV⟩ := nonempty_preirreducible_inter U.isOpen V.isOpen hUne hVne
  obtain ⟨f, g, hfg, hxf⟩ := exists_basicOpen_le_affine_inter hU hV x ⟨hxU, hxV⟩
  have hxg : x ∈ X.basicOpen g := hfg ▸ hxf
  rw [← ringKrullDim_basicOpen_eq π hU f ⟨x, hxf⟩, ← ringKrullDim_basicOpen_eq π hV g ⟨x, hxg⟩,
    hfg]

include π in
/-- **The dimension of an integral scheme locally of finite type over a field is the Krull
dimension of the coordinate ring of any nonempty affine open.** -/
theorem topologicalKrullDim_eq_ringKrullDim {U : X.Opens} (hU : IsAffineOpen U)
    (hne : (U : Set X).Nonempty) : topologicalKrullDim X = ringKrullDim Γ(X, U) := by
  apply le_antisymm
  · apply topologicalKrullDim_le_of_forall
    intro x
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact ⟨V, hxV, ((topologicalKrullDim_isAffineOpen hV).trans
      (ringKrullDim_eq_of_isAffineOpen π hV hU ⟨x, hxV⟩ hne)).le⟩
  · rw [← topologicalKrullDim_isAffineOpen hU]
    exact topologicalKrullDim_subspace_le X U

end Scheme

end FlagVarieties.Dimension
