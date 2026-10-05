import Schubert.FlagVarieties.Foundations.Schemes.QuotientLineSheafAffineChart

/-!
# The original two ordered sections of a quotient sheaf

The source is the free sheaf on two ordered generators. Its two
canonical projections decompose every section, on every open. For a
quotient epimorphism, affine exactness therefore proves that the
two original quotient sections generate on each affine open.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientPair

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

/-- The structure sheaf of `X`, as a sheaf of modules. -/
abbrev unitSheaf (X : Scheme.{u}) : X.Modules := SheafOfModules.unit X.ringCatSheaf

/-- The inclusion `𝒪_X ⟶ 𝒪_X²` of the summand `i`. -/
def orderedFreeInclusion (X : Scheme.{u}) (i : QuotientPairIndex.{u}) :
    unitSheaf X ⟶ orderedFreeSheaf X := SheafOfModules.ιFree i

/-- The projection `𝒪_X² ⟶ 𝒪_X` onto the summand `i`. -/
def orderedFreeProjection (X : Scheme.{u}) (i : QuotientPairIndex.{u}) :
    orderedFreeSheaf X ⟶ unitSheaf X := by
  classical
  exact Sigma.desc (fun j => if j = i then 𝟙 _ else 0)

@[reassoc (attr := simp)] theorem orderedFreeInclusion_projection
    (X : Scheme.{u}) (i j : QuotientPairIndex.{u}) :
    orderedFreeInclusion X i ≫ orderedFreeProjection X j =
      if i = j then 𝟙 _ else 0 := by
  classical
  exact Sigma.ι_comp_desc _ i

theorem orderedFree_total (X : Scheme.{u}) :
    orderedFreeProjection X ⟨0⟩ ≫ orderedFreeInclusion X ⟨0⟩ +
      orderedFreeProjection X ⟨1⟩ ≫ orderedFreeInclusion X ⟨1⟩ = 𝟙 (orderedFreeSheaf X) := by
  classical
  apply Sigma.hom_ext
  intro i
  rcases i with ⟨i⟩
  fin_cases i <;>
    simp [orderedFreeProjection, orderedFreeInclusion, orderedFreeSheaf, SheafOfModules.ιFree,
      Preadditive.comp_add, ← Category.assoc]
    <;> exact (Category.comp_id _).symm

variable {X : Scheme.{u}} {N : X.Modules}

/-- The original quotient section indexed by one of the two free summands. -/
def orderedQuotientSection (q : orderedFreeSheaf X ⟶ N) (U : X.Opens)
    (i : QuotientPairIndex.{u}) : Γ(N, U) :=
  (orderedFreeInclusion X i ≫ q).app U (1 : Γ(X, U))

theorem unitSheaf_hom_apply (t : unitSheaf X ⟶ N) (U : X.Opens) (a : Γ(X, U)) :
    t.app U a = a • t.app U (1 : Γ(X, U)) := by
  simpa only [smul_eq_mul, mul_one] using t.app_smul a (1 : Γ(X, U))

/-- Naturality preserves the original generator labels under sheaf restriction. -/
theorem orderedQuotientSection_restrict (q : orderedFreeSheaf X ⟶ N)
    {U V : X.Opens} (h : V ≤ U) (i : QuotientPairIndex.{u}) :
    N.presheaf.map (homOfLE h).op (orderedQuotientSection q U i) =
      orderedQuotientSection q V i := by
  have hn := ConcreteCategory.congr_hom
    ((orderedFreeInclusion X i ≫ q).mapPresheaf.naturality (homOfLE h).op)
    (1 : Γ(X, U))
  change (orderedFreeInclusion X i ≫ q).app V
      ((X.presheaf.map (homOfLE h).op) 1) =
    N.presheaf.map (homOfLE h).op (orderedQuotientSection q U i) at hn
  simpa only [map_one, orderedQuotientSection] using hn.symm

/-- The ordered pair of quotient sections, over the ring of the open. -/
def orderedQuotientSectionPair (q : orderedFreeSheaf X ⟶ N) (U : X.Opens) :
    Γ(X, U) × Γ(X, U) →ₗ[Γ(X, U)] Γ(N, U) :=
  (LinearMap.fst _ _ _).smulRight (orderedQuotientSection q U ⟨0⟩) +
    (LinearMap.snd _ _ _).smulRight (orderedQuotientSection q U ⟨1⟩)

@[simp] theorem orderedQuotientSectionPair_apply (q : orderedFreeSheaf X ⟶ N)
    (U : X.Opens) (a b : Γ(X, U)) :
    orderedQuotientSectionPair q U (a, b) =
      a • orderedQuotientSection q U ⟨0⟩ + b • orderedQuotientSection q U ⟨1⟩ := rfl

theorem orderedQuotientSectionPair_surjective [N.IsQuasicoherent]
    (q : orderedFreeSheaf X ⟶ N) [Epi q] (U : X.Opens) (hU : IsAffineOpen U) :
    Function.Surjective (orderedQuotientSectionPair q U) := by
  intro z
  obtain ⟨w, rfl⟩ := affineOpen_app_surjective q U hU z
  refine ⟨((orderedFreeProjection X ⟨0⟩).app U w,
    (orderedFreeProjection X ⟨1⟩).app U w), ?_⟩
  have ht := congrArg (fun t : orderedFreeSheaf X ⟶ orderedFreeSheaf X => t ≫ q)
    (orderedFree_total X)
  simp only [Preadditive.add_comp, Category.assoc, Category.id_comp] at ht
  have hv := ConcreteCategory.congr_hom (congrArg (fun t => t.app U) ht) w
  change (orderedFreeInclusion X ⟨0⟩ ≫ q).app U ((orderedFreeProjection X ⟨0⟩).app U w) +
      (orderedFreeInclusion X ⟨1⟩ ≫ q).app U ((orderedFreeProjection X ⟨1⟩).app U w) =
    q.app U w at hv
  rw [unitSheaf_hom_apply (orderedFreeInclusion X ⟨0⟩ ≫ q) U
      ((orderedFreeProjection X ⟨0⟩).app U w),
    unitSheaf_hom_apply (orderedFreeInclusion X ⟨1⟩ ≫ q) U
      ((orderedFreeProjection X ⟨1⟩).app U w)] at hv
  exact hv

/-- In a frame, the two quotient sections have coprime coefficients. -/
theorem orderedQuotientSection_coprime [N.IsQuasicoherent]
    (q : orderedFreeSheaf X ⟶ N) [Epi q] (U : X.Opens) (hU : IsAffineOpen U)
    (frame : Γ(N, U) ≃ₗ[Γ(X, U)] Γ(X, U)) :
    IsCoprime (frame (orderedQuotientSection q U ⟨0⟩))
      (frame (orderedQuotientSection q U ⟨1⟩)) := by
  obtain ⟨⟨a, b⟩, hab⟩ := orderedQuotientSectionPair_surjective q U hU (frame.symm 1)
  refine ⟨a, b, ?_⟩
  simpa only [orderedQuotientSectionPair_apply, map_add, map_smul, smul_eq_mul,
    LinearEquiv.apply_symm_apply] using congrArg frame hab

end FlagVarieties.Foundations.QuotientPair
