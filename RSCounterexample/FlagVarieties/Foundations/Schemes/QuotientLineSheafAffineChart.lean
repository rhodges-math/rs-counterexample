import RSCounterexample.FlagVarieties.Foundations.Schemes.AffineSheafLineRefinement

/-!
# Affine charts of a quotient line sheaf on a general scheme

Local triviality is stated using isomorphisms of sheaves over open
subsets. It is preserved by restriction along open immersions. Thus a
quotient line sheaf on a general scheme supplies all data needed
for the affine Proj morphism, without affine module presentations or
finite-projectivity assumptions.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientPair

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

/-- Convert a local frame on the open site to a frame on the open subscheme. -/
def overFrameToRestrict {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf :=
  ((Scheme.Modules.overFunctorEquiv U).app M).symm ≪≫
    (Scheme.Modules.overEquiv U).functor.mapIso e ≪≫
    U.sheafOfModulesEquivOverUnit X.ringCatSheaf

/-- Convert a local frame on an open subscheme to the equivalent open-site frame. -/
def restrictFrameToOver {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) :
    M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U) :=
  (Scheme.Modules.overEquiv U).fullyFaithfulFunctor.preimageIso
    ((Scheme.Modules.overFunctorEquiv U).app M ≪≫ e ≪≫
      (U.sheafOfModulesEquivOverUnit X.ringCatSheaf).symm)

/-- Local line-sheaf triviality is preserved by restriction along open immersions. -/
theorem locally_trivial_sheaf_restrict {X Y : Scheme.{u}} (M : X.Modules)
    (hline : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Nonempty (M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)))
    (f : Y ⟶ X) [IsOpenImmersion f] :
    ∀ y : Y, ∃ V : Y.Opens, y ∈ V ∧
      Nonempty ((M.restrict f).over V ≅ SheafOfModules.unit (Y.ringCatSheaf.over V)) := by
  intro y
  obtain ⟨U, hyU, ⟨e⟩⟩ := hline (f y)
  let V := f ⁻¹ᵁ U
  let g : V.toScheme ⟶ U.toScheme := f.resLE U V le_rfl
  have hg : g ≫ U.ι = V.ι ≫ f := f.resLE_comp_ι le_rfl
  let : IsOpenImmersion (g ≫ U.ι) := by rw [hg]; infer_instance
  let : IsOpenImmersion g := IsOpenImmersion.of_comp g U.ι
  let er : (M.restrict f).restrict V.ι ≅
      SheafOfModules.unit V.toScheme.ringCatSheaf :=
    ((Scheme.Modules.restrictFunctorComp V.ι f).app M).symm ≪≫
      (Scheme.Modules.restrictFunctorCongr hg.symm).app M ≪≫
      (Scheme.Modules.restrictFunctorComp g U.ι).app M ≪≫
      (Scheme.Modules.restrictFunctor g).mapIso (overFrameToRestrict M U e) ≪≫
      Scheme.Modules.restrictUnitIso g
  exact ⟨V, hyU, ⟨restrictFrameToOver (M.restrict f) V er⟩⟩

variable {X : Scheme.{u}} {R : CommRingCat.{u}} (N : X.Modules)
  (hline : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
    Nonempty (N.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)))
  (f : Spec R ⟶ X) [IsOpenImmersion f]

include hline

/-- Finite projectivity on any affine chart is derived from the general-scheme line sheaf. -/
theorem quotientLineSheaf_affine_finite_projective :
    Module.Finite R (sheafGlobalModule (N.restrict f)) ∧
      Module.Projective R (sheafGlobalModule (N.restrict f)) :=
  locally_trivial_sheaf_finite_projective (N.restrict f)
    (locally_trivial_sheaf_restrict N hline f)

theorem quotientLineSheaf_affine_rank_one (p : PrimeSpectrum R) :
    Module.rankAtStalk (sheafGlobalModule (N.restrict f)) p = 1 :=
  locally_trivial_sheaf_rank_one (N.restrict f) (locally_trivial_sheaf_restrict N hline f) p

variable {A : Type u} [CommRing A]

/-- The affine-chart morphism of an ordered quotient line sheaf on a general scheme. -/
def quotientLineSheafChartMorphism (φ : A →+* R) (q : orderedFreeSheaf X ⟶ N) [Epi q] :
    Spec R ⟶ ProjectiveLine.scheme A :=
  fromAffineQuotientLineSheaf f φ q (locally_trivial_sheaf_restrict N hline f)

theorem quotientLineSheafChartMorphism_toSpec (φ : A →+* R)
    (q : orderedFreeSheaf X ⟶ N) [Epi q] :
    quotientLineSheafChartMorphism N hline f φ q ≫ ProjectiveLine.toSpec A =
      Spec.map (CommRingCat.ofHom φ) :=
  fromAffineQuotientLineSheaf_toSpec f φ q (locally_trivial_sheaf_restrict N hline f)

end FlagVarieties.Foundations.QuotientPair
