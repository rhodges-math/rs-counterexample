import RSCounterexample.FlagVarieties.Foundations.Schemes.ModuleSheafLocalQuotientIso
import Mathlib.AlgebraicGeometry.Cover.Open

/-!
# Module-sheaf equality tested on a scheme open cover

The cover maps may be arbitrary open immersions, including the localization
maps in the derived affine presentation cover. No identification of a cover
domain with an open subscheme is required.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.ModuleSheafGluing
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u v
variable {X : Scheme.{u}} {M N : X.Modules}

theorem hom_ext_of_openCover (C : X.OpenCover.{v}) (f g : M ⟶ N)
    (h : ∀ i, (Scheme.Modules.restrictFunctor (C.f i)).map f =
      (Scheme.Modules.restrictFunctor (C.f i)).map g) : f = g := by
  apply Scheme.Modules.hom_ext
  intro W
  ext s
  apply N.isSheaf.section_ext
  intro x hx
  obtain ⟨i, y, hy⟩ := C.exists_eq x
  let V : (C.X i).Opens := C.f i ⁻¹ᵁ W
  let U : X.Opens := C.f i ''ᵁ V
  have hU : U ≤ W := (C.f i).image_preimage_le W
  have hxU : x ∈ U := ⟨y, by change C.f i y ∈ W; rwa [hy], hy⟩
  refine ⟨U, hU, hxU, ?_⟩
  let a : U ⟶ W := homOfLE hU
  have he : f.app U (M.presheaf.map a.op s) = g.app U (M.presheaf.map a.op s) :=
    congrArg (fun z => z.app V (M.presheaf.map a.op s)) (h i)
  have hf := congrArg (fun z => z s) (f.mapPresheaf.naturality a.op)
  have hg := congrArg (fun z => z s) (g.mapPresheaf.naturality a.op)
  exact hf.symm.trans (he.trans hg)

theorem hom_ext_of_pullbackCover (C : X.OpenCover.{v}) (f g : M ⟶ N)
    (h : ∀ i, (Scheme.Modules.pullback (C.f i)).map f =
      (Scheme.Modules.pullback (C.f i)).map g) : f = g := by
  apply hom_ext_of_openCover C f g
  intro i
  apply (cancel_mono ((Scheme.Modules.restrictFunctorIsoPullback (C.f i)).hom.app N)).mp
  rw [(Scheme.Modules.restrictFunctorIsoPullback (C.f i)).hom.naturality f,
    (Scheme.Modules.restrictFunctorIsoPullback (C.f i)).hom.naturality g, h i]

end FlagVarieties.Foundations.ModuleSheafGluing
