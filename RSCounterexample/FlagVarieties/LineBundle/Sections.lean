import RSCounterexample.FlagVarieties.LineBundle.SemiInvariant
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits

/-!
# Sections of semi-invariant sheaves

* `FlagVarieties.kernelSectionsIso`: sections of the kernel of a morphism of sheaves of modules
  are the kernel of the morphism on sections.
* `FlagVarieties.kernel_ι_app_injective`, `FlagVarieties.mem_range_kernel_ι_app_iff`: a section
  of the target comes from the kernel iff the morphism kills it, and then uniquely.
-/

noncomputable section

namespace FlagVarieties

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

section Kernel

variable {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N) (U : X.Opens)

/-- Evaluation of sheaves of modules on the open `U`. -/
abbrev evalAt : X.Modules ⥤ ModuleCat Γ(X, U) :=
  SheafOfModules.evaluation X.ringCatSheaf (op U)

instance : (evalAt (X := X) U).Additive where
  map_add := rfl

instance : PreservesFiniteLimits (evalAt (X := X) U) :=
  SheafOfModules.Finite.evaluationPreservesFiniteLimits _ _

/-- Sections of a kernel are the kernel on sections. -/
def kernelSectionsIso :
    (evalAt U).obj (kernel φ) ≅ ModuleCat.of Γ(X, U) (LinearMap.ker ((evalAt U).map φ).hom) :=
  PreservesKernel.iso (evalAt U) φ ≪≫ ModuleCat.kernelIsoKer _

theorem kernelSectionsIso_hom_subtype :
    (kernelSectionsIso φ U).hom ≫
        ModuleCat.ofHom (LinearMap.ker ((evalAt U).map φ).hom).subtype =
      (evalAt U).map (kernel.ι φ) := by
  rw [kernelSectionsIso, Iso.trans_hom, Category.assoc, ModuleCat.kernelIsoKer_hom_ker_subtype,
    PreservesKernel.iso_hom, kernelComparison_comp_ι]

/-- The inclusion of a kernel is injective on sections. -/
theorem kernel_ι_app_injective : Function.Injective ((evalAt U).map (kernel.ι φ)).hom := by
  rw [← kernelSectionsIso_hom_subtype, ModuleCat.hom_comp, LinearMap.coe_comp]
  exact Subtype.val_injective.comp (kernelSectionsIso φ U).toLinearEquiv.injective

/-- A section lies in the kernel iff the morphism kills it. -/
theorem mem_range_kernel_ι_app_iff (x : (evalAt U).obj M) :
    x ∈ Set.range ((evalAt U).map (kernel.ι φ)).hom ↔ ((evalAt U).map φ).hom x = 0 := by
  constructor
  · rintro ⟨y, rfl⟩
    have h := congrArg (fun g => ((evalAt U).map g).hom y) (kernel.condition φ)
    simpa only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
      Functor.map_zero, ModuleCat.hom_zero, LinearMap.zero_apply] using h
  · intro hx
    refine ⟨(kernelSectionsIso φ U).inv ⟨x, hx⟩, ?_⟩
    have h := congrArg (fun g => g.hom ((kernelSectionsIso φ U).inv ⟨x, hx⟩))
      (kernelSectionsIso_hom_subtype φ U)
    refine h.symm.trans ?_
    simp

end Kernel

namespace BorelAction

variable {R : Type u} [CommRing R] {n : ℕ} {T : Scheme.{u}} (E : BorelAction R n T)

theorem preimage_actionFst_q (V : T.Opens) :
    (E.actionFst ≫ E.q) ⁻¹ᵁ V = E.act ⁻¹ᵁ (E.q ⁻¹ᵁ V) := by
  rw [← E.act_q, Scheme.Hom.comp_preimage]

/-- The map `f ↦ a^* f` on sections over `V`. -/
theorem pullbackAct_app (V : T.Opens) (f : Γ(E.P, E.q ⁻¹ᵁ V)) :
    (E.pullbackAct.app V).hom f =
      (E.act.appLE (E.q ⁻¹ᵁ V) ((E.actionFst ≫ E.q) ⁻¹ᵁ V) (E.preimage_actionFst_q V).le).hom
          f := by
  rfl

/-- The map `f ↦ pr₂^* η⁻¹ · pr₁^* f` on sections over `V`. -/
theorem pullbackTwist_app (η : Fin n → ℤ) (V : T.Opens) (f : Γ(E.P, E.q ⁻¹ᵁ V)) :
    ((E.pullbackTwist η).app V).hom f =
      (E.actionDomain.presheaf.map (homOfLE le_top).op).hom (E.twist η) *
        (E.actionFst.app (E.q ⁻¹ᵁ V)).hom f :=
  rfl

end BorelAction

end FlagVarieties
