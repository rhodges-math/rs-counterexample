import RSCounterexample.FlagVarieties.Foundations.Schemes.ModuleSheafGluingImage

/-!
# Overlap isomorphisms identify common-source kernels

A module sheaf pushed forward from an open subscheme sees only intersection
with that open. Consequently transition isomorphisms commuting with a
common source imply the kernel condition needed by the image construction.
Intersections need not be affine.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.ModuleSheafGluing

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

variable {X : Scheme.{u}}

/-- For an open pushforward, restriction to intersection with its source
open is injective (indeed an isomorphism). -/
theorem pushforward_inf_restriction_injective (U W : X.Opens) (Q : U.toScheme.Modules) :
    Function.Injective
      (((Scheme.Modules.pushforward U.ι).obj Q).presheaf.map
        (homOfLE (inf_le_left : W ⊓ U ≤ W)).op) := by
  let a := (Opens.map U.ι.base).map (homOfLE (inf_le_left : W ⊓ U ≤ W))
  have ha : U.ι ⁻¹ᵁ (W ⊓ U) = U.ι ⁻¹ᵁ W := by
    simp [Scheme.Hom.preimage_inf]
  have ea : a = eqToHom ha := Subsingleton.elim _ _
  change Function.Injective (Q.presheaf.map a.op)
  rw [ea]
  exact (AddCommGrpCat.mono_iff_injective _).mp inferInstance

variable {I : Type u} (E : X.Modules) (U : I → X.Opens)
  (Q : ∀ i, (U i).toScheme.Modules)

/-- The chart module sheaf pushed forward to the ambient scheme. -/
def chartPushforward (i : I) : X.Modules :=
  (Scheme.Modules.pushforward (U i).ι).obj (Q i)

variable (q : ∀ i, E.restrict (U i).ι ⟶ Q i)

/-- The canonical adjoint of a local quotient map. -/
def chartAdjoint (i : I) : E ⟶ chartPushforward U Q i :=
  (Scheme.Modules.restrictAdjunction (U i).ι).homEquiv E (Q i) (q i)

@[reassoc (attr := simp)]
theorem chartAdjoint_counit (i : I) :
    (Scheme.Modules.restrictFunctor (U i).ι).map (chartAdjoint E U Q q i) ≫
      (Scheme.Modules.restrictAdjunction (U i).ι).counit.app (Q i) = q i := by
  exact ((Scheme.Modules.restrictAdjunction (U i).ι).homEquiv_symm_apply E (Q i)
    (chartAdjoint E U Q q i)).symm.trans
      (((Scheme.Modules.restrictAdjunction (U i).ι).homEquiv E (Q i)).symm_apply_apply (q i))

instance chartAdjoint_restrict_epi (i : I) [Epi (q i)] :
    Epi ((Scheme.Modules.restrictFunctor (U i).ι).map (chartAdjoint E U Q q i)) := by
  have : Epi ((Scheme.Modules.restrictFunctor (U i).ι).map (chartAdjoint E U Q q i) ≫
      (Scheme.Modules.restrictAdjunction (U i).ι).counit.app (Q i)) := by
    rw [chartAdjoint_counit]
    infer_instance
  exact (epi_comp_iff_of_isIso _ _).mp this

/-- The source-preserving transition is an isomorphism of module
sheaves over the full overlap site. No affine-intersection hypothesis occurs. -/
def Compatible : Prop :=
  ∀ i j, ∃ e : (chartPushforward U Q i).over (U i ⊓ U j) ≅
      (chartPushforward U Q j).over (U i ⊓ U j),
    (chartAdjoint E U Q q i).over (U i ⊓ U j) ≫ e.hom =
      (chartAdjoint E U Q q j).over (U i ⊓ U j)

/-- Overlap transitions force equality of the section kernels on each
chart; the second map is tested on the whole open through pushforward. -/
theorem compatible_kernel (h : Compatible E U Q q) (i : I) (W : X.Opens)
    (hW : W ≤ U i) (x : Γ(E, W))
    (hx : (chartAdjoint E U Q q i).app W x = 0) (j : I) :
    (chartAdjoint E U Q q j).app W x = 0 := by
  let V := W ⊓ U j
  let a : V ⟶ W := homOfLE inf_le_left
  let xV : Γ(E, V) := E.presheaf.map a.op x
  have hxi : (chartAdjoint E U Q q i).app V xV = 0 := by
    have hn := congrArg (fun f => f x)
      ((chartAdjoint E U Q q i).mapPresheaf.naturality a.op).symm
    change ((chartPushforward U Q i).presheaf.map a.op)
      ((chartAdjoint E U Q q i).app W x) =
      (chartAdjoint E U Q q i).app V xV at hn
    rw [hx, map_zero] at hn
    exact hn.symm
  obtain ⟨e, he⟩ := h i j
  let B : Over (U i ⊓ U j) :=
    Over.mk (homOfLE (show V ≤ U i ⊓ U j from inf_le_inf hW le_rfl))
  have hxj : (chartAdjoint E U Q q j).app V xV = 0 := by
    have hh := congrArg (fun f => f.val.app (.op B) xV) he
    change e.hom.val.app (.op B) ((chartAdjoint E U Q q i).app V xV) =
      (chartAdjoint E U Q q j).app V xV at hh
    rw [hxi, map_zero] at hh
    exact hh.symm
  apply pushforward_inf_restriction_injective (U j) W (Q j)
  rw [map_zero]
  have hn := congrArg (fun f => f x)
    ((chartAdjoint E U Q q j).mapPresheaf.naturality a.op)
  exact hn.symm.trans hxj

end FlagVarieties.Foundations.ModuleSheafGluing
