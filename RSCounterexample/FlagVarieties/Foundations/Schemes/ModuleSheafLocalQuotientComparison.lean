import RSCounterexample.FlagVarieties.Foundations.Schemes.ModuleSheafGluingRestriction

/-!
# Descent of source-preserving comparisons of quotient sheaves

Two epimorphic quotients of one module sheaf are isomorphic if their
restrictions to an open cover are isomorphic compatibly with the source.
Compatibility on overlaps follows from the epimorphisms; it is not additional
input. No surjectivity on sections is assumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.ModuleSheafGluing
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u
variable {X : Scheme.{u}} {I : Type u} {E M N : X.Modules}

/-- Morphisms of module sheaves agree if they agree over an open cover. -/
theorem hom_ext_of_over (U : I → X.Opens) (hcover : ∀ x : X, ∃ i, x ∈ U i)
    (f g : M ⟶ N) (h : ∀ i, f.over (U i) = g.over (U i)) : f = g := by
  apply Scheme.Modules.hom_ext
  intro W
  ext s
  apply N.isSheaf.section_ext
  intro x hx
  obtain ⟨i, hi⟩ := hcover x
  refine ⟨W ⊓ U i, inf_le_left, ⟨hx, hi⟩, ?_⟩
  let a : W ⊓ U i ⟶ W := homOfLE inf_le_left
  let B : Over (U i) := Over.mk (homOfLE (inf_le_right : W ⊓ U i ≤ U i))
  have he : f.app (W ⊓ U i) (M.presheaf.map a.op s) =
      g.app (W ⊓ U i) (M.presheaf.map a.op s) :=
    congrArg (fun v => v.val.app (.op B) (M.presheaf.map a.op s)) (h i)
  have hf := congrArg (fun v => v s) (f.mapPresheaf.naturality a.op)
  have hg := congrArg (fun v => v s) (g.mapPresheaf.naturality a.op)
  exact hf.symm.trans (he.trans hg)

/-- The local source comparisons force the second quotient to kill the kernel
of the first. This is an equality of sheaf morphisms, not a section-surjectivity claim. -/
theorem kernel_comp_eq_zero_of_over (U : I → X.Opens)
    (hcover : ∀ x : X, ∃ i, x ∈ U i) (q : E ⟶ M) (r : E ⟶ N)
    (e : ∀ i, M.over (U i) ≅ N.over (U i))
    (he : ∀ i, q.over (U i) ≫ (e i).hom = r.over (U i)) :
    kernel.ι q ≫ r = 0 := by
  apply hom_ext_of_over U hcover
  intro i
  have hi : (SheafOfModules.overFunctor X.ringCatSheaf (U i)).map q ≫ (e i).hom =
      (SheafOfModules.overFunctor X.ringCatSheaf (U i)).map r := he i
  change (SheafOfModules.overFunctor X.ringCatSheaf (U i)).map (kernel.ι q ≫ r) =
    (SheafOfModules.overFunctor X.ringCatSheaf (U i)).map 0
  rw [Functor.map_comp, ← hi, ← Category.assoc, ← Functor.map_comp,
    kernel.condition]
  change (0 : (kernel q).over (U i) ⟶ M.over (U i)) ≫ (e i).hom = 0
  exact zero_comp

/-- A comparison of quotient sheaves, descended through the first epi. -/
def quotientComparisonOfOver (U : I → X.Opens)
    (hcover : ∀ x : X, ∃ i, x ∈ U i) (q : E ⟶ M) [Epi q] (r : E ⟶ N)
    (e : ∀ i, M.over (U i) ≅ N.over (U i))
    (he : ∀ i, q.over (U i) ≫ (e i).hom = r.over (U i)) : M ⟶ N :=
  Abelian.epiDesc q r (kernel_comp_eq_zero_of_over U hcover q r e he)

@[reassoc (attr := simp)]
theorem quotientComparisonOfOver_source (U : I → X.Opens)
    (hcover : ∀ x : X, ∃ i, x ∈ U i) (q : E ⟶ M) [Epi q] (r : E ⟶ N)
    (e : ∀ i, M.over (U i) ≅ N.over (U i))
    (he : ∀ i, q.over (U i) ≫ (e i).hom = r.over (U i)) :
    q ≫ quotientComparisonOfOver U hcover q r e he = r :=
  Abelian.comp_epiDesc _ _ _

end FlagVarieties.Foundations.ModuleSheafGluing
