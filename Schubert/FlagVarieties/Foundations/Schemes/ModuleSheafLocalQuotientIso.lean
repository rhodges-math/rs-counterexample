import Schubert.FlagVarieties.Foundations.Schemes.ModuleSheafLocalQuotientComparison

/-!
# Global isomorphisms from local comparisons of two quotient sheaves

Both maps are epimorphisms from one fixed source. The comparison and
its inverse descend through those epimorphisms; their inverse identities and
uniqueness follow by cancellation. Local compatibility on overlaps is forced.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.ModuleSheafGluing
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u
variable {X : Scheme.{u}} {I : Type u} {E M N : X.Modules}

theorem over_source_symm (U : I → X.Opens) (q : E ⟶ M) (r : E ⟶ N)
    (e : ∀ i, M.over (U i) ≅ N.over (U i))
    (he : ∀ i, q.over (U i) ≫ (e i).hom = r.over (U i)) (i : I) :
    r.over (U i) ≫ (e i).inv = q.over (U i) := by
  rw [← he i, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The uniquely source-preserving global isomorphism of the two quotients. -/
def quotientIsoOfOver (U : I → X.Opens)
    (hcover : ∀ x : X, ∃ i, x ∈ U i) (q : E ⟶ M) [Epi q] (r : E ⟶ N) [Epi r]
    (e : ∀ i, M.over (U i) ≅ N.over (U i))
    (he : ∀ i, q.over (U i) ≫ (e i).hom = r.over (U i)) : M ≅ N where
  hom := quotientComparisonOfOver U hcover q r e he
  inv := quotientComparisonOfOver U hcover r q (fun i => (e i).symm)
    (over_source_symm U q r e he)
  hom_inv_id := by
    apply (cancel_epi q).mp
    rw [← Category.assoc, quotientComparisonOfOver_source,
      quotientComparisonOfOver_source, Category.comp_id]
  inv_hom_id := by
    apply (cancel_epi r).mp
    rw [← Category.assoc, quotientComparisonOfOver_source,
      quotientComparisonOfOver_source, Category.comp_id]

@[reassoc]
theorem quotientIsoOfOver_source (U : I → X.Opens)
    (hcover : ∀ x : X, ∃ i, x ∈ U i) (q : E ⟶ M) [Epi q] (r : E ⟶ N) [Epi r]
    (e : ∀ i, M.over (U i) ≅ N.over (U i))
    (he : ∀ i, q.over (U i) ≫ (e i).hom = r.over (U i)) :
    q ≫ (quotientIsoOfOver U hcover q r e he).hom = r :=
  quotientComparisonOfOver_source U hcover q r e he

/-- Two source-preserving comparisons of an epimorphic quotient coincide. -/
theorem quotientIso_unique (q : E ⟶ M) [Epi q] (r : E ⟶ N)
    (e f : M ≅ N) (he : q ≫ e.hom = r) (hf : q ≫ f.hom = r) : e = f := by
  apply Iso.ext
  exact (cancel_epi q).mp (he.trans hf.symm)

/-- A version formulated on the original open subschemes of the cover. -/
def quotientIsoOfRestrictions (U : I → X.Opens)
    (hcover : ∀ x : X, ∃ i, x ∈ U i) (q : E ⟶ M) [Epi q] (r : E ⟶ N) [Epi r]
    (e : ∀ i, M.restrict (U i).ι ≅ N.restrict (U i).ι)
    (he : ∀ i, (Scheme.Modules.restrictFunctor (U i).ι).map q ≫ (e i).hom =
      (Scheme.Modules.restrictFunctor (U i).ι).map r) : M ≅ N :=
  quotientIsoOfOver U hcover q r (fun i => restrictionIsoToOver (U i) (e i))
    (fun i => restrictionIsoToOver_source (U i) q r (e i) (he i))

@[reassoc]
theorem quotientIsoOfRestrictions_source (U : I → X.Opens)
    (hcover : ∀ x : X, ∃ i, x ∈ U i) (q : E ⟶ M) [Epi q] (r : E ⟶ N) [Epi r]
    (e : ∀ i, M.restrict (U i).ι ≅ N.restrict (U i).ι)
    (he : ∀ i, (Scheme.Modules.restrictFunctor (U i).ι).map q ≫ (e i).hom =
      (Scheme.Modules.restrictFunctor (U i).ι).map r) :
    q ≫ (quotientIsoOfRestrictions U hcover q r e he).hom = r :=
  quotientIsoOfOver_source U hcover q r _ _

end FlagVarieties.Foundations.ModuleSheafGluing
