import Schubert.FlagVarieties.Foundations.Schemes.ModuleSheafOpenCoverEquality

/-!
# Descent of quotient comparisons along an open-immersion cover

The input comparisons live on the pullbacks to the cover domains.
The global comparison and inverse are derived from local kernel agreement
and the epimorphisms, without a separate overlap-compatibility assumption.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.ModuleSheafGluing
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u v
variable {X : Scheme.{u}} {E M N : X.Modules}

theorem kernel_comp_eq_zero_of_pullbackCover (C : X.OpenCover.{v})
    (q : E ⟶ M) (r : E ⟶ N)
    (e : ∀ i, (Scheme.Modules.pullback (C.f i)).obj M ≅
      (Scheme.Modules.pullback (C.f i)).obj N)
    (he : ∀ i, (Scheme.Modules.pullback (C.f i)).map q ≫ (e i).hom =
      (Scheme.Modules.pullback (C.f i)).map r) : kernel.ι q ≫ r = 0 := by
  apply hom_ext_of_pullbackCover C
  intro i
  rw [Functor.map_comp, ← he i, ← Category.assoc, ← Functor.map_comp,
    kernel.condition]
  simp

/-- The factorization `M ⟶ N` of `r` through the epimorphism `q`; it exists because the pullbacks of
`q` and `r` to the members of the cover `C` are compatible. -/
def quotientComparisonOfPullbackCover (C : X.OpenCover.{v})
    (q : E ⟶ M) [Epi q] (r : E ⟶ N)
    (e : ∀ i, (Scheme.Modules.pullback (C.f i)).obj M ≅
      (Scheme.Modules.pullback (C.f i)).obj N)
    (he : ∀ i, (Scheme.Modules.pullback (C.f i)).map q ≫ (e i).hom =
      (Scheme.Modules.pullback (C.f i)).map r) : M ⟶ N :=
  Abelian.epiDesc q r (kernel_comp_eq_zero_of_pullbackCover C q r e he)

@[reassoc (attr := simp)]
theorem quotientComparisonOfPullbackCover_source (C : X.OpenCover.{v})
    (q : E ⟶ M) [Epi q] (r : E ⟶ N)
    (e : ∀ i, (Scheme.Modules.pullback (C.f i)).obj M ≅
      (Scheme.Modules.pullback (C.f i)).obj N)
    (he : ∀ i, (Scheme.Modules.pullback (C.f i)).map q ≫ (e i).hom =
      (Scheme.Modules.pullback (C.f i)).map r) :
    q ≫ quotientComparisonOfPullbackCover C q r e he = r :=
  Abelian.comp_epiDesc _ _ _

theorem pullbackCover_source_symm (C : X.OpenCover.{v})
    (q : E ⟶ M) (r : E ⟶ N)
    (e : ∀ i, (Scheme.Modules.pullback (C.f i)).obj M ≅
      (Scheme.Modules.pullback (C.f i)).obj N)
    (he : ∀ i, (Scheme.Modules.pullback (C.f i)).map q ≫ (e i).hom =
      (Scheme.Modules.pullback (C.f i)).map r) (i : C.I₀) :
    (Scheme.Modules.pullback (C.f i)).map r ≫ (e i).inv =
      (Scheme.Modules.pullback (C.f i)).map q := by
  rw [← he i, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The global comparison, uniquely specified by its original source map. -/
def quotientIsoOfPullbackCover (C : X.OpenCover.{v})
    (q : E ⟶ M) [Epi q] (r : E ⟶ N) [Epi r]
    (e : ∀ i, (Scheme.Modules.pullback (C.f i)).obj M ≅
      (Scheme.Modules.pullback (C.f i)).obj N)
    (he : ∀ i, (Scheme.Modules.pullback (C.f i)).map q ≫ (e i).hom =
      (Scheme.Modules.pullback (C.f i)).map r) : M ≅ N where
  hom := quotientComparisonOfPullbackCover C q r e he
  inv := quotientComparisonOfPullbackCover C r q (fun i => (e i).symm)
    (pullbackCover_source_symm C q r e he)
  hom_inv_id := by
    apply (cancel_epi q).mp
    rw [← Category.assoc, quotientComparisonOfPullbackCover_source,
      quotientComparisonOfPullbackCover_source, Category.comp_id]
  inv_hom_id := by
    apply (cancel_epi r).mp
    rw [← Category.assoc, quotientComparisonOfPullbackCover_source,
      quotientComparisonOfPullbackCover_source, Category.comp_id]

@[reassoc]
theorem quotientIsoOfPullbackCover_source (C : X.OpenCover.{v})
    (q : E ⟶ M) [Epi q] (r : E ⟶ N) [Epi r]
    (e : ∀ i, (Scheme.Modules.pullback (C.f i)).obj M ≅
      (Scheme.Modules.pullback (C.f i)).obj N)
    (he : ∀ i, (Scheme.Modules.pullback (C.f i)).map q ≫ (e i).hom =
      (Scheme.Modules.pullback (C.f i)).map r) :
    q ≫ (quotientIsoOfPullbackCover C q r e he).hom = r :=
  quotientComparisonOfPullbackCover_source C q r e he

end FlagVarieties.Foundations.ModuleSheafGluing
