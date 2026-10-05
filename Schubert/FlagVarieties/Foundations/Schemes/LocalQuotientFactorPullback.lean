import Schubert.FlagVarieties.Foundations.Schemes.LocalQuotientFactor

/-!
# Factors specified on a pullback open cover

This formulation accepts local factors between the pullbacks to
the domains of an arbitrary scheme open cover. It produces the same
unique global factor, and recovers every local factor by pullback.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.ModuleSheafGluing
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u v

variable {X : Scheme.{u}} {S M N : X.Modules}
  (C : X.OpenCover.{v}) (q : S ⟶ M) (r : S ⟶ N)
  (t : ∀ i : C.I₀,
    (Scheme.Modules.pullback (C.f i)).obj M ⟶
      (Scheme.Modules.pullback (C.f i)).obj N)
  (ht : ∀ i : C.I₀,
    (Scheme.Modules.pullback (C.f i)).map q ≫ t i =
      (Scheme.Modules.pullback (C.f i)).map r)

include C t ht

theorem kernel_comp_eq_zero_of_local_pullback_factors : kernel.ι q ≫ r = 0 := by
  apply hom_ext_of_pullbackCover C
  intro i
  rw [Functor.map_comp, ← ht i, ← Category.assoc, ← Functor.map_comp,
    kernel.condition]
  simp

variable [Epi q]

/-- The factorization `M ⟶ N` of `r` through the epimorphism `q`; it exists because it exists
locally on the cover `C`. -/
def localPullbackQuotientFactor : M ⟶ N :=
  Abelian.epiDesc q r (kernel_comp_eq_zero_of_local_pullback_factors C q r t ht)

@[reassoc]
theorem localPullbackQuotientFactor_source :
    q ≫ localPullbackQuotientFactor C q r t ht = r :=
  Abelian.comp_epiDesc _ _ _

theorem localPullbackQuotientFactor_local (i : C.I₀) :
    (Scheme.Modules.pullback (C.f i)).map
      (localPullbackQuotientFactor C q r t ht) = t i := by
  apply (cancel_epi ((Scheme.Modules.pullback (C.f i)).map q)).mp
  rw [← Functor.map_comp, localPullbackQuotientFactor_source, ht]

theorem existsUnique_localPullbackQuotientFactor :
    ∃! a : M ⟶ N, q ≫ a = r := by
  refine ⟨localPullbackQuotientFactor C q r t ht,
    localPullbackQuotientFactor_source C q r t ht, ?_⟩
  intro a ha
  apply (cancel_epi q).mp
  rw [localPullbackQuotientFactor_source, ha]

end FlagVarieties.Foundations.ModuleSheafGluing
