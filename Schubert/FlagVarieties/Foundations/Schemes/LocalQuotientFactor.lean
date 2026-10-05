import Schubert.FlagVarieties.Foundations.Schemes.ModuleSheafOpenCoverEquality

/-!
# Descent of factor maps through a quotient on an open cover

Local factorizations of two maps from the same sheaf force the second map
to annihilate the kernel of the first. Since the first map is an
epimorphism in the abelian category of module sheaves, there is then a
unique global factor. No compatibility of the chosen local factors is an
input; it follows from the common source equations and the local epis.
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
    (Scheme.Modules.restrictFunctor (C.f i)).obj M ⟶
      (Scheme.Modules.restrictFunctor (C.f i)).obj N)
  (ht : ∀ i : C.I₀,
    (Scheme.Modules.restrictFunctor (C.f i)).map q ≫ t i =
      (Scheme.Modules.restrictFunctor (C.f i)).map r)

include C t ht

/-- The local factors prove that the second global map kills the
categorical kernel of the first. -/
theorem kernel_comp_eq_zero_of_local_factors : kernel.ι q ≫ r = 0 := by
  apply hom_ext_of_openCover C
  intro i
  rw [Functor.map_comp, ← ht i, ← Category.assoc, ← Functor.map_comp,
    kernel.condition]
  simp

variable [Epi q]

/-- The canonical global factor forced by the local source equations. -/
def localQuotientFactor : M ⟶ N :=
  Abelian.epiDesc q r (kernel_comp_eq_zero_of_local_factors C q r t ht)

@[reassoc]
theorem localQuotientFactor_source : q ≫ localQuotientFactor C q r t ht = r :=
  Abelian.comp_epiDesc _ _ _

/-- Every chosen local factor is the restriction of the single global
factor; in particular all overlap compatibility is derived. -/
theorem localQuotientFactor_restrict (i : C.I₀) :
    (Scheme.Modules.restrictFunctor (C.f i)).map
      (localQuotientFactor C q r t ht) = t i := by
  apply (cancel_epi ((Scheme.Modules.restrictFunctor (C.f i)).map q)).mp
  rw [← Functor.map_comp, localQuotientFactor_source, ht]

/-- A global source-preserving factor exists uniquely; overlap
compatibility of local factors is therefore automatic. -/
theorem existsUnique_localQuotientFactor :
    ∃! a : M ⟶ N, q ≫ a = r := by
  refine ⟨localQuotientFactor C q r t ht,
    localQuotientFactor_source C q r t ht, ?_⟩
  intro a ha
  apply (cancel_epi q).mp
  rw [localQuotientFactor_source, ha]

end FlagVarieties.Foundations.ModuleSheafGluing
