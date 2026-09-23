import Schubert.RS.JosephPolo.PresentationSl2
import Schubert.RS.JosephPolo.Sl2RelationsAction
import Schubert.RS.PolynomialRootModule

namespace Schubert.RS.Representation
noncomputable section
open FinPermutation
attribute [local instance 100] LieRing.ofAssociativeRing
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} (u : Composition n) (i : AdjacentPosition n)
  (hu : u i.left ≤ u i.right)

/-- The rank-one action on the presentation quotient induced by the
descended operators. -/
def presentationSl2Action :
    (polynomialSl2Triple i.left i.right i.left_ne_right).toLieSubalgebra ℂ →ₗ⁅ℂ⁆
      Module.End ℂ (PresentationQuotient u) := by
  apply sl2ActionOfRelations _ (presentationRaising u i) (presentationLowering u i hu)
    (presentationCartan u i)
  · exact (presentation_sl2_relations u i hu).1
  · change presentationCartan u i * presentationRaising u i -
      presentationRaising u i * presentationCartan u i = (2 : ℕ) • presentationRaising u i
    simpa only [two_smul] using (presentation_sl2_relations u i hu).2.1
  · change presentationCartan u i * presentationLowering u i hu -
      presentationLowering u i hu * presentationCartan u i = -((2 : ℕ) • presentationLowering u i hu)
    rw [(presentation_sl2_relations u i hu).2.2]
    module

@[instance_reducible]
def presentationSl2LieRingModule :
    LieRingModule ((polynomialSl2Triple i.left i.right i.left_ne_right).toLieSubalgebra ℂ)
      (PresentationQuotient u) :=
  LieRingModule.compLieHom (PresentationQuotient u) (presentationSl2Action u i hu)



theorem presentationSl2LieModule :
    letI := presentationSl2LieRingModule u i hu
    LieModule ℂ ((polynomialSl2Triple i.left i.right i.left_ne_right).toLieSubalgebra ℂ)
      (PresentationQuotient u) :=
  LieModule.compLieHom (PresentationQuotient u) (presentationSl2Action u i hu)


theorem presentationSl2_raising (x : PresentationQuotient u) :
    letI := presentationSl2LieRingModule u i hu
    ⁅sl2RaisingElement (polynomialSl2Triple i.left i.right i.left_ne_right),x⁆ =
      presentationRaising u i x := by


  change (presentationSl2Action u i hu (sl2RaisingElement
    (polynomialSl2Triple i.left i.right i.left_ne_right))) x = _
  change sl2ActionLinear (polynomialSl2Triple i.left i.right i.left_ne_right)
    (presentationRaising u i) (presentationLowering u i hu) (presentationCartan u i)
    (sl2RaisingElement (polynomialSl2Triple i.left i.right i.left_ne_right)) x = _
  rw [sl2ActionLinear_raising]

theorem presentationSl2_lowering (x : PresentationQuotient u) :
    letI := presentationSl2LieRingModule u i hu
    ⁅sl2LoweringElement (polynomialSl2Triple i.left i.right i.left_ne_right),x⁆ =
      presentationLowering u i hu x := by

  change (presentationSl2Action u i hu (sl2LoweringElement
    (polynomialSl2Triple i.left i.right i.left_ne_right))) x = _
  change sl2ActionLinear (polynomialSl2Triple i.left i.right i.left_ne_right)
    (presentationRaising u i) (presentationLowering u i hu) (presentationCartan u i)
    (sl2LoweringElement (polynomialSl2Triple i.left i.right i.left_ne_right)) x = _
  rw [sl2ActionLinear_lowering]

theorem presentationSl2_cartan (x : PresentationQuotient u) :
    letI := presentationSl2LieRingModule u i hu
    ⁅sl2CartanElement (polynomialSl2Triple i.left i.right i.left_ne_right),x⁆ =
      presentationCartan u i x := by

  change (presentationSl2Action u i hu (sl2CartanElement
    (polynomialSl2Triple i.left i.right i.left_ne_right))) x = _
  change sl2ActionLinear (polynomialSl2Triple i.left i.right i.left_ne_right)
    (presentationRaising u i) (presentationLowering u i hu) (presentationCartan u i)
    (sl2CartanElement (polynomialSl2Triple i.left i.right i.left_ne_right)) x = _
  rw [sl2ActionLinear_cartan]

end
end Schubert.RS.Representation






