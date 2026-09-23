import Schubert.RS.JosephPolo.CartanCovariance

namespace Schubert.RS.Representation
noncomputable section
open FinPermutation
attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 500000

def presentationUpperLie {n : ℕ} (u : Composition n) :
    upperNilpotent n →ₗ⁅ℂ⁆ Module.End ℂ (PresentationQuotient u) :=
  (Algebra.lsmul ℂ ℂ (PresentationQuotient u)).toLieHom.comp (UniversalEnvelopingAlgebra.ι ℂ)

theorem presentationLowering_generator_smul {n : ℕ} (u : Composition n) (i : AdjacentPosition n)
    (hu : u i.left ≤ u i.right) (A : upperNilpotent n) (x : PresentationQuotient u) :
    presentationLowering u i hu (UniversalEnvelopingAlgebra.ι ℂ A • x) =
      UniversalEnvelopingAlgebra.ι ℂ A • presentationLowering u i hu x+
        UniversalEnvelopingAlgebra.ι ℂ (loweringUpper i A) • x-
          upperSimpleCoefficient i A • presentationCartan u i x := by
  obtain ⟨b,rfl⟩ := Submodule.Quotient.mk_surjective (jpLeftIdeal u) x
  rw [← Submodule.Quotient.mk_smul, presentationLowering_mk, presentationLowering_mk,
    presentationCartan_mk, adjacentWeight_gap u i hu]
  rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul]
  let q : Enveloping n →ₗ[ℂ] PresentationQuotient u := ((jpLeftIdeal u).restrictScalars ℂ).mkQ
  change q (loweringEnveloping i (-((u i.right-u i.left : ℕ) : ℂ))
    (UniversalEnvelopingAlgebra.ι ℂ A*b)) =
      q (UniversalEnvelopingAlgebra.ι ℂ A*loweringEnveloping i (-((u i.right-u i.left : ℕ) : ℂ)) b)+
        q (UniversalEnvelopingAlgebra.ι ℂ (loweringUpper i A)*b)-
          upperSimpleCoefficient i A • q (cartanEnveloping (adjacentCartanDiagonal i) b+
            (-((u i.right-u i.left : ℕ) : ℂ)) • b)
  rw [add_sub_assoc, ← q.map_smul, ← q.map_sub, ← q.map_add]
  exact congrArg q (loweringEnveloping_generator_mul i (-((u i.right-u i.left : ℕ) : ℂ)) A b)

theorem presentationUpperLie_raising {n : ℕ} (u : Composition n) (i : AdjacentPosition n) :
    presentationUpperLie u (rootVector (adjacentPositiveRoot i))=presentationRaising u i := rfl

theorem presentationUpperLie_cartan {n : ℕ} (u : Composition n) (i : AdjacentPosition n)
    (A : upperNilpotent n) :
    ⁅presentationCartan u i,presentationUpperLie u A⁆ =
      presentationUpperLie u (cartanUpper (adjacentCartanDiagonal i) A) := by
  apply LinearMap.ext
  intro x
  change presentationCartan u i (UniversalEnvelopingAlgebra.ι ℂ A • x)-
    UniversalEnvelopingAlgebra.ι ℂ A • presentationCartan u i x = _
  rw [presentationCartan_smul, cartanEnveloping_generator, add_sub_cancel_right]
  rfl

theorem presentationUpperLie_lowering {n : ℕ} (u : Composition n) (i : AdjacentPosition n)
    (hu : u i.left ≤ u i.right) (A : upperNilpotent n) :
    ⁅presentationLowering u i hu,presentationUpperLie u A⁆ =
      presentationUpperLie u (loweringUpper i A)-
        upperSimpleCoefficient i A • presentationCartan u i := by
  apply LinearMap.ext
  intro x
  change presentationLowering u i hu (UniversalEnvelopingAlgebra.ι ℂ A • x)-
    UniversalEnvelopingAlgebra.ι ℂ A • presentationLowering u i hu x =
      UniversalEnvelopingAlgebra.ι ℂ (loweringUpper i A) • x-
        upperSimpleCoefficient i A • presentationCartan u i x
  rw [presentationLowering_generator_smul]
  abel

end
end Schubert.RS.Representation
