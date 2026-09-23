import Schubert.RS.JosephPolo.PresentationSl2
import Schubert.RS.JosephPolo.AdjacentComparison
import Schubert.RS.AdjacentCompletionGenerator

namespace Schubert.RS.Representation
noncomputable section
open FinPermutation
attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 200000
set_option Elab.async false

theorem cartan_representation_covariance {n : ℕ} {X : Type*}
    [AddCommGroup X] [Module ℂ X] (h : Fin n → ℂ)
    (ρ : Enveloping n →ₐ[ℂ] Module.End ℂ X) (T : Module.End ℂ X)
    (hT : ∀ A x, T (ρ (UniversalEnvelopingAlgebra.ι ℂ A) x) =
      ρ (UniversalEnvelopingAlgebra.ι ℂ (cartanUpper h A)) x +
        ρ (UniversalEnvelopingAlgebra.ι ℂ A) (T x))
    (a : Enveloping n) (x : X) :
    T (ρ a x) = ρ (cartanEnveloping h a) x + ρ a (T x) := by
  induction a using enveloping_induction generalizing x with
  | hC c =>
    simp only [Algebra.algebraMap_eq_smul_one, map_smul, cartanEnveloping_one,
      smul_zero, map_zero, LinearMap.zero_apply, zero_add, map_one,
      LinearMap.smul_apply, Module.End.one_apply]
  | hι A => rw [cartanEnveloping_generator]; exact hT A x
  | hmul a b ha hb =>
    simp only [map_mul, Module.End.mul_apply, ha, hb, cartanEnveloping_mul,
      map_add, LinearMap.add_apply]
    abel
  | hadd a b ha hb =>
    simp only [map_add, LinearMap.add_apply, ha, hb]
    abel

theorem presentationCartan_generator {n : ℕ} (u : Composition n) (i : AdjacentPosition n) :
    presentationCartan u i (presentationGenerator u) =
      ((u i.left : ℂ)-(u i.right : ℂ)) • presentationGenerator u := by
  rw [presentationGenerator, presentationCartan_mk]
  change Submodule.Quotient.mk (cartanEnveloping (adjacentCartanDiagonal i) 1+
    ((u i.left : ℂ)-(u i.right : ℂ)) • 1) = _
  rw [cartanEnveloping_one, zero_add]
  exact (((jpLeftIdeal u).restrictScalars ℂ).mkQ).map_smul _ _

theorem presentationCartan_smul {n : ℕ} (u : Composition n) (i : AdjacentPosition n)
    (a : Enveloping n) (x : PresentationQuotient u) :
    presentationCartan u i (a • x) =
      cartanEnveloping (adjacentCartanDiagonal i) a • x + a • presentationCartan u i x := by
  obtain ⟨b,rfl⟩ := Submodule.Quotient.mk_surjective (jpLeftIdeal u) x
  rw [← Submodule.Quotient.mk_smul, presentationCartan_mk, presentationCartan_mk,
    ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_add]
  apply congrArg (fun b : Enveloping n => (Submodule.Quotient.mk b : PresentationQuotient u))
  change cartanEnveloping (adjacentCartanDiagonal i) (a*b)+
    ((u i.left : ℂ)-(u i.right : ℂ)) • (a*b) =
    cartanEnveloping (adjacentCartanDiagonal i) a*b+
      a*(cartanEnveloping (adjacentCartanDiagonal i) b+((u i.left : ℂ)-(u i.right : ℂ)) • b)
  rw [cartanEnveloping_mul, mul_add, mul_smul_comm]
  abel

theorem polynomialLie_adjacentCartan {n : ℕ} (i : AdjacentPosition n) :
    polynomialLie n (adjacentCartanMatrix i) = polynomialRootCartan i.left i.right := by
  change polynomialLie n (Matrix.single i.left i.left 1-Matrix.single i.right i.right 1)=_
  rw [map_sub]
  rfl

theorem polynomial_cartan_covariance {n : ℕ} (i : AdjacentPosition n)
    (a : Enveloping n) (p : MatrixPolynomial n) :
    polynomialRootCartan i.left i.right (polynomialEnveloping n a p) =
      polynomialEnveloping n (cartanEnveloping (adjacentCartanDiagonal i) a) p+
        polynomialEnveloping n a (polynomialRootCartan i.left i.right p) := by
  apply cartan_representation_covariance
  intro A q
  have h := LieHom.map_lie (polynomialLie n) (adjacentCartanMatrix i) A.val
  rw [polynomialLie_adjacentCartan] at h
  have hm : (cartanUpper (adjacentCartanDiagonal i) A).val = ⁅adjacentCartanMatrix i,A.val⁆ := by
    change cartanMatrix (adjacentCartanDiagonal i) A.val=_
    rw [cartanMatrix_eq_commutator, adjacentCartanMatrix_eq_diagonal]
    rfl
  simp only [polynomialEnveloping, UniversalEnvelopingAlgebra.lift_ι_apply]
  change polynomialRootCartan i.left i.right (polynomialUpperLie n A q) =
    polynomialUpperLie n (cartanUpper (adjacentCartanDiagonal i) A) q+
      polynomialUpperLie n A (polynomialRootCartan i.left i.right q)
  change polynomialRootCartan i.left i.right (polynomialLie n A.val q)=
    polynomialLie n (cartanUpper (adjacentCartanDiagonal i) A).val q+
      polynomialLie n A.val (polynomialRootCartan i.left i.right q)
  rw [hm]
  have he := LinearMap.congr_fun h q
  change _=polynomialRootCartan i.left i.right (polynomialLie n A.val q)-
    polynomialLie n A.val (polynomialRootCartan i.left i.right q) at he
  rw [he]
  abel

theorem compositionPresentationMap_cartan {n : ℕ} (u : Composition n) (i : AdjacentPosition n)
    (x : PresentationQuotient u) :
    (compositionPresentationMap u (presentationCartan u i x)).val =
      polynomialRootCartan i.left i.right (compositionPresentationMap u x).val := by
  obtain ⟨a,rfl⟩ := presentation_is_cyclic u x
  have hg : polynomialRootCartan i.left i.right (compositionFlagGenerator u).val =
      ((u i.left : ℂ)-(u i.right : ℂ)) • (compositionFlagGenerator u).val := by
    rw [polynomialRootCartan_weight _ _ _ _ (compositionFlagGenerator_polynomial_weight u)]
    simp only [Int.cast_sub, Int.cast_natCast]
  rw [presentationCartan_smul, map_add, map_smul, map_smul, compositionPresentationMap_generator,
    presentationCartan_generator]
  rw [(compositionPresentationMap u).map_smul]
  rw [compositionPresentationMap_generator]
  change polynomialEnveloping n (cartanEnveloping (adjacentCartanDiagonal i) a)
      (compositionFlagGenerator u).val + polynomialEnveloping n a
      (((compositionPresentationMap u).restrictScalars ℂ)
        (((u i.left : ℂ)-(u i.right : ℂ)) • presentationGenerator u)).val =
      polynomialRootCartan i.left i.right (polynomialEnveloping n a (compositionFlagGenerator u).val)
  rw [map_smul, LinearMap.restrictScalars_apply, compositionPresentationMap_generator,
    polynomial_cartan_covariance, hg]
  rfl

end
end Schubert.RS.Representation

