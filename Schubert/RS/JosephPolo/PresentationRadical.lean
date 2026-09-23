import Schubert.RS.JosephPolo.PresentationAction
import Schubert.RS.JosephPolo.PresentationCommutators
import Schubert.RS.JosephPolo.RadicalLevi
import Schubert.RS.Sl2FullPrimitive

namespace Schubert.RS.Representation
noncomputable section
open FinPermutation TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false

def radicalUpperLie {n : ℕ} (i : AdjacentPosition n) : radicalEndLie i →ₗ⁅ℂ⁆ upperNilpotent n where
  toLinearMap := radicalUpper i
  map_lie' {r s} := radicalUpper_bracket i r s

def presentationRadicalLie {n : ℕ} (u : Composition n) (i : AdjacentPosition n) :
    radicalEndLie i →ₗ⁅ℂ⁆ Module.End ℂ (PresentationQuotient u) :=
  (presentationUpperLie u).comp (radicalUpperLie i)

@[instance_reducible]
def presentationRadicalLieRingModule {n : ℕ} (u : Composition n) (i : AdjacentPosition n) :
    LieRingModule (radicalEndLie i) (PresentationQuotient u) :=
  LieRingModule.compLieHom (PresentationQuotient u) (presentationRadicalLie u i)

theorem presentationRadicalLieModule {n : ℕ} (u : Composition n) (i : AdjacentPosition n) :
    letI := presentationRadicalLieRingModule u i
    LieModule ℂ (radicalEndLie i) (PresentationQuotient u) :=
  LieModule.compLieHom (PresentationQuotient u) (presentationRadicalLie u i)

theorem presentationRadical_apply {n : ℕ} (u : Composition n) (i : AdjacentPosition n)
    (r : radicalEndLie i) (x : PresentationQuotient u) :
    letI := presentationRadicalLieRingModule u i
    ⁅r,x⁆=UniversalEnvelopingAlgebra.ι ℂ (radicalUpper i r) • x := rfl

theorem presentationRadical_raising {n : ℕ} (u : Composition n) (i : AdjacentPosition n)
    (r : radicalEndLie i) :
    ⁅presentationRaising u i,presentationRadicalLie u i r⁆ =
      presentationRadicalLie u i
        ⁅sl2RaisingElement (polynomialSl2Triple i.left i.right i.left_ne_right),r⁆ := by
  change ⁅presentationRaising u i,presentationUpperLie u (radicalUpper i r)⁆ =
    presentationUpperLie u (radicalUpper i _)
  rw [radicalUpper_raising, LieHom.map_lie, presentationUpperLie_raising]

theorem presentationRadical_cartan {n : ℕ} (u : Composition n) (i : AdjacentPosition n)
    (r : radicalEndLie i) :
    ⁅presentationCartan u i,presentationRadicalLie u i r⁆ =
      presentationRadicalLie u i
        ⁅sl2CartanElement (polynomialSl2Triple i.left i.right i.left_ne_right),r⁆ := by
  change ⁅presentationCartan u i,presentationUpperLie u (radicalUpper i r)⁆ =
    presentationUpperLie u (radicalUpper i _)
  rw [radicalUpper_cartan, presentationUpperLie_cartan]

theorem presentationRadical_lowering {n : ℕ} (u : Composition n) (i : AdjacentPosition n)
    (hu : u i.left ≤ u i.right) (r : radicalEndLie i) :
    ⁅presentationLowering u i hu,presentationRadicalLie u i r⁆ =
      presentationRadicalLie u i
        ⁅sl2LoweringElement (polynomialSl2Triple i.left i.right i.left_ne_right),r⁆ := by
  change ⁅presentationLowering u i hu,presentationUpperLie u (radicalUpper i r)⁆ =
    presentationUpperLie u (radicalUpper i _)
  rw [radicalUpper_lowering, presentationUpperLie_lowering, radicalUpper_simple_zero,
    zero_smul, sub_zero]

theorem presentationRadical_isLieTower {n : ℕ} (u : Composition n) (i : AdjacentPosition n)
    (hu : u i.left ≤ u i.right) :
    letI := presentationSl2LieRingModule u i hu
    letI := presentationRadicalLieRingModule u i
    IsLieTower ((polynomialSl2Triple i.left i.right i.left_ne_right).toLieSubalgebra ℂ)
      (radicalEndLie i) (PresentationQuotient u) := by
  letI := presentationSl2LieRingModule u i hu
  letI := presentationSl2LieModule u i hu
  letI := presentationRadicalLieRingModule u i
  letI := presentationRadicalLieModule u i
  have hcomm (z : (polynomialSl2Triple i.left i.right i.left_ne_right).toLieSubalgebra ℂ)
      (r : radicalEndLie i) :
      ⁅presentationSl2Action u i hu z,presentationRadicalLie u i r⁆=
        presentationRadicalLie u i ⁅z,r⁆ := by
    obtain ⟨a,b,c,rfl⟩ := sl2_element_expansion (polynomialSl2Triple i.left i.right i.left_ne_right) z
    have he : presentationSl2Action u i hu
        (sl2RaisingElement (polynomialSl2Triple i.left i.right i.left_ne_right))=presentationRaising u i := by
      apply LinearMap.ext
      exact presentationSl2_raising u i hu
    have hf : presentationSl2Action u i hu
        (sl2LoweringElement (polynomialSl2Triple i.left i.right i.left_ne_right))=presentationLowering u i hu := by
      apply LinearMap.ext
      exact presentationSl2_lowering u i hu
    have hh : presentationSl2Action u i hu
        (sl2CartanElement (polynomialSl2Triple i.left i.right i.left_ne_right))=presentationCartan u i := by
      apply LinearMap.ext
      exact presentationSl2_cartan u i hu
    have hs (c : ℂ) (P Q : Module.End ℂ (PresentationQuotient u)) :
        ⁅c • P,Q⁆=c • ⁅P,Q⁆ := by
      simp only [Ring.lie_def, smul_mul_assoc, mul_smul_comm, smul_sub]
    simp only [map_add, map_smul, add_lie, smul_lie, he, hf, hh,
      hs, presentationRadical_raising, presentationRadical_lowering u i hu, presentationRadical_cartan]
  refine ⟨?_⟩
  intro z r x
  have hc := LinearMap.congr_fun (hcomm z r) x
  change (presentationSl2Action u i hu z) ((presentationRadicalLie u i r) x) =
    (presentationRadicalLie u i ⁅z,r⁆) x+
      (presentationRadicalLie u i r) ((presentationSl2Action u i hu z) x)
  change (presentationSl2Action u i hu z) ((presentationRadicalLie u i r) x)-
    (presentationRadicalLie u i r) ((presentationSl2Action u i hu z) x)=_ at hc
  exact sub_eq_iff_eq_add.mp hc

def presentationRadicalAction {n : ℕ} (u : Composition n) (i : AdjacentPosition n)
    (hu : u i.left ≤ u i.right) :
    letI := presentationSl2LieRingModule u i hu
    letI := presentationSl2LieModule u i hu
    (radicalEndLie i ⊗[ℂ] PresentationQuotient u) →ₗ⁅ℂ,
      (polynomialSl2Triple i.left i.right i.left_ne_right).toLieSubalgebra ℂ⁆ PresentationQuotient u := by
  letI := presentationSl2LieRingModule u i hu
  letI := presentationSl2LieModule u i hu
  letI := presentationRadicalLieRingModule u i
  letI := presentationRadicalLieModule u i
  letI := presentationRadical_isLieTower u i hu
  exact
    { toLinearMap := (LieModule.toModuleHom ℂ (radicalEndLie i) (PresentationQuotient u)).toLinearMap
      map_lie' := by
        intro z t
        change LieModule.toModuleHom ℂ (radicalEndLie i) (PresentationQuotient u) ⁅z,t⁆ =
          ⁅z,LieModule.toModuleHom ℂ (radicalEndLie i) (PresentationQuotient u) t⁆
        induction t using TensorProduct.induction_on with
        | zero => simp
        | tmul r x =>
          simp only [TensorProduct.LieModule.lie_tmul_right, map_add, LieModule.toModuleHom_apply]
          exact (IsLieTower.leibniz_lie z r x).symm
        | add t s ht hs => simp only [lie_add, map_add, ht, hs] }

theorem presentationRadicalAction_tmul {n : ℕ} (u : Composition n) (i : AdjacentPosition n)
    (hu : u i.left ≤ u i.right) (r : radicalEndLie i) (x : PresentationQuotient u) :
    letI := presentationSl2LieRingModule u i hu
    letI := presentationSl2LieModule u i hu
    presentationRadicalAction u i hu (r ⊗ₜ[ℂ] x) =
      UniversalEnvelopingAlgebra.ι ℂ (radicalUpper i r) • x := by
  letI := presentationRadicalLieRingModule u i
  letI := presentationRadicalLieModule u i
  change LieModule.toModuleHom ℂ (radicalEndLie i) (PresentationQuotient u) (r ⊗ₜ[ℂ] x)=_
  rw [LieModule.toModuleHom_apply, presentationRadical_apply]

end
end Schubert.RS.Representation
