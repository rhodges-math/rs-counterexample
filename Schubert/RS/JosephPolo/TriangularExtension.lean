import Schubert.RS.Representation.EnvelopingIntertwining
import Mathlib.LinearAlgebra.Prod

/-! Triangular extensions of operators on the enveloping algebra through
its universal property, under an explicit Lie-cocycle identity. -/

namespace Schubert.RS.Representation
noncomputable section
attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 1200000

variable {n : ℕ} {X : Type*} [AddCommGroup X] [Module ℂ X]

def triangularEnd (P Q : Module.End ℂ X) : Module.End ℂ (X × X) where
  toFun z := (P z.1, P z.2+Q z.1)
  map_add' z w := by simp only [Prod.fst_add, Prod.snd_add, map_add, Prod.mk_add_mk]; congr 1; abel
  map_smul' c z := by simp only [Prod.smul_fst, Prod.smul_snd, map_smul, smul_add, Prod.smul_mk, RingHom.id_apply]

def triangularLie (ρ : Enveloping n →ₐ[ℂ] Module.End ℂ X)
    (δ : upperNilpotent n →ₗ[ℂ] Module.End ℂ X)
    (hδ : ∀ A B, δ ⁅A,B⁆ =
      ρ (UniversalEnvelopingAlgebra.ι ℂ A) * δ B + δ A * ρ (UniversalEnvelopingAlgebra.ι ℂ B) -
      ρ (UniversalEnvelopingAlgebra.ι ℂ B) * δ A - δ B * ρ (UniversalEnvelopingAlgebra.ι ℂ A)) :
    upperNilpotent n →ₗ⁅ℂ⁆ Module.End ℂ (X × X) where
  toFun A := triangularEnd (ρ (UniversalEnvelopingAlgebra.ι ℂ A)) (δ A)
  map_add' A B := by
    apply LinearMap.ext
    intro z
    simp only [triangularEnd, LinearMap.coe_mk, AddHom.coe_mk, map_add, LinearMap.add_apply]
    apply Prod.ext
    · rfl
    · change _+(_+_)=(_+_)+(_+_)
      abel
  map_smul' c A := by
    apply LinearMap.ext
    intro z
    simp only [triangularEnd, LinearMap.coe_mk, AddHom.coe_mk, map_smul,
      LinearMap.smul_apply, RingHom.id_apply, Prod.smul_mk, smul_add]
  map_lie' {A B} := by
    have hρ : ρ (UniversalEnvelopingAlgebra.ι ℂ ⁅A,B⁆) =
        ρ (UniversalEnvelopingAlgebra.ι ℂ A) * ρ (UniversalEnvelopingAlgebra.ι ℂ B) -
        ρ (UniversalEnvelopingAlgebra.ι ℂ B) * ρ (UniversalEnvelopingAlgebra.ι ℂ A) := by
      rw [LieHom.map_lie]
      change ρ (_*_ - _*_) = _
      rw [map_sub, map_mul, map_mul]
    apply LinearMap.ext
    intro z
    apply Prod.ext
    · change ρ (UniversalEnvelopingAlgebra.ι ℂ ⁅A,B⁆) z.1 = _
      rw [hρ]
      rfl
    · change ρ (UniversalEnvelopingAlgebra.ι ℂ ⁅A,B⁆) z.2 + δ ⁅A,B⁆ z.1 = _
      rw [hρ, hδ]
      simp only [triangularEnd, LinearMap.coe_mk, AddHom.coe_mk,
        Ring.lie_def, Module.End.mul_apply, LinearMap.add_apply, LinearMap.sub_apply,
        Prod.snd_sub, map_add]
      abel

variable (ρ : Enveloping n →ₐ[ℂ] Module.End ℂ X)
  (δ : upperNilpotent n →ₗ[ℂ] Module.End ℂ X)
  (hδ : ∀ A B, δ ⁅A,B⁆ =
    ρ (UniversalEnvelopingAlgebra.ι ℂ A) * δ B + δ A * ρ (UniversalEnvelopingAlgebra.ι ℂ B) -
    ρ (UniversalEnvelopingAlgebra.ι ℂ B) * δ A - δ B * ρ (UniversalEnvelopingAlgebra.ι ℂ A))

def triangularEnveloping : Enveloping n →ₐ[ℂ] Module.End ℂ (X × X) :=
  UniversalEnvelopingAlgebra.lift ℂ (triangularLie ρ δ hδ)

theorem triangularEnveloping_ι (A : upperNilpotent n) :
    triangularEnveloping ρ δ hδ (UniversalEnvelopingAlgebra.ι ℂ A) =
      triangularEnd (ρ (UniversalEnvelopingAlgebra.ι ℂ A)) (δ A) :=
  UniversalEnvelopingAlgebra.lift_ι_apply ℂ _ A

theorem triangularEnveloping_fst (a : Enveloping n) (z : X × X) :
    (triangularEnveloping ρ δ hδ a z).1 = ρ a z.1 := by
  exact enveloping_intertwines (triangularEnveloping ρ δ hδ) ρ (LinearMap.fst ℂ X X)
    (fun A z => by rw [triangularEnveloping_ι]; rfl) a z

theorem triangularEnveloping_inr (a : Enveloping n) (x : X) :
    triangularEnveloping ρ δ hδ a (0,x) = (0,ρ a x) := by
  symm
  apply enveloping_intertwines ρ (triangularEnveloping ρ δ hδ) (LinearMap.inr ℂ X X)
  intro A x
  rw [triangularEnveloping_ι]
  change (0, ρ (UniversalEnvelopingAlgebra.ι ℂ A) x) =
    (ρ (UniversalEnvelopingAlgebra.ι ℂ A) 0, ρ (UniversalEnvelopingAlgebra.ι ℂ A) x + δ A 0)
  rw [map_zero, map_zero, add_zero]

/-- Left multiplication on the actual enveloping algebra. -/
def regularEnvelopingAction (n : ℕ) : Enveloping n →ₐ[ℂ] Module.End ℂ (Enveloping n) :=
  Algebra.lsmul ℂ ℂ (Enveloping n)

section Regular
variable (δ : upperNilpotent n →ₗ[ℂ] Module.End ℂ (Enveloping n))
  (hδ : ∀ A B, δ ⁅A,B⁆ =
    regularEnvelopingAction n (UniversalEnvelopingAlgebra.ι ℂ A) * δ B +
      δ A * regularEnvelopingAction n (UniversalEnvelopingAlgebra.ι ℂ B) -
      regularEnvelopingAction n (UniversalEnvelopingAlgebra.ι ℂ B) * δ A -
      δ B * regularEnvelopingAction n (UniversalEnvelopingAlgebra.ι ℂ A))

def envelopingCocycleOperator : Module.End ℂ (Enveloping n) where
  toFun a := (triangularEnveloping (regularEnvelopingAction n) δ hδ a (1,0)).2
  map_add' a b := by rw [map_add]; rfl
  map_smul' c a := by rw [map_smul]; rfl

theorem envelopingCocycleOperator_one : envelopingCocycleOperator δ hδ 1=0 := by
  change (triangularEnveloping (regularEnvelopingAction n) δ hδ 1 (1,0)).2=0
  rw [map_one]
  rfl

theorem envelopingCocycleOperator_generator_mul (A : upperNilpotent n) (a : Enveloping n) :
    envelopingCocycleOperator δ hδ (UniversalEnvelopingAlgebra.ι ℂ A * a) =
      UniversalEnvelopingAlgebra.ι ℂ A * envelopingCocycleOperator δ hδ a + δ A a := by
  change (triangularEnveloping (regularEnvelopingAction n) δ hδ
    (UniversalEnvelopingAlgebra.ι ℂ A * a) (1,0)).2 = _
  rw [map_mul, Module.End.mul_apply, triangularEnveloping_ι]
  change UniversalEnvelopingAlgebra.ι ℂ A * envelopingCocycleOperator δ hδ a +
    δ A (triangularEnveloping (regularEnvelopingAction n) δ hδ a (1,0)).1 = _
  rw [triangularEnveloping_fst]
  change _ + δ A (a*1) = _
  rw [mul_one]

theorem envelopingCocycleOperator_generator (A : upperNilpotent n) :
    envelopingCocycleOperator δ hδ (UniversalEnvelopingAlgebra.ι ℂ A) = δ A 1 := by
  have h := envelopingCocycleOperator_generator_mul δ hδ A 1
  simpa only [mul_one, envelopingCocycleOperator_one, mul_zero, zero_add] using h

end Regular

end
end Schubert.RS.Representation
