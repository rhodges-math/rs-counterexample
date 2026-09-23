import Schubert.RS.JosephPolo.LoweringIdeal
import Schubert.RS.JosephPolo.LoweringHomogeneity

namespace Schubert.RS.Representation
noncomputable section
open FinPermutation
attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 1600000

theorem end_commutator_transfer {X Y : Type*} [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] (q : X →ₗ[ℂ] Y) (hq : Function.Surjective q)
    (A B C : Module.End ℂ X) (A' B' C' : Module.End ℂ Y)
    (ha : ∀ x, q (A x)=A' (q x)) (hb : ∀ x, q (B x)=B' (q x))
    (hc : ∀ x, q (C x)=C' (q x)) (h : A*B-B*A=C) : A'*B'-B'*A'=C' := by
  apply LinearMap.ext
  intro y
  obtain ⟨x,rfl⟩ := hq y
  change A' (B' (q x))-B' (A' (q x))=C' (q x)
  calc
    _ = q (A (B x))-q (B (A x)) := by rw [ha, hb, hb, ha]
    _ = q (A (B x)-B (A x)) := (q.map_sub _ _).symm
    _ = q (C x) := congrArg q (LinearMap.congr_fun h x)
    _ = _ := hc x

def presentationCartan {n : ℕ} (u : Composition n) (i : AdjacentPosition n) :
    Module.End ℂ (PresentationQuotient u) :=
  ((jpLeftIdeal u).restrictScalars ℂ).mapQ ((jpLeftIdeal u).restrictScalars ℂ)
    (cartanEnveloping (adjacentCartanDiagonal i)+((u i.left : ℂ)-(u i.right : ℂ)) • 1)
    (fun a ha => (jpLeftIdeal u).add_mem (cartanEnveloping_mem_jp _ u ha)
      (((jpLeftIdeal u).restrictScalars ℂ).smul_mem _ ha))

def presentationRaising {n : ℕ} (u : Composition n) (i : AdjacentPosition n) :
    Module.End ℂ (PresentationQuotient u) :=
  (Algebra.lsmul ℂ ℂ (PresentationQuotient u)) (rootOperator (adjacentPositiveRoot i))

theorem presentationCartan_mk {n : ℕ} (u : Composition n) (i : AdjacentPosition n)
    (a : Enveloping n) :
    presentationCartan u i (Submodule.Quotient.mk a) =
      Submodule.Quotient.mk ((cartanEnveloping (adjacentCartanDiagonal i)+
        ((u i.left : ℂ)-(u i.right : ℂ)) • 1) a) := rfl

theorem adjacentWeight_gap {n : ℕ} (u : Composition n) (i : AdjacentPosition n)
    (hu : u i.left ≤ u i.right) :
    (u i.left : ℂ)-(u i.right : ℂ) = -((u i.right-u i.left : ℕ) : ℂ) := by
  have hc : ((u i.right-u i.left : ℕ) : ℂ)+(u i.left : ℂ)=(u i.right : ℂ) := by
    exact_mod_cast Nat.sub_add_cancel hu
  linear_combination hc

theorem presentationRaising_mk {n : ℕ} (u : Composition n) (i : AdjacentPosition n)
    (a : Enveloping n) :
    presentationRaising u i (Submodule.Quotient.mk a) =
      Submodule.Quotient.mk (rootOperator (adjacentPositiveRoot i)*a) := by
  change rootOperator (adjacentPositiveRoot i) • (Submodule.Quotient.mk a : PresentationQuotient u) = _
  rw [← Submodule.Quotient.mk_smul]
  rfl

theorem enveloping_raising_lowering {n : ℕ} (i : AdjacentPosition n) (w : ℂ) :
    regularEnvelopingAction n (rootOperator (adjacentPositiveRoot i))*loweringEnveloping i w -
      loweringEnveloping i w*regularEnvelopingAction n (rootOperator (adjacentPositiveRoot i)) =
      cartanEnveloping (adjacentCartanDiagonal i)+w • 1 := by
  apply LinearMap.ext
  intro a
  change rootOperator (adjacentPositiveRoot i)*loweringEnveloping i w a -
    loweringEnveloping i w (rootOperator (adjacentPositiveRoot i)*a) =
    cartanEnveloping (adjacentCartanDiagonal i) a+w • a
  rw [loweringEnveloping_simple_mul]
  abel

theorem enveloping_cartan_raising {n : ℕ} (i : AdjacentPosition n) (w : ℂ) :
    (cartanEnveloping (adjacentCartanDiagonal i)+w • 1)*
        regularEnvelopingAction n (rootOperator (adjacentPositiveRoot i)) -
      regularEnvelopingAction n (rootOperator (adjacentPositiveRoot i))*
        (cartanEnveloping (adjacentCartanDiagonal i)+w • 1) =
      (2 : ℂ) • regularEnvelopingAction n (rootOperator (adjacentPositiveRoot i)) := by
  have h := shiftedCartanEnveloping_commutator (adjacentCartanDiagonal i) w
    (rootVector (adjacentPositiveRoot i))
  rw [cartanUpper_root] at h
  have he : adjacentCartanDiagonal i (adjacentPositiveRoot i).val.1-
      adjacentCartanDiagonal i (adjacentPositiveRoot i).val.2=2 := adjacentCartan_simple_weight i
  rw [he, map_smul, map_smul] at h
  exact h

/-- All three sl2 relations on Q_u, including cases where the action is
trivial. No nonzero or faithful-action hypothesis is imposed. -/
theorem presentation_sl2_relations {n : ℕ} (u : Composition n) (i : AdjacentPosition n)
    (hu : u i.left ≤ u i.right) :
    (presentationRaising u i*presentationLowering u i hu-
      presentationLowering u i hu*presentationRaising u i = presentationCartan u i) ∧
    (presentationCartan u i*presentationRaising u i-
      presentationRaising u i*presentationCartan u i = (2 : ℂ) • presentationRaising u i) ∧
    (presentationCartan u i*presentationLowering u i hu-
      presentationLowering u i hu*presentationCartan u i = (-2 : ℂ) • presentationLowering u i hu) := by
  let q : Enveloping n →ₗ[ℂ] PresentationQuotient u := ((jpLeftIdeal u).restrictScalars ℂ).mkQ
  have hq : Function.Surjective q := Submodule.mkQ_surjective _
  let w : ℂ := -((u i.right-u i.left : ℕ) : ℂ)
  let E := regularEnvelopingAction n (rootOperator (adjacentPositiveRoot i))
  let H := cartanEnveloping (adjacentCartanDiagonal i)+w • 1
  let F := loweringEnveloping i w
  have hE (a : Enveloping n) : q (E a)=presentationRaising u i (q a) :=
    (presentationRaising_mk u i a).symm
  have hH (a : Enveloping n) : q (H a)=presentationCartan u i (q a) := by
    have h := presentationCartan_mk u i a
    rw [adjacentWeight_gap u i hu] at h
    exact h.symm
  have hF (a : Enveloping n) : q (F a)=presentationLowering u i hu (q a) :=
    (presentationLowering_mk u i hu a).symm
  refine ⟨end_commutator_transfer q hq E F H _ _ _ hE hF hH (enveloping_raising_lowering i w), ?_, ?_⟩
  · apply end_commutator_transfer q hq H E ((2 : ℂ) • E) _ _ _ hH hE
    · intro a
      change q ((2 : ℂ) • E a)=(2 : ℂ) • presentationRaising u i (q a)
      rw [map_smul, hE]
    · exact enveloping_cartan_raising i w
  · apply end_commutator_transfer q hq H F ((-2 : ℂ) • F) _ _ _ hH hF
    · intro a
      change q ((-2 : ℂ) • F a)=(-2 : ℂ) • presentationLowering u i hu (q a)
      rw [map_smul, hF]
    · exact shiftedCartanEnveloping_lowering i w

end
end Schubert.RS.Representation
