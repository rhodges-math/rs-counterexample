import Schubert.FlagVarieties.Foundations.Schemes.QuotientPairScheme

/-! # Independence of the covering family for quotient-frame morphisms -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientPair

open AlgebraicGeometry CategoryTheory TensorProduct TopologicalSpace

universe u v w

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
  {ι : Type v} {κ : Type w} {U : ι → X.Opens} {V : κ → X.Opens}
  {Q : Type u} [AddCommGroup Q] [Module Γ(X, ⊤) Q]

attribute [local instance] openAlgebra

/-- The pairwise intersections of two open covers form an open cover. -/
theorem intersection_isOpenCover (hU : IsOpenCover U) (hV : IsOpenCover V) :
    IsOpenCover (fun ij : ι × κ => U ij.1 ⊓ V ij.2) := by
  apply top_le_iff.mp
  intro x hx
  obtain ⟨i, hi⟩ := hU.exists_mem x
  obtain ⟨j, hj⟩ := hV.exists_mem x
  exact Opens.mem_iSup.mpr ⟨(i, j), hi, hj⟩

/-- Two quotient frames on possibly different opens agree as full maps on their intersection. -/
theorem framedPair_overlap
    (q : Γ(X, ⊤) × Γ(X, ⊤) →ₗ[Γ(X, ⊤)] Q) (hq : Function.Surjective q)
    (φ : R →+* Γ(X, ⊤)) (A B : X.Opens)
    (frameA : ModuleOn (Q := Q) A ≃ₗ[RingOn A] RingOn A)
    (frameB : ModuleOn (Q := Q) B ≃ₗ[RingOn B] RingOn B) :
    X.homOfLE (inf_le_left : A ⊓ B ≤ A) ≫
        ProjectiveLine.fromPair (ProjectiveLine.coefficientsOn φ A)
          (frameA (1 ⊗ₜ[Γ(X, ⊤)] q (1, 0))) (frameA (1 ⊗ₜ[Γ(X, ⊤)] q (0, 1)))
          (frame_coordinates_coprime q hq frameA) =
      X.homOfLE (inf_le_right : A ⊓ B ≤ B) ≫
        ProjectiveLine.fromPair (ProjectiveLine.coefficientsOn φ B)
          (frameB (1 ⊗ₜ[Γ(X, ⊤)] q (1, 0))) (frameB (1 ⊗ₜ[Γ(X, ⊤)] q (0, 1)))
          (frame_coordinates_coprime q hq frameB) := by
  rw [ProjectiveLine.fromPair_naturality, ProjectiveLine.fromPair_naturality]
  simp only [ProjectiveLine.coefficientsOn_restrict]
  obtain ⟨unit, hδ, hε⟩ := quotient_frame_change_pair
    (restrictFrame (inf_le_right : A ⊓ B ≤ B) frameB)
    (restrictFrame (inf_le_left : A ⊓ B ≤ A) frameA)
    (1 ⊗ₜ[Γ(X, ⊤)] q (1, 0)) (1 ⊗ₜ[Γ(X, ⊤)] q (0, 1))
  simp only [restrictFrame_one_tmul] at hδ hε
  simp only [hδ, hε]
  exact ProjectiveLine.fromPair_unit_mul _ _ _
    ((frame_coordinates_coprime q hq frameB).map
      (X.homOfLE (inf_le_right : A ⊓ B ≤ B)).appTop.hom) unit

/-- The scheme morphism is independent of both the frame and the covering family. -/
theorem fromFrames_cover_independent
    (q : Γ(X, ⊤) × Γ(X, ⊤) →ₗ[Γ(X, ⊤)] Q) (hq : Function.Surjective q)
    (framesU : ∀ i, ModuleOn (Q := Q) (U i) ≃ₗ[RingOn (U i)] RingOn (U i))
    (framesV : ∀ j, ModuleOn (Q := Q) (V j) ≃ₗ[RingOn (V j)] RingOn (V j))
    (φ : R →+* Γ(X, ⊤)) (hU : IsOpenCover U) (hV : IsOpenCover V) :
    fromFrames q hq framesU φ hU = fromFrames q hq framesV φ hV := by
  apply (X.openCoverOfIsOpenCover _ (intersection_isOpenCover hU hV)).hom_ext
  rintro ⟨i, j⟩
  change (U i ⊓ V j).ι ≫ _ = (U i ⊓ V j).ι ≫ _
  conv_lhs =>
    rw [← X.homOfLE_ι (inf_le_left : U i ⊓ V j ≤ U i), Category.assoc,
      restrict_fromFrames]
  conv_rhs =>
    rw [← X.homOfLE_ι (inf_le_right : U i ⊓ V j ≤ V j), Category.assoc,
      restrict_fromFrames]
  exact framedPair_overlap q hq φ (U i) (V j) (framesU i) (framesV j)

end FlagVarieties.Foundations.QuotientPair

