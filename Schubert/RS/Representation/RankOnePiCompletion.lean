import Schubert.RS.Representation.RankOnePiModule

namespace Schubert.RS.Representation
noncomputable section
universe u v
open LieModule Module
open scoped BigOperators

variable {L : Type v} [LieRing L] [LieAlgebra ℂ L]
  {I : Type u} [Fintype I] {M X : I → Type u}
  [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
  [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)]
  [∀ i, LieRingModule L (X i)] [∀ i, LieModule ℂ L (X i)]
  [∀ i, Module.Finite ℂ (X i)]
  {e h : L} {E H : ∀ i, Module.End ℂ (M i)} {ι : ∀ i, M i →ₗ[ℂ] X i}

/-- A finite product of exhibited completions is the actual completion of
the componentwise source. Its universal map is the sum of component lifts. -/
theorem IsRankOneCompletion.pi (C : ∀ i, IsRankOneCompletion e h (E i) (H i) (ι i)) :
    IsRankOneCompletion e h (LinearMap.piMap E) (LinearMap.piMap H) (LinearMap.piMap ι) := by
  classical
  refine { injective := ?_, map_e := ?_, map_h := ?_, universal := ?_ }
  · intro x y hxy
    funext i
    exact (C i).injective (congrFun hxy i)
  · intro x
    funext i
    exact (C i).map_e (x i)
  · intro x
    funext i
    exact (C i).map_h (x i)
  · intro N _ _ _ _ _ g ge gh
    let gi : ∀ i, M i →ₗ[ℂ] N := fun i => g.comp (LinearMap.single ℂ M i)
    have gei : ∀ i m, gi i (E i m) = ⁅e,gi i m⁆ := by
      intro i m
      change g (Pi.single i (E i m)) = ⁅e,g (Pi.single i m)⁆
      rw [← piLinearMap_single E]
      exact ge (Pi.single i m)
    have ghi : ∀ i m, gi i (H i m) = ⁅h,gi i m⁆ := by
      intro i m
      change g (Pi.single i (H i m)) = ⁅h,g (Pi.single i m)⁆
      rw [← piLinearMap_single H]
      exact gh (Pi.single i m)
    let Fi : ∀ i, X i →ₗ⁅ℂ,L⁆ N := fun i => (C i).lift (gi i) (gei i) (ghi i)
    let F := piLieSum Fi
    have hF : ∀ x, F (LinearMap.piMap ι x) = g x := by
      intro x
      rw [piLieSum_apply]
      change (∑ i, Fi i (ι i (x i))) = g x
      simp only [Fi,IsRankOneCompletion.lift_boundary]
      change (∑ i, g (Pi.single i (x i))) = g x
      rw [← map_sum,Finset.univ_sum_single]
    refine ⟨F,hF,?_⟩
    intro Ψ hΨ
    apply piLieHom_ext
    intro i x
    have hi : Ψ.comp (piLieSingle (L := L) X i) = F.comp (piLieSingle (L := L) X i) := by
      apply (C i).hom_ext
      intro m
      change Ψ (Pi.single i (ι i m)) = F (Pi.single i (ι i m))
      rw [← piLinearMap_single ι]
      exact (hΨ (Pi.single i m)).trans (hF (Pi.single i m)).symm
    exact LieModuleHom.congr_fun hi x

end
end Schubert.RS.Representation
