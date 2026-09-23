import Schubert.RS.Representation.RankOneCompletion
import Mathlib.LinearAlgebra.Pi

namespace Schubert.RS.Representation
noncomputable section
universe u v
open LieModule Module
open scoped BigOperators

variable {L : Type v} [LieRing L] [LieAlgebra ℂ L]
  {I : Type u} (X : I → Type u) [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)]
  [∀ i, LieRingModule L (X i)] [∀ i, LieModule ℂ L (X i)]

instance completionPiLieRingModule : LieRingModule L (∀ i, X i) where
  bracket a x i := ⁅a,x i⁆
  add_lie a b x := by funext i; exact add_lie a b (x i)
  lie_add a x y := by funext i; exact lie_add a (x i) (y i)
  leibniz_lie a b x := by funext i; exact leibniz_lie a b (x i)

instance completionPiLieModule : LieModule ℂ L (∀ i, X i) where
  smul_lie c a x := by funext i; exact smul_lie c a (x i)
  lie_smul c a x := by funext i; exact lie_smul c a (x i)

omit [∀ i, LieModule ℂ L (X i)] in
@[simp] theorem completionPiLie_apply (a : L) (x : ∀ i, X i) (i : I) :
    ⁅a,x⁆ i = ⁅a,x i⁆ := rfl

def piLieSingle [DecidableEq I] (i : I) : X i →ₗ⁅ℂ,L⁆ (∀ j, X j) where
  toLinearMap := LinearMap.single ℂ X i
  map_lie' := by
    intro a x
    apply funext
    intro j
    change Pi.single i ⁅a,x⁆ j = ⁅a,Pi.single i x j⁆
    by_cases hji : j=i
    · subst j; simp
    · simp only [Pi.single_eq_of_ne hji,lie_zero]

omit [∀ i, LieModule ℂ L (X i)] in
@[simp] theorem piLieSingle_apply [DecidableEq I] (i : I) (x : X i) :
    piLieSingle (L := L) X i x = Pi.single i x := rfl

def piLieProj (i : I) : (∀ j, X j) →ₗ⁅ℂ,L⁆ X i where
  toLinearMap := LinearMap.proj i
  map_lie' := rfl

variable {X} {N : Type u} [AddCommGroup N] [Module ℂ N]
  [LieRingModule L N] [LieModule ℂ L N]

def piLieSum [Fintype I] [DecidableEq I] (F : ∀ i, X i →ₗ⁅ℂ,L⁆ N) :
    (∀ i, X i) →ₗ⁅ℂ,L⁆ N where
  toLinearMap := LinearMap.lsum ℂ X ℂ (fun i => (F i).toLinearMap)
  map_lie' := by
    intro a x
    change (LinearMap.lsum ℂ X ℂ (fun i => (F i).toLinearMap)) ⁅a,x⁆ =
      ⁅a,(LinearMap.lsum ℂ X ℂ (fun i => (F i).toLinearMap)) x⁆
    simp only [LinearMap.lsum_apply,LinearMap.sum_apply,LinearMap.comp_apply,
      LinearMap.proj_apply,completionPiLie_apply,LieModuleHom.coe_toLinearMap,
      LieModuleHom.map_lie,lie_sum]

theorem piLieSum_apply [Fintype I] [DecidableEq I] (F : ∀ i, X i →ₗ⁅ℂ,L⁆ N)
    (x : ∀ i, X i) : piLieSum F x = ∑ i, F i (x i) := by
  change (LinearMap.lsum ℂ X ℂ (fun i => (F i).toLinearMap)) x = _
  simp only [LinearMap.lsum_apply,LinearMap.sum_apply,LinearMap.comp_apply,
    LinearMap.proj_apply,LieModuleHom.coe_toLinearMap]

theorem piLieSum_single [Fintype I] [DecidableEq I] (F : ∀ i, X i →ₗ⁅ℂ,L⁆ N)
    (i : I) (x : X i) : piLieSum F (Pi.single i x) = F i x :=
  LinearMap.lsum_piSingle ℂ X ℂ (fun i => (F i).toLinearMap) i x

theorem piLieHom_ext [Fintype I] [DecidableEq I]
    {F G : (∀ i, X i) →ₗ⁅ℂ,L⁆ N}
    (h : ∀ i x, F (Pi.single i x) = G (Pi.single i x)) : F = G := by
  have hh : F.toLinearMap = G.toLinearMap := LinearMap.pi_ext h
  exact LieModuleHom.ext (LinearMap.congr_fun hh)

omit [∀ i, LieRingModule L (X i)] [∀ i, LieModule ℂ L (X i)] in
theorem piLinearMap_single {Y : I → Type u} [∀ i, AddCommGroup (Y i)] [∀ i, Module ℂ (Y i)]
    [DecidableEq I] (F : ∀ i, X i →ₗ[ℂ] Y i) (i : I) (x : X i) :
    LinearMap.piMap F (Pi.single i x) = Pi.single i (F i x) := by
  apply funext
  intro j
  change F j (Pi.single i x j) = Pi.single i (F i x) j
  by_cases hji : j=i
  · subst j; simp
  · simp only [Pi.single_eq_of_ne hji,map_zero]

end
end Schubert.RS.Representation
