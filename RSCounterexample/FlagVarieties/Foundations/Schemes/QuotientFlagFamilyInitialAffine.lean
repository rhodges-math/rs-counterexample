import RSCounterexample.FlagVarieties.Foundations.Schemes.AffineCoordinateSheafQuotient
import RSCounterexample.FlagVarieties.Foundations.Schemes.AffineSheafCoordinateRefinement
import RSCounterexample.FlagVarieties.Foundations.Flags.SplitModules
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Equal-rank affine free quotient epimorphisms

Over an affine scheme, an epimorphism of the same finite-rank coordinate
free sheaf is an isomorphism. The map on global sections is a
surjective endomorphism of a finite free module over a commutative ring;
affine quasicoherent descent reflects its inverse back to the sheaf.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory QuotientPair
universe u

/-- A surjection from the rank-`n` coordinate module onto a finite
projective module of the same stalk rank is injective as well. -/
theorem coordinate_surjective_equal_rank_bijective
    (A : Type u) [CommRing A] {Q : Type u} [AddCommGroup Q] [Module A Q]
    [Module.Finite A Q] [Module.Projective A Q] (n : ℕ)
    (f : (Fin n → A) →ₗ[A] Q) (hf : Function.Surjective f)
    (hrank : ∀ p : PrimeSpectrum A, Module.rankAtStalk (R := A) Q p = n) :
    Function.Bijective f := by
  obtain ⟨s, hs⟩ := f.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hf)
  let : Module.Finite A (LinearMap.ker f) := FlagVarieties.Foundations.finite_kernel_of_split f s hs
  let : Module.Projective A (LinearMap.ker f) :=
    FlagVarieties.Foundations.projective_kernel_of_split f s hs
  have hker : Module.rankAtStalk (R := A) (LinearMap.ker f) = 0 := by
    funext p
    have h := FlagVarieties.Foundations.splitKernel_rankAtStalk f s hs p
    rw [hrank p] at h
    have hsrc : Module.rankAtStalk (R := A) (Fin n → A) p = n := by
      let : Nontrivial A := p.nontrivial
      rw [Module.rankAtStalk_eq_finrank_of_free]
      simp
    rw [hsrc] at h
    change Module.rankAtStalk (R := A) (LinearMap.ker f) p = 0
    omega
  have hsub : Subsingleton (LinearMap.ker f) :=
    Module.rankAtStalk_eq_zero_iff_subsingleton.mp hker
  have hbot : LinearMap.ker f = ⊥ := by
    let : Subsingleton (LinearMap.ker f) := hsub
    exact Submodule.eq_bot_of_subsingleton
  exact ⟨LinearMap.ker_eq_bot.mp hbot, hf⟩

theorem coordinateFreeSheaf_epi_isIso
    (A : CommRingCat.{u}) (n : ℕ)
    (q : coordinateFreeSheaf (Spec A) n ⟶ coordinateFreeSheaf (Spec A) n)
    [Epi q] : IsIso q := by
  let M := coordinateFreeSheaf (Spec A) n
  let e : sheafGlobalModule M ≃ₗ[A] (Fin n → A) :=
    (coordinateFreeGlobalIso A n).toLinearEquiv.symm
  let : Module.Free A (sheafGlobalModule M) := Module.Free.of_equiv e.symm
  let : Module.Finite A (sheafGlobalModule M) := Module.Finite.equiv e.symm
  have hs : Function.Surjective (moduleSpecΓFunctor.map q).hom :=
    sheafGlobalMap_surjective q
  have hi : Function.Injective (moduleSpecΓFunctor.map q).hom :=
    Module.End.injective_of_surjective A (sheafGlobalModule M) hs
  haveI hm : IsIso (moduleSpecΓFunctor.map q) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr ⟨hi, hs⟩
  letI : IsIso M.fromTildeΓ :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := A) M
  have hn : (tilde.functor A).map (moduleSpecΓFunctor.map q) ≫ M.fromTildeΓ =
      M.fromTildeΓ ≫ q := Scheme.Modules.fromTildeΓNatTrans.naturality q
  haveI : IsIso (M.fromTildeΓ ≫ q) := by
    rw [← hn]
    infer_instance
  exact IsIso.of_isIso_comp_left M.fromTildeΓ q

/-- The same equal-rank argument for an arbitrary locally framed affine
target, with no global basis chosen for that target. -/
theorem coordinateFreeSheaf_epi_isIso_of_local_frames
    (A : CommRingCat.{u}) (n : ℕ) {M : (Spec A).Modules}
    (q : coordinateFreeSheaf (Spec A) n ⟶ M) [Epi q]
    (hfree : ∀ x : Spec A, ∃ U : (Spec A).Opens, x ∈ U ∧
      Nonempty (M.over U ≅
        SheafOfModules.free (R := (Spec A).ringCatSheaf.over U)
          (CoordinateIndex.{u} n))) : IsIso q := by
  let : M.IsQuasicoherent := locally_coordinate_trivial_isQuasicoherent M n hfree
  obtain ⟨hfinite, hprojective⟩ := locally_coordinate_trivial_finite_projective M n hfree
  let : Module.Finite A (sheafGlobalModule M) := hfinite
  let : Module.Projective A (sheafGlobalModule M) := hprojective
  have hsurj : Function.Surjective (affineCoordinateQuotientMap A q) :=
    affineCoordinateQuotientMap_surjective A q
  have hbij : Function.Bijective (affineCoordinateQuotientMap A q) :=
    coordinate_surjective_equal_rank_bijective A n _ hsurj
      (locally_coordinate_trivial_rank M n hfree)
  haveI : IsIso ((coordinateFreeGlobalIso A n).hom ≫ moduleSpecΓFunctor.map q) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  haveI : IsIso (moduleSpecΓFunctor.map q) :=
    IsIso.of_isIso_comp_left (coordinateFreeGlobalIso A n).hom _
  let E := coordinateFreeSheaf (Spec A) n
  letI : IsIso E.fromTildeΓ :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := A) E
  letI : IsIso M.fromTildeΓ :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := A) M
  have hn : (tilde.functor A).map (moduleSpecΓFunctor.map q) ≫ M.fromTildeΓ =
      E.fromTildeΓ ≫ q := Scheme.Modules.fromTildeΓNatTrans.naturality q
  haveI : IsIso (E.fromTildeΓ ≫ q) := by
    rw [← hn]
    infer_instance
  exact IsIso.of_isIso_comp_left E.fromTildeΓ q

end FlagVarieties.Foundations.QuotientCharts
