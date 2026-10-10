import RSCounterexample.FlagVarieties.Foundations.Schemes.CoordinateQuotientCoverDescent
import RSCounterexample.FlagVarieties.Foundations.Schemes.AffineSheafLocalFiniteFree

/-!
# The module quotient determined by an affine sheaf quotient

The free source is identified by its original coordinates. Surjectivity of
the resulting affine module map is proved from the sheaf epimorphism and
quasicoherence, not supplied as a hypothesis. The associated-sheaf source
equation is the tilde adjunction triangle.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits QuotientPair
universe u
variable (A : CommRingCat.{u}) {n : ℕ} {M : (Spec A).Modules}

/-- The canonical free source in affine global sections. -/
def coordinateFreeGlobalIso (n : ℕ) :
    ModuleCat.of A (Fin n → A) ≅
      moduleSpecΓFunctor.obj (coordinateFreeSheaf (Spec A) n) :=
  asIso ((tilde.adjunction (R := A)).unit.app (ModuleCat.of A (Fin n → A))) ≪≫
    moduleSpecΓFunctor.mapIso (coordinateTildeFreeIso A n)

/-- The affine module map of the given original quotient sheaf map. -/
def affineCoordinateQuotientMap (q : coordinateFreeSheaf (Spec A) n ⟶ M) :
    (Fin n → A) →ₗ[A] sheafGlobalModule M :=
  ((coordinateFreeGlobalIso A n).hom ≫ moduleSpecΓFunctor.map q).hom

theorem affineCoordinateQuotientMap_surjective [M.IsQuasicoherent]
    (q : coordinateFreeSheaf (Spec A) n ⟶ M) [Epi q] :
    Function.Surjective (affineCoordinateQuotientMap A q) := by
  exact (sheafGlobalMap_surjective q).comp
    ((ModuleCat.epi_iff_surjective (coordinateFreeGlobalIso A n).hom).mp inferInstance)

/-- Associated sheafification recovers the original quotient source map. -/
@[reassoc]
theorem affineCoordinateQuotientMap_source
    (q : coordinateFreeSheaf (Spec A) n ⟶ M) :
    tilde.map (ModuleCat.ofHom (affineCoordinateQuotientMap A q)) ≫ M.fromTildeΓ =
      (coordinateTildeFreeIso A n).hom ≫ q := by
  change ((tilde.adjunction (R := A)).homEquiv _ M).symm
    ((coordinateFreeGlobalIso A n).hom ≫ moduleSpecΓFunctor.map q) = _
  rw [coordinateFreeGlobalIso, Iso.trans_hom, asIso_hom, Functor.mapIso_hom,
    Category.assoc, ← Functor.map_comp]
  exact ((tilde.adjunction (R := A)).homEquiv _ M).symm_apply_apply
    ((coordinateTildeFreeIso A n).hom ≫ q)

variable [M.IsQuasicoherent] (q : coordinateFreeSheaf (Spec A) n ⟶ M) [Epi q]

/-- The quotient by the affine kernel is the global-section module. -/
def affineCoordinateQuotientEquiv :
    ((Fin n → A) ⧸ LinearMap.ker (affineCoordinateQuotientMap A q)) ≃ₗ[A]
      sheafGlobalModule M :=
  (affineCoordinateQuotientMap A q).quotKerEquivOfSurjective
    (affineCoordinateQuotientMap_surjective A q)

/-- A finite-projective rank-d affine quotient yields its coordinate
Grassmannian point with the unchanged ambient kernel. -/
def affineCoordinateGrassmannian (d : ℕ)
    [Module.Finite A (sheafGlobalModule M)] [Module.Projective A (sheafGlobalModule M)]
    (hrank : ∀ p : PrimeSpectrum A, Module.rankAtStalk (sheafGlobalModule M) p = d) :
    Module.Grassmannian A (Fin n → A) d where
  toSubmodule := LinearMap.ker (affineCoordinateQuotientMap A q)
  finite_quotient := Module.Finite.equiv (affineCoordinateQuotientEquiv A q).symm
  projective_quotient := Module.Projective.of_equiv (affineCoordinateQuotientEquiv A q).symm
  rankAtStalk_eq p := by
    rw [Module.rankAtStalk_eq_of_equiv (affineCoordinateQuotientEquiv A q), hrank]

end FlagVarieties.Foundations.QuotientCharts
