import Schubert.FlagVarieties.Foundations.Schemes.AffineCoordinateSheafQuotient

/-!
# Source-preserving presentation of an affine quotient sheaf

The kernel is taken in the original finite-coordinate module, and the
associated quotient is identified with the given sheaf by its
global sections and the tilde counit. The sheaf epimorphism is
retained throughout.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory QuotientPair
universe u
variable (A : CommRingCat.{u}) {n : ℕ} {M : (Spec A).Modules} [M.IsQuasicoherent]
  (q : coordinateFreeSheaf (Spec A) n ⟶ M) [Epi q]

theorem affineCoordinateQuotientEquiv_source :
    (affineCoordinateQuotientEquiv A q).toLinearMap.comp
      (LinearMap.ker (affineCoordinateQuotientMap A q)).mkQ =
    affineCoordinateQuotientMap A q := by
  apply LinearMap.ext
  intro x
  exact LinearMap.quotKerEquivOfSurjective_apply_mk (affineCoordinateQuotientMap A q)
    (affineCoordinateQuotientMap_surjective A q) x

/-- The sheaf is the associated sheaf of its original coordinate-kernel quotient. -/
def affineCoordinateQuotientSheafIso :
    tilde (ModuleCat.of A
      ((Fin n → A) ⧸ LinearMap.ker (affineCoordinateQuotientMap A q))) ≅ M := by
  letI : IsIso M.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := A) M
  exact (tilde.functor A).mapIso (affineCoordinateQuotientEquiv A q).toModuleIso ≪≫
    asIso M.fromTildeΓ

@[reassoc]
theorem affineCoordinateQuotientSheafIso_source :
    (coordinateTildeFreeIso A n).inv ≫
      tilde.map (ModuleCat.ofHom (LinearMap.ker (affineCoordinateQuotientMap A q)).mkQ) ≫
      (affineCoordinateQuotientSheafIso A q).hom = q := by
  simp only [affineCoordinateQuotientSheafIso, Iso.trans_hom, Functor.mapIso_hom,
    asIso_hom]
  change (coordinateTildeFreeIso A n).inv ≫
    tilde.map (ModuleCat.ofHom (LinearMap.ker (affineCoordinateQuotientMap A q)).mkQ) ≫
    tilde.map (ModuleCat.ofHom (affineCoordinateQuotientEquiv A q).toLinearMap) ≫
    M.fromTildeΓ = q
  rw [← Category.assoc (tilde.map _) (tilde.map _), ← tilde.map_comp,
    ← ModuleCat.ofHom_comp, affineCoordinateQuotientEquiv_source,
    affineCoordinateQuotientMap_source, Iso.inv_hom_id_assoc]

variable (d : ℕ) [Module.Finite A (sheafGlobalModule M)]
  [Module.Projective A (sheafGlobalModule M)]
  (hrank : ∀ p : PrimeSpectrum A, Module.rankAtStalk (sheafGlobalModule M) p = d)

/-- A finite-projective affine quotient sheaf has its Grassmannian
presentation, with precisely the original labelled source map. -/
def affineCoordinateGrassmannianSheafIso :
    coordinateQuotientSheaf A (affineCoordinateGrassmannian A q d hrank) ≅ M :=
  affineCoordinateQuotientSheafIso A q

@[reassoc]
theorem affineCoordinateGrassmannianSheafIso_source :
    coordinateQuotientSheafMap A (affineCoordinateGrassmannian A q d hrank) ≫
      (affineCoordinateGrassmannianSheafIso A q d hrank).hom = q :=
  affineCoordinateQuotientSheafIso_source A q

end FlagVarieties.Foundations.QuotientCharts
