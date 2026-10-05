import Schubert.FlagVarieties.Foundations.Schemes.ConstantMatrixSheaf
import Schubert.FlagVarieties.Foundations.Schemes.SelectedUniversalPullbackCoherence

/-! Naturality of a constant matrix action under arbitrary scheme pullback. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientCharts

open AlgebraicGeometry CategoryTheory

universe u
variable (R : Type u) [CommRing R] {X Y : Scheme.{u}} {n : ℕ}
  (b : X ⟶ Spec (CommRingCat.of R)) (f : Y ⟶ X)
  (L : Matrix (Fin n) (Fin n) R) (hL : IsUnit L)

/-- The original labelled free-source comparison intertwines a constant
matrix action with arbitrary geometric pullback. -/
@[reassoc]
theorem constantMatrixSheafIso_pullback :
    (Scheme.Modules.pullback f).map (constantMatrixSheafIso R b L hL).hom ≫
      (coordinatePullbackIso f n).hom =
    (coordinatePullbackIso f n).hom ≫
      (constantMatrixSheafIso R (f ≫ b) L hL).hom := by
  have hcoh := coordinatePullbackFreeIso_comp f b n
  simp only [constantMatrixSheafIso, Iso.trans_hom, Iso.symm_hom,
    Functor.map_comp, Functor.mapIso_hom, Category.assoc]
  simp only [coordinatePullbackIso_eq] at *
  have hmid :
      (Scheme.Modules.pullback f).map (coordinatePullbackFreeIso b n).hom ≫
          (coordinatePullbackFreeIso f n).hom ≫
            (coordinatePullbackFreeIso (f ≫ b) n).inv =
        (Scheme.Modules.pullbackComp f b).hom.app
          (coordinateFreeSheaf (Spec (CommRingCat.of R)) n) := by
    apply (cancel_epi ((Scheme.Modules.pullbackComp f b).inv.app
      (coordinateFreeSheaf (Spec (CommRingCat.of R)) n))).mp
    rw [← Category.assoc
      ((Scheme.Modules.pullback f).map (coordinatePullbackFreeIso b n).hom)
      (coordinatePullbackFreeIso f n).hom
      (coordinatePullbackFreeIso (f ≫ b) n).inv]
    rw [← Category.assoc
      ((Scheme.Modules.pullbackComp f b).inv.app
        (coordinateFreeSheaf (Spec (CommRingCat.of R)) n))]
    rw [hcoh]
    simp
  have hhead :
      (coordinatePullbackFreeIso f n).hom ≫
          (coordinatePullbackFreeIso (f ≫ b) n).inv =
        (Scheme.Modules.pullback f).map (coordinatePullbackFreeIso b n).inv ≫
          (Scheme.Modules.pullbackComp f b).hom.app
            (coordinateFreeSheaf (Spec (CommRingCat.of R)) n) := by
    apply (cancel_epi ((Scheme.Modules.pullback f).map
      (coordinatePullbackFreeIso b n).hom)).mp
    simp only [Iso.hom_inv_id_map_assoc]
    rw [hmid]
  rw [← Category.assoc (coordinatePullbackFreeIso f n).hom
    (coordinatePullbackFreeIso (f ≫ b) n).inv]
  rw [hhead]
  simp only [Category.assoc]
  rw [← Category.assoc
    ((Scheme.Modules.pullbackComp f b).hom.app
      (coordinateFreeSheaf (Spec (CommRingCat.of R)) n))
    ((Scheme.Modules.pullback (f ≫ b)).map (constantMatrixSpecIso R L hL).hom)
    (coordinatePullbackFreeIso (f ≫ b) n).hom]
  rw [← (Scheme.Modules.pullbackComp f b).hom.naturality
    (constantMatrixSpecIso R L hL).hom]
  simp only [Functor.comp_map, Category.assoc]
  rw [← hcoh]
  simp

end FlagVarieties.Foundations.QuotientCharts
