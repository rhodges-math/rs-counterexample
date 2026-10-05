import Schubert.FlagVarieties.Foundations.Schemes.SelectedFlagMorphismFaithfulness

/-!
# Quotient projections jointly detect morphisms from every scheme

No affineness or separation assumption is imposed on the source. The common
base map follows from any one quotient projection. An affine open
cover then reduces equality to the proved affine statement.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory
universe u
variable (R : Type u) [CommRing R] {n : ℕ} {X : Scheme.{u}}

theorem selectedFlagMorphism_eq_of_projections_eq
    (F G : X ⟶ selectedFlagChartScheme R n)
    (h : ∀ j, F ≫ selectedFlagChartSchemeStep R n j = G ≫ selectedFlagChartSchemeStep R n j) :
    F = G := by
  have hbase : F ≫ selectedFlagChartSchemeToSpec R n =
      G ≫ selectedFlagChartSchemeToSpec R n := by
    have he := congrArg (fun f => f ≫ selectedChartSchemeToSpec R n (n-(0 : Fin (n+1)).val)) (h 0)
    simpa only [Category.assoc, selectedFlagChartSchemeStep_toSpec] using he
  let C := X.affineOpenCover
  apply C.openCover.hom_ext F G
  intro i
  let j := C.f i
  let A := C.X i
  let b : Spec A ⟶ Spec (CommRingCat.of R) :=
    (j ≫ F) ≫ selectedFlagChartSchemeToSpec R n
  let : Algebra R A := (Spec.fullyFaithful.preimage b).unop.hom.toAlgebra
  have hb : Spec.map (CommRingCat.ofHom (algebraMap R A)) = b := by
    change Spec.map (Spec.fullyFaithful.preimage b).unop = b
    exact Spec.map_preimage_unop b
  have hF : (j ≫ F) ≫ selectedFlagChartSchemeToSpec R n =
      Spec.map (CommRingCat.ofHom (algebraMap R A)) := hb.symm
  have hG : (j ≫ G) ≫ selectedFlagChartSchemeToSpec R n =
      Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
    calc
      (j ≫ G) ≫ selectedFlagChartSchemeToSpec R n =
          j ≫ (G ≫ selectedFlagChartSchemeToSpec R n) := Category.assoc _ _ _
      _ = j ≫ (F ≫ selectedFlagChartSchemeToSpec R n) :=
        congrArg (fun f => j ≫ f) hbase.symm
      _ = Spec.map (CommRingCat.ofHom (algebraMap R A)) :=
        (Category.assoc _ _ _).symm.trans hF
  apply selectedFlagAffineMorphism_eq_of_projections_eq (R := R) (A := A) (j ≫ F) (j ≫ G) hF hG
  intro l
  simpa only [Category.assoc] using congrArg (fun f => j ≫ f) (h l)

end FlagVarieties.Foundations.QuotientCharts
