import RSCounterexample.FlagVarieties.Foundations.Schemes.AffineCoordinateQuotientBaseChangeAlgebra
import RSCounterexample.FlagVarieties.Foundations.Schemes.SelectedUniversalAffinePresented

/-!
# The associated sheaf of a base-changed coordinate quotient

The target uses the original Grassmannian quotient's kernel after scalar
extension, with no choice of a global basis or flatness hypothesis.
-/

noncomputable section

namespace FlagVarieties.Foundations.QuotientCharts

open AlgebraicGeometry CategoryTheory TensorProduct

universe u

variable (R B : Type u) [CommRing R] [CommRing B] [algebraRB : Algebra R B]
  {n d : ℕ} (P : Module.Grassmannian R (Fin n → R) d)

/-- The module-category scalar extension uses the given algebra instance after
transport along the equality of algebra structures. -/
theorem coordinateExtendScalarsObjEq (M : ModuleCat.{u} R) :
    (ModuleCat.extendScalars (algebraMap R B)).obj M =
      ModuleCat.of B (B ⊗[R] M) := by
  have h : (algebraMap R B).toAlgebra = algebraRB :=
    toAlgebra_algebraMap
  rw [← h]
  rfl

/-- The object equality also transports each original module morphism to
its ordinary tensor scalar extension. -/
theorem coordinateExtendScalarsMapEq {M N : ModuleCat.{u} R} (q : M ⟶ N) :
    (ModuleCat.extendScalars (algebraMap R B)).map q ≫
      (eqToIso (coordinateExtendScalarsObjEq R B N)).hom =
    (eqToIso (coordinateExtendScalarsObjEq R B M)).hom ≫
      ModuleCat.ofHom (q.hom.baseChange B) := by
  have h : (algebraMap R B).toAlgebra = algebraRB :=
    toAlgebra_algebraMap
  rw [← h]
  apply ModuleCat.hom_ext
  rfl

/-- The original labelled ambient module after scalar extension. -/
def coordinateExtendedFreeIso :
    (ModuleCat.extendScalars (algebraMap R B)).obj (ModuleCat.of R (Fin n → R)) ≅
      ModuleCat.of B (Fin n → B) :=
  eqToIso (coordinateExtendScalarsObjEq R B (ModuleCat.of R (Fin n → R))) ≪≫
    (coordinateTensorFreeEquiv R B (n := n)).toModuleIso

/-- The original quotient target after scalar extension. -/
def coordinateExtendedQuotientIso :
    (ModuleCat.extendScalars (algebraMap R B)).obj
        (ModuleCat.of R ((Fin n → R) ⧸ P.toSubmodule)) ≅
      ModuleCat.of B ((Fin n → B) ⧸
        (coordinateGrassmannianBaseChange B P).toSubmodule) :=
  eqToIso (coordinateExtendScalarsObjEq R B
      (ModuleCat.of R ((Fin n → R) ⧸ P.toSubmodule))) ≪≫
    (coordinateTensorQuotientEquiv R B P).toModuleIso

/-- Both extended-module identifications carry the original
ambient quotient map to the new coordinate quotient map. -/
theorem coordinateExtendedQuotientIso_source :
    (ModuleCat.extendScalars (algebraMap R B)).map
        (ModuleCat.ofHom P.toSubmodule.mkQ) ≫
      (coordinateExtendedQuotientIso R B P).hom =
    (coordinateExtendedFreeIso R B (n := n)).hom ≫
      ModuleCat.ofHom (coordinateGrassmannianBaseChange B P).toSubmodule.mkQ := by
  unfold coordinateExtendedQuotientIso coordinateExtendedFreeIso
  simp only [Iso.trans_hom, Category.assoc]
  rw [← Category.assoc, coordinateExtendScalarsMapEq]
  simp only [Category.assoc]
  congr 1
  apply ModuleCat.hom_ext
  exact coordinateTensorQuotientEquiv_source R B P

/-- Pulling back the original quotient sheaf gives the
associated sheaf of its coordinate Grassmannian base change. -/
def coordinateQuotientSheafPullbackIso :
    (Scheme.Modules.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap R B)))).obj
        (coordinateQuotientSheaf (CommRingCat.of R) P) ≅
      coordinateQuotientSheaf (CommRingCat.of B)
        (coordinateGrassmannianBaseChange B P) :=
  AffineTildePullback.baseChangeIso (CommRingCat.ofHom (algebraMap R B))
      (ModuleCat.of R ((Fin n → R) ⧸ P.toSubmodule)) ≪≫
    (tilde.functor (CommRingCat.of B)).mapIso
      (coordinateExtendedQuotientIso R B P)

end FlagVarieties.Foundations.QuotientCharts
