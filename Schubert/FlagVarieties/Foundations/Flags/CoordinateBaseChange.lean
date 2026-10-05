import Schubert.FlagVarieties.Foundations.Flags.SelectedCoordinateChart
import Schubert.FlagVarieties.Foundations.Flags.MatrixChartBaseChange

/-!
# Scalar extension of coordinate Grassmannian quotients

The quotient map is tensored and its kernel taken, with finite coordinates
identified by the canonical tensor equivalence. The original selected map
commutes with this construction. No flatness is required.
-/

noncomputable section

namespace FlagVarieties.Foundations.QuotientCharts

open TensorProduct

variable {R : Type*} [CommRing R] (B : Type*) [CommRing B] [Algebra R B]
  {n d : ℕ}

/-- The scalar-extended quotient map, in the ambient finite coordinates. -/
def coordinateQuotientMap (P : Module.Grassmannian R (Fin n → R) d) :
    (Fin n → B) →ₗ[B] (B ⊗[R] ((Fin n → R) ⧸ P.toSubmodule)) :=
  (P.toSubmodule.mkQ.baseChange B).comp
    (TensorProduct.piScalarRight R B B (Fin n)).symm.toLinearMap

theorem coordinateQuotientMap_surjective (P : Module.Grassmannian R (Fin n → R) d) :
    Function.Surjective (coordinateQuotientMap B P) :=
  (LinearMap.baseChange_surjective B P.toSubmodule.mkQ_surjective).comp
    (TensorProduct.piScalarRight R B B (Fin n)).symm.surjective

/-- Canonical identification of the new quotient with the tensored quotient. -/
def coordinateQuotientEquiv (P : Module.Grassmannian R (Fin n → R) d) :=
  (coordinateQuotientMap B P).quotKerEquivOfSurjective
    (coordinateQuotientMap_surjective B P)

/-- The base-changed Grassmannian quotient in finite coordinates. -/
def coordinateGrassmannianBaseChange (P : Module.Grassmannian R (Fin n → R) d) :
    Module.Grassmannian B (Fin n → B) d where
  toSubmodule := LinearMap.ker (coordinateQuotientMap B P)
  finite_quotient := Module.Finite.equiv (coordinateQuotientEquiv B P).symm
  projective_quotient := Module.Projective.of_equiv (coordinateQuotientEquiv B P).symm
  rankAtStalk_eq p := by
    rw [congrFun (Module.rankAtStalk_eq_of_equiv (coordinateQuotientEquiv B P)) p]
    simpa only [Module.rankAtStalk_baseChange] using
      P.rankAtStalk_eq (PrimeSpectrum.comap (algebraMap R B) p)

/-- Selected coordinate inclusions commute with arbitrary scalar extension. -/
theorem coordinateInclusion_baseChange (a : Fin d ↪ Fin n) :
    (TensorProduct.piScalarRight R B B (Fin n)).symm.toLinearMap.comp
        (coordinateInclusion (R := B) a) =
      ((coordinateInclusion (R := R) a).baseChange B).comp
        (TensorProduct.piScalarRight R B B (Fin d)).symm.toLinearMap := by
  apply (Pi.basisFun B (Fin d)).ext
  intro i
  simp only [LinearMap.comp_apply, Pi.basisFun_apply, coordinateInclusion_basis,
    LinearEquiv.coe_coe, TensorProduct.piScalarRight_symm_single, LinearMap.baseChange_tmul]

/-- The quotient/selection square is an equality of linear maps. -/
theorem coordinateQuotientMap_selected (P : Module.Grassmannian R (Fin n → R) d)
    (a : Fin d ↪ Fin n) :
    (coordinateQuotientMap B P).comp (coordinateInclusion a) =
      ((P.toSubmodule.mkQ.comp (coordinateInclusion a)).baseChange B).comp
        (TensorProduct.piScalarRight R B B (Fin d)).symm.toLinearMap := by
  unfold coordinateQuotientMap
  rw [LinearMap.comp_assoc, coordinateInclusion_baseChange, ← LinearMap.comp_assoc,
    ← LinearMap.baseChange_comp]

/-- The new quotient's selected map is bijective precisely when the
scalar extension of the original selected map is bijective. -/
theorem coordinateGrassmannianBaseChange_selected_iff
    (P : Module.Grassmannian R (Fin n → R) d) (a : Fin d ↪ Fin n) :
    Function.Bijective ((coordinateGrassmannianBaseChange B P).toSubmodule.mkQ.comp
      (coordinateInclusion a)) ↔
    Function.Bijective ((P.toSubmodule.mkQ.comp (coordinateInclusion a)).baseChange B) := by
  let e := coordinateQuotientEquiv B P
  have he : e.toLinearMap.comp
      ((coordinateGrassmannianBaseChange B P).toSubmodule.mkQ.comp (coordinateInclusion a)) =
      (coordinateQuotientMap B P).comp (coordinateInclusion a) := by
    apply LinearMap.ext
    intro v
    change (coordinateQuotientMap B P).quotKerEquivOfSurjective
        (coordinateQuotientMap_surjective B P)
      (Submodule.Quotient.mk (coordinateInclusion a v)) = _
    exact LinearMap.quotKerEquivOfSurjective_apply_mk _ _ _
  have hleft := e.bijective.of_comp_iff'
    ((coordinateGrassmannianBaseChange B P).toSubmodule.mkQ.comp (coordinateInclusion a))
  change Function.Bijective (e.toLinearMap.comp
    ((coordinateGrassmannianBaseChange B P).toSubmodule.mkQ.comp (coordinateInclusion a))) ↔ _
      at hleft
  rw [he, coordinateQuotientMap_selected] at hleft
  exact hleft.symm.trans
    ((TensorProduct.piScalarRight R B B (Fin d)).symm.bijective.of_comp_iff _)

end FlagVarieties.Foundations.QuotientCharts
