import RSCounterexample.Demazure.Representation.EigenspaceExhaustion
import RSCounterexample.Demazure.Representation.TruncationPieces

/-!
# Degree pieces as cut-torus eigenspaces

`cutWeightSpace u ρ d` is the joint eigenspace of the cut tori for the root degree `d`. The degree
pieces of both presentation quotients are these eigenspaces (`josephPoloDegreePiece_eq_weightSpace`,
`linearDegreePiece_eq_weightSpace`), so the eigenspaces are finite dimensional and have equal
dimensions for degrees below the truncation bound (`truncationWeightSpace_finrank`).
-/

open Schubert

namespace Demazure.FlagModule
noncomputable section

/-- The genuine simultaneous eigenspace, defined using the actual action,
independently of PBW, a quotient basis, or any desired character. -/
def cutWeightSpace {n : ℕ} {E : Type*} [AddCommGroup E] [Module ℂ E]
    (u : Fin n → ℕ) (ρ : DiagonalTorus n →* Module.End ℂ E) (d : RootDegree n) :
    Submodule ℂ E where
  carrier := {x | ∀ k, ρ (cutTorus k) x =
    (weightScalar u (cutTorus k) * (2 : ℂ)^d k) • x}
  zero_mem' := by intro k; simp
  add_mem' := by intro x y hx hy k; simp only [map_add, hx k, hy k, smul_add]
  smul_mem' := by intro c x hx k; simp only [map_smul, hx k, smul_comm c]

theorem josephPoloDegreePiece_eq_weightSpace {n : ℕ} (u : Fin n → ℕ) (hpbw : HasOrderedPBWBasis n)
    (d : RootDegree n) :
    josephPoloDegreePiece u hpbw d = cutWeightSpace u (josephPoloTorusRep u) d := by
  ext x
  exact mem_josephPoloDegreePiece_iff_cut_eigen u hpbw d x

theorem linearDegreePiece_eq_weightSpace {n : ℕ} (u : Fin n → ℕ) (hpbw : HasOrderedPBWBasis n)
    (d : RootDegree n) :
    linearDegreePiece u hpbw d = cutWeightSpace u (linearTorusRepresentation u) d := by
  ext x
  exact mem_linearDegreePiece_iff_cut_eigen u hpbw d x

theorem josephPoloWeightSpace_finite {n : ℕ} (u : Fin n → ℕ) (hpbw : HasOrderedPBWBasis n)
    (d : RootDegree n) : FiniteDimensional ℂ (cutWeightSpace u (josephPoloTorusRep u) d) := by
  rw [← josephPoloDegreePiece_eq_weightSpace u hpbw d]
  infer_instance

theorem linearWeightSpace_finite {n : ℕ} (u : Fin n → ℕ) (hpbw : HasOrderedPBWBasis n)
    (d : RootDegree n) : FiniteDimensional ℂ
        (cutWeightSpace u (linearTorusRepresentation u) d) := by
  rw [← linearDegreePiece_eq_weightSpace u hpbw d]
  infer_instance

/-- Equality of finite dimensions of the genuine eigenspaces throughout the
coefficient box; eigenspace exhaustion is proved before taking finrank. -/
theorem truncationWeightSpace_finrank {n : ℕ} (u : Fin n → ℕ) (hpbw : HasOrderedPBWBasis n)
    (β d : RootDegree n) (hd : d ≤ β)
    (hβ : ∀ r : PositiveRoot n, u r.val.1 < u r.val.2 →
      ¬ josephPoloExponent u r • rootDegree r.val.1 r.val.2 ≤ β) :
    Module.finrank ℂ (cutWeightSpace u (linearTorusRepresentation u) d) =
      Module.finrank ℂ (cutWeightSpace u (josephPoloTorusRep u) d) := by
  rw [← linearDegreePiece_eq_weightSpace u hpbw d, ← josephPoloDegreePiece_eq_weightSpace u hpbw d]
  exact truncationDegree_finrank u hpbw β d hd hβ

end
end Demazure.FlagModule
