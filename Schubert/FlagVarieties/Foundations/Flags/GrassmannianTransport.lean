import Schubert.FlagVarieties.Foundations.Flags.Ring

/-!
# Coordinate transport of the quotient Grassmannian

The submodule is mapped by the given linear equivalence. Its quotient
is unchanged up to the induced quotient equivalence, preserving finite
projectivity and stalk rank. This supplies coordinate changes for charts.
-/

namespace FlagVarieties.Foundations

variable {R M N V : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup V] [Module R V] {d : ℕ}

/-- Change ambient coordinates of a Grassmannian point. -/
noncomputable def grassmannianTransport (P : Module.Grassmannian R M d)
    (e : M ≃ₗ[R] N) : Module.Grassmannian R N d where
  toSubmodule := P.toSubmodule.map e.toLinearMap
  finite_quotient := Module.Finite.equiv (Submodule.Quotient.equiv _ _ e rfl)
  projective_quotient := Module.Projective.of_equiv (Submodule.Quotient.equiv _ _ e rfl)
  rankAtStalk_eq p := by
    have h := congrFun (Module.rankAtStalk_eq_of_equiv
      (Submodule.Quotient.equiv P.toSubmodule _ e rfl)) p
    exact h.symm.trans (P.rankAtStalk_eq p)

@[simp] theorem grassmannianTransport_submodule (P : Module.Grassmannian R M d)
    (e : M ≃ₗ[R] N) :
    (grassmannianTransport P e).toSubmodule = P.toSubmodule.map e.toLinearMap := rfl

@[simp] theorem grassmannianTransport_refl (P : Module.Grassmannian R M d) :
    grassmannianTransport P (LinearEquiv.refl R M) = P := by
  apply Module.Grassmannian.ext
  simp

theorem grassmannianTransport_trans (P : Module.Grassmannian R M d)
    (e : M ≃ₗ[R] N) (f : N ≃ₗ[R] V) :
    grassmannianTransport (grassmannianTransport P e) f =
      grassmannianTransport P (e.trans f) := by
  apply Module.Grassmannian.ext
  exact (Submodule.map_comp e.toLinearMap f.toLinearMap P.toSubmodule).symm

@[simp] theorem grassmannianTransport_symm (P : Module.Grassmannian R M d)
    (e : M ≃ₗ[R] N) :
    grassmannianTransport (grassmannianTransport P e) e.symm = P := by
  rw [grassmannianTransport_trans, e.self_trans_symm, grassmannianTransport_refl]

/-- Coordinate transport is an equivalence of Grassmannian points. -/
noncomputable def grassmannianTransportEquiv (e : M ≃ₗ[R] N) :
    Module.Grassmannian R M d ≃ Module.Grassmannian R N d where
  toFun P := grassmannianTransport P e
  invFun P := grassmannianTransport P e.symm
  left_inv P := grassmannianTransport_symm P e
  right_inv P := grassmannianTransport_symm P e.symm

end FlagVarieties.Foundations
