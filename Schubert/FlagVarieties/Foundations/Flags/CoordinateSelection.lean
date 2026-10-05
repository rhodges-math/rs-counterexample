import Schubert.FlagVarieties.Foundations.Flags.LocalCoordinateBasis

/-!
# Selected-coordinate maps into a quotient

The coordinate inclusion sends each standard basis vector to its selected
ambient standard basis vector. Over a local ring, some such inclusion
followed by a Grassmannian quotient map is an isomorphism. This is the
chart applicability assertion over local rings.
-/

namespace FlagVarieties.Foundations.QuotientCharts

variable {R Q : Type*} [CommRing R] [AddCommGroup Q] [Module R Q] {n d : ℕ}

/-- Include the coordinates specified by an injection of the finite index sets. -/
noncomputable def coordinateInclusion (a : Fin d ↪ Fin n) :
    (Fin d → R) →ₗ[R] (Fin n → R) :=
  (Pi.basisFun R (Fin d)).constr R (fun i => Pi.single (a i) 1)

@[simp] theorem coordinateInclusion_basis (a : Fin d ↪ Fin n) (i : Fin d) :
    coordinateInclusion (R := R) a (Pi.single i 1) = Pi.single (a i) 1 := by
  rw [← Pi.basisFun_apply R (Fin d) i]
  exact (Pi.basisFun R (Fin d)).constr_basis R _ i

/-- When the selected images form a basis, the selected quotient map is its inverse frame. -/
theorem selectedMap_eq_basis_inverse (f : (Fin n → R) →ₗ[R] Q)
    (a : Fin d ↪ Fin n) (b : Module.Basis (Fin d) R Q)
    (hb : ∀ i, b i = f (Pi.single (a i) 1)) :
    f.comp (coordinateInclusion a) = b.equivFun.symm.toLinearMap := by
  apply (Pi.basisFun R (Fin d)).ext
  intro i
  simp only [LinearMap.comp_apply, Pi.basisFun_apply, coordinateInclusion_basis,
    LinearEquiv.coe_coe, Module.Basis.equivFun_symm_apply]
  simpa using (hb i).symm

theorem selectedMap_bijective_of_basis (f : (Fin n → R) →ₗ[R] Q)
    (a : Fin d ↪ Fin n) (b : Module.Basis (Fin d) R Q)
    (hb : ∀ i, b i = f (Pi.single (a i) 1)) :
    Function.Bijective (f.comp (coordinateInclusion a)) := by
  rw [selectedMap_eq_basis_inverse f a b hb]
  exact b.equivFun.symm.bijective

/-- Some coordinate chart applies to every Grassmannian quotient over a local ring. -/
theorem grassmannian_exists_bijective_selectedMap_local [IsLocalRing R]
    (P : Module.Grassmannian R (Fin n → R) d) :
    ∃ a : Fin d ↪ Fin n,
      Function.Bijective (P.toSubmodule.mkQ.comp (coordinateInclusion a)) := by
  obtain ⟨a, b, hb⟩ := grassmannian_exists_coordinate_basis_local P
  exact ⟨a, selectedMap_bijective_of_basis P.toSubmodule.mkQ a b hb⟩

end FlagVarieties.Foundations.QuotientCharts
