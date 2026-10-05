import Schubert.FlagVarieties.Foundations.Flags.GrassmannianChart

/-!
# Coordinate quotient bases over local rings

A finite projective quotient of a coordinate module over a local ring has
a basis consisting of distinct images of coordinate vectors. The rank is
the quotient rank, so the selected coordinate set has precisely
the Grassmannian's prescribed size. This is local-ring coverage data;
spreading the chosen chart to a principal open is a further step.
-/

noncomputable section

namespace FlagVarieties.Foundations.QuotientCharts

variable {R Q : Type*} [CommRing R] [IsLocalRing R]
  [AddCommGroup Q] [Module R Q] [Module.Finite R Q] [Module.Projective R Q]
  {n d : ℕ}

/-- A surjective coordinate presentation of a finite projective module over
a local ring contains a basis of distinct coordinate images. -/
theorem exists_coordinate_basis_of_surjective
    (f : (Fin n → R) →ₗ[R] Q) (hf : Function.Surjective f)
    (hd : Module.finrank R Q = d) :
    ∃ (a : Fin d ↪ Fin n) (b : Module.Basis (Fin d) R Q),
      ∀ i, b i = f (Pi.single (a i) 1) := by
  classical
  let : Module.FinitePresentation R Q := Module.finitePresentation_of_projective R Q
  have hspan : Submodule.span R (Set.range (fun i => f (Pi.basisFun R (Fin n) i))) = ⊤ := by
    change Submodule.span R (Set.range (f ∘ (Pi.basisFun R (Fin n)))) = ⊤
    rw [Set.range_comp, ← Submodule.map_span, (Pi.basisFun R (Fin n)).span_eq,
      Submodule.map_top, LinearMap.range_eq_top.mpr hf]
  obtain ⟨κ, a, b, hb⟩ := Module.exists_basis_of_span_of_flat
    (fun i => f (Pi.basisFun R (Fin n) i)) hspan
  have : Finite κ := Module.Finite.finite_basis b
  let : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = d := (Module.finrank_eq_card_basis b).symm.trans hd
  let e : κ ≃ Fin d := Fintype.equivFinOfCardEq hcard
  have ha : Function.Injective a := by
    intro i j hij
    apply b.injective
    rw [hb, hb, hij]
  refine ⟨⟨a ∘ e.symm, ha.comp e.symm.injective⟩, b.reindex e, ?_⟩
  intro i
  simpa only [Module.Basis.reindex_apply, Function.comp_apply, Function.Embedding.coeFn_mk,
    Pi.basisFun_apply] using hb (e.symm i)

/-- The prescribed Grassmannian quotient rank is its local free-module rank. -/
theorem grassmannian_finrank_quotient_local
    (P : Module.Grassmannian R (Fin n → R) d) :
    Module.finrank R ((Fin n → R) ⧸ P.toSubmodule) = d := by
  let : Module.Free R ((Fin n → R) ⧸ P.toSubmodule) :=
    Module.free_of_flat_of_isLocalRing
  let p : PrimeSpectrum R := ⟨IsLocalRing.maximalIdeal R, inferInstance⟩
  have h := P.rankAtStalk_eq p
  simpa using h

/-- Every Grassmannian quotient over a local ring has a basis
selected from the original coordinate vectors. -/
theorem grassmannian_exists_coordinate_basis_local
    (P : Module.Grassmannian R (Fin n → R) d) :
    ∃ (a : Fin d ↪ Fin n)
      (b : Module.Basis (Fin d) R ((Fin n → R) ⧸ P.toSubmodule)),
      ∀ i, b i = P.toSubmodule.mkQ (Pi.single (a i) 1) :=
  exists_coordinate_basis_of_surjective P.toSubmodule.mkQ
    P.toSubmodule.mkQ_surjective (grassmannian_finrank_quotient_local P)

end FlagVarieties.Foundations.QuotientCharts
