import Schubert.FlagVarieties.Foundations.Flags.CoordinateSelection

/-!
# Coordinate chart neighborhoods at every prime

For every Grassmannian quotient and every prime of its base ring,
some set of coordinate images is a basis after localization at that prime.
Finite presentation spreads the same selected quotient map to a principal
neighborhood. This proves existence of local coordinate presentations over
arbitrary commutative rings, without assuming a global quotient frame.
-/

noncomputable section

namespace FlagVarieties.Foundations.QuotientCharts

variable {R : Type*} [CommRing R] {n d : ℕ}

/-- Coordinate images contain a basis at each prime of the original base. -/
theorem grassmannian_exists_coordinate_basis_atPrime
    (P : Module.Grassmannian R (Fin n → R) d) (p : PrimeSpectrum R) :
    ∃ (a : Fin d ↪ Fin n)
      (b : Module.Basis (Fin d) (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl ((Fin n → R) ⧸ P.toSubmodule))),
      ∀ i, b i = LocalizedModule.mk
        (P.toSubmodule.mkQ (Pi.single (a i) 1)) 1 := by
  classical
  let Q := (Fin n → R) ⧸ P.toSubmodule
  let Rp := Localization.AtPrime p.asIdeal
  let Qp := LocalizedModule p.asIdeal.primeCompl Q
  let v : Fin n → Qp := fun i => LocalizedModule.mk (P.toSubmodule.mkQ (Pi.single i 1)) 1
  have hspanR : Submodule.span R
      (Set.range (fun i => P.toSubmodule.mkQ (Pi.basisFun R (Fin n) i))) = ⊤ := by
    change Submodule.span R (Set.range (P.toSubmodule.mkQ ∘ Pi.basisFun R (Fin n))) = ⊤
    rw [Set.range_comp, ← Submodule.map_span,
      (Pi.basisFun R (Fin n)).span_eq, Submodule.map_top,
      LinearMap.range_eq_top.mpr P.toSubmodule.mkQ_surjective]
  have hspan : Submodule.span Rp (Set.range v) = ⊤ := by
    have h := span_eq_top_of_isLocalizedModule Rp p.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl Q) hspanR
    simpa only [← Set.range_comp, Function.comp_def, Pi.basisFun_apply,
      LocalizedModule.mkLinearMap_apply] using h
  let f : (Fin n → Rp) →ₗ[Rp] Qp := (Pi.basisFun Rp (Fin n)).constr Rp v
  have hf : Function.Surjective f := by
    rw [← LinearMap.range_eq_top, Module.Basis.constr_range]
    exact hspan
  have hrank : Module.finrank Rp Qp = d := P.rankAtStalk_eq p
  obtain ⟨a, b, hb⟩ := exists_coordinate_basis_of_surjective f hf hrank
  refine ⟨a, b, ?_⟩
  intro i
  simpa only [f, ← Pi.basisFun_apply Rp (Fin n), Module.Basis.constr_basis] using hb i

/-- A selected coordinate quotient map is bijective after localization at each prime. -/
theorem grassmannian_exists_bijective_selectedMap_atPrime
    (P : Module.Grassmannian R (Fin n → R) d) (p : PrimeSpectrum R) :
    ∃ a : Fin d ↪ Fin n,
      Function.Bijective (LocalizedModule.map p.asIdeal.primeCompl
        (P.toSubmodule.mkQ.comp (coordinateInclusion a))) := by
  obtain ⟨a, b, hb⟩ := grassmannian_exists_coordinate_basis_atPrime P p
  let b0 := (Pi.basisFun R (Fin d)).ofIsLocalizedModule (Localization.AtPrime p.asIdeal)
    p.asIdeal.primeCompl (LocalizedModule.mkLinearMap p.asIdeal.primeCompl (Fin d → R))
  have he : LocalizedModule.map p.asIdeal.primeCompl
      (P.toSubmodule.mkQ.comp (coordinateInclusion a)) =
      (b0.equiv b (Equiv.refl (Fin d))).toLinearMap := by
    apply b0.ext
    intro i
    simp only [LinearEquiv.coe_coe, Module.Basis.equiv_apply, Equiv.refl_apply]
    rw [show b0 i = LocalizedModule.mk (Pi.single i 1) 1 by
      simp [b0, Module.Basis.ofIsLocalizedModule_apply]]
    simp only [LocalizedModule.map_mk, LinearMap.comp_apply, coordinateInclusion_basis]
    exact (hb i).symm
  exact ⟨a, he ▸ (b0.equiv b (Equiv.refl (Fin d))).bijective⟩

/-- The same coordinate selection works on a principal neighborhood of the prime. -/
theorem grassmannian_exists_bijective_selectedMap_neighborhood
    (P : Module.Grassmannian R (Fin n → R) d) (p : PrimeSpectrum R) :
    ∃ (a : Fin d ↪ Fin n) (g : R), g ∉ p.asIdeal ∧
      Function.Bijective (LocalizedModule.map (Submonoid.powers g)
        (P.toSubmodule.mkQ.comp (coordinateInclusion a))) := by
  let : Module.FinitePresentation R ((Fin n → R) ⧸ P.toSubmodule) :=
    Module.finitePresentation_of_projective R _
  obtain ⟨a, ha⟩ := grassmannian_exists_bijective_selectedMap_atPrime P p
  obtain ⟨g, hg, hbij⟩ := Module.FinitePresentation.exists_notMem_bijective
    (P.toSubmodule.mkQ.comp (coordinateInclusion a)) p.asIdeal
    (LocalizedModule.mkLinearMap p.asIdeal.primeCompl (Fin d → R))
    (LocalizedModule.mkLinearMap p.asIdeal.primeCompl ((Fin n → R) ⧸ P.toSubmodule)) ha
  exact ⟨a, g, hg, hbij⟩

end FlagVarieties.Foundations.QuotientCharts
