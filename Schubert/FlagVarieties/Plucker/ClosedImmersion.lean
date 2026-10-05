import Schubert.FlagVarieties.Plucker.Embedding

/-!
# The Plücker embedding is a closed immersion

* `pluckerSegre_preimage_chart`: the preimage under the Segre–Plücker morphism of the standard
  chart `D₊(X_{T_v})`, `T_v = (v{0..k})_k`, is the big cell of `v`.
* **`isClosedImmersion_pluckerSegre`**: over every commutative ring `R`, the Segre–Plücker
  morphism `Fl_n ⟶ ℙ(⊗_k ∧^{k+1} R^n)` is a closed immersion. Closed immersions are local on the
  target; the target is covered by the charts `D₊(X_{T_v})`, over which the morphism is `Spec` of a
  surjection (`exists_chart_surjective`), and by the complement of the (closed) image.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace FlagVarieties.Plucker

open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open Foundations Foundations.QuotientCharts Demazure.FlagModule

universe u

variable (R : Type u) [CommRing R] {n : ℕ}

/-- A big cell lies in the preimage of its chart. -/
theorem bigCell_le_preimage_chart (v : Equiv.Perm (Fin n)) :
    bigCell R v ≤ pluckerSegre R n ⁻¹ᵁ chart R (SegreIndex n) (prefixTuple v) := by
  rintro x ⟨y, rfl⟩
  obtain ⟨ψ, hfac, -⟩ := exists_chart_surjective R v
  change (specChart R n v ≫ pluckerSegre R n) y ∈ chart R (SegreIndex n) (prefixTuple v)
  rw [hfac, chart, ← Proj.opensRange_awayι _ _ (X_mem_grading_one (prefixTuple v)) Nat.one_pos]
  exact ⟨_, rfl⟩

/-- The preimage of a chart lies in the big cell: a point of the big cell of `w` where the
coordinate `p_{T_v}` does not vanish lies in the big cell of `v` (big cell criterion). -/
theorem preimage_chart_le_bigCell (v : Equiv.Perm (Fin n)) :
    pluckerSegre R n ⁻¹ᵁ chart R (SegreIndex n) (prefixTuple v) ≤ bigCell R v := by
  intro x hx
  obtain ⟨w, y, rfl⟩ := exists_mem_bigCell R x
  have hy : y ∈ specChart R n w ⁻¹ᵁ (pluckerSegre R n ⁻¹ᵁ
      chart R (SegreIndex n) (prefixTuple v)) := hx
  rw [← Scheme.Hom.comp_preimage, specChart_pluckerSegre, chartMorphism,
    fromSections_preimage_chart, chartSections, basicOpen_eq_of_affine] at hy
  -- localize at the coordinate
  set σ := segreSec (chartMatrix R n w) (prefixTuple v)
  obtain ⟨y', hy'⟩ :=
    (PrimeSpectrum.localization_away_comap_range (Localization.Away σ) σ).ge hy
  let a : bigCellRing R w →ₐ[R] Localization.Away σ :=
    { algebraMap (bigCellRing R w) (Localization.Away σ) with
      commutes' := fun r =>
        (IsScalarTower.algebraMap_apply R (bigCellRing R w) (Localization.Away σ) r).symm }
  have hσ : IsUnit (a.toRingHom σ) := IsLocalization.Away.algebraMap_isUnit σ
  have hP : InBigCell v (matrixFlag ((bigCellUniversalMatrix R w).map a)
      (isUnit_det_map a.toRingHom (isUnit_det_bigCellMatrix _))) := by
    rw [inBigCell_matrixFlag_iff_minor]
    rw [← segreSec_map] at hσ
    exact IsUnit.prod_univ_iff.mp hσ
  obtain ⟨g, hg⟩ := exists_factor_of_inBigCell (R := R) v _ hP
  have he : Spec.map (CommRingCat.ofHom a.toRingHom) ≫ bigCellChart R w = g ≫ bigCellChart R v :=
    (spec_map_comp_bigCellChart w a).trans hg.symm
  have hy'' : Spec.map (CommRingCat.ofHom a.toRingHom) y' = y := hy'
  rw [← hy'']
  change (Spec.map (CommRingCat.ofHom a.toRingHom) ≫ bigCellChart R w) y' ∈ _
  rw [he]
  exact ⟨_, rfl⟩

/-- **The preimage of the chart `D₊(X_{T_v})` is the big cell of `v`.** -/
theorem pluckerSegre_preimage_chart (v : Equiv.Perm (Fin n)) :
    pluckerSegre R n ⁻¹ᵁ chart R (SegreIndex n) (prefixTuple v) = bigCell R v :=
  le_antisymm (preimage_chart_le_bigCell R v) (bigCell_le_preimage_chart R v)

/-- The restriction of the Segre–Plücker morphism over the chart `D₊(X_{T_v})` is a closed
immersion. -/
theorem isClosedImmersion_restrict_chart (v : Equiv.Perm (Fin n)) :
    IsClosedImmersion (pluckerSegre R n ∣_ chart R (SegreIndex n) (prefixTuple v)) := by
  obtain ⟨ψ, hfac, hsurj⟩ := exists_chart_surjective R v
  have := IsClosedImmersion.spec_of_surjective ψ hsurj
  have hpre : (specChart R n v).opensRange =
      pluckerSegre R n ⁻¹ᵁ chart R (SegreIndex n) (prefixTuple v) :=
    (pluckerSegre_preimage_chart R v).symm
  let e := (specChart R n v).isoOpensRange ≪≫ (FlagScheme R n).isoOfEq hpre
  have he : e.hom ≫ (pluckerSegre R n ⁻¹ᵁ chart R (SegreIndex n) (prefixTuple v)).ι =
      specChart R n v := by
    simp only [e, Iso.trans_hom, Category.assoc, Scheme.isoOfEq_hom_ι,
      Scheme.Hom.isoOpensRange_hom_ι]
  have key : pluckerSegre R n ∣_ chart R (SegreIndex n) (prefixTuple v) =
      e.inv ≫ Spec.map ψ ≫ (Proj.basicOpenIsoSpec (grading R (SegreIndex n))
        (MvPolynomial.X (prefixTuple v)) (X_mem_grading_one _) Nat.one_pos).inv := by
    rw [Iso.eq_inv_comp, ← cancel_mono (chart R (SegreIndex n) (prefixTuple v)).ι,
      Category.assoc, morphismRestrict_ι, ← Category.assoc, he, hfac, Category.assoc]
    rfl
  rw [key]
  infer_instance

/-- **The Plücker embedding**: over every commutative ring, the Segre–Plücker morphism
`Fl_n ⟶ ℙ(⊗_k ∧^{k+1} R^n)` is a closed immersion. -/
theorem isClosedImmersion_pluckerSegre : IsClosedImmersion (pluckerSegre R n) := by
  let U : Option (Equiv.Perm (Fin n)) → (projSpace R (SegreIndex n)).Opens := fun i =>
    match i with
    | none =>
      ⟨(Set.range (pluckerSegre R n))ᶜ, (isClosed_range_pluckerSegre R (n := n)).isOpen_compl⟩
    | some v => chart R (SegreIndex n) (prefixTuple v)
  refine IsZariskiLocalAtTarget.of_iSup_eq_top U ?_ fun i => ?_
  · rw [eq_top_iff]
    intro p _
    rw [TopologicalSpace.Opens.mem_iSup]
    by_cases hp : p ∈ Set.range (pluckerSegre R n)
    · obtain ⟨x, rfl⟩ := hp
      obtain ⟨v, hv⟩ := exists_mem_bigCell R x
      exact ⟨some v, bigCell_le_preimage_chart R v hv⟩
    · exact ⟨none, hp⟩
  · cases i with
    | none =>
      have : IsEmpty (pluckerSegre R n ⁻¹ᵁ U none).toScheme :=
        ⟨fun x => x.2 ⟨x.1, rfl⟩⟩
      infer_instance
    | some v => exact isClosedImmersion_restrict_chart R v

instance : IsClosedImmersion (pluckerSegre R n) :=
  isClosedImmersion_pluckerSegre R

end FlagVarieties.Plucker
