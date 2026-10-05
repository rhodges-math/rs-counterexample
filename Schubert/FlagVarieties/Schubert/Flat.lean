import Schubert.FlagVarieties.Charts.OrbitMap
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# The orbit map is flat; images commute with flat base change

* `FlagVarieties.flat_orbitMap`: if `𝒪(B)` is flat over `R` (e.g. `R` a field), the orbit map
  `π : GLₙ ⟶ Flₙ` is flat. Over the big cell of `v` it is `bigCell v × B ⟶ bigCell v`.
* `FlagVarieties.isSchemeTheoreticallyDominant_toImage`: `X ⟶ f.image` is scheme-theoretically
  dominant for quasi-compact `f`.
* `FlagVarieties.comap_ker_eq_ker`: for flat `π` and quasi-compact `h`, the pullback along `π` of
  the scheme-theoretic image of `h` is the scheme-theoretic image of the base change of `h`.
-/

noncomputable section

namespace FlagVarieties

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

variable (R : Type u) [CommRing R] (n : ℕ)

theorem flat_prodInl [Module.Flat R (BorelCoord R n)] (v : Equiv.Perm (Fin n)) :
    (prodInl R v).toRingHom.Flat := by
  change (algebraMap (bigCellRing R v) (bigCellRing R v ⊗[R] BorelCoord R n)).Flat
  rw [RingHom.flat_algebraMap_iff]
  infer_instance

theorem flat_preimageChartComorphism [Module.Flat R (BorelCoord R n)] (v : Equiv.Perm (Fin n)) :
    (preimageChartComorphism R v).toRingHom.Flat := by
  rw [preimageChartComorphism_eq]
  exact RingHom.Flat.comp (flat_prodInl R n v)
    (RingHom.Flat.of_bijective (bigCellTrivialization R v).symm.bijective)

set_option backward.isDefEq.respectTransparency false in
/-- **The orbit map `π : GLₙ ⟶ Flₙ` is flat** (when `𝒪(B)` is flat over `R`). -/
instance flat_orbitMap [Module.Flat R (BorelCoord R n)] : Flat (FlagScheme.orbitMap R n) := by
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @Flat)
    (fun v : Equiv.Perm (Fin n) => (preimageChart R v).opensRange) ?_ ?_
  · rw [eq_top_iff]
    intro x _
    obtain ⟨v, hv⟩ := exists_mem_bigCell R (FlagScheme.orbitMap R n x)
    refine TopologicalSpace.Opens.mem_iSup.mpr ⟨v, ?_⟩
    rw [preimageChart_opensRange]
    exact hv
  · intro v
    have e : (preimageChart R v).opensRange.ι =
        (IsOpenImmersion.isoOfRangeEq (preimageChart R v).opensRange.ι (preimageChart R v)
          (by rw [Scheme.Opens.range_ι, Scheme.Hom.coe_opensRange])).hom ≫ preimageChart R v :=
      (IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _).symm
    rw [e, Category.assoc, preimageChart_orbitMap]
    have : Flat (Spec.map (CommRingCat.ofHom (preimageChartComorphism R v).toRingHom)) := by
      rw [Flat.SpecMap_iff]
      exact flat_preimageChartComorphism R n v
    infer_instance

/-- `X ⟶ f.image` has trivial kernel: it is scheme-theoretically dominant. -/
theorem ker_toImage_eq_bot {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] : f.toImage.ker = ⊥ := by
  apply le_bot_iff.mp
  refine Scheme.IdealSheafData.le_of_iSup_eq_top
    (fun V : Y.affineOpens => (⟨f.imageι ⁻¹ᵁ V.1, V.2.preimage f.imageι⟩ : f.image.affineOpens))
    ?_ ?_
  · change ⨆ V : Y.affineOpens, f.imageι ⁻¹ᵁ V.1 = ⊤
    rw [← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top, Scheme.Hom.preimage_top]
  · intro V x hx
    rw [Scheme.Hom.ker_apply, RingHom.mem_ker] at hx
    have h0 := f.toImage_app_injective V (hx.trans (map_zero _).symm)
    rw [h0]
    exact Ideal.zero_mem _

instance isSchemeTheoreticallyDominant_toImage {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] :
    IsSchemeTheoreticallyDominant f.toImage :=
  ⟨ker_toImage_eq_bot f⟩

set_option backward.isDefEq.respectTransparency false in
/-- **Scheme-theoretic images commute with flat base change**: for flat `π` and quasi-compact
`h`, the pullback along `π` of the image of `h` is the image of the base change of `h`. -/
theorem comap_ker_eq_ker {X Y Z : Scheme.{u}} (π : Z ⟶ Y) (h : X ⟶ Y) [Flat π]
    [QuasiCompact h] :
    h.ker.comap π = (pullback.fst (pullback.snd π h.imageι) h.toImage ≫
      pullback.fst π h.imageι).ker := by
  have : Flat (pullback.snd π h.imageι) := MorphismProperty.pullback_snd _ _ inferInstance
  rw [Scheme.Hom.ker_comp, Scheme.Hom.ker_eq_bot (pullback.fst (pullback.snd π h.imageι) h.toImage),
    Scheme.IdealSheafData.map_bot]
  rfl

end FlagVarieties
