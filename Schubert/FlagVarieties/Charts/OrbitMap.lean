import Schubert.FlagVarieties.Charts.Trivialization
import Schubert.FlagVarieties.Charts.Cover

/-!
# The orbit map over a big cell

* `FlagVarieties.preimageChart R v : Spec 𝒪(GLₙ)[1/f_v] ⟶ GLₙ`, the open immersion of `D(f_v)`;
* `FlagVarieties.preimageChart_orbitMap`: over the big cell, `π` is the spectrum of
  `preimageChartComorphism R v : C_v → 𝒪(GLₙ)[1/f_v]`;
* `FlagVarieties.preimageChart_opensRange`: `D(f_v) = π⁻¹(bigCell v)`.
-/

noncomputable section

namespace FlagVarieties

open AlgebraicGeometry CategoryTheory
open Foundations Foundations.QuotientCharts

universe u

variable (R : Type u) [CommRing R] {n : ℕ} (v : Equiv.Perm (Fin n))

/-- The comorphism `C_v → 𝒪(GLₙ)[1/f_v]` of `D(f_v) ⟶ bigCell v`, `g ↦ π(g)`. -/
def preimageChartComorphism : bigCellRing R v →ₐ[R] BigCellPreimageRing R v :=
  bigCellPoint R (inBigCell_preimageMatrix v)

theorem preimageChartComorphism_eq :
    preimageChartComorphism R v = (trivBackward R v).comp (prodInl R v) :=
  (prodLift_comp_prodInl v _ _).symm

/-- `D(f_v) ⊆ GLₙ`, as the open immersion `Spec 𝒪(GLₙ)[1/f_v] ⟶ GLₙ`. -/
abbrev preimageChart : Spec (CommRingCat.of (BigCellPreimageRing R v)) ⟶ GLScheme R n :=
  GLScheme.point R n (preimageInclusion R v)

instance : IsOpenImmersion (preimageChart R v) := by
  have := IsOpenImmersion.of_isLocalization (S := BigCellPreimageRing R v) (bigCellFunction R v)
  change IsOpenImmersion (Spec.map (CommRingCat.ofHom
    (algebraMap (GLCoord R n) (BigCellPreimageRing R v))) ≫ _)
  infer_instance

/-- Over the big cell, the orbit map is the spectrum of `C_v → 𝒪(GLₙ)[1/f_v]`. -/
theorem preimageChart_orbitMap : preimageChart R v ≫ FlagScheme.orbitMap R n =
    Spec.map (CommRingCat.ofHom (preimageChartComorphism R v).toRingHom) ≫ bigCellChart R v := by
  rw [FlagScheme.orbitMap_point, preimageChartComorphism, spec_bigCellPoint_bigCellChart]
  rfl

/-- **`D(f_v) = π⁻¹(bigCell v)`.** -/
theorem preimageChart_opensRange :
    (preimageChart R v).opensRange = FlagScheme.orbitMap R n ⁻¹ᵁ bigCell R v := by
  have hinv : ∀ x, (TauCeti.GeneralLinear.groupSchemeSpecIso R n).inv
      ((TauCeti.GeneralLinear.groupSchemeSpecIso R n).hom x) = x := fun x => by
    rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]
    rfl
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    have h := congrArg (fun f : Spec (CommRingCat.of (BigCellPreimageRing R v)) ⟶
      FlagScheme R n => f y) (preimageChart_orbitMap R v)
    simp only [Scheme.Hom.comp_apply] at h
    exact ⟨_, h.symm⟩
  · intro hx
    let p := (TauCeti.GeneralLinear.groupSchemeSpecIso R n).hom x
    have hp : specOrbitMap R p ∈ bigCell R v := by
      change FlagScheme.orbitMap R n ((TauCeti.GeneralLinear.groupSchemeSpecIso R n).inv
        ((TauCeti.GeneralLinear.groupSchemeSpecIso R n).hom x)) ∈ bigCell R v
      rw [hinv]
      exact hx
    have hf := (mem_bigCell_iff v p).mp hp
    have hr : p ∈ Set.range (PrimeSpectrum.comap
        (algebraMap (GLCoord R n) (BigCellPreimageRing R v))) := by
      rw [PrimeSpectrum.localization_away_comap_range _ (bigCellFunction R v)]
      exact hf
    obtain ⟨q, hq⟩ := hr
    refine ⟨q, ?_⟩
    change (TauCeti.GeneralLinear.groupSchemeSpecIso R n).inv
      ((Spec.map (CommRingCat.ofHom (algebraMap (GLCoord R n) (BigCellPreimageRing R v)))) q) = x
    rw [show (Spec.map (CommRingCat.ofHom (algebraMap (GLCoord R n)
      (BigCellPreimageRing R v)))) q = p from hq, hinv]

end FlagVarieties
