import Schubert.FlagVarieties.Foundations.Flags.CoordinateChartNeighborhood
import Mathlib.Topology.Sets.OpenCover

/-!
# Principal-open covers carrying coordinate quotient presentations

The pointwise neighborhood theorem yields an open cover of the base
spectrum. Compactness gives a finite such cover. Each covering localization
uses selected coordinates from the original ambient module, with its
localized quotient map bijective. The normalized matrix presentations on
such a cover are constructed in `Flags/LocalizedCoordinateChart.lean`.
-/

namespace FlagVarieties.Foundations.QuotientCharts

variable {R : Type*} [CommRing R] {n d : ℕ}

/-- The selected coordinate quotient presentations hold on a principal-open cover. -/
theorem grassmannian_exists_selectedMap_openCover
    (P : Module.Grassmannian R (Fin n → R) d) :
    ∃ (a : PrimeSpectrum R → (Fin d ↪ Fin n)) (g : PrimeSpectrum R → R),
      (∀ p, g p ∉ p.asIdeal) ∧
      TopologicalSpace.IsOpenCover (fun p => PrimeSpectrum.basicOpen (g p)) ∧
      ∀ p, Function.Bijective (LocalizedModule.map (Submonoid.powers (g p))
        (P.toSubmodule.mkQ.comp (coordinateInclusion (a p)))) := by
  classical
  choose a g hg hbij using grassmannian_exists_bijective_selectedMap_neighborhood P
  refine ⟨a, g, hg, ?_, hbij⟩
  apply TopologicalSpace.IsOpenCover.mk
  apply top_le_iff.mp
  intro p _
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨p, hg p⟩

/-- A finite principal-open cover suffices, including the empty spectrum. -/
theorem grassmannian_exists_selectedMap_finiteOpenCover
    (P : Module.Grassmannian R (Fin n → R) d) :
    ∃ (s : Finset (PrimeSpectrum R)) (a : s → (Fin d ↪ Fin n)) (g : s → R),
      TopologicalSpace.IsOpenCover (fun p => PrimeSpectrum.basicOpen (g p)) ∧
      ∀ p, Function.Bijective (LocalizedModule.map (Submonoid.powers (g p))
        (P.toSubmodule.mkQ.comp (coordinateInclusion (a p)))) := by
  classical
  obtain ⟨a, g, _, hcover, hbij⟩ := grassmannian_exists_selectedMap_openCover P
  obtain ⟨s, hs⟩ := hcover.exists_finite_of_compactSpace
  exact ⟨s, fun p => a p.val, fun p => g p.val, hs, fun p => hbij p.val⟩

end FlagVarieties.Foundations.QuotientCharts
