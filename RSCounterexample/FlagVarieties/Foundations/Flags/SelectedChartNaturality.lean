import RSCounterexample.FlagVarieties.Foundations.Flags.SelectedChartOverlap
import RSCounterexample.FlagVarieties.Foundations.Flags.MatrixChartTransitionFormula

/-!
# Scalar naturality of the selected chart blocks

The coordinate orderings depend only on the index injections. Ring maps
therefore commute with these orderings, the normalized quotient, and the
selected and remaining blocks. These identities identify universal
polynomial blocks with the quotient blocks at every algebra-valued
point, including nonflat base changes.
-/

namespace FlagVarieties.Foundations.QuotientCharts

variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) {n d : ℕ}

theorem selectedCoordinateEquiv_map (a : Fin d ↪ Fin n) (v : Fin n → R) :
    selectedCoordinateEquiv a (f ∘ v) =
      (f ∘ (selectedCoordinateEquiv a v).1, f ∘ (selectedCoordinateEquiv a v).2) := by
  apply Prod.ext
  · ext i
    simp
  · ext j
    rfl

theorem selectedCoordinateEquiv_symm_map (a : Fin d ↪ Fin n)
    (v : (Fin d → R) × (Fin (n - d) → R)) :
    (selectedCoordinateEquiv a).symm (f ∘ v.1, f ∘ v.2) =
      f ∘ (selectedCoordinateEquiv a).symm v := by
  apply (selectedCoordinateEquiv a).injective
  rw [LinearEquiv.apply_symm_apply, selectedCoordinateEquiv_map]
  simp

theorem selectedCoordinateChange_symm_map (a b : Fin d ↪ Fin n)
    (v : (Fin d → R) × (Fin (n - d) → R)) :
    (selectedCoordinateChange a b).symm (f ∘ v.1, f ∘ v.2) =
      (f ∘ ((selectedCoordinateChange a b).symm v).1,
        f ∘ ((selectedCoordinateChange a b).symm v).2) := by
  change selectedCoordinateEquiv a ((selectedCoordinateEquiv b).symm (f ∘ v.1, f ∘ v.2)) = _
  rw [selectedCoordinateEquiv_symm_map, selectedCoordinateEquiv_map]
  rfl

theorem normalizedMatrix_map {c : ℕ} (C : Matrix (Fin d) (Fin c) R)
    (v : (Fin d → R) × (Fin c → R)) :
    normalizedMap (Matrix.toLin' (C.map f)) (f ∘ v.1, f ∘ v.2) =
      f ∘ normalizedMap (Matrix.toLin' C) v := by
  ext i
  simp [normalizedMap_apply, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
    Function.comp_def, Matrix.map, map_sum]

theorem selectedBlock_toMatrix_map (a b : Fin d ↪ Fin n)
    (C : Matrix (Fin d) (Fin (n - d)) R) :
    (LinearMap.toMatrix' (selectedBlock (Matrix.toLin' C)
      (selectedCoordinateChange a b))).map f =
      LinearMap.toMatrix' (selectedBlock (Matrix.toLin' (C.map f))
        (selectedCoordinateChange a b)) := by
  classical
  ext i j
  have h := congrFun (normalizedMatrix_map f C ((selectedCoordinateChange a b).symm
    (Pi.single j 1, 0))) i
  rw [← selectedCoordinateChange_symm_map] at h
  have hs : f ∘ (Pi.single j (1 : R)) = Pi.single j (1 : S) := by
    ext t
    simp [Pi.single_apply]
  have hz : f ∘ (0 : Fin (n - d) → R) = 0 := by ext t; simp
  rw [hs, hz] at h
  simpa only [LinearMap.toMatrix'_apply, selectedBlock, LinearMap.comp_apply,
    LinearMap.inl_apply, Matrix.map_apply, Function.comp_apply, LinearEquiv.coe_coe] using h.symm

theorem remainingBlock_toMatrix_map (a b : Fin d ↪ Fin n)
    (C : Matrix (Fin d) (Fin (n - d)) R) :
    (LinearMap.toMatrix' (remainingBlock (Matrix.toLin' C)
      (selectedCoordinateChange a b))).map f =
      LinearMap.toMatrix' (remainingBlock (Matrix.toLin' (C.map f))
        (selectedCoordinateChange a b)) := by
  classical
  ext i j
  have h := congrFun (normalizedMatrix_map f C ((selectedCoordinateChange a b).symm
    (0, Pi.single j 1))) i
  rw [← selectedCoordinateChange_symm_map] at h
  have hs : f ∘ (Pi.single j (1 : R)) = Pi.single j (1 : S) := by
    ext t
    simp [Pi.single_apply]
  have hz : f ∘ (0 : Fin d → R) = 0 := by ext t; simp
  rw [hs, hz] at h
  simpa only [LinearMap.toMatrix'_apply, remainingBlock, LinearMap.comp_apply,
    LinearMap.inr_apply, Matrix.map_apply, Function.comp_apply, LinearEquiv.coe_coe] using h.symm

end FlagVarieties.Foundations.QuotientCharts
