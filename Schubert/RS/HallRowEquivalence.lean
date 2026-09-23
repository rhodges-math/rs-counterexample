import Schubert.RS.LatticeHeightRecovery
import Schubert.RS.HallPathEquivalence

/-! Complete Hall matrix entries: every path corresponds to a weak height word. -/

namespace Schubert.RS.HallLattice
noncomputable section
variable {d M : ℕ} (y : Fin d → Fin (M+1)) {j i : Fin d}
variable {k : ℕ} (hk : hallSource j+k = hallSource i+1)

abbrev WeakHeights (k y : ℕ) := {r : Fin k → Fin (y+1) // Monotone (fun q => (r q).val)}

def rowDiagonalPath (r : WeakHeights k (y i).val) :
    DiagonalLatticePath (hallSource j) (hallSource i+1) (y i).val where
  horizontal := thresholdHorizontal (hallSource j) r.val
  nonempty := by omega
  source := thresholdHorizontal_source _ _
  target := by rw [← hk]; exact thresholdHorizontal_target _ _
  step t hs he := (thresholdPath (hallSource j) r.val r.property).step t hs (by omega)

def heightWordPath (r : WeakHeights k (y i).val) : LayeredPath (edges y) (start j) (finish i) :=
  encodedPath y (rowDiagonalPath y hk r)

theorem heightWordPath_horizontal (r : WeakHeights k (y i).val) (t : ℕ)
    (hs : hallSource j ≤ t) (he : t ≤ hallSource i+1+(y i).val) :
    pathHorizontal y (heightWordPath y hk r) t = thresholdHorizontal (hallSource j) r.val t :=
  decoded_encoded_horizontal y _ t hs he

def rowDecodedPath (P : LayeredPath (edges y) (start j) (finish i)) :
    DiagonalLatticePath (hallSource j) (hallSource j+k) (y i).val where
  horizontal := pathHorizontal y P
  nonempty := by rw [hk]; exact (decodedPath y P).nonempty
  source := (decodedPath y P).source
  target := by rw [hk]; exact (decodedPath y P).target
  step t hs he := (decodedPath y P).step t hs (by omega)

theorem heightWordPath_injective : Function.Injective (heightWordPath y hk) := by
  intro r q he
  apply Subtype.ext
  rw [← crossingHeight_thresholdPath (hallSource j) r.val r.property,
      ← crossingHeight_thresholdPath (hallSource j) q.val q.property]
  apply crossingHeight_ext
  intro t hs ht
  have h := congrArg (fun P => pathHorizontal y P t) he
  rw [heightWordPath_horizontal y hk r t hs (by omega),
    heightWordPath_horizontal y hk q t hs (by omega)] at h
  exact h

theorem heightWordPath_surjective : Function.Surjective (heightWordPath y hk) := by
  intro P
  let Q := rowDecodedPath y hk P
  let r : WeakHeights k (y i).val := ⟨crossingHeight Q, crossingHeight_monotone Q⟩
  refine ⟨r, path_ext_active y _ P ?_⟩
  intro t hs ht
  rw [heightWordPath_horizontal y hk r t hs ht]
  exact thresholdHorizontal_crossingHeight Q t hs (by omega)

def rowPathEquiv : WeakHeights k (y i).val ≃ LayeredPath (edges y) (start j) (finish i) :=
  Equiv.ofBijective (heightWordPath y hk)
    ⟨heightWordPath_injective y hk, heightWordPath_surjective y hk⟩

theorem no_path_negative_degree (h : hallSource i+1 < hallSource j) :
    IsEmpty (LayeredPath (edges y) (start j) (finish i)) :=
  ⟨fun P => (Nat.not_le_of_gt h) (decodedPath y P).source_le_target⟩

end
end Schubert.RS.HallLattice
