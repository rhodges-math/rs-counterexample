import Schubert.RS.LatticeCrossings

/-! The weak height word and the complete path determine one another. -/

namespace Schubert.RS
noncomputable section
variable {s k y : ℕ}

theorem threshold_card_le (e : Fin k → ℕ) (t : ℕ) : (thresholdSet e t).card ≤ k := by
  have h := Finset.card_le_card (Finset.filter_subset (fun q => e q ≤ t) Finset.univ)
  simpa only [thresholdSet, Finset.card_univ, Fintype.card_fin] using h

theorem lt_threshold_card_iff (e : Fin k → ℕ) (he : Monotone e) (q : Fin k) (t : ℕ) :
    q.val < (thresholdSet e t).card ↔ e q ≤ t :=
  Tuple.lt_card_le_iff_apply_le_of_monotone he

theorem thresholdHorizontal_crossingHeight
    (P : DiagonalLatticePath s (s+k) y) (t : ℕ) (hs : s ≤ t) (he : t ≤ s+k+y) :
    thresholdHorizontal s (crossingHeight P) t = P.horizontal t := by
  have ee : eastTime s (crossingHeight P) = crossingTime P := funext (eastTime_crossingHeight P)
  change (s : ℤ)+((thresholdSet (eastTime s (crossingHeight P)) t).card : ℤ) = _
  rw [ee]
  let c := (thresholdSet (crossingTime P) t).card
  have hck : c ≤ k := threshold_card_le _ _
  have hlow := (northEast_interval_bounds P.horizontal s (s+k+y) P.step s t le_rfl hs he).1
  rw [P.source] at hlow
  have hhigh := P.horizontal_le_target t hs he
  change (s : ℤ)+(c : ℤ) = P.horizontal t
  rcases lt_trichotomy ((s : ℤ)+(c : ℤ)) (P.horizontal t) with h | h | h
  · have hlt : c < k := by omega
    let q : Fin k := ⟨c, hlt⟩
    have hcross : crossingTime P q ≤ t := (crossingTime_le_iff P q t hs he).mpr (by
      change ((s+c+1 : ℕ) : ℤ) ≤ P.horizontal t; omega)
    have hn := (lt_threshold_card_iff _ (crossingTime_strictMono P).monotone q t).mpr hcross
    change c < c at hn
    omega
  · exact h
  · have hcpos : 0 < c := by omega
    let q : Fin k := ⟨c-1, by omega⟩
    have hcross := (lt_threshold_card_iff _ (crossingTime_strictMono P).monotone q t).mp
      (show q.val < (thresholdSet (crossingTime P) t).card by change c-1 < c; omega)
    have hh := (crossingTime_le_iff P q t hs he).mp hcross
    change ((s+(c-1)+1 : ℕ) : ℤ) ≤ P.horizontal t at hh
    omega

theorem crossingTime_thresholdPath (s : ℕ) (r : Fin k → Fin (y+1))
    (hr : Monotone (fun q => (r q).val)) (q : Fin k) :
    crossingTime (thresholdPath s r hr) q = eastTime s r q := by
  let P := thresholdPath s r hr
  have hes : s ≤ eastTime s r q := by unfold eastTime; omega
  have hee : eastTime s r q ≤ s+k+y := by
    have hq := q.isLt
    have hheight := (r q).isLt
    unfold eastTime
    omega
  apply le_antisymm
  · apply (crossingTime_le_iff P q _ hes hee).mpr
    have h := (lt_threshold_card_iff (eastTime s r) (eastTime_strictMono s r hr).monotone
      q (eastTime s r q)).mpr le_rfl
    change ((s+q.val+1 : ℕ) : ℤ) ≤ thresholdHorizontal s r (eastTime s r q)
    unfold thresholdHorizontal
    omega
  · have h := crossingTime_horizontal P q
    change thresholdHorizontal s r (crossingTime P q) = ((s+q.val+1 : ℕ) : ℤ) at h
    unfold thresholdHorizontal at h
    apply (lt_threshold_card_iff (eastTime s r) (eastTime_strictMono s r hr).monotone
      q (crossingTime P q)).mp
    omega

theorem crossingHeight_thresholdPath (s : ℕ) (r : Fin k → Fin (y+1))
    (hr : Monotone (fun q => (r q).val)) : crossingHeight (thresholdPath s r hr) = r := by
  funext q
  apply Fin.ext
  have h := eastTime_crossingHeight (thresholdPath s r hr) q
  rw [crossingTime_thresholdPath] at h
  unfold eastTime at h
  omega

theorem crossingHeight_ext (P Q : DiagonalLatticePath s (s+k) y)
    (h : ∀ t, s ≤ t → t ≤ s+k+y → P.horizontal t = Q.horizontal t) :
    crossingHeight P = crossingHeight Q := by
  have hc (q : Fin k) : crossingTime P q = crossingTime Q q := by
    apply le_antisymm
    · apply (crossingTime_le_iff P q _ (crossingTime_spec Q q).1 (crossingTime_le_end Q q)).mpr
      rw [h _ (crossingTime_spec Q q).1 (crossingTime_le_end Q q), crossingTime_horizontal]
    · apply (crossingTime_le_iff Q q _ (crossingTime_spec P q).1 (crossingTime_le_end P q)).mpr
      rw [← h _ (crossingTime_spec P q).1 (crossingTime_le_end P q), crossingTime_horizontal]
  funext q
  apply Fin.ext
  change crossingTime P q-s-q.val-1 = crossingTime Q q-s-q.val-1
  rw [hc]

end
end Schubert.RS
