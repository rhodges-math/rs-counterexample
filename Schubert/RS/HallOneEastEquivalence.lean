import Schubert.RS.HallPathEquivalence
import Schubert.RS.HallPathMatching

/-! Identity-matching paths are exactly the possible east-step heights. -/

namespace Schubert.RS.HallLattice
noncomputable section
variable {d M : ℕ} (y : Fin d → Fin (M+1)) (i : Fin d)

def heightPath (r : Fin ((y i).val+1)) :
    LayeredPath (edges y) (start i) (finish i) :=
  encodedPath y (oneEastPath (hallSource i) (y i).val r.val (by omega))

theorem heightPath_horizontal (r : Fin ((y i).val+1)) (t : ℕ)
    (hs : hallSource i ≤ t) (he : t ≤ hallSource i+1+(y i).val) :
    pathHorizontal y (heightPath y i r) t = oneEastHorizontal (hallSource i) r.val t :=
  decoded_encoded_horizontal y _ t hs he

theorem heightPath_injective : Function.Injective (heightPath y i) := by
  intro r q hp
  apply Fin.ext
  by_contra hn
  have neq (r q : Fin ((y i).val+1)) (h : r.val < q.val)
      (heq : heightPath y i r = heightPath y i q) : False := by
    have hr := r.isLt
    have hq := q.isLt
    have hh := congrArg (fun P => pathHorizontal y P (hallSource i+r.val+1)) heq
    rw [heightPath_horizontal y i r _ (by omega) (by omega),
      heightPath_horizontal y i q _ (by omega) (by omega)] at hh
    simp only [oneEastHorizontal, if_neg (show ¬hallSource i+r.val+1 ≤ hallSource i+r.val by omega),
      if_pos (show hallSource i+r.val+1 ≤ hallSource i+q.val by omega)] at hh
    omega
  rcases lt_or_gt_of_ne hn with h | h
  · exact neq r q h hp
  · exact neq q r h hp.symm

theorem heightPath_surjective : Function.Surjective (heightPath y i) := by
  intro P
  obtain ⟨r, hr, he⟩ := oneEastPath_classification (hallSource i) (y i).val (decodedPath y P)
  refine ⟨⟨r, by omega⟩, path_ext_active y _ P ?_⟩
  intro t hs ht
  rw [heightPath_horizontal y i _ t hs ht]
  exact (he t hs ht).symm

def heightPathEquiv : Fin ((y i).val+1) ≃ LayeredPath (edges y) (start i) (finish i) :=
  Equiv.ofBijective (heightPath y i) ⟨heightPath_injective y i, heightPath_surjective y i⟩

end
end Schubert.RS.HallLattice
