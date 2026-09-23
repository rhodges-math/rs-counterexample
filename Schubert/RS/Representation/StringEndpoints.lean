import Schubert.RS.Representation.AdjacentInclusion

namespace Schubert.RS.Representation
noncomputable section

/-- The low extremal endpoint is killed by the actual opposite matrix unit. -/
theorem extremalFlag_lowering_zero {n : ℕ} (m : ColumnShape n) (w : Equiv.Perm (Fin n))
    (a b : Fin n) (hu : extremalWeight m w a < extremalWeight m w b) :
    matrixUnitDerivation b a (extremalFlag m w) = 0 := by
  have hba : w.symm b < w.symm a := by
    by_contra h
    exact (not_lt_of_ge (shapeWeight_antitone m (le_of_not_gt h))) hu
  change matrixUnitDerivation b a (rowRename w (highestFlag m)) = 0
  rw [matrixUnitDerivation_rowRename]
  have hz := rootDerivation_highestFlag ⟨(w.symm b,w.symm a), hba⟩ m
  change matrixUnitDerivation (w.symm b) (w.symm a) (highestFlag m) = 0 at hz
  rw [hz, map_zero]

theorem extremalFlag_string_next_zero {n : ℕ} (m : ColumnShape n) (w : Equiv.Perm (Fin n))
    (a b : Fin n) (hu : extremalWeight m w a < extremalWeight m w b) :
    derivationIter (matrixUnitDerivation a b) (extremalWeight m w b - extremalWeight m w a + 1)
      (extremalFlag m w) = 0 := by
  have hba : w.symm b < w.symm a := by
    by_contra h
    exact (not_lt_of_ge (shapeWeight_antitone m (le_of_not_gt h))) hu
  have hz := (highestFlag_derivationTop m (w.symm a) (w.symm b) hba).2
  rw [stringDegree_eq_weight_sub m _ _ hba] at hz
  change derivationIter _ _ (rowRename w (highestFlag m)) = 0
  simp only [extremalWeight]
  rw [derivationIter_rowRename, hz, map_zero]

theorem extremalFlag_string_top_ne_zero {n : ℕ} (m : ColumnShape n) (w : Equiv.Perm (Fin n))
    (a b : Fin n) (hu : extremalWeight m w a < extremalWeight m w b) :
    derivationIter (matrixUnitDerivation a b) (extremalWeight m w b - extremalWeight m w a)
      (extremalFlag m w) ≠ 0 := by
  obtain ⟨c, hc, he⟩ := extremalFlag_swap_iter_weight m w a b hu
  intro hz
  rw [hz, smul_zero] at he
  apply extremalFlag_ne_zero m (Equiv.swap a b * w)
  change rowRename (Equiv.swap a b * w) (highestFlag m) = 0
  rw [rowRename_mul]
  exact he

/-- The reflected seed returns along an actual lowering string of the same
length. This statement concerns the endpoints, not saturation of the module. -/
theorem extremalFlag_reverse_string {n : ℕ} (m : ColumnShape n) (w : Equiv.Perm (Fin n))
    (a b : Fin n) (hu : extremalWeight m w a < extremalWeight m w b) :
    ∃ c : ℂ, c ≠ 0 ∧ extremalFlag m w = c •
      derivationIter (matrixUnitDerivation b a) (extremalWeight m w b - extremalWeight m w a)
        (rowRename (Equiv.swap a b) (extremalFlag m w)) := by
  let v := Equiv.swap a b * w
  have hv : extremalWeight m v b < extremalWeight m v a := by
    simpa only [v, extremalWeight_swap_mul, Function.comp_apply, Equiv.swap_apply_left, Equiv.swap_apply_right] using hu
  obtain ⟨c, hc, he⟩ := extremalFlag_swap_iter_weight m v b a hv
  refine ⟨c, hc, ?_⟩
  have hs : rowRename (Equiv.swap b a) (extremalFlag m v) = extremalFlag m w := by
    change rowRename (Equiv.swap b a) (rowRename (Equiv.swap a b * w) (highestFlag m)) = _
    rw [← rowRename_mul]
    have hp : Equiv.swap b a * (Equiv.swap a b * w) = w := by
      apply Equiv.ext
      intro i
      change Equiv.swap b a (Equiv.swap a b (w i)) = w i
      rw [Equiv.swap_comm b a, Equiv.swap_apply_self]
    rw [hp]
    rfl
  rw [hs] at he
  have ha' : extremalWeight m v a = extremalWeight m w b := by simp [v, extremalWeight_swap_mul]
  have hb' : extremalWeight m v b = extremalWeight m w a := by simp [v, extremalWeight_swap_mul]
  rw [ha', hb'] at he
  change _ = c • derivationIter _ _ (rowRename (Equiv.swap a b) (rowRename w (highestFlag m)))
  rw [← rowRename_mul]
  exact he

end
end Schubert.RS.Representation

