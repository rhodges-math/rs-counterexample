import Schubert.RS.Representation.FlagTies
namespace Schubert.RS.Representation
noncomputable section
set_option maxHeartbeats 100000
theorem rowRename_mul {n : ℕ} (w v : Equiv.Perm (Fin n)) (p : MatrixPolynomial n) :
    rowRename (w*v) p = rowRename w (rowRename v p) := by
  change MvPolynomial.rename (fun rc : Fin n × Fin n => ((w*v) rc.1, rc.2)) p =
    MvPolynomial.rename (fun rc : Fin n × Fin n => (w rc.1, rc.2))
      (MvPolynomial.rename (fun rc : Fin n × Fin n => (v rc.1, rc.2)) p)
  rw [MvPolynomial.rename_rename]
  rfl

theorem extremalFlag_line_of_weight_eq {n : ℕ} (m : ColumnShape n)
    (w v : Equiv.Perm (Fin n)) (h : extremalWeight m w = extremalWeight m v) :
    ∃ c : ℂ, c ≠ 0 ∧ extremalFlag m v = c • extremalFlag m w := by
  let t := w.symm * v
  have ht : ∀ i, shapeWeight m (t i) = shapeWeight m i := by
    intro i
    have hi := congrFun h (v i)
    simpa [extremalWeight, t] using hi
  refine ⟨stabilizerSeedScalar m t ht, stabilizerSeedScalar_ne_zero m t ht, ?_⟩
  have hv : w*t = v := by
    apply Equiv.ext
    intro i
    exact w.apply_symm_apply (v i)
  change rowRename v (highestFlag m) = _ • rowRename w (highestFlag m)
  calc
    rowRename v (highestFlag m) = rowRename (w*t) (highestFlag m) := congrArg (fun z => rowRename z (highestFlag m)) hv.symm
    _ = rowRename w (rowRename t (highestFlag m)) := rowRename_mul w t _
    _ = rowRename w (stabilizerSeedScalar m t ht • highestFlag m) := congrArg (rowRename w) (stabilizer_highestFlag m t ht)
    _ = _ := map_smul (rowRename w) _ _

theorem upperCyclic_smul_of_ne_zero {n : ℕ} (p : MatrixPolynomial n) (c : ℂ) (hc : c ≠ 0) :
    upperCyclic (c • p) = upperCyclic p := by
  apply le_antisymm
  · apply upperCyclic_le_of_seed_mem
    exact (upperCyclic p).smul_mem c (upperCyclic_seed p)
  · apply upperCyclic_le_of_seed_mem
    have h := (upperCyclic (c • p)).smul_mem c⁻¹ (upperCyclic_seed (c • p))
    simpa [smul_smul, hc] using h

theorem flagDemazure_eq_of_weight_eq {n : ℕ} (m : ColumnShape n)
    (w v : Equiv.Perm (Fin n)) (h : extremalWeight m w = extremalWeight m v) :
    flagDemazure m w = flagDemazure m v := by
  obtain ⟨c, hc, he⟩ := extremalFlag_line_of_weight_eq m w v h
  unfold flagDemazure
  rw [he, upperCyclic_smul_of_ne_zero _ c hc]

/-- Equality of the actual subspaces gives the identity on ambient polynomials. -/
def flagTiesEquiv {n : ℕ} (m : ColumnShape n) (w v : Equiv.Perm (Fin n))
    (h : extremalWeight m w = extremalWeight m v) :
    flagDemazure m w ≃ₗ[ℂ] flagDemazure m v :=
  LinearEquiv.ofEq _ _ (flagDemazure_eq_of_weight_eq m w v h)
theorem flagTiesEquiv_val {n : ℕ} (m : ColumnShape n) (w v : Equiv.Perm (Fin n))
    (h : extremalWeight m w = extremalWeight m v) (p : flagDemazure m w) :
    (flagTiesEquiv m w v h p).val = p.val :=
  LinearEquiv.coe_ofEq_apply (flagDemazure_eq_of_weight_eq m w v h) p

theorem flagTiesEquiv_torus {n : ℕ} (m : ColumnShape n) (w v : Equiv.Perm (Fin n))
    (h : extremalWeight m w = extremalWeight m v) (t : DiagonalTorus n) (p : flagDemazure m w) :
    flagTiesEquiv m w v h (flagTorus m w t p) = flagTorus m v t (flagTiesEquiv m w v h p) := by
  apply Subtype.ext
  calc
    (flagTiesEquiv m w v h (flagTorus m w t p)).val = (flagTorus m w t p).val := flagTiesEquiv_val m w v h _
    _ = polynomialTorus n t p.val := flagTorus_val m w t p
    _ = polynomialTorus n t (flagTiesEquiv m w v h p).val := congrArg (polynomialTorus n t) (flagTiesEquiv_val m w v h p).symm
    _ = (flagTorus m v t (flagTiesEquiv m w v h p)).val := (flagTorus_val m v t _).symm

theorem flagTies_weight_finrank {n : ℕ} (m : ColumnShape n) (w v : Equiv.Perm (Fin n))
    (h : extremalWeight m w = extremalWeight m v) (z : Weight n) :
    Module.finrank ℂ (torusWeightSpace (flagTorus m w) z) =
      Module.finrank ℂ (torusWeightSpace (flagTorus m v) z) :=
  torusWeightSpace_finrank_eq _ _ (flagTiesEquiv m w v h) (flagTiesEquiv_torus m w v h) z

/-- Any alternative descending sorting permutation produces the canonical
cyclic module, including every choice within equal-weight blocks. -/
theorem compositionFlag_eq_alternative {n : ℕ} (u : Composition n) (v : Equiv.Perm (Fin n))
    (hv : Antitone (u ∘ v)) :
    compositionFlag u = flagDemazure (compositionShape u) v := by
  apply flagDemazure_eq_of_weight_eq
  rw [composition_extremalWeight]
  funext i
  change u i = shapeWeight (compositionShape u) (v.symm i)
  rw [compositionShape_weight, ← dominantComposition_unique u v hv]
  simp

end
end Schubert.RS.Representation










