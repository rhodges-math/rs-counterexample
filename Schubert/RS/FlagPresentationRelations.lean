import Schubert.RS.Representation.StringEndpoints

namespace Schubert.RS.Representation
noncomputable section

/-- Every matrix unit whose weight moves away from an extremal weight is
zero on its actual flag generator. Ties are included. -/
theorem extremalFlag_killing_root_zero {n : ℕ} (m : ColumnShape n)
    (w : Equiv.Perm (Fin n)) (a b : Fin n) (hab : a ≠ b)
    (hu : extremalWeight m w b ≤ extremalWeight m w a) :
    matrixUnitDerivation a b (extremalFlag m w) = 0 := by
  change matrixUnitDerivation a b (rowRename w (highestFlag m)) = 0
  rw [matrixUnitDerivation_rowRename]
  by_cases hlt : w.symm a < w.symm b
  · have hz := rootDerivation_highestFlag ⟨(w.symm a,w.symm b),hlt⟩ m
    change matrixUnitDerivation (w.symm a) (w.symm b) (highestFlag m)=0 at hz
    rw [hz,map_zero]
  · have hne : w.symm a ≠ w.symm b := fun h => hab (w.symm.injective h)
    have hgt : w.symm b < w.symm a := lt_of_le_of_ne (le_of_not_gt hlt) hne.symm
    have hz := (highestFlag_derivationTop m (w.symm a) (w.symm b) hgt).2
    rw [stringDegree_eq_weight_sub m _ _ hgt] at hz
    change shapeWeight m (w.symm b) ≤ shapeWeight m (w.symm a) at hu
    rw [Nat.sub_eq_zero_of_le hu] at hz
    have hz' : matrixUnitDerivation (w.symm a) (w.symm b) (highestFlag m)=0 := by
      simpa only [zero_add,derivationIter_succ,derivationIter_zero] using hz
    rw [hz',map_zero]

theorem polynomialEnveloping_root_pow {n : ℕ} (r : PositiveRoot n) (k : ℕ)
    (p : MatrixPolynomial n) :
    polynomialEnveloping n (rootOperator r ^ k) p =
      derivationIter (matrixUnitDerivation r.val.1 r.val.2) k p := by
  rw [map_pow]
  have he : polynomialEnveloping n (rootOperator r) =
      (matrixUnitDerivation r.val.1 r.val.2).toLinearMap := polynomialEnveloping_root r
  rw [he]
  rfl

/-- All defining Joseph--Polo powers annihilate the independently constructed
extremal vector. This proves relations, not completeness of the presentation. -/
theorem flagGenerator_jp_relation {n : ℕ} (m : ColumnShape n)
    (w : Equiv.Perm (Fin n)) (r : PositiveRoot n) :
    polynomialEnveloping n (rootOperator r ^ jpExponent (extremalWeight m w) r)
      (extremalFlag m w) = 0 := by
  rw [polynomialEnveloping_root_pow]
  by_cases hu : extremalWeight m w r.val.1 < extremalWeight m w r.val.2
  · exact extremalFlag_string_next_zero m w r.val.1 r.val.2 hu
  · rw [jpExponent_eq_one _ r (le_of_not_gt hu),derivationIter_succ,derivationIter_zero]
    exact extremalFlag_killing_root_zero m w r.val.1 r.val.2
      (ne_of_lt r.property) (le_of_not_gt hu)

theorem jpLeftIdeal_le_flagCyclic_ker {n : ℕ} (m : ColumnShape n)
    (w : Equiv.Perm (Fin n)) :
    jpLeftIdeal (extremalWeight m w) ≤ LinearMap.ker (flagCyclicModuleMap m w) := by
  apply Submodule.span_le.mpr
  rintro x ⟨r,rfl⟩
  apply Subtype.ext
  exact flagGenerator_jp_relation m w r

end
end Schubert.RS.Representation
