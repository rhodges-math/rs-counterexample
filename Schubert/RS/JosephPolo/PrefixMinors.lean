import Schubert.RS.JosephPolo.TriangularMinors

namespace Schubert.RS.Representation
noncomputable section
open scoped BigOperators

/-- The row set of the Weyl-translated prefix of length k+1. -/
def flagPrefixRows {n : ℕ} (w : Equiv.Perm (Fin n)) (k : Fin n) : FlagMinorRowSet k :=
  ⟨Finset.univ.image (fun j => w (prefixIndex k j)), by
    classical
    apply Finset.mem_powersetCard.mpr
    refine ⟨Finset.subset_univ _,?_⟩
    simpa only [Function.comp_def,Finset.card_univ,Fintype.card_fin] using
      Finset.card_image_of_injective Finset.univ (w.injective.comp (prefixIndex_injective k))⟩

private def flagPrefixPosition {n : ℕ} (w : Equiv.Perm (Fin n)) (k : Fin n)
    (j : Fin (k.val+1)) : Fin (k.val+1) :=
  ((flagPrefixRows w k).val.orderIsoOfFin
    (Finset.mem_powersetCard.mp (flagPrefixRows w k).property).2).symm
      ⟨w (prefixIndex k j),Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩⟩

private theorem flagPrefixPosition_spec {n : ℕ} (w : Equiv.Perm (Fin n)) (k : Fin n)
    (j : Fin (k.val+1)) :
    (flagPrefixRows w k).rows (flagPrefixPosition w k j) = w (prefixIndex k j) := by
  exact congrArg Subtype.val
    (((flagPrefixRows w k).val.orderIsoOfFin
      (Finset.mem_powersetCard.mp (flagPrefixRows w k).property).2).apply_symm_apply _)

/-- The permutation recording the original order of a sorted Weyl prefix. -/
def flagPrefixPermutation {n : ℕ} (w : Equiv.Perm (Fin n)) (k : Fin n) :
    Equiv.Perm (Fin (k.val+1)) :=
  Equiv.ofBijective (flagPrefixPosition w k) (by
    apply Function.Injective.bijective_of_finite
    intro i j hij
    apply prefixIndex_injective k
    apply w.injective
    rw [← flagPrefixPosition_spec w k i,← flagPrefixPosition_spec w k j,hij])

theorem flagPrefixPermutation_spec {n : ℕ} (w : Equiv.Perm (Fin n)) (k : Fin n)
    (j : Fin (k.val+1)) :
    (flagPrefixRows w k).rows (flagPrefixPermutation w k j) = w (prefixIndex k j) :=
  flagPrefixPosition_spec w k j

theorem flagOrbitRestriction_minor_sorted {n : ℕ} (w : Equiv.Perm (Fin n))
    (z : List (PositiveRoot n × ℂ)) (k : Fin n) (s : Fin (k.val+1) → Fin n) :
    flagOrbitRestriction w (flagRowMinor k s) z =
      (Equiv.Perm.sign (flagPrefixPermutation w k) : ℂ) *
        ((upperRowMatrix z).submatrix s (flagPrefixRows w k).rows).det := by
  rw [flagOrbitRestriction_minor]
  have hm : (upperRowMatrix z * rowPermutationMatrix w).submatrix s (prefixIndex k) =
      ((upperRowMatrix z).submatrix s (flagPrefixRows w k).rows).submatrix
        id (flagPrefixPermutation w k) := by
    apply Matrix.ext
    intro i j
    simp only [Matrix.submatrix_apply,mul_rowPermutationMatrix,id_eq,flagPrefixPermutation_spec]
  rw [hm,Matrix.det_permute']

/-- A forbidden sorted minor vanishes identically on the specified orbit. -/
theorem flagOrbitRestriction_minor_zero {n : ℕ} (w : Equiv.Perm (Fin n))
    (k : Fin n) (S : FlagMinorRowSet k)
    (h : ¬ ∀ i, S.rows i ≤ (flagPrefixRows w k).rows i) :
    flagOrbitRestriction w (flagRowMinor k S.rows) = 0 := by
  funext z
  rw [flagOrbitRestriction_minor_sorted,
    upperTriangular_minor_zero _ (upperRowMatrix_upper z) S.rows (flagPrefixRows w k).rows h,
    mul_zero]
  rfl

/-- The matching prefix minor is a constant sign, hence never vanishes. -/
theorem flagOrbitRestriction_prefix_minor {n : ℕ} (w : Equiv.Perm (Fin n))
    (k : Fin n) (z : List (PositiveRoot n × ℂ)) :
    flagOrbitRestriction w (flagRowMinor k (flagPrefixRows w k).rows) z =
      (Equiv.Perm.sign (flagPrefixPermutation w k) : ℂ) := by
  rw [flagOrbitRestriction_minor_sorted,upperRowMatrix_principal_det,mul_one]

theorem flagOrbitRestriction_prefix_minor_ne_zero {n : ℕ} (w : Equiv.Perm (Fin n))
    (k : Fin n) (z : List (PositiveRoot n × ℂ)) :
    flagOrbitRestriction w (flagRowMinor k (flagPrefixRows w k).rows) z ≠ 0 := by
  rw [flagOrbitRestriction_prefix_minor]
  exact_mod_cast Units.ne_zero (Equiv.Perm.sign (flagPrefixPermutation w k))

end
end Schubert.RS.Representation
