import Schubert.TypeA.Permutations.NorthwestRankBounds

/-!
# Bruhat duality from the longest permutation

Postcomposing a permutation with `Fin.revPerm` complements its values.  On
northwest ranks this exchanges a value cutoff with its complementary cutoff,
and hence reverses strong Bruhat order.  The arbitrary natural-cutoff form is
convenient for constructing the maximal permutation which avoids one fixed
bigrassmannian rank condition.
-/

namespace Schubert

namespace FinPermutation

noncomputable section

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

variable {n : ℕ}

/-- Northwest ranks at complementary value cutoffs partition a prefix after
postcomposition with the longest permutation. -/
theorem northwestRankNat_trans_revPerm_add
    (w : FinPermutation n) (R S : ℕ) (hR : R ≤ n) (hS : S ≤ n) :
    northwestRankNat (w.trans (Fin.revPerm : FinPermutation n)) R S +
        northwestRankNat w R (n - S) = R := by
  classical
  let P := Finset.univ.filter (fun i : Fin n ↦ i.1 < R)
  let L := P.filter (fun i : Fin n ↦ (w i).1 < n - S)
  let H := P.filter (fun i : Fin n ↦ ¬ (w i).1 < n - S)
  have hpart := Finset.card_filter_add_card_filter_not
    (s := P) (fun i : Fin n ↦ (w i).1 < n - S)
  have hP : P.card = R := by
    exact card_filter_fin_val_lt R hR
  have hL : L.card = northwestRankNat w R (n - S) := by
    congr 1
    ext i
    simp [L, P, northwestRankNat]
  have hH : H.card =
      northwestRankNat
        (w.trans (Fin.revPerm : FinPermutation n)) R S := by
    congr 1
    ext i
    simp only [H, P, northwestRankNat, Finset.mem_filter,
      Finset.mem_univ, true_and, Equiv.trans_apply, Fin.revPerm_apply,
      Fin.rev, Fin.val_mk]
    constructor
    · rintro ⟨hi, hv⟩
      exact ⟨hi, by omega⟩
    · rintro ⟨hi, hv⟩
      exact ⟨hi, by omega⟩
  rw [← hH, ← hL, add_comm, hpart, hP]

/-- Postcomposition with the longest permutation reverses strong Bruhat
order. -/
theorem strongBruhatLE_trans_revPerm_iff (u v : FinPermutation n) :
    u.trans (Fin.revPerm : FinPermutation n) ≤ᴮ
        v.trans (Fin.revPerm : FinPermutation n) ↔ v ≤ᴮ u := by
  rw [strongBruhatLE_iff_northwestRankNat_all,
    strongBruhatLE_iff_northwestRankNat_all]
  constructor
  · intro h R S hR hS
    have hcomp := h R (n - S) hR (Nat.sub_le n S)
    have hu := northwestRankNat_trans_revPerm_add u R (n - S) hR
      (Nat.sub_le n S)
    have hv := northwestRankNat_trans_revPerm_add v R (n - S) hR
      (Nat.sub_le n S)
    rw [Nat.sub_sub_self hS] at hu hv
    omega
  · intro h R S hR hS
    have hcomp := h R (n - S) hR (Nat.sub_le n S)
    have hu := northwestRankNat_trans_revPerm_add u R S hR hS
    have hv := northwestRankNat_trans_revPerm_add v R S hR hS
    omega

/-- A form of longest-element duality with the transformed permutations on
the right of the equivalence. -/
theorem strongBruhatLE_iff_trans_revPerm_reverse (u v : FinPermutation n) :
    u ≤ᴮ v ↔
      v.trans (Fin.revPerm : FinPermutation n) ≤ᴮ
        u.trans (Fin.revPerm : FinPermutation n) := by
  simpa using (strongBruhatLE_trans_revPerm_iff v u).symm

end

end FinPermutation

end Schubert
