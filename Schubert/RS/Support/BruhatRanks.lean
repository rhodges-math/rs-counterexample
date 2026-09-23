import Schubert.TypeA.Permutations.Bruhat

/-! Elementary northwest ranks and inversion symmetry of Bruhat order.
Extracted without the unrelated inclusion-ideal developments. -/
namespace Schubert.FinPermutation
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq
variable {n : ℕ}

def northwestRankNat (w : FinPermutation n) (r s : ℕ) : ℕ :=
  (Finset.univ.filter fun i : Fin n ↦ i.1 < r ∧ (w i).1 < s).card

/-- Southwest rank and the complementary northwest rank partition a prefix. -/
theorem bruhatRank_add_northwestRankNat
    (w : FinPermutation n) (p q : Fin n) :
    w.bruhatRank p q + northwestRankNat w (p.1 + 1) q.1 = p.1 + 1 := by
  classical
  let P := Finset.Iic p
  let H := P.filter (fun i => q ≤ w i)
  let L := P.filter (fun i => ¬ q ≤ w i)
  have hpart := Finset.card_filter_add_card_filter_not
    (s := P) (fun i => q ≤ w i)
  have hH : H.card = w.bruhatRank p q := by
    congr 1
    ext i
    simp [H, P, bruhatRank]
  have hL : L.card = northwestRankNat w (p.1 + 1) q.1 := by
    congr 1
    ext i
    simp [L, P, northwestRankNat, not_le]
  have hP : P.card = p.1 + 1 := by simp [P]
  rw [← hH, ← hL, ← hP]
  simpa [H, L] using hpart

/-- Strong Bruhat order in the equivalent northwest-rank convention. -/
theorem strongBruhatLE_iff_northwestRankNat
    (u v : FinPermutation n) :
    u ≤ᴮ v ↔
      ∀ p q : Fin n,
        northwestRankNat v (p.1 + 1) q.1 ≤
          northwestRankNat u (p.1 + 1) q.1 := by
  constructor
  · intro huv p q
    have h := huv p q
    have hu := bruhatRank_add_northwestRankNat u p q
    have hv := bruhatRank_add_northwestRankNat v p q
    omega
  · intro hnw p q
    have h := hnw p q
    have hu := bruhatRank_add_northwestRankNat u p q
    have hv := bruhatRank_add_northwestRankNat v p q
    omega

/-- Northwest ranks transpose under inversion. -/
theorem northwestRankNat_symm (w : FinPermutation n) (r s : ℕ) :
    northwestRankNat (w.symm : FinPermutation n) r s =
      northwestRankNat w s r := by
  classical
  unfold northwestRankNat
  apply Finset.card_bij (fun i _ => w.symm i)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    simpa using ⟨hi.2, hi.1⟩
  · intro i hi j hj hij
    exact w.symm.injective hij
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    refine ⟨w j, ?_, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simpa using ⟨hj.2, hj.1⟩

/-- Northwest-rank formulation with arbitrary natural cutoffs in the closed
range `0,…,n`; this form is symmetric in positions and values. -/
theorem strongBruhatLE_iff_northwestRankNat_all
    (u v : FinPermutation n) :
    u ≤ᴮ v ↔
      ∀ r s : ℕ, r ≤ n → s ≤ n →
        northwestRankNat v r s ≤ northwestRankNat u r s := by
  constructor
  · intro huv r s hr hs
    by_cases hr0 : r = 0
    · subst r
      simp [northwestRankNat]
    by_cases hs0 : s = 0
    · subst s
      simp [northwestRankNat]
    by_cases hsn : s = n
    · subst s
      have hfull : ∀ w : FinPermutation n,
          northwestRankNat w r n =
            (Finset.univ.filter fun i : Fin n => i.1 < r).card := by
        intro w
        unfold northwestRankNat
        congr 1
        ext i
        simp [w i |>.isLt]
      rw [hfull v, hfull u]
    · let p : Fin n := ⟨r - 1, by omega⟩
      let q : Fin n := ⟨s, by omega⟩
      have h := (strongBruhatLE_iff_northwestRankNat u v).mp huv p q
      simpa [p, q, Nat.sub_add_cancel (Nat.pos_of_ne_zero hr0)] using h
  · intro h
    apply (strongBruhatLE_iff_northwestRankNat u v).mpr
    intro p q
    exact h (p.1 + 1) q.1 (by omega) (by omega)

/-- Strong Bruhat order is invariant under inversion. -/
theorem strongBruhatLE_symm_iff (u v : FinPermutation n) :
    (u.symm : FinPermutation n) ≤ᴮ (v.symm : FinPermutation n) ↔ u ≤ᴮ v := by
  rw [strongBruhatLE_iff_northwestRankNat_all,
    strongBruhatLE_iff_northwestRankNat_all]
  constructor
  · intro h r s hr hs
    simpa only [northwestRankNat_symm] using h s r hs hr
  · intro h r s hr hs
    simpa only [northwestRankNat_symm] using h s r hs hr


end
end Schubert.FinPermutation
