import Schubert.RS.JosephPolo.WeylSaturation
import Schubert.TypeA.Permutations.BruhatGraded
import Schubert.RS.Support.BruhatRanks

namespace Schubert.RS.Representation
noncomputable section
open FinPermutation

private theorem rightAdjacentSwap_symm {n : ℕ} (w : FinPermutation n) (i : AdjacentPosition n) :
    (w.rightAdjacentSwap i).symm = Equiv.swap i.left i.right * w.symm := by
  rfl

/-- Bruhat monotonicity of the independent polynomial modules, proved by
adjacent lifting and actual saturation, without a character formula. -/
theorem flagDemazure_symm_mono {n : ℕ} (m : ColumnShape n) {u v : FinPermutation n}
    (huv : u ≤ᴮ v) : flagDemazure m u.symm ≤ flagDemazure m v.symm := by
  generalize hl : v.length = l
  induction l using Nat.strong_induction_on generalizing u v with
  | h l ih =>
    by_cases hvrefl : v = Equiv.refl (Fin n)
    · subst v
      have hueq : u = Equiv.refl (Fin n) :=
        strongBruhat_antisymm huv (refl_strongBruhatLE u)
      rw [hueq]
    · obtain ⟨i,j,hj,hd⟩ := exists_descent_of_ne_refl v hvrefl
      let a : AdjacentPosition n := ⟨i,by rw [← hj]; exact j.isLt⟩
      have hv : v.HasDescent a.left := ⟨j,hj,hd⟩
      have hvlt : (v.rightAdjacentSwap a).length < l := by
        have := length_rightAdjacentSwap_of_descent v a hv
        omega
      have hvd := (hasDescent_left_iff v a).mp hv
      have hsatv : loweringSaturation a.left a.right
          (flagDemazure m (v.rightAdjacentSwap a).symm) = flagDemazure m v.symm := by
        rw [rightAdjacentSwap_symm]
        exact flagDemazure_adjacent_saturation_of_inverse_descent m v.symm a hvd
      rcases descent_or_ascent u a with hu | hu
      · have hsmaller := rightAdjacentSwap_strongBruhatLE_of_both_descent a huv hu hv
        have hind := ih (v.rightAdjacentSwap a).length hvlt hsmaller rfl
        have hsatu : loweringSaturation a.left a.right
            (flagDemazure m (u.rightAdjacentSwap a).symm) = flagDemazure m u.symm := by
          rw [rightAdjacentSwap_symm]
          exact flagDemazure_adjacent_saturation_of_inverse_descent m u.symm a
            ((hasDescent_left_iff u a).mp hu)
        rw [← hsatu,← hsatv]
        exact loweringSaturation_mono a.left a.right hind
      · have hsmaller := strongBruhatLE_rightAdjacentSwap_of_ascent_descent a huv hu hv
        have hind := ih (v.rightAdjacentSwap a).length hvlt hsmaller rfl
        exact hind.trans (by rw [← hsatv]; exact le_loweringSaturation _ _ _)

theorem flagDemazure_mono {n : ℕ} (m : ColumnShape n) {u v : FinPermutation n}
    (huv : u ≤ᴮ v) : flagDemazure m u ≤ flagDemazure m v :=
  flagDemazure_symm_mono m (u := u.symm) (v := v.symm)
    ((strongBruhatLE_symm_iff u v).mpr huv)

/-- Vanishing on a larger Bruhat orbit transfers to the smaller one for
every polynomial in the fixed-shape minor-product span. -/
theorem flagOrbitRestriction_zero_of_bruhat {n : ℕ} (m : ColumnShape n)
    {u v : FinPermutation n} (huv : u ≤ᴮ v) (q : MatrixPolynomial n)
    (hq : q ∈ Submodule.span ℂ (Set.range (flagTableauPolynomial m)))
    (hz : flagOrbitRestriction v q = 0) : flagOrbitRestriction u q = 0 :=
  flagOrbitRestriction_zero_of_flagDemazure_le m u v (flagDemazure_mono m huv) q hq hz

end
end Schubert.RS.Representation
