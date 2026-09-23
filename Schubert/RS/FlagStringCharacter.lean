import Schubert.RS.FlagRootStringBasis
import Schubert.RS.FlagCharacterInduction

namespace Schubert.RS.Representation
noncomputable section
open FinPermutation

theorem polynomial_weight_nonnegative {n : ℕ} (p : MatrixPolynomial n) (hp0 : p≠0)
    (v : Weight n) (hp : ∀ t, polynomialTorus n t p=integerWeightScalar v t • p) :
    ∀ i, 0≤v i := by
  obtain ⟨d,hd⟩ : ∃ d, MvPolynomial.coeff d p≠0 := by
    by_contra hn
    push Not at hn
    apply hp0
    ext d
    simpa using hn d
  have he : matrixMonomialWeight d=v := by
    apply integerWeightScalar_injective
    funext t
    apply mul_right_cancel₀ hd
    rw [← polynomialTorus_coeff_weight,hp,MvPolynomial.coeff_smul,smul_eq_mul]
  intro i
  rw [← he]
  exact Int.natCast_nonneg _

def nonnegativeWeightExponent {n : ℕ} (v : Weight n) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (v i).toNat)

theorem nonnegativeWeightExponent_weight {n : ℕ} (v : Weight n) (hv : ∀ i, 0≤v i) :
    exponentWeight (nonnegativeWeightExponent v)=v := by
  funext i
  change ((v i).toNat : ℤ)=v i
  exact Int.toNat_of_nonneg (hv i)

def PolynomialRootStringBasis.character {n : ℕ} {a b : Fin n}
    {S : Submodule ℂ (MatrixPolynomial n)} (B : PolynomialRootStringBasis a b S) : RS.Polynomial n :=
  labelledCharacter (fun j : (Σ i,Fin (B.length i+1)) =>
    nonnegativeWeightExponent (B.weight j.1+j.2.val • positiveRoot a b))

theorem PolynomialRootStringBasis.hasFlagCharacter {n : ℕ} {a b : Fin n}
    {m : ColumnShape n} {w : Equiv.Perm (Fin n)}
    (B : PolynomialRootStringBasis a b (flagDemazure m w)) :
    HasTorusCharacter (flagTorus m w) B.character := by
  apply hasTorusCharacter_of_eigenbasis (flagTorus m w) B.basis
  intro t j
  have hn : ∀ i, 0≤(B.weight j.1+j.2.val • positiveRoot a b) i :=
    polynomial_weight_nonnegative _
      (derivationIter_ne_zero_of_le _ _ (by omega) (B.top_ne_zero j.1)) _
      (matrixUnit_derivationIter_weight a b (B.seed j.1) (B.weight j.1) (B.seed_weight j.1) j.2.val)
  rw [nonnegativeWeightExponent_weight _ hn]
  exact B.flag_basis_weight t j

/-- An explicit polynomial character exists for the actual composition module
at any positive root. Its identification with the key is a separate theorem. -/
theorem exists_composition_character_at_root {n : ℕ} (u : Composition n) (r : PositiveRoot n) :
    ∃ p : RS.Polynomial n, HasTorusCharacter (compositionFlagTorus u) p := by
  obtain ⟨B⟩ := exists_compositionRootStringBasis u r
  exact ⟨B.character,B.hasFlagCharacter⟩

/-- Adjacent character recursion implies the Demazure character formula. -/
theorem compositionFlagDemazureCharacter_of_adjacent_character_recursion {n : ℕ}
    (hstep : ∀ u : Composition n, ¬Antitone u →
      ∃ (i : AdjacentPosition n), u i.left<u i.right ∧
        ∃ p : RS.Polynomial n,
          HasTorusCharacter (compositionFlagTorus (swapComposition u i)) p ∧
          HasTorusCharacter (compositionFlagTorus u) (isobaric i p)) :
    ∀ u : Composition n, CompositionFlagDemazureCharacter u := by
  intro u
  induction u using (measure sortingMeasure).wf.induction with
  | h u ih =>
    by_cases hu : Antitone u
    · exact compositionFlagDemazureCharacter_of_antitone u hu
    obtain ⟨i,hi,p,hprev,hnext⟩ := hstep u hu
    have hkey := (compositionFlagDemazureCharacter_iff_character _).mp (ih _ (sortingMeasure_swap_lt u i hi))
    have he := hprev.unique hkey
    apply (compositionFlagDemazureCharacter_iff_character u).mpr
    rw [key_any_ascent u i hi,← he]
    exact hnext

end
end Schubert.RS.Representation
