import Schubert.RS.Representation.WeightFiltration
import Schubert.RS.Representation.RankOneCharacter

namespace Schubert.RS.Representation
noncomputable section
open FinPermutation Schubert
open scoped BigOperators

/-- A polynomial represents the dimensions of the actual full-torus eigenspaces. -/
def HasTorusCharacter {n : ℕ} {E : Type*} [AddCommGroup E] [Module ℂ E]
    (ρ : DiagonalTorus n →* Module.End ℂ E) (p : RS.Polynomial n) : Prop :=
  ∀ w, (Module.finrank ℂ (torusWeightSpace ρ w) : ℤ) = (toLaurent p).coeff w

def labelledCharacter {n : ℕ} {I : Type*} [Fintype I]
    (a : I → Fin n →₀ ℕ) : RS.Polynomial n := ∑ j, MvPolynomial.monomial (a j) 1

theorem labelledCharacter_coeff {n : ℕ} {I : Type*} [Fintype I]
    (a : I → Fin n →₀ ℕ) (w : Weight n) :
    (toLaurent (labelledCharacter a)).coeff w =
      (Fintype.card {j : I // exponentWeight (a j) = w} : ℤ) := by
  classical
  simp [labelledCharacter, map_sum, AddMonoidAlgebra.coeff_sum,
    Fintype.card_subtype, Finsupp.single_apply, eq_comm]

theorem WeightBasisFiltration.character {n : ℕ} {E : Type*}
    [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    {ρ : DiagonalTorus n →* Module.End ℂ E} {L : ℕ}
    {I : Fin L → Type*} [∀ k, Fintype (I k)] (a : ∀ k, I k → Fin n →₀ ℕ)
    (F : WeightBasisFiltration ρ L I (fun k j => exponentWeight (a k j))) :
    HasTorusCharacter ρ (∑ k, labelledCharacter (a k)) := by
  intro w
  rw [F.finrank]
  simp [map_sum, AddMonoidAlgebra.coeff_sum, labelledCharacter_coeff]

/-- Index zero is the low endpoint and index `d` the highest endpoint. -/
def selectedStringWeight {n : ℕ} (i : AdjacentPosition n) (a : Fin n →₀ ℕ)
    (full : Bool) : Fin (if full then a i.left - a i.right + 1 else 1) → Fin n →₀ ℕ :=
  match full with
  | true => stringWeight i a
  | false => fun _ => a

theorem selectedStringCharacter {n : ℕ} (i : AdjacentPosition n) (a : Fin n →₀ ℕ)
    (full : Bool) :
    labelledCharacter (selectedStringWeight i a full) =
      if full then labelledCharacter (stringWeight i a) else MvPolynomial.monomial a 1 := by
  cases full <;> simp [selectedStringWeight, labelledCharacter]

theorem stringCharacter_isobaric {n : ℕ} (i : AdjacentPosition n) (a : Fin n →₀ ℕ)
    (ha : a i.right ≤ a i.left) :
    labelledCharacter (stringWeight i a) = isobaric i (MvPolynomial.monomial a 1) := by
  unfold labelledCharacter
  rw [← cyclicCharacter_eq_sum]
  exact cyclicCharacter_eq_isobaric i a ha

theorem isobaric_selectedStringCharacter {n : ℕ} (i : AdjacentPosition n)
    (a : Fin n →₀ ℕ) (ha : a i.right ≤ a i.left) (full : Bool) :
    isobaric i (labelledCharacter (selectedStringWeight i a full)) =
      labelledCharacter (stringWeight i a) := by
  rw [selectedStringCharacter, stringCharacter_isobaric i a ha]
  cases full <;> simp

/-- Spectral part of a common string filtration: exact maps, not a character
identity. Every target factor is a full string; the corresponding source is
exactly its highest line or the full string, with repetitions retained by `k`.
The stronger compatibility with the raising/lowering operators is stated below. -/
structure StringSpectralFiltration {n : ℕ} {M N : Type*}
    [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
    (σ : DiagonalTorus n →* Module.End ℂ M)
    (ρ : DiagonalTorus n →* Module.End ℂ N) (i : AdjacentPosition n) (L : ℕ) where
  endpoint : Fin L → Fin n →₀ ℕ
  dominant : ∀ k, endpoint k i.right ≤ endpoint k i.left
  full : Fin L → Bool
  source : WeightBasisFiltration σ L
    (fun k => Fin (if full k then endpoint k i.left - endpoint k i.right + 1 else 1))
    (fun k j => exponentWeight (selectedStringWeight i (endpoint k) (full k) j))
  target : WeightBasisFiltration ρ L
    (fun k => Fin (endpoint k i.left - endpoint k i.right + 1))
    (fun k j => exponentWeight (stringWeight i (endpoint k) j))

theorem StringSpectralFiltration.character_recursion {n : ℕ} {M N : Type*}
    [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
    [AddCommGroup N] [Module ℂ N] [FiniteDimensional ℂ N]
    {σ : DiagonalTorus n →* Module.End ℂ M}
    {ρ : DiagonalTorus n →* Module.End ℂ N} {i : AdjacentPosition n} {L : ℕ}
    (F : StringSpectralFiltration σ ρ i L) :
    ∃ p : RS.Polynomial n, HasTorusCharacter σ p ∧ HasTorusCharacter ρ (isobaric i p) := by
  classical
  refine ⟨∑ k, labelledCharacter (selectedStringWeight i (F.endpoint k) (F.full k)),
    F.source.character _, ?_⟩
  have hadd (s : Finset (Fin L)) :
      isobaric i (∑ k ∈ s, labelledCharacter
        (selectedStringWeight i (F.endpoint k) (F.full k))) =
        ∑ k ∈ s, labelledCharacter (stringWeight i (F.endpoint k)) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert k s hk ih =>
      simp only [Finset.sum_insert hk, isobaric_add, ih,
        isobaric_selectedStringCharacter i _ (F.dominant k)]
  rw [hadd]
  exact F.target.character _


theorem HasTorusCharacter.unique {n : ℕ} {E : Type*}
    [AddCommGroup E] [Module ℂ E] {ρ : DiagonalTorus n →* Module.End ℂ E}
    {p q : RS.Polynomial n} (hp : HasTorusCharacter ρ p) (hq : HasTorusCharacter ρ q) :
    p = q := by
  apply toLaurent_injective
  ext w
  exact (hp w).symm.trans (hq w)

theorem StringSpectralFiltration.character_recursion_of_character {n : ℕ} {M N : Type*}
    [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
    [AddCommGroup N] [Module ℂ N] [FiniteDimensional ℂ N]
    {σ : DiagonalTorus n →* Module.End ℂ M}
    {ρ : DiagonalTorus n →* Module.End ℂ N} {i : AdjacentPosition n} {L : ℕ}
    (F : StringSpectralFiltration σ ρ i L) {p : RS.Polynomial n}
    (hp : HasTorusCharacter σ p) : HasTorusCharacter ρ (isobaric i p) := by
  obtain ⟨q, hq, hn⟩ := F.character_recursion
  rw [hp.unique hq]
  exact hn

end
end Schubert.RS.Representation

