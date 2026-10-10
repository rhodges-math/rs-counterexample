import RSCounterexample.FlagVarieties.Modules.Character
import Mathlib.Data.Fin.Tuple.Sort

/-!
# The Schubert index and the fibre weight of a weight

Following van der Kallen [*Lectures on Frobenius splittings and B-modules*, Definitions 2.3.2 and
2.3.4], a weight `ν ∈ ℤⁿ` determines

* its **fibre weight** `η = η(ν)`, the weakly increasing (antidominant) rearrangement of `ν`
  (`FlagVarieties.fibreWeight`);
* its **Schubert index** `σ = σ(ν)`, the shortest permutation with `σ · η = ν`, where
  `(σ · η)ᵢ = η_{σ⁻¹(i)}` (`FlagVarieties.schubertIndex`).

The dual Joseph module is then `P(ν) = H⁰(X_σ, 𝓛(η))`, and the minimal relative Schubert module
`Q(ν)` is the kernel of the restriction from `X_σ` to its boundary.

We take `σ = Tuple.sort ν`, the permutation sorting `ν` into weakly increasing order with ties
kept in index order, and `η = ν ∘ σ`. That `σ` is shortest is the tie condition
(`FlagVarieties.schubertIndex_lt_of_fibreWeight_eq`): `σ` is increasing on each block of equal
entries of `η`. Together with `σ · η = ν` this characterizes `σ`
(`FlagVarieties.eq_schubertIndex_iff`).
-/

namespace FlagVarieties

variable {n : ℕ}

/-- The **Schubert index** `σ(ν)` of a weight `ν ∈ ℤⁿ`: the permutation sorting `ν` into weakly
increasing order, ties kept in index order. It is the shortest permutation with
`σ · η(ν) = ν`. -/
def schubertIndex (ν : Fin n → ℤ) : Equiv.Perm (Fin n) := Tuple.sort ν

/-- The **fibre weight** `η(ν) = ν ∘ σ(ν)`: the weakly increasing rearrangement of `ν`. -/
def fibreWeight (ν : Fin n → ℤ) : Fin n → ℤ := ν ∘ schubertIndex ν

theorem fibreWeight_apply (ν : Fin n → ℤ) (i : Fin n) :
    fibreWeight ν i = ν (schubertIndex ν i) :=
  rfl

/-- The fibre weight is antidominant (weakly increasing). -/
theorem isAntidominant_fibreWeight (ν : Fin n → ℤ) : IsAntidominant (fibreWeight ν) :=
  Tuple.monotone_sort ν

/-- **`σ · η = ν`**: `η_{σ⁻¹(i)} = νᵢ`. -/
theorem fibreWeight_schubertIndex_symm (ν : Fin n → ℤ) (i : Fin n) :
    fibreWeight ν ((schubertIndex ν).symm i) = ν i := by
  rw [fibreWeight_apply, Equiv.apply_symm_apply]

/-- **`σ` is shortest**: it is increasing on each block of equal entries of `η`. -/
theorem schubertIndex_lt_of_fibreWeight_eq (ν : Fin n → ℤ) {i j : Fin n} (hij : i < j)
    (he : fibreWeight ν i = fibreWeight ν j) : schubertIndex ν i < schubertIndex ν j :=
  (Tuple.eq_sort_iff.mp rfl).2 i j hij he

/-- The Schubert index is the only permutation `σ` such that `ν ∘ σ` is weakly increasing and `σ`
is increasing on the blocks where `ν ∘ σ` is constant. -/
theorem eq_schubertIndex_iff (ν : Fin n → ℤ) (σ : Equiv.Perm (Fin n)) :
    σ = schubertIndex ν ↔
      Monotone (ν ∘ σ) ∧ ∀ i j, i < j → ν (σ i) = ν (σ j) → σ i < σ j :=
  Tuple.eq_sort_iff

/-- The Schubert index of an antidominant weight is the identity. -/
theorem schubertIndex_eq_one_iff (ν : Fin n → ℤ) : schubertIndex ν = 1 ↔ IsAntidominant ν :=
  Tuple.sort_eq_refl_iff_monotone

/-- An antidominant weight is its own fibre weight. -/
theorem fibreWeight_eq_self {ν : Fin n → ℤ} (hν : IsAntidominant ν) : fibreWeight ν = ν := by
  rw [fibreWeight, (schubertIndex_eq_one_iff ν).mpr hν]
  rfl

/-- Rearranging a weight does not change its shift `max(0, max ν)`. -/
theorem weightShift_comp_perm (ν : Fin n → ℤ) (τ : Equiv.Perm (Fin n)) :
    weightShift (ν ∘ τ) = weightShift ν := by
  unfold weightShift
  apply le_antisymm
  · exact Finset.sup_le fun i _ => Finset.le_sup (f := fun i => (ν i).toNat) (Finset.mem_univ (τ i))
  · refine Finset.sup_le fun i _ => ?_
    have := Finset.le_sup (f := fun i => ((ν ∘ τ) i).toNat) (Finset.mem_univ (τ.symm i))
    simpa using this

theorem weightShift_fibreWeight (ν : Fin n → ℤ) : weightShift (fibreWeight ν) = weightShift ν :=
  weightShift_comp_perm ν _

theorem weightComplement_fibreWeight (ν : Fin n → ℤ) :
    weightComplement (fibreWeight ν) = weightComplement ν ∘ schubertIndex ν := by
  funext i
  simp only [weightComplement, weightShift_fibreWeight, fibreWeight_apply, Function.comp_apply]

/-! ### Negatives of weak compositions -/

/-- The weight `−u` of a weak composition `u ∈ ℕⁿ`. -/
def negWeight (u : Fin n → ℕ) : Fin n → ℤ := fun i => -(u i : ℤ)

theorem weightShift_negWeight (u : Fin n → ℕ) : weightShift (negWeight u) = 0 := by
  refine Nat.eq_zero_of_le_zero (Finset.sup_le fun i _ => ?_)
  simp [negWeight]

theorem weightComplement_negWeight (u : Fin n → ℕ) : weightComplement (negWeight u) = u := by
  funext i
  simp [weightComplement, weightShift_negWeight, negWeight]

end FlagVarieties
