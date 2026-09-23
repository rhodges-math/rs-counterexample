import Schubert.TypeA.Permutations.RotheDiagram

/-! # Essential permutations -/

namespace Schubert

namespace FinPermutation

variable {n : ℕ}

/-- The paper's essential permutations: Bruhat-minimal permutations outside
the interval below `w`. -/
abbrev essentialSet (w : FinPermutation n) : Set (FinPermutation n) :=
  w.bruhatEssentialSet

/-- The property that every essential permutation is bigrassmannian. -/
def HasBigrassmannianEssentialSet (w : FinPermutation n) : Prop :=
  ∀ v ∈ w.essentialSet, v.IsBigrassmannian

/-- Every essential permutation in rank n is bigrassmannian. -/
def EssentialBigrassmannianProperty (n : ℕ) : Prop :=
  ∀ w : FinPermutation n, w.HasBigrassmannianEssentialSet

/-- Distinct essential permutations are incomparable in strong Bruhat
order.  This is the antichain property used to order inclusion conditions
and to force the genuine mixed crossing inequalities. -/
theorem essentialSet_not_le_of_ne
    {w u v : FinPermutation n}
    (hu : u ∈ w.essentialSet) (hv : v ∈ w.essentialSet)
    (hne : u ≠ v) : ¬ u ≤ᴮ v := by
  intro huv
  exact hu.1 (hv.2 u huv hne)

theorem essentialSet_incomparable_of_ne
    {w u v : FinPermutation n}
    (hu : u ∈ w.essentialSet) (hv : v ∈ w.essentialSet)
    (hne : u ≠ v) : ¬ u ≤ᴮ v ∧ ¬ v ≤ᴮ u := by
  exact ⟨essentialSet_not_le_of_ne hu hv hne,
    essentialSet_not_le_of_ne hv hu hne.symm⟩

/-- Specialize the global essential-bigrassmannian property to one essential
permutation. -/
theorem isBigrassmannian_of_mem_essentialSet
    (h : EssentialBigrassmannianProperty n)
    {w v : FinPermutation n} (hv : v ∈ w.essentialSet) :
    v.IsBigrassmannian :=
  h w v hv

/-- Every permutation outside the principal Bruhat interval above `w` lies
above an essential permutation.  This is the finite-poset fact underlying the
essential-set decomposition. -/
theorem exists_mem_essentialSet_le_of_not_le
    {w u : FinPermutation n} (hu : ¬u ≤ᴮ w) :
    ∃ v : FinPermutation n, v ∈ w.essentialSet ∧ v ≤ᴮ u := by
  letI : PartialOrder (FinPermutation n) := strongBruhatPartialOrder n
  let S : Set (FinPermutation n) := {x | ¬x ≤ w ∧ x ≤ u}
  have huS : u ∈ S := ⟨hu, le_rfl⟩
  obtain ⟨v, hv⟩ := (Set.toFinite S).exists_minimal ⟨u, huS⟩
  refine ⟨v, ?_, hv.1.2⟩
  refine ⟨hv.1.1, ?_⟩
  intro z hzv hne
  by_contra hzw
  have hzS : z ∈ S := ⟨hzw, strongBruhat_trans hzv hv.1.2⟩
  have hvz : v ≤ z := hv.2 hzS hzv
  exact hne (le_antisymm hzv hvz)

end FinPermutation

end Schubert
