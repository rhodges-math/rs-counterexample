import Mathlib.LinearAlgebra.Basis.Flag
import Mathlib.LinearAlgebra.StdBasis
import RSCounterexample.TypeA.Permutations.Basic

/-!
# Complete flags in a coordinate vector space

This file begins the geometric layer of the project.  It defines an honest
complete flag as a maximal indexed chain of linear subspaces.  This is the
field-valued object represented by the type-`A` complete flag variety.

No representability claim is made here: constructing the scheme representing
this functor is deliberately kept separate from the linear-algebraic object
and from the later affine-patch construction.
-/

namespace Schubert

namespace Geometry

universe u

variable (K : Type u) (n : ℕ)

/-- The standard `n`-dimensional coordinate space over `K`. -/
abbrev CoordinateSpace := Fin n → K

/-- A complete flag in `K^n`, indexed so that `step p` has dimension `p`.

The covering condition is the order-theoretic formulation of the assertion
that consecutive subspaces differ by one dimension.  Together with the two
endpoint conditions it makes the chain maximal. -/
structure CompleteFlag [DivisionRing K] where
  /-- The subspace at each rank from `0` through `n`. -/
  step : Fin (n + 1) → Submodule K (CoordinateSpace K n)
  /-- The rank-zero member is the zero subspace. -/
  step_zero : step 0 = ⊥
  /-- The rank-`n` member is the whole coordinate space. -/
  step_last : step (Fin.last n) = ⊤
  /-- Consecutive members form a cover in the subspace lattice. -/
  step_covBy : ∀ i : Fin n, step i.castSucc ⋖ step i.succ

namespace CompleteFlag

variable {K n} [DivisionRing K]

/-- Consecutive members of a complete flag are nested. -/
theorem step_castSucc_le_step_succ (F : CompleteFlag K n) (i : Fin n) :
    F.step i.castSucc ≤ F.step i.succ :=
  (F.step_covBy i).le

/-- The indexed subspaces of a complete flag are monotone. -/
theorem step_mono (F : CompleteFlag K n) : Monotone F.step :=
  Fin.monotone_iff_le_succ.mpr F.step_castSucc_le_step_succ

/-- Earlier steps of a complete flag are contained in later steps. -/
theorem step_le_step (F : CompleteFlag K n) {p q : Fin (n + 1)}
    (hpq : p ≤ q) : F.step p ≤ F.step q :=
  F.step_mono hpq

/-- Every ordered basis determines a complete flag by taking successive
spans. -/
def ofBasis (b : Module.Basis (Fin n) K (CoordinateSpace K n)) : CompleteFlag K n where
  step := b.flag
  step_zero := b.flag_zero
  step_last := b.flag_last
  step_covBy := b.flag_covBy

/-- The canonical coordinate basis of `K^n`. -/
noncomputable def coordinateBasis : Module.Basis (Fin n) K (CoordinateSpace K n) :=
  Pi.basisFun K (Fin n)

/-- The reference flag
`0 ⊂ <e₁> ⊂ <e₁,e₂> ⊂ ⋯ ⊂ K^n`. -/
noncomputable def referenceFlag : CompleteFlag K n :=
  ofBasis (coordinateBasis (K := K) (n := n))

@[simp]
theorem referenceFlag_step
    (p : Fin (n + 1)) :
    (referenceFlag (K := K) (n := n)).step p =
      (coordinateBasis (K := K) (n := n)).flag p :=
  rfl

/-- Reorder the coordinate basis by a permutation.  Its `i`th vector is
`e_{w(i)}`. -/
noncomputable def permutationBasis (w : FinPermutation n) :
    Module.Basis (Fin n) K (CoordinateSpace K n) :=
  (coordinateBasis (K := K) (n := n)).reindex w.symm

@[simp]
theorem permutationBasis_apply (w : FinPermutation n) (i : Fin n) :
    permutationBasis (K := K) w i =
      coordinateBasis (K := K) (n := n) (w i) := by
  simp [permutationBasis]

/-- The coordinate flag fixed by the permutation `w`; its `p`th member is
spanned by `e_{w(0)},\ldots,e_{w(p-1)}`. -/
noncomputable def permutationFlag (w : FinPermutation n) : CompleteFlag K n :=
  ofBasis (permutationBasis (K := K) w)

@[simp]
theorem permutationFlag_step (w : FinPermutation n) (p : Fin (n + 1)) :
    (permutationFlag (K := K) w).step p =
      (permutationBasis (K := K) w).flag p :=
  rfl

end CompleteFlag

end Geometry

end Schubert
