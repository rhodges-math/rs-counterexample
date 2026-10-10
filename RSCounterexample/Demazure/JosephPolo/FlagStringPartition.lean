import RSCounterexample.Demazure.JosephPolo.StringPartitions
import RSCounterexample.Demazure.JosephPolo.ColumnPartition
import RSCounterexample.Demazure.JosephPolo.MovingChainStrings

/-!
# Partitions of tableaux into strings

`FiniteStringPartition X` partitions a finite type into finite nonempty strings. Tensoring with a
new column (`FiniteStringPartition.tensorColumn`) builds, column by column, the string partition
`flagStringPartition i d h` of all tuples of row sets for an adjacent position `i`.
-/

open Schubert

namespace Demazure.FlagModule
noncomputable section
open FinPermutation
attribute [local instance] Classical.propDecidable

/-- A finite set partitioned into finite nonempty strings. The equivalence
certifies disjointness and exhaustion, including all multiplicities. -/
structure FiniteStringPartition (X : Type) where
  /-- The index type of the strings. -/
  Index : Type
  finiteIndex : Fintype Index
  /-- The length of each string; string `a` has `length a + 1` elements. -/
  length : Index → ℕ
  /-- The identification of the disjoint union of the strings with the partitioned type. -/
  position : (Σ a : Index, Fin (length a + 1)) ≃ X

attribute [instance] FiniteStringPartition.finiteIndex

/-- Transport of a string partition along an equivalence. -/
def FiniteStringPartition.map {X Y : Type} (S : FiniteStringPartition X)
    (e : X ≃ Y) : FiniteStringPartition Y :=
  ⟨S.Index,S.finiteIndex,S.length,S.position.trans e⟩

/-- The string partition of `FlagMinorRowSet k × X` obtained from a partition of `X` and the
partition of row sets along the adjacent position `i`. -/
def FiniteStringPartition.tensorColumn {n : ℕ} {X : Type}
    (S : FiniteStringPartition X) (i : AdjacentPosition n) (k : Fin n) :
    FiniteStringPartition (FlagMinorRowSet k × X) where
  Index := TensorStringHead (FixedFlagColumns i k) (RaisedFlagColumns i k) S.Index S.length
  finiteIndex := inferInstance
  length := tensorStringLength S.length
  position := (tensorStringPositions S.length).trans
    (Equiv.prodCongr (flagColumnPartition i k).symm S.position)

/-- The partition of the families indexed by `Fin 0` into one string of length zero. -/
def emptyFlagStringPartition {n : ℕ} (h : Fin 0 → Fin n) :
    FiniteStringPartition ((j : Fin 0) → FlagMinorRowSet (h j)) where
  Index := Unit
  finiteIndex := inferInstance
  length := fun _ => 0
  position := {
    toFun := fun _ j => Fin.elim0 j
    invFun := fun _ => ⟨(),0⟩
    left_inv := fun ⟨a,k⟩ => by
      cases a
      have hk : k = 0 := Fin.ext (by have hk : k.val < 1 := k.isLt; omega)
      subst k
      rfl
    right_inv := fun f => funext fun j => Fin.elim0 j }

/-- The string partition of the families of row sets along the adjacent position `i`, built one
column at a time. -/
def flagStringPartition {n : ℕ} (i : AdjacentPosition n) (d : ℕ)
    (h : Fin d → Fin n) : FiniteStringPartition ((j : Fin d) → FlagMinorRowSet (h j)) :=
  match d with
  | 0 => emptyFlagStringPartition h
  | d+1 =>
    ((flagStringPartition i d (fun j => h j.castSucc)).tensorColumn i (h (Fin.last d))).map
      (Fin.snocEquiv (fun j => FlagMinorRowSet (h j)))

theorem emptyFlagDefiningChain {n : ℕ} (h : Fin 0 → Fin n)
    (T : (j : Fin 0) → FlagMinorRowSet (h j)) (w : FinPermutation n) :
    HasFlagDefiningChain h T w := by
  exact ⟨fun j => Fin.elim0 j,fun j => Fin.elim0 j,
    fun j => Fin.elim0 j,fun j => Fin.elim0 j⟩

end
end Demazure.FlagModule
