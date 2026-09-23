import Schubert.RS.JosephPolo.StringPartitions
import Schubert.RS.JosephPolo.ColumnPartition
import Schubert.RS.JosephPolo.MovingChainStrings

namespace Schubert.RS.Representation
noncomputable section
open FinPermutation
attribute [local instance] Classical.propDecidable

/-- A finite set partitioned into finite nonempty strings. The equivalence
certifies disjointness and exhaustion, including all multiplicities. -/
structure FiniteStringPartition (X : Type) where
  Index : Type
  finiteIndex : Fintype Index
  length : Index → ℕ
  position : (Σ a : Index, Fin (length a + 1)) ≃ X

attribute [instance] FiniteStringPartition.finiteIndex

def FiniteStringPartition.map {X Y : Type} (S : FiniteStringPartition X)
    (e : X ≃ Y) : FiniteStringPartition Y :=
  ⟨S.Index,S.finiteIndex,S.length,S.position.trans e⟩

def FiniteStringPartition.tensorColumn {n : ℕ} {X : Type}
    (S : FiniteStringPartition X) (i : AdjacentPosition n) (k : Fin n) :
    FiniteStringPartition (FlagMinorRowSet k × X) where
  Index := TensorStringHead (FixedFlagColumns i k) (RaisedFlagColumns i k) S.Index S.length
  finiteIndex := inferInstance
  length := tensorStringLength S.length
  position := (tensorStringPositions S.length).trans
    (Equiv.prodCongr (flagColumnPartition i k).symm S.position)

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
end Schubert.RS.Representation
