import Schubert.RS.LayeredPathFamilies
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-! Expand a determinant of path sums and apply the paper's tail cancellation. -/

namespace Schubert.RS
noncomputable section
variable {V : Type*} {d T : ℕ}

@[ext] structure LayeredPath (E : Fin T → V → V → Prop) (a b : V) where
  vertex : Fin (T + 1) → V
  start : vertex 0 = a
  finish : vertex (Fin.last T) = b
  edges : ∀ k, E k (vertex k.castSucc) (vertex k.succ)

variable {E : Fin T → V → V → Prop} {s f : Fin d → V}

instance [Fintype V] (a b : V) : Fintype (LayeredPath E a b) := by
  classical
  apply Fintype.ofInjective LayeredPath.vertex
  intro P Q h
  exact LayeredPath.ext h

def pathFamilyEquiv :
    (Σ σ : Equiv.Perm (Fin d), ∀ i, LayeredPath E (s i) (f (σ i))) ≃
      LayeredPathFamily E s f where
  toFun P :=
    { matching := P.1
      path := fun i => (P.2 i).vertex
      start := fun i => (P.2 i).start
      finish := fun i => (P.2 i).finish
      edges := fun i => (P.2 i).edges }
  invFun P := ⟨P.matching, fun i =>
    { vertex := P.path i
      start := P.start i
      finish := P.finish i
      edges := P.edges i }⟩
  left_inv P := by
    rcases P with ⟨σ, p⟩
    congr 1
  right_inv P := by
    apply LayeredPathFamily.ext <;> rfl

def layeredPathWeight {R : Type*} [CommMonoid R] (w : Fin T → V → V → R)
    {a b : V} (P : LayeredPath E a b) : R :=
  ∏ k, w k (P.vertex k.castSucc) (P.vertex k.succ)

theorem pathFamilyEquiv_weight {R : Type*} [CommRing R] (w : Fin T → V → V → R)
    (P : Σ σ : Equiv.Perm (Fin d), ∀ i, LayeredPath E (s i) (f (σ i))) :
    pathFamilyWeight w (pathFamilyEquiv P) =
      (P.1.sign : ℤ) • ∏ i, layeredPathWeight w (P.2 i) := by
  unfold pathFamilyWeight layeredPathWeight
  change (P.1.sign : ℤ) • (∏ k, ∏ i, w k ((P.2 i).vertex k.castSucc)
    ((P.2 i).vertex k.succ)) = _
  rw [Finset.prod_comm]

set_option backward.isDefEq.respectTransparency false in
/-- This determinant expands over all endpoint permutations and all paths;
no restriction to nonintersecting paths occurs before cancellation. -/
theorem determinant_path_sum [Fintype V] {R : Type*} [CommRing R]
    (w : Fin T → V → V → R) :
    Matrix.det (fun i j : Fin d =>
      ∑ P : LayeredPath E (s j) (f i), layeredPathWeight w P) =
      ∑ P : LayeredPathFamily E s f, pathFamilyWeight w P := by
  classical
  rw [Matrix.det_apply]
  simp_rw [Fintype.prod_sum, Finset.smul_sum, Units.smul_def]
  rw [← Fintype.sum_sigma (fun P : Σ σ : Equiv.Perm (Fin d),
    ∀ i, LayeredPath E (s i) (f (σ i)) =>
      (P.1.sign : ℤ) • ∏ i, layeredPathWeight w (P.2 i))]
  rw [← Equiv.sum_comp pathFamilyEquiv (pathFamilyWeight w)]
  apply Finset.sum_congr rfl
  intro P _
  exact (pathFamilyEquiv_weight w P).symm

/-- The path determinant equals the signed sum of nonintersecting families.
For the Hall lattice geometry, planarity will force their matching to be
the identity and their single east steps to form a strict column. -/
theorem determinant_nonintersecting_paths [Fintype V] {R : Type*} [CommRing R]
    (w : Fin T → V → V → R) (hf : Function.Injective f) :
    Matrix.det (fun i j : Fin d =>
      ∑ P : LayeredPath E (s j) (f i), layeredPathWeight w P) =
      ∑ P : {P : LayeredPathFamily E s f // ¬(pathCollisionTimes P.path).Nonempty},
        pathFamilyWeight w P.val := by
  rw [determinant_path_sum]
  exact path_family_sum_nonintersecting w hf

end
end Schubert.RS
