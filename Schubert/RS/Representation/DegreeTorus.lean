import Schubert.RS.Representation.RelativePBWBasis
import Schubert.RS.RootDegreeFibers

namespace Schubert.RS.Representation
noncomputable section
open scoped BigOperators

abbrev RootDegree (n : ℕ) := Fin (n - 1) →₀ ℕ

def monomialDegree {n : ℕ} (a : PositiveRoot n → ℕ) : RootDegree n :=
  ∑ r, a r • rootDegree r.val.1 r.val.2

def ascentMonomialDegree {n : ℕ} (u : Fin n → ℕ) (a : AscentRoot u → ℕ) : RootDegree n :=
  ∑ r, a r • rootDegree r.val.val.1 r.val.val.2

/-- A cut detects precisely the roots crossing it. This is an actual diagonal
torus element, so no grading on the enveloping algebra is assumed. -/
def cutTorus {n : ℕ} (k : Fin (n - 1)) : DiagonalTorus n :=
  fun i => if i.val ≤ k.val then Units.mk0 (2 : ℂ) (by norm_num) else 1

theorem rootScalar_cut {n : ℕ} (r : PositiveRoot n) (k : Fin (n - 1)) :
    rootScalar (cutTorus k) r.val.1 r.val.2 = (2 : ℂ) ^ rootDegree r.val.1 r.val.2 k := by
  have hij : r.val.1.val < r.val.2.val := r.property
  by_cases hi : r.val.1.val ≤ k.val <;> by_cases hj : r.val.2.val ≤ k.val
  · simp [rootScalar, cutTorus, hi, hj, rootDegree_apply, Nat.not_lt.mpr hj]
  · simp [rootScalar, cutTorus, hi, hj, rootDegree_apply, Nat.lt_of_not_ge hj]
  · omega
  · simp [rootScalar, cutTorus, hi, hj, rootDegree_apply]

theorem rootOrder_toFinset {n : ℕ} (order : RootOrdering n) : order.roots.toFinset = Finset.univ := by
  classical
  ext r
  simp [order.complete r]

theorem orderedMonomialScalar_cut {n : ℕ} (order : RootOrdering n)
    (a : PositiveRoot n → ℕ) (k : Fin (n - 1)) :
    orderedMonomialScalar order a (cutTorus k) = (2 : ℂ) ^ monomialDegree a k := by
  classical
  unfold orderedMonomialScalar
  simp only [rootScalar_cut, ← pow_mul]
  rw [← List.prod_toFinset _ order.nodup, rootOrder_toFinset]
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  simp [monomialDegree, Finsupp.finset_sum_apply, Finsupp.smul_apply, mul_comm]

theorem torusEnveloping_monomialDegree {n : ℕ} (order : RootOrdering n)
    (a : PositiveRoot n → ℕ) (k : Fin (n - 1)) :
    torusEnveloping (cutTorus k) (orderedRootMonomial order a) =
      (2 : ℂ) ^ monomialDegree a k • orderedRootMonomial order a := by
  rw [torusEnveloping_ordered, orderedMonomialScalar_cut]

theorem complex_two_pow_injective : Function.Injective (fun d : ℕ => (2 : ℂ) ^ d) := by
  intro a b h
  change (2 : ℂ) ^ a = 2 ^ b at h
  have hh : (2 : ℕ) ^ a = 2 ^ b := by exact_mod_cast h
  exact Nat.pow_right_injective (by decide : 2 ≤ (2 : ℕ)) hh

theorem monomialDegree_fiber_finite {n : ℕ} (d : RootDegree n) :
    {a : PositiveRoot n → ℕ | monomialDegree a = d}.Finite :=
  degree_fiber_finite (ι := PositiveRoot n) (σ := Fin (n - 1))
    (fun r => rootDegree r.val.1 r.val.2)
    (fun r => rootFirstCut r.val.1 r.val.2 r.property)
    (fun r => rootDegree_first r.val.1 r.val.2 r.property) d

theorem ascentMonomialDegree_fiber_finite {n : ℕ} (u : Fin n → ℕ) (d : RootDegree n) :
    {a : AscentRoot u → ℕ | ascentMonomialDegree u a = d}.Finite := by
  classical
  exact degree_fiber_finite (ι := AscentRoot u) (σ := Fin (n - 1))
    (fun r => rootDegree r.val.val.1 r.val.val.2)
    (fun r => rootFirstCut r.val.val.1 r.val.val.2 r.val.property)
    (fun r => rootDegree_first r.val.val.1 r.val.val.2 r.val.property) d

end
end Schubert.RS.Representation
