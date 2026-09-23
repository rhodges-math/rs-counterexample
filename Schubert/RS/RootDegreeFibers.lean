import Schubert.RS.RootDegrees
import Mathlib.Data.Fintype.Pi

/-! Finite degree fibers for ordered root monomials. -/

namespace Schubert.RS

noncomputable section

/-- A marked simple-root coordinate bounds each PBW exponent separately. -/
theorem degree_fiber_bound {ι σ : Type*} [Fintype ι]
    (degree : ι → σ →₀ ℕ) (cut : ι → σ) (hcut : ∀ r, degree r (cut r) = 1)
    (β : σ →₀ ℕ) (p : ι → ℕ) (hp : ∑ r, p r • degree r = β) (r : ι) :
    p r ≤ β (cut r) := by
  classical
  have h := Finset.single_le_sum (f := fun s => p s * degree s (cut r))
    (fun s _ => Nat.zero_le _) (Finset.mem_univ r)
  have he := congrArg (fun d : σ →₀ ℕ => d (cut r)) hp
  simp only [Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul] at he
  simpa only [hcut, mul_one, he] using h

/-- The simple-root degree fibers are finite before any character is defined.
This prevents an infinite-dimensional weight space being silently assigned
the finite-rank convention zero. -/
theorem degree_fiber_finite {ι σ : Type*} [Fintype ι]
    (degree : ι → σ →₀ ℕ) (cut : ι → σ) (hcut : ∀ r, degree r (cut r) = 1)
    (β : σ →₀ ℕ) :
    {p : ι → ℕ | ∑ r, p r • degree r = β}.Finite := by
  have hf : {p : ι → ℕ | ∀ r, p r ∈ (Finset.range (β (cut r) + 1) : Set ℕ)}.Finite :=
    Set.Finite.pi' (fun r => (Finset.range (β (cut r) + 1)).finite_toSet)
  apply hf.subset
  intro p hp r
  have hb := degree_fiber_bound degree cut hcut β p hp r
  simpa using Nat.lt_succ_of_le hb

end
end Schubert.RS
