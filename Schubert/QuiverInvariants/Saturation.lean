import Schubert.QuiverInvariants.Determinantal
import Schubert.QuiverInvariants.King
import Schubert.QuiverInvariants.Positivity
import Schubert.QuiverInvariants.Schofield

/-!
# Semi-invariants of quivers and saturation

Let `Q` be a forward quiver, `ι` a vertex family of dimension vector `n = dim ι` and `K` an
infinite field. This file proves Theorem 4.2 of Baldoni–Vergne–Walter in the following form
(`FQuiver.exists_semiInvariant_iff`): the representations on `ι` have a nonzero semi-invariant of
weight `σ` if and only if
* `∑_p σ_p n_p = 0`, and
* `∑_p σ_p β_p ≥ 0` for every `β` such that a general representation on `ι` has a quotient of
  dimension `β`.

Both conditions are invariant under `σ ↦ N • σ` for `N > 0`, which gives the saturation property
of Derksen–Weyman for semi-invariants (`FQuiver.exists_semiInvariant_of_nsmul`).

The forward implication is King's (`QuiverInvariants.King`). For the converse, the dimension
vector `A = liftWeight` attached to `σ` is nonnegative (Lemma 4.4, `QuiverInvariants.Positivity`)
and satisfies `⟨A, β⟩ = ∑_p σ_p β_p` for every general quotient `β` and `⟨A, n⟩ = 0`. Schofield's
criterion (`FQuiver.exists_extDim_eq_zero`) then gives `ext(V, W) = 0` for some `V` of dimension
`A` and `W` on `ι`, and the determinantal semi-invariant `c^V` is a nonzero semi-invariant of
weight `σ` (`QuiverInvariants.Determinantal`).

## Main results

* `FQuiver.exists_semiInvariant_iff`: Theorem 4.2 of Baldoni–Vergne–Walter.
* `FQuiver.exists_semiInvariant_of_nsmul`: saturation for semi-invariants.
-/

open MvPolynomial

namespace QuiverInvariants

noncomputable section

namespace FQuiver

variable (Q : FQuiver) {K : Type*} [Field K]

variable {ι : Fin Q.s → Type} [∀ p, Fintype (ι p)] [∀ p, DecidableEq (ι p)]

omit [∀ p, DecidableEq (ι p)] in
/-- A general quotient of representations on `ι` has dimensions at most `dim ι`. -/
theorem GeneralQuot.le_card {β : Fin Q.s → ℕ} (h : Q.GeneralQuot K ι β) (p : Fin Q.s) :
    β p ≤ Fintype.card (ι p) := by
  obtain ⟨_, ⟨V, ⟨S, -, hdim⟩, rfl⟩⟩ := h.nonempty
  have := hdim p
  omega

/-- The character `χ_σ` only depends on `σ` at the vertices of positive dimension. -/
theorem chi_congr {σ σ' : Fin Q.s → ℤ} (h : ∀ q, Fintype.card (ι q) ≠ 0 → σ q = σ' q)
    (g : GLFamily K ι) : chi σ g = chi σ' g := by
  refine Finset.prod_congr rfl fun q _ => ?_
  by_cases hq : Fintype.card (ι q) = 0
  · have : IsEmpty (ι q) := Fintype.card_eq_zero_iff.mp hq
    have hdet : Matrix.GeneralLinearGroup.det (g q) = 1 := by
      ext
      rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_isEmpty, Units.val_one]
    rw [hdet, one_zpow, one_zpow]
  · rw [h q hq]

/-- A semi-invariant of weight `σ` is a semi-invariant of every weight agreeing with `σ` at the
vertices of positive dimension. -/
theorem IsSemiInvariant.congr_weight {σ σ' : Fin Q.s → ℤ} {f : MvPolynomial (Q.Entry ι) K}
    (hf : Q.IsSemiInvariant σ f) (h : ∀ q, Fintype.card (ι q) ≠ 0 → σ q = σ' q) :
    Q.IsSemiInvariant σ' f := fun g V => by
  rw [hf g V, Q.chi_congr h g]

omit [∀ p, DecidableEq (ι p)] in
/-- **The dimension vector attached to a weight pairs like the weight.** If `β` vanishes off the
support of `dim ι`, then `⟨liftWeight σ, β⟩ = ∑_p σ_p β_p`. -/
theorem euler_liftWeight (σ : Fin Q.s → ℤ) {β : Fin Q.s → ℤ}
    (hβ : ∀ q, Fintype.card (ι q) = 0 → β q = 0) :
    Q.euler (liftWeight Q.arrows (dimVec ι) σ) β = ∑ q, σ q * β q := by
  rw [← sum_eulerWeight_mul]
  refine Finset.sum_congr rfl fun q _ => ?_
  by_cases hq : Fintype.card (ι q) = 0
  · rw [hβ q hq, mul_zero, mul_zero]
  · rw [eulerWeight, liftWeight_sub_sum Q.forward (dimVec ι) σ (by rwa [dimVec_apply])]

/-- **Theorem 4.2 of Baldoni–Vergne–Walter, the converse direction.** If `∑_p σ_p n_p = 0` and
`∑_p σ_p β_p ≥ 0` for every general quotient `β` of the representations on `ι`, then there is a
nonzero semi-invariant of weight `σ`. -/
theorem exists_semiInvariant_of_forall_generalQuot [Infinite K]
    (σ : Fin Q.s → ℤ) (h₀ : ∑ p, σ p * (Fintype.card (ι p) : ℤ) = 0)
    (h₁ : ∀ β : Fin Q.s → ℕ, Q.GeneralQuot K ι β → 0 ≤ ∑ p, σ p * (β p : ℤ)) :
    ∃ f : MvPolynomial (Q.Entry ι) K, f ≠ 0 ∧ Q.IsSemiInvariant σ f := by
  set A := liftWeight Q.arrows (dimVec ι) σ with hA
  have hA0 : ∀ p, 0 ≤ A p := Q.liftWeight_nonneg_of_generalQuot σ h₁
  -- the vertex family of dimension `A`
  set α : Fin Q.s → Type := finFam fun p => (A p).toNat
  have hcard : (fun p => (Fintype.card (α p) : ℤ)) = A := funext fun p => by
    simp [α, Int.toNat_of_nonneg (hA0 p)]
  -- Schofield's criterion gives `ext(V, W) = 0`
  obtain ⟨V, W, hext⟩ := Q.exists_extDim_eq_zero (K := K) α ι fun β hβ => by
    rw [hcard, Q.euler_liftWeight σ fun q hq => by
      have := hβ.le_card Q q
      omega]
    exact h₁ β hβ
  -- the Euler form vanishes
  have heuler : Q.euler (fun p => (Fintype.card (α p) : ℤ)) (fun p => (Fintype.card (ι p) : ℤ)) =
      0 := by
    rw [hcard, Q.euler_liftWeight σ fun q hq => by rw [hq, Nat.cast_zero]]
    exact h₀
  -- the determinantal semi-invariant
  obtain ⟨f, hf0, hf⟩ := Q.exists_semiInvariant_of_extDim_eq_zero heuler hext
  refine ⟨f, hf0, hf.congr_weight Q fun q hq => ?_⟩
  rw [hcard, eulerWeight, liftWeight_sub_sum Q.forward (dimVec ι) σ (by rwa [dimVec_apply])]

/-- **Theorem 4.2 of Baldoni–Vergne–Walter.** The representations on `ι` have a nonzero
semi-invariant of weight `σ` if and only if
`∑_p σ_p n_p = 0` and `∑_p σ_p β_p ≥ 0` for every `β` such that a general representation on `ι`
has a quotient of dimension `β`. -/
theorem exists_semiInvariant_iff [Infinite K] (σ : Fin Q.s → ℤ) :
    (∃ f : MvPolynomial (Q.Entry ι) K, f ≠ 0 ∧ Q.IsSemiInvariant σ f) ↔
      (∑ p, σ p * (Fintype.card (ι p) : ℤ) = 0 ∧
        ∀ β : Fin Q.s → ℕ, Q.GeneralQuot K ι β → 0 ≤ ∑ p, σ p * (β p : ℤ)) := by
  constructor
  · rintro ⟨f, hf0, hf⟩
    exact ⟨hf.sum_mul_card_eq_zero Q hf0, fun β hβ => hf.sum_mul_nonneg_of_generalQuot Q hf0 hβ⟩
  · rintro ⟨h₀, h₁⟩
    exact Q.exists_semiInvariant_of_forall_generalQuot σ h₀ h₁

/-- **Saturation for semi-invariants** (Derksen–Weyman). If the representations on `ι` have a
nonzero semi-invariant of weight `N • σ` with `N > 0`, then they have a nonzero semi-invariant of
weight `σ`. -/
theorem exists_semiInvariant_of_nsmul [Infinite K] (σ : Fin Q.s → ℤ) {N : ℕ} (hN : 0 < N)
    (h : ∃ f : MvPolynomial (Q.Entry ι) K, f ≠ 0 ∧ Q.IsSemiInvariant (N • σ) f) :
    ∃ f : MvPolynomial (Q.Entry ι) K, f ≠ 0 ∧ Q.IsSemiInvariant σ f := by
  obtain ⟨h₀, h₁⟩ := (Q.exists_semiInvariant_iff (N • σ)).mp h
  have hN' : (0 : ℤ) < N := by exact_mod_cast hN
  refine (Q.exists_semiInvariant_iff σ).mpr ⟨?_, fun β hβ => ?_⟩
  · simp only [Pi.smul_apply, nsmul_eq_mul, mul_assoc, ← Finset.mul_sum] at h₀
    exact (mul_eq_zero.mp h₀).resolve_left hN'.ne'
  · have := h₁ β hβ
    simp only [Pi.smul_apply, nsmul_eq_mul, mul_assoc, ← Finset.mul_sum] at this
    exact nonneg_of_mul_nonneg_right (by linarith) hN'

end FQuiver

end

end QuiverInvariants
