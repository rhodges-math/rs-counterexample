import Schubert.Demazure.Representation.EnvelopingGrading

/-!
# Truncating the Joseph–Polo left ideal

`outsideTruncationSpan β` is the span of the PBW monomials whose root degree is not below `β`; it is
closed under left multiplication (`mul_mem_outsideTruncation`). If no Joseph–Polo power of an ascent
root has root degree below `β`, the Joseph–Polo left ideal lies in the linear left ideal plus this
span (`josephPoloLeftIdeal_le_linear_sup_outside`).
-/

open Schubert

namespace Demazure.FlagModule
noncomputable section

/-- The span of the ordered root monomials whose root degree is not below `β`. -/
def outsideTruncationSpan {n : ℕ} (order : RootOrdering n) (hpbw : HasOrderedPBWBasis n)
    (β : RootDegree n) : Submodule ℂ (Enveloping n) :=
  Submodule.span ℂ (envelopingBasis order hpbw '' {a | ¬ monomialDegree a ≤ β})

theorem degreePiece_le_outside {n : ℕ} (order : RootOrdering n) (hpbw : HasOrderedPBWBasis n)
    (β d : RootDegree n) (hd : ¬ d ≤ β) :
    envelopingDegreePiece order hpbw d ≤ outsideTruncationSpan order hpbw β := by
  apply Submodule.span_mono
  apply Set.image_mono
  intro a ha
  change monomialDegree a = d at ha
  change ¬ monomialDegree a ≤ β
  simpa only [ha] using hd

theorem basis_mem_degreePiece {n : ℕ} (order : RootOrdering n) (hpbw : HasOrderedPBWBasis n)
    (a : PositiveRoot n → ℕ) :
    envelopingBasis order hpbw a ∈ envelopingDegreePiece order hpbw (monomialDegree a) :=
  Submodule.subset_span ⟨a, rfl, rfl⟩

/-- The complement of a downward degree box is closed under arbitrary LEFT
multiplication. Positivity and the proved multiplication grading are essential. -/
theorem mul_mem_outsideTruncation {n : ℕ} (order : RootOrdering n) (hpbw : HasOrderedPBWBasis n)
    (β : RootDegree n) (x : Enveloping n) {y : Enveloping n}
    (hy : y ∈ outsideTruncationSpan order hpbw β) : x * y ∈ outsideTruncationSpan order hpbw β := by
  have hx : x ∈ Submodule.span ℂ (Set.range (envelopingBasis order hpbw)) := by
    rw [(envelopingBasis order hpbw).span_eq]; trivial
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, hb, rfl⟩ := hy
      apply degreePiece_le_outside order hpbw β (monomialDegree a + monomialDegree b)
      · intro h
        apply hb
        exact le_trans (by intro k; simp only [Finsupp.add_apply]; omega) h
      · exact envelopingDegreePiece_mul order hpbw _ _
          (basis_mem_degreePiece order hpbw a) (basis_mem_degreePiece order hpbw b)
    | zero => simp
    | add y z hy hz iy iz => simpa only [mul_add] using (outsideTruncationSpan order hpbw β).add_mem
                               iy iz
    | smul c y hy iy =>
      rw [mul_smul_comm]
      exact (outsideTruncationSpan order hpbw β).smul_mem c iy
  | zero => simp
  | add x z hx hz ix iz => simpa only [add_mul] using (outsideTruncationSpan order hpbw β).add_mem
                             ix iz
  | smul c x hx ix =>
    rw [smul_mul_assoc]
    exact (outsideTruncationSpan order hpbw β).smul_mem c ix

theorem rootPower_mem_degreePiece {n : ℕ} (order : RootOrdering n) (hpbw : HasOrderedPBWBasis n)
    (r : PositiveRoot n) (q : ℕ) :
    rootOperator r ^ q ∈ envelopingDegreePiece order hpbw (q • rootDegree r.val.1 r.val.2) := by
  apply cut_eigen_mem_degreePiece
  intro k
  rw [map_pow, torusEnveloping_root, rootScalar_cut, smul_pow]
  simp only [← pow_mul, Finsupp.smul_apply, smul_eq_mul, Nat.mul_comm]

/-- No homogeneous-ideal assumption is used: this follows from actual root-power
eigenvectors and the proved closure of the outside-box subspace. -/
theorem josephPoloLeftIdeal_le_linear_sup_outside {n : ℕ} (u : Fin n → ℕ)
    (hpbw : HasOrderedPBWBasis n) (β : RootDegree n)
    (hβ : ∀ r : PositiveRoot n, u r.val.1 < u r.val.2 →
      ¬ josephPoloExponent u r • rootDegree r.val.1 r.val.2 ≤ β) :
    (josephPoloLeftIdeal u).restrictScalars ℂ ≤
      (linearLeftIdeal u).restrictScalars ℂ ⊔ outsideTruncationSpan (adaptedRootOrdering u) hpbw
          β := by
  intro x hx
  change x ∈ josephPoloLeftIdeal u at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨r, rfl⟩ := hx
    by_cases hr : u r.val.1 < u r.val.2
    · apply Submodule.mem_sup_right
      exact degreePiece_le_outside _ hpbw β _ (hβ r hr) (rootPower_mem_degreePiece _ hpbw r _)
    · apply Submodule.mem_sup_left
      change rootOperator r ^ josephPoloExponent u r ∈ linearLeftIdeal u
      have he : josephPoloExponent u r = 1 := by
          simp [josephPoloExponent, Nat.sub_eq_zero_of_le (Nat.le_of_not_gt hr)]
      rw [he, pow_one]
      exact Submodule.subset_span ⟨r, Nat.le_of_not_gt hr, rfl⟩
  | zero => exact Submodule.zero_mem _
  | add x y hx hy ix iy => exact Submodule.add_mem _ ix iy
  | smul a x hx ix =>
    obtain ⟨l, hl, h, hh, rfl⟩ := Submodule.mem_sup.mp ix
    change a * (l + h) ∈ _
    rw [mul_add]
    apply Submodule.add_mem
    · exact Submodule.mem_sup_left ((linearLeftIdeal u).smul_mem a hl)
    · exact Submodule.mem_sup_right (mul_mem_outsideTruncation _ hpbw β a hh)

end
end Demazure.FlagModule
