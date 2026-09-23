import Schubert.RS.Representation.WindowPieces

namespace Schubert.RS.Representation
noncomputable section

theorem weightScalar_ne_zero {n : ℕ} (u : Fin n → ℕ) (t : DiagonalTorus n) :
    weightScalar u t ≠ 0 := by
  unfold weightScalar
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (Units.ne_zero (t i)))

/-- The degree label of a nonzero joint eigenvector is unique. The twist by
the cyclic weight is nonzero and cancels; natural powers of two separate cuts. -/
theorem cutEigen_degree_unique {n : ℕ} {E : Type*} [AddCommGroup E] [Module ℂ E]
    (u : Fin n → ℕ) (T : Fin (n - 1) → E →ₗ[ℂ] E) (d e : RootDegree n)
    {x : E} (hx : x ≠ 0)
    (hd : ∀ k, T k x = (weightScalar u (cutTorus k) * (2 : ℂ) ^ d k) • x)
    (he : ∀ k, T k x = (weightScalar u (cutTorus k) * (2 : ℂ) ^ e k) • x) : d = e := by
  ext k
  apply complex_two_pow_injective
  apply mul_left_cancel₀ (weightScalar_ne_zero u (cutTorus k))
  exact smul_left_injective ℂ hx ((hd k).symm.trans (he k))

theorem linearDegreePiece_disjoint {n : ℕ} (u : Fin n → ℕ) (hpbw : HasOrderedPBWBasis n)
    (d e : RootDegree n) (hne : d ≠ e) :
    Disjoint (linearDegreePiece u hpbw d) (linearDegreePiece u hpbw e) := by
  rw [disjoint_iff_inf_le]
  intro x hx
  change x = 0
  by_contra hn
  exact hne (cutEigen_degree_unique u (fun k => linearTorusRepresentation u (cutTorus k)) d e hn
    (linearDegreePiece_cut_eigen u hpbw d hx.1) (linearDegreePiece_cut_eigen u hpbw e hx.2))

theorem jpDegreePiece_disjoint {n : ℕ} (u : Fin n → ℕ) (hpbw : HasOrderedPBWBasis n)
    (d e : RootDegree n) (hne : d ≠ e) :
    Disjoint (jpDegreePiece u hpbw d) (jpDegreePiece u hpbw e) := by
  rw [disjoint_iff_inf_le]
  intro x hx
  change x = 0
  by_contra hn
  exact hne (cutEigen_degree_unique u (fun k => jpTorusRepresentation u (cutTorus k)) d e hn
    (jpDegreePiece_cut_eigen u hpbw d hx.1) (jpDegreePiece_cut_eigen u hpbw e hx.2))

theorem windowDegreeEquiv_apply {n : ℕ} (u : Fin n → ℕ) (hpbw : HasOrderedPBWBasis n)
    (β d : RootDegree n) (hd : d ≤ β)
    (hβ : ∀ r : PositiveRoot n, u r.val.1 < u r.val.2 →
      ¬ jpExponent u r • rootDegree r.val.1 r.val.2 ≤ β)
    (x : linearDegreePiece u hpbw d) :
    (windowDegreeEquiv u hpbw β d hd hβ x).val = linearToJP u x.val := rfl

end
end Schubert.RS.Representation
