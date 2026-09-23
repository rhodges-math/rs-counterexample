import Schubert.RS.Representation.RelativePBW

namespace Schubert.RS.Representation
noncomputable section
attribute [local instance 100] LieRing.ofAssociativeRing

def joinedRoot {n : ℕ} (r s : PositiveRoot n) (h : r.val.2 = s.val.1) : PositiveRoot n :=
  ⟨(r.val.1, s.val.2), by
    calc r.val.1 < r.val.2 := r.property
      _ = s.val.1 := h
      _ < s.val.2 := s.property⟩

theorem rootVector_bracket_forward {n : ℕ} (r s : PositiveRoot n)
    (h : r.val.2 = s.val.1) : ⁅rootVector r, rootVector s⁆ = rootVector (joinedRoot r s h) := by
  apply Subtype.ext
  have hne : s.val.2 ≠ r.val.1 := ne_of_gt (joinedRoot r s h).property
  change Matrix.single r.val.1 r.val.2 (1 : ℂ) * Matrix.single s.val.1 s.val.2 1 -
    Matrix.single s.val.1 s.val.2 1 * Matrix.single r.val.1 r.val.2 1 =
      Matrix.single r.val.1 s.val.2 1
  rw [h, Matrix.single_mul_single_same,
    Matrix.single_mul_single_of_ne (1 : ℂ) s.val.1 s.val.2 r.val.1 hne]
  simp

theorem rootVector_bracket_zero {n : ℕ} (r s : PositiveRoot n)
    (h : r.val.2 ≠ s.val.1) (h' : s.val.2 ≠ r.val.1) : ⁅rootVector r, rootVector s⁆ = 0 := by
  apply Subtype.ext
  change Matrix.single r.val.1 r.val.2 (1 : ℂ) * Matrix.single s.val.1 s.val.2 1 -
    Matrix.single s.val.1 s.val.2 1 * Matrix.single r.val.1 r.val.2 1 = 0
  rw [Matrix.single_mul_single_of_ne (1 : ℂ) r.val.1 r.val.2 s.val.1 h,
    Matrix.single_mul_single_of_ne (1 : ℂ) s.val.1 s.val.2 r.val.1 h']
  simp

theorem rootOperator_commutator_forward {n : ℕ} (r s : PositiveRoot n)
    (h : r.val.2 = s.val.1) :
    rootOperator r * rootOperator s - rootOperator s * rootOperator r =
      rootOperator (joinedRoot r s h) := by
  change ⁅UniversalEnvelopingAlgebra.ι ℂ (rootVector r),
    UniversalEnvelopingAlgebra.ι ℂ (rootVector s)⁆ = _
  rw [← LieHom.map_lie, rootVector_bracket_forward r s h]
  rfl

theorem rootOperator_commutator_zero {n : ℕ} (r s : PositiveRoot n)
    (h : r.val.2 ≠ s.val.1) (h' : s.val.2 ≠ r.val.1) :
    rootOperator r * rootOperator s - rootOperator s * rootOperator r = 0 := by
  change ⁅UniversalEnvelopingAlgebra.ι ℂ (rootVector r),
    UniversalEnvelopingAlgebra.ι ℂ (rootVector s)⁆ = _
  rw [← LieHom.map_lie, rootVector_bracket_zero r s h h', map_zero]

def killingOperatorSpan {n : ℕ} (u : Fin n → ℕ) : Submodule ℂ (Enveloping n) :=
  Submodule.span ℂ {a | ∃ r : PositiveRoot n, u r.val.2 ≤ u r.val.1 ∧ a = rootOperator r}

/-- The commutator error from exchanging two killing generators remains
linear in killing generators. This is the length-decreasing straightening step. -/
theorem killing_commutator_mem {n : ℕ} (u : Fin n → ℕ) (r s : PositiveRoot n)
    (hr : u r.val.2 ≤ u r.val.1) (hs : u s.val.2 ≤ u s.val.1) :
    rootOperator r * rootOperator s - rootOperator s * rootOperator r ∈ killingOperatorSpan u := by
  by_cases h : r.val.2 = s.val.1
  · rw [rootOperator_commutator_forward r s h]
    apply Submodule.subset_span
    refine ⟨joinedRoot r s h, ?_, rfl⟩
    change u s.val.2 ≤ u r.val.1
    calc u s.val.2 ≤ u s.val.1 := hs
      _ = u r.val.2 := congrArg u h.symm
      _ ≤ u r.val.1 := hr
  · by_cases h' : s.val.2 = r.val.1
    · have he : rootOperator r * rootOperator s - rootOperator s * rootOperator r =
          -rootOperator (joinedRoot s r h') := by
        rw [← rootOperator_commutator_forward s r h']
        abel
      rw [he]
      apply Submodule.neg_mem
      apply Submodule.subset_span
      refine ⟨joinedRoot s r h', ?_, rfl⟩
      change u r.val.2 ≤ u s.val.1
      calc u r.val.2 ≤ u r.val.1 := hr
        _ = u s.val.2 := congrArg u h'.symm
        _ ≤ u s.val.1 := hs
    · rw [rootOperator_commutator_zero r s h h']
      exact Submodule.zero_mem _

end
end Schubert.RS.Representation
