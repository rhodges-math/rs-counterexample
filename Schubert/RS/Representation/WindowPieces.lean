import Schubert.RS.Representation.WindowIdeal
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

namespace Schubert.RS.Representation
noncomputable section

theorem linearIdeal_eq_basisSpan {n : ℕ} (u : Fin n → ℕ) (hpbw : HasOrderedPBWBasis n) :
    (linearLeftIdeal u).restrictScalars ℂ = Submodule.span ℂ
      (envelopingBasis (adaptedRootOrdering u) hpbw '' {a | HasKillingPower u a}) := by
  rw [linearLeftIdeal_eq_blocked u hpbw]
  unfold blockedPBWSpan
  congr 1
  ext z
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, envelopingBasis_apply _ _ a⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, envelopingBasis_apply _ _ a⟩

/-- The additional JP relations have zero intersection with a low homogeneous
piece modulo the linear relations, including arbitrary left coefficients. -/
theorem jp_mem_lowDegree_mem_linear {n : ℕ} (u : Fin n → ℕ) (hpbw : HasOrderedPBWBasis n)
    (β d : RootDegree n) (hd : d ≤ β)
    (hβ : ∀ r : PositiveRoot n, u r.val.1 < u r.val.2 →
      ¬ jpExponent u r • rootDegree r.val.1 r.val.2 ≤ β)
    {x : Enveloping n} (hx : x ∈ envelopingDegreePiece (adaptedRootOrdering u) hpbw d)
    (hj : x ∈ jpLeftIdeal u) : x ∈ linearLeftIdeal u := by
  have hm := jpLeftIdeal_le_linear_sup_outside u hpbw β hβ hj
  obtain ⟨l, hl, h, hh, rfl⟩ := Submodule.mem_sup.mp hm
  change l + h ∈ (linearLeftIdeal u).restrictScalars ℂ
  rw [linearIdeal_eq_basisSpan u hpbw] at hl ⊢
  apply (envelopingBasis (adaptedRootOrdering u) hpbw).mem_span_image.mpr
  intro a ha
  by_contra hn
  have hlzero : (envelopingBasis (adaptedRootOrdering u) hpbw).repr l a = 0 := by
    by_contra hz
    exact hn (((envelopingBasis (adaptedRootOrdering u) hpbw).mem_span_image.mp hl)
      (Finsupp.mem_support_iff.mpr hz))
  have hadeg : monomialDegree a = d :=
    ((envelopingBasis (adaptedRootOrdering u) hpbw).mem_span_image.mp hx) ha
  have hhzero : (envelopingBasis (adaptedRootOrdering u) hpbw).repr h a = 0 := by
    by_contra hz
    have hout := ((envelopingBasis (adaptedRootOrdering u) hpbw).mem_span_image.mp hh)
      (Finsupp.mem_support_iff.mpr hz)
    exact hout (hadeg ▸ hd)
  exact (Finsupp.mem_support_iff.mp ha) (by simp [map_add, hlzero, hhzero])

instance envelopingDegreePiece_finite {n : ℕ} (order : RootOrdering n) (hpbw : HasOrderedPBWBasis n)
    (d : RootDegree n) : FiniteDimensional ℂ (envelopingDegreePiece order hpbw d) :=
  FiniteDimensional.span_of_finite ℂ
    ((monomialDegree_fiber_finite d).image (envelopingBasis order hpbw))

/-- A genuine homogeneous piece in the actual quotient, obtained from the
proved homogeneous subspace of its enveloping algebra. -/
def linearDegreePiece {n : ℕ} (u : Fin n → ℕ) (hpbw : HasOrderedPBWBasis n) (d : RootDegree n) :
    Submodule ℂ (LinearPresentationQuotient u) :=
  (envelopingDegreePiece (adaptedRootOrdering u) hpbw d).map
    ((linearLeftIdeal u).mkQ.restrictScalars ℂ)

def jpDegreePiece {n : ℕ} (u : Fin n → ℕ) (hpbw : HasOrderedPBWBasis n) (d : RootDegree n) :
    Submodule ℂ (PresentationQuotient u) :=
  (envelopingDegreePiece (adaptedRootOrdering u) hpbw d).map
    ((jpLeftIdeal u).mkQ.restrictScalars ℂ)

instance linearDegreePiece_finite {n : ℕ} (u : Fin n → ℕ) (hpbw : HasOrderedPBWBasis n)
    (d : RootDegree n) : FiniteDimensional ℂ (linearDegreePiece u hpbw d) :=
  inferInstanceAs (Module.Finite ℂ ((envelopingDegreePiece (adaptedRootOrdering u) hpbw d).map _))

instance jpDegreePiece_finite {n : ℕ} (u : Fin n → ℕ) (hpbw : HasOrderedPBWBasis n)
    (d : RootDegree n) : FiniteDimensional ℂ (jpDegreePiece u hpbw d) :=
  inferInstanceAs (Module.Finite ℂ ((envelopingDegreePiece (adaptedRootOrdering u) hpbw d).map _))

def degreePieceToJP {n : ℕ} (u : Fin n → ℕ) (hpbw : HasOrderedPBWBasis n) (d : RootDegree n) :
    linearDegreePiece u hpbw d →ₗ[ℂ] jpDegreePiece u hpbw d where
  toFun x := ⟨linearToJP u x.val, by
    obtain ⟨a, ha, he⟩ := x.property
    refine ⟨a, ha, ?_⟩
    rw [← he]
    rfl⟩
  map_add' x y := Subtype.ext (map_add (linearToJP u) x.val y.val)
  map_smul' c x := Subtype.ext (map_smul ((linearToJP u).restrictScalars ℂ) c x.val)

theorem degreePieceToJP_surjective {n : ℕ} (u : Fin n → ℕ) (hpbw : HasOrderedPBWBasis n)
    (d : RootDegree n) : Function.Surjective (degreePieceToJP u hpbw d) := by
  intro x
  obtain ⟨a, ha, he⟩ := x.property
  refine ⟨⟨Submodule.Quotient.mk a, ⟨a, ha, rfl⟩⟩, ?_⟩
  exact Subtype.ext he

theorem degreePieceToJP_injective {n : ℕ} (u : Fin n → ℕ) (hpbw : HasOrderedPBWBasis n)
    (β d : RootDegree n) (hd : d ≤ β)
    (hβ : ∀ r : PositiveRoot n, u r.val.1 < u r.val.2 →
      ¬ jpExponent u r • rootDegree r.val.1 r.val.2 ≤ β) :
    Function.Injective (degreePieceToJP u hpbw d) := by
  apply (LinearMap.ker_eq_bot).mp
  apply le_antisymm
  · intro x hx
    obtain ⟨a, ha, he⟩ := x.property
    have hz : (Submodule.Quotient.mk a : PresentationQuotient u) = 0 := by
      have hv := congrArg Subtype.val hx
      change linearToJP u x.val = 0 at hv
      rw [← he] at hv
      exact hv
    have hj : a ∈ jpLeftIdeal u := (Submodule.Quotient.mk_eq_zero _).mp hz
    have hl := jp_mem_lowDegree_mem_linear u hpbw β d hd hβ ha hj
    have hlz : (Submodule.Quotient.mk a : LinearPresentationQuotient u) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr hl
    change x = 0
    apply Subtype.ext
    exact he.symm.trans hlz
  · exact bot_le

/-- The paper's coefficient-window bridge for the actual cyclic quotients.
Only universal PBW is an input; homogeneity and ideal exclusion are proved. -/
def windowDegreeEquiv {n : ℕ} (u : Fin n → ℕ) (hpbw : HasOrderedPBWBasis n)
    (β d : RootDegree n) (hd : d ≤ β)
    (hβ : ∀ r : PositiveRoot n, u r.val.1 < u r.val.2 →
      ¬ jpExponent u r • rootDegree r.val.1 r.val.2 ≤ β) :
    linearDegreePiece u hpbw d ≃ₗ[ℂ] jpDegreePiece u hpbw d :=
  LinearEquiv.ofBijective (degreePieceToJP u hpbw d)
    ⟨degreePieceToJP_injective u hpbw β d hd hβ, degreePieceToJP_surjective u hpbw d⟩

theorem linearDegreePiece_cut_eigen {n : ℕ} (u : Fin n → ℕ) (hpbw : HasOrderedPBWBasis n)
    (d : RootDegree n) {x : LinearPresentationQuotient u}
    (hx : x ∈ linearDegreePiece u hpbw d) (k : Fin (n - 1)) :
    linearTorusRepresentation u (cutTorus k) x =
      (weightScalar u (cutTorus k) * (2 : ℂ) ^ d k) • x := by
  obtain ⟨a, ha, rfl⟩ := hx
  change weightScalar u (cutTorus k) • quotientScale (linearLeftIdeal u) _ (cutTorus k)
    (Submodule.Quotient.mk a) = _
  rw [quotientScale_mk, degreePiece_cut_eigen _ hpbw d ha,
    Submodule.Quotient.mk_smul, smul_smul]
  rfl

theorem jpDegreePiece_cut_eigen {n : ℕ} (u : Fin n → ℕ) (hpbw : HasOrderedPBWBasis n)
    (d : RootDegree n) {x : PresentationQuotient u}
    (hx : x ∈ jpDegreePiece u hpbw d) (k : Fin (n - 1)) :
    jpTorusRepresentation u (cutTorus k) x =
      (weightScalar u (cutTorus k) * (2 : ℂ) ^ d k) • x := by
  obtain ⟨a, ha, rfl⟩ := hx
  change weightScalar u (cutTorus k) • quotientScale (jpLeftIdeal u) _ (cutTorus k)
    (Submodule.Quotient.mk a) = _
  rw [quotientScale_mk, degreePiece_cut_eigen _ hpbw d ha,
    Submodule.Quotient.mk_smul, smul_smul]
  rfl

theorem windowDegree_finrank {n : ℕ} (u : Fin n → ℕ) (hpbw : HasOrderedPBWBasis n)
    (β d : RootDegree n) (hd : d ≤ β)
    (hβ : ∀ r : PositiveRoot n, u r.val.1 < u r.val.2 →
      ¬ jpExponent u r • rootDegree r.val.1 r.val.2 ≤ β) :
    Module.finrank ℂ (linearDegreePiece u hpbw d) =
      Module.finrank ℂ (jpDegreePiece u hpbw d) :=
  (windowDegreeEquiv u hpbw β d hd hβ).finrank_eq

end
end Schubert.RS.Representation
