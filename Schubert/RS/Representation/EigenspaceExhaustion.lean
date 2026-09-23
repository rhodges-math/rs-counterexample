import Schubert.RS.Representation.DegreeSeparation

namespace Schubert.RS.Representation
noncomputable section

def cutFilter {n : ℕ} (k : Fin (n - 1)) (d e : ℕ) (a : Enveloping n) : Enveloping n :=
  ((2 : ℂ)^d - 2^e)⁻¹ • (torusEnveloping (cutTorus k) a - (2 : ℂ)^e • a)

theorem cutFilter_coord {n : ℕ} (order : RootOrdering n) (hpbw : HasOrderedPBWBasis n)
    (k : Fin (n - 1)) (d e : ℕ) (a : Enveloping n) (b : PositiveRoot n → ℕ) :
    (envelopingBasis order hpbw).repr (cutFilter k d e a) b =
      ((2 : ℂ)^d - 2^e)⁻¹ * ((2 : ℂ) ^ monomialDegree b k - 2^e) *
        (envelopingBasis order hpbw).repr a b := by
  simp only [cutFilter, map_smul, map_sub, Finsupp.smul_apply, Finsupp.sub_apply,
    smul_eq_mul, enveloping_coord_cut]
  ring

theorem cutFilter_support_subset_erase {n : ℕ} (order : RootOrdering n) (hpbw : HasOrderedPBWBasis n)
    (k : Fin (n - 1)) (d : ℕ) (a : Enveloping n) (b : PositiveRoot n → ℕ) :
    ((envelopingBasis order hpbw).repr (cutFilter k d (monomialDegree b k) a)).support ⊆
      ((envelopingBasis order hpbw).repr a).support.erase b := by
  classical
  intro c hc
  have hn := Finsupp.mem_support_iff.mp hc
  rw [cutFilter_coord] at hn
  apply Finset.mem_erase.mpr
  constructor
  · intro h
    subst c
    simp at hn
  · apply Finsupp.mem_support_iff.mpr
    intro hz
    simp [hz] at hn

theorem cutFilter_preserves_quotient {n : ℕ} (I : Submodule (Enveloping n) (Enveloping n))
    (hI : TorusStable I) (k : Fin (n - 1)) (d e : ℕ) (hde : d ≠ e)
    (a : Enveloping n) (x : Enveloping n ⧸ I) (ha : Submodule.Quotient.mk a = x)
    (hx : quotientScale I hI (cutTorus k) x = (2 : ℂ)^d • x) :
    Submodule.Quotient.mk (cutFilter k d e a) = x := by
  have hne : (2 : ℂ)^d - 2^e ≠ 0 := sub_ne_zero.mpr
    (fun h => hde (complex_two_pow_injective h))
  change ((2 : ℂ)^d - 2^e)⁻¹ •
    ((Submodule.Quotient.mk (torusEnveloping (cutTorus k) a) : Enveloping n ⧸ I) -
      (2 : ℂ)^e • Submodule.Quotient.mk a) = x
  rw [← quotientScale_mk I hI, ha, hx, ← sub_smul, smul_smul, inv_mul_cancel₀ hne, one_smul]

/-- A simultaneous eigenvector in a stable quotient has a homogeneous lift.
The proof repeatedly removes one unwanted PBW support coordinate while fixing
the quotient vector. The finite-support measure strictly decreases. -/
theorem homogeneous_lift_from {n : ℕ} (order : RootOrdering n) (hpbw : HasOrderedPBWBasis n)
    (I : Submodule (Enveloping n) (Enveloping n)) (hI : TorusStable I)
    (d : RootDegree n) (x : Enveloping n ⧸ I)
    (hx : ∀ k, quotientScale I hI (cutTorus k) x = (2 : ℂ)^d k • x)
    (a : Enveloping n) (ha : Submodule.Quotient.mk a = x) :
    ∃ b ∈ envelopingDegreePiece order hpbw d, Submodule.Quotient.mk b = x := by
  classical
  by_cases hg : ∀ b ∈ ((envelopingBasis order hpbw).repr a).support, monomialDegree b = d
  · exact ⟨a, (envelopingBasis order hpbw).mem_span_image.mpr hg, ha⟩
  · push Not at hg
    obtain ⟨b, hb, hbd⟩ := hg
    obtain ⟨k, hk⟩ : ∃ k, monomialDegree b k ≠ d k := by
      by_contra hn
      push Not at hn
      exact hbd (Finsupp.ext hn)
    let a' := cutFilter k (d k) (monomialDegree b k) a
    have ha' : (Submodule.Quotient.mk a' : Enveloping n ⧸ I) = x :=
      cutFilter_preserves_quotient I hI k (d k) (monomialDegree b k) (Ne.symm hk) a x ha (hx k)
    have hlt : ((envelopingBasis order hpbw).repr a').support.card <
        ((envelopingBasis order hpbw).repr a).support.card := by
      exact (Finset.card_le_card (cutFilter_support_subset_erase order hpbw k (d k) a b)).trans_lt
        (Finset.card_erase_lt_of_mem hb)
    exact homogeneous_lift_from order hpbw I hI d x hx a' ha'
termination_by ((envelopingBasis order hpbw).repr a).support.card

theorem homogeneous_lift {n : ℕ} (order : RootOrdering n) (hpbw : HasOrderedPBWBasis n)
    (I : Submodule (Enveloping n) (Enveloping n)) (hI : TorusStable I)
    (d : RootDegree n) (x : Enveloping n ⧸ I)
    (hx : ∀ k, quotientScale I hI (cutTorus k) x = (2 : ℂ)^d k • x) :
    ∃ a ∈ envelopingDegreePiece order hpbw d, Submodule.Quotient.mk a = x := by
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective I x
  exact homogeneous_lift_from order hpbw I hI d x hx a ha

theorem quotientScale_eigen_of_twisted {n : ℕ} (u : Fin n → ℕ)
    (I : Submodule (Enveloping n) (Enveloping n)) (hI : TorusStable I)
    (d : RootDegree n) (x : Enveloping n ⧸ I)
    (hx : ∀ k, quotientTorusRepresentation u I hI (cutTorus k) x =
      (weightScalar u (cutTorus k) * (2 : ℂ)^d k) • x) (k : Fin (n - 1)) :
    quotientScale I hI (cutTorus k) x = (2 : ℂ)^d k • x := by
  apply smul_right_injective _ (weightScalar_ne_zero u (cutTorus k))
  have h := hx k
  change weightScalar u (cutTorus k) • quotientScale I hI (cutTorus k) x =
    (weightScalar u (cutTorus k) * (2 : ℂ)^d k) • x at h
  simpa only [smul_smul] using h

/-- The constructed JP degree piece equals the genuine simultaneous cut-torus
eigenspace, rather than merely being a subspace of it. -/
theorem mem_jpDegreePiece_iff_cut_eigen {n : ℕ} (u : Fin n → ℕ) (hpbw : HasOrderedPBWBasis n)
    (d : RootDegree n) (x : PresentationQuotient u) :
    x ∈ jpDegreePiece u hpbw d ↔ ∀ k,
      jpTorusRepresentation u (cutTorus k) x =
        (weightScalar u (cutTorus k) * (2 : ℂ)^d k) • x := by
  constructor
  · exact jpDegreePiece_cut_eigen u hpbw d
  · intro hx
    obtain ⟨a, ha, he⟩ := homogeneous_lift (adaptedRootOrdering u) hpbw (jpLeftIdeal u)
      (fun t _ hm => torusEnveloping_mem_jp u t hm) d x
      (quotientScale_eigen_of_twisted u _ _ d x hx)
    exact ⟨a, ha, he⟩

theorem mem_linearDegreePiece_iff_cut_eigen {n : ℕ} (u : Fin n → ℕ) (hpbw : HasOrderedPBWBasis n)
    (d : RootDegree n) (x : LinearPresentationQuotient u) :
    x ∈ linearDegreePiece u hpbw d ↔ ∀ k,
      linearTorusRepresentation u (cutTorus k) x =
        (weightScalar u (cutTorus k) * (2 : ℂ)^d k) • x := by
  constructor
  · exact linearDegreePiece_cut_eigen u hpbw d
  · intro hx
    obtain ⟨a, ha, he⟩ := homogeneous_lift (adaptedRootOrdering u) hpbw (linearLeftIdeal u)
      (fun t _ hm => torusEnveloping_mem_linear u t hm) d x
      (quotientScale_eigen_of_twisted u _ _ d x hx)
    exact ⟨a, ha, he⟩

end
end Schubert.RS.Representation
