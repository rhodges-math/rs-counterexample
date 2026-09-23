import Schubert.RS.FullWeightWindow
import Schubert.RS.PresentationCharacter

/-! Positive-root support of actual quotient characters and operator keys. -/

namespace Schubert.RS
noncomputable section
open Representation
variable {n : ℕ}

def fullWeightFilter (t : DiagonalTorus n) (v w : Weight n) (a : Enveloping n) : Enveloping n :=
  (integerWeightScalar v t - integerWeightScalar w t)⁻¹ •
    (torusEnveloping t a - integerWeightScalar w t • a)

theorem enveloping_coord_full (order : RootOrdering n) (hpbw : HasOrderedPBWBasis n)
    (t : DiagonalTorus n) (a : PositiveRoot n → ℕ) (x : Enveloping n) :
    (envelopingBasis order hpbw).repr (torusEnveloping t x) a =
      integerWeightScalar (rootWeight (monomialDegree a)) t * (envelopingBasis order hpbw).repr x a := by
  apply basis_coord_eigenmap (envelopingBasis order hpbw) (torusEnveloping t).toLinearMap
    (fun a => integerWeightScalar (rootWeight (monomialDegree a)) t)
  intro a
  change torusEnveloping t (envelopingBasis order hpbw a) = _
  rw [envelopingBasis_apply, torusEnveloping_ordered, monomialScalar_fullWeight]

theorem fullWeightFilter_coord (order : RootOrdering n) (hpbw : HasOrderedPBWBasis n)
    (t : DiagonalTorus n) (v w : Weight n) (a : Enveloping n) (b : PositiveRoot n → ℕ) :
    (envelopingBasis order hpbw).repr (fullWeightFilter t v w a) b =
      (integerWeightScalar v t - integerWeightScalar w t)⁻¹ *
        (integerWeightScalar (rootWeight (monomialDegree b)) t - integerWeightScalar w t) *
          (envelopingBasis order hpbw).repr a b := by
  simp only [fullWeightFilter, map_smul, map_sub, Finsupp.smul_apply,
    Finsupp.sub_apply, smul_eq_mul, enveloping_coord_full]
  ring

theorem fullWeightFilter_support (order : RootOrdering n) (hpbw : HasOrderedPBWBasis n)
    (t : DiagonalTorus n) (v : Weight n) (a : Enveloping n) (b : PositiveRoot n → ℕ) :
    ((envelopingBasis order hpbw).repr
      (fullWeightFilter t v (rootWeight (monomialDegree b)) a)).support ⊆
        ((envelopingBasis order hpbw).repr a).support.erase b := by
  classical
  intro c hc
  have hn := Finsupp.mem_support_iff.mp hc
  rw [fullWeightFilter_coord] at hn
  apply Finset.mem_erase.mpr
  constructor
  · intro h; subst c; simp at hn
  · apply Finsupp.mem_support_iff.mpr
    intro hz; simp [hz] at hn

theorem fullWeightFilter_quotient (I : Submodule (Enveloping n) (Enveloping n))
    (hI : TorusStable I) (t : DiagonalTorus n) (v w : Weight n)
    (hne : integerWeightScalar v t ≠ integerWeightScalar w t)
    (a : Enveloping n) (x : Enveloping n ⧸ I) (ha : Submodule.Quotient.mk a = x)
    (hx : quotientScale I hI t x = integerWeightScalar v t • x) :
    Submodule.Quotient.mk (fullWeightFilter t v w a) = x := by
  change (integerWeightScalar v t - integerWeightScalar w t)⁻¹ •
    ((Submodule.Quotient.mk (torusEnveloping t a) : Enveloping n ⧸ I) -
      integerWeightScalar w t • Submodule.Quotient.mk a) = x
  rw [← quotientScale_mk I hI, ha, hx, ← sub_smul, smul_smul,
    inv_mul_cancel₀ (sub_ne_zero.mpr hne), one_smul]

/-- A quotient cannot acquire a weight absent from all positive-root PBW
monomials. The proof eliminates finite support strictly, preserving the
quotient vector at every step. -/
theorem quotient_weight_zero_from (order : RootOrdering n) (hpbw : HasOrderedPBWBasis n)
    (I : Submodule (Enveloping n) (Enveloping n)) (hI : TorusStable I)
    (v : Weight n) (hv : ∀ d : RootDegree n, rootWeight d ≠ v)
    (x : Enveloping n ⧸ I) (hx : ∀ t, quotientScale I hI t x = integerWeightScalar v t • x)
    (a : Enveloping n) (ha : Submodule.Quotient.mk a = x) : x = 0 := by
  classical
  by_cases hz : a = 0
  · simpa [hz] using ha.symm
  · have hs : ((envelopingBasis order hpbw).repr a).support.Nonempty := by
      apply Finset.nonempty_iff_ne_empty.mpr
      intro he
      have hr : (envelopingBasis order hpbw).repr a = 0 := Finsupp.support_eq_empty.mp he
      exact hz ((envelopingBasis order hpbw).repr.injective (hr.trans (map_zero _).symm))
    obtain ⟨b, hb⟩ := hs
    obtain ⟨t, ht⟩ : ∃ t, integerWeightScalar v t ≠
        integerWeightScalar (rootWeight (monomialDegree b)) t := by
      by_contra hn
      push Not at hn
      exact hv _ (integerWeightScalar_injective (funext hn)).symm
    let a' := fullWeightFilter t v (rootWeight (monomialDegree b)) a
    have ha' : (Submodule.Quotient.mk a' : Enveloping n ⧸ I) = x :=
      fullWeightFilter_quotient I hI t v _ ht a x ha (hx t)
    have hlt : ((envelopingBasis order hpbw).repr a').support.card <
        ((envelopingBasis order hpbw).repr a).support.card :=
      (Finset.card_le_card (fullWeightFilter_support order hpbw t v a b)).trans_lt
        (Finset.card_erase_lt_of_mem hb)
    exact quotient_weight_zero_from order hpbw I hI v hv x hx a' ha'
termination_by ((envelopingBasis order hpbw).repr a).support.card

/-- There are no full-torus weights outside the cyclic weight plus the
nonnegative root cone. No degree-window restriction is needed here. -/
theorem jpWeightSpace_eq_bot_of_outside (u : Composition n) (hpbw : HasOrderedPBWBasis n)
    (w : Weight n) (hw : ¬∃ d : RootDegree n, weightOfRootDegree u d = w) :
    torusWeightSpace (jpTorusRepresentation u) w = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro x hx
  change x = 0
  let v : Weight n := w - (fun i => (u i : ℤ))
  have hv : ∀ d : RootDegree n, rootWeight d ≠ v := by
    intro d hd
    apply hw
    refine ⟨d, ?_⟩
    funext i
    have h := congrFun hd i
    change (u i : ℤ) + rootWeight d i = w i
    change rootWeight d i = w i - u i at h
    omega
  have heigen (t : DiagonalTorus n) : quotientScale (jpLeftIdeal u)
      (fun t _ hm => torusEnveloping_mem_jp u t hm) t x = integerWeightScalar v t • x := by
    have hs : weightScalar u t * integerWeightScalar v t = integerWeightScalar w t := by
      rw [← integerWeightScalar_nat, ← integerWeightScalar_add]
      congr 1
      funext i
      change (u i : ℤ) + (w i - u i) = w i
      ring
    apply smul_right_injective _ (weightScalar_ne_zero u t)
    change jpTorusRepresentation u t x = weightScalar u t • (integerWeightScalar v t • x)
    rw [smul_smul, hs]
    exact hx t
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective (jpLeftIdeal u) x
  exact quotient_weight_zero_from (adaptedRootOrdering u) hpbw (jpLeftIdeal u)
    (fun t _ hm => torusEnveloping_mem_jp u t hm) v hv x heigen a ha

variable {E : Type*} [AddCommGroup E] [Module ℂ E]
  [Module (Enveloping n) E] [IsScalarTower ℂ (Enveloping n) E]

theorem key_support_positive_root_cone (u : Composition n)
    (ρ : DiagonalTorus n →* Module.End ℂ E) (ξ : E)
    (hJP : HasJosephPoloPresentation u ρ ξ) (hDCF : HasDemazureCharacter u ρ)
    (hpbw : HasOrderedPBWBasis n) (w : Weight n) (hw : (toLaurent (key u)).coeff w ≠ 0) :
    ∃ d : RootDegree n, weightOfRootDegree u d = w := by
  by_contra hn
  have h := jpWeight_coefficient u ρ ξ hJP hDCF w
  rw [jpWeightSpace_eq_bot_of_outside u hpbw w hn] at h
  simp only [finrank_bot, Int.natCast_zero] at h
  exact hw h.symm

end
end Schubert.RS
