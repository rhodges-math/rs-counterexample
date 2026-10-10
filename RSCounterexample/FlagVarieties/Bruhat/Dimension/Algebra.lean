import Mathlib.RingTheory.Ideal.HasGoingUp
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.Localization.InvSubmonoid
import Mathlib.RingTheory.KrullDimension.Field

/-!
# Krull dimension of affine domains

* `ringKrullDim_eq_of_isIntegral`: an injective integral ring extension does not change the Krull
  dimension (going up and incomparability).
* `exists_ringKrullDim_eq_trdeg`: **the Krull dimension of a finitely generated domain `A` over a
  field `K` is its transcendence degree**, through Noether normalization.
* `ringKrullDim_localization_eq`: hence localizing such an `A` at a nonzero element does not change
  the Krull dimension.
-/

namespace FlagVarieties.Dimension

open Cardinal Algebra

universe u

/-! ### Integral extensions -/

section Integral

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Algebra.IsIntegral R S]

theorem strictMono_comap : StrictMono (PrimeSpectrum.comap (algebraMap R S)) := by
  intro p q hpq
  have h : p.asIdeal < q.asIdeal := hpq
  exact Ideal.IsIntegral.under_lt_under (R := R) h

theorem ringKrullDim_le_of_isIntegral : ringKrullDim S ≤ ringKrullDim R :=
  Order.krullDim_le_of_strictMono _ strictMono_comap

theorem ringKrullDim_le_of_isIntegral_of_injective (h : Function.Injective (algebraMap R S)) :
    ringKrullDim R ≤ ringKrullDim S := by
  refine iSup_le fun l => ?_
  obtain ⟨P, -, hP, hPl⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := S)
    l.head.asIdeal ⊥ (by
      intro x hx
      have hx0 : algebraMap R S x = 0 := hx
      rw [(map_eq_zero_iff _ h).mp hx0]
      exact Ideal.zero_mem _)
  have : P.LiesOver l.head.asIdeal := ⟨hPl.symm⟩
  obtain ⟨L, hlen, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P
  rw [← hlen]
  exact Order.LTSeries.length_le_krullDim L

/-- **An injective integral extension has the same Krull dimension.** -/
theorem ringKrullDim_eq_of_isIntegral (h : Function.Injective (algebraMap R S)) :
    ringKrullDim S = ringKrullDim R :=
  le_antisymm ringKrullDim_le_of_isIntegral (ringKrullDim_le_of_isIntegral_of_injective h)

end Integral

/-! ### Affine domains -/

section Affine

variable (K : Type u) [Field K] (A : Type u) [CommRing A] [IsDomain A] [Algebra K A]
  [Algebra.FiniteType K A]

/-- **The Krull dimension of a finitely generated domain is its transcendence degree.** -/
theorem exists_ringKrullDim_eq_trdeg :
    ∃ s : ℕ, ringKrullDim A = s ∧ Algebra.trdeg K A = s := by
  obtain ⟨s, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg K A
  let _ : Algebra (MvPolynomial (Fin s) K) A := g.toRingHom.toAlgebra
  have _ : Algebra.IsIntegral (MvPolynomial (Fin s) K) A := ⟨fun x => hint x⟩
  have hinj' : Function.Injective (algebraMap (MvPolynomial (Fin s) K) A) := hinj
  have _ : @IsScalarTower K (MvPolynomial (Fin s) K) A Algebra.toSMul Algebra.toSMul
      Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq fun r => (g.commutes r).symm
  have _ : FaithfulSMul (MvPolynomial (Fin s) K) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj'
  refine ⟨s, ?_, ?_⟩
  · rw [ringKrullDim_eq_of_isIntegral hinj',
      MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field,
      zero_add, Nat.card_fin]
  · have := trdeg_add_eq K (MvPolynomial (Fin s) K) (A := A)
    rw [MvPolynomial.trdeg_of_isDomain, mk_fin, lift_natCast,
      trdeg_eq_zero (R := MvPolynomial (Fin s) K) (A := A), add_zero] at this
    exact this.symm

include K in
/-- **Localizing an affine domain at a nonzero element does not change its Krull dimension.** -/
theorem ringKrullDim_localization_eq {f : A} (hf : f ≠ 0) (B : Type u) [CommRing B]
    [Algebra A B] [IsLocalization.Away f B] : ringKrullDim B = ringKrullDim A := by
  have hM : Submonoid.powers f ≤ nonZeroDivisors A :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hf
  have _ : IsDomain B := IsLocalization.isDomain_of_le_nonZeroDivisors B hM
  let _ : Algebra K B := ((algebraMap A B).comp (algebraMap K A)).toAlgebra
  have _ : IsScalarTower K A B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have _ : Algebra.FiniteType A B := IsLocalization.finiteType_of_monoid_fg (Submonoid.powers f) B
  have _ : Algebra.FiniteType K B := Algebra.FiniteType.trans (S := A) inferInstance inferInstance
  have _ : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective _ _).mpr
    (IsLocalization.injective B hM)
  have _ : FaithfulSMul K A := (faithfulSMul_iff_algebraMap_injective _ _).mpr
    (algebraMap K A).injective
  have _ : Algebra.IsAlgebraic A B := IsLocalization.isAlgebraic B (Submonoid.powers f)
  obtain ⟨s, hsA, htA⟩ := exists_ringKrullDim_eq_trdeg K A
  obtain ⟨t, hsB, htB⟩ := exists_ringKrullDim_eq_trdeg K B
  have htr := trdeg_add_eq K A (A := B)
  rw [trdeg_eq_zero (R := A) (A := B), add_zero, htA, htB] at htr
  rw [hsA, hsB, Nat.cast_inj.mp htr]

end Affine

end FlagVarieties.Dimension
