import Schubert.RS.RootWeights
import Schubert.RS.Representation.WindowWeightSpaces
import Schubert.RS.Representation.FullWeightSpaces

/-! Full torus weights of the coefficient-window degree pieces. -/

namespace Schubert.RS
noncomputable section
open Representation
variable {n : ℕ}

theorem integerWeightScalar_zero (t : DiagonalTorus n) :
    integerWeightScalar (0 : Weight n) t = 1 := by simp [integerWeightScalar]

theorem integerWeightScalar_nsmul (r : ℕ) (w : Weight n) (t : DiagonalTorus n) :
    integerWeightScalar (r • w) t = integerWeightScalar w t ^ r := by
  induction r with
  | zero => simp [integerWeightScalar_zero]
  | succ r ih =>
    rw [succ_nsmul, integerWeightScalar_add, ih, pow_succ]

theorem integerWeightScalar_sum {ι : Type*} (s : Finset ι)
    (w : ι → Weight n) (t : DiagonalTorus n) :
    integerWeightScalar (∑ i ∈ s, w i) t = ∏ i ∈ s, integerWeightScalar (w i) t := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [integerWeightScalar_zero]
  | @insert i s hi ih => simp [hi, integerWeightScalar_add, ih]

theorem integerWeightScalar_sub (v w : Weight n) (t : DiagonalTorus n) :
    integerWeightScalar (v-w) t = integerWeightScalar v t / integerWeightScalar w t := by
  simp only [integerWeightScalar, Pi.sub_apply, zpow_sub₀ (Units.ne_zero _),
    Finset.prod_div_distrib]

theorem integerWeightScalar_positiveRoot (a b : Fin n) (t : DiagonalTorus n) :
    integerWeightScalar (positiveRoot a b) t = rootScalar t a b := by
  rw [positiveRoot, integerWeightScalar_sub]
  simp [integerWeightScalar, Pi.single_apply, rootScalar]

theorem integerWeightScalar_cut (w : Weight n) (k : Fin (n-1)) :
    integerWeightScalar w (cutTorus k) =
      (2 : ℂ) ^ prefixWeight w ⟨k.val+1, by omega⟩ := by
  classical
  have hp (s : Finset (Fin n)) : (∏ i ∈ s, (2 : ℂ) ^ w i) =
      (2 : ℂ) ^ (∑ i ∈ s, w i) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih => simp [hi, zpow_add₀ (by norm_num : (2 : ℂ) ≠ 0), ih]
  calc
    _ = ∏ i ∈ Finset.univ.filter (fun i : Fin n => i.val ≤ k.val), (2 : ℂ) ^ w i := by
      rw [Finset.prod_filter]
      apply Finset.prod_congr rfl
      intro i _
      by_cases hi : i.val ≤ k.val <;> simp [cutTorus, hi]
    _ = _ := by
      rw [hp]
      congr 1
      unfold prefixWeight
      apply Finset.sum_congr
      · ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_mk]
        omega
      · intros; rfl

theorem rootWeight_monomialDegree (a : PositiveRoot n → ℕ) :
    rootWeight (monomialDegree a) = ∑ r, a r • positiveRoot r.val.1 r.val.2 := by
  change rootWeightHom (∑ r, a r • rootDegree r.val.1 r.val.2) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro r _
  exact (rootWeight_nsmul (a r) _).trans (congrArg (fun w => a r • w)
    (rootWeight_rootDegree r.val.1 r.val.2 r.property))

theorem monomialScalar_fullWeight (order : RootOrdering n) (a : PositiveRoot n → ℕ)
    (t : DiagonalTorus n) :
    integerWeightScalar (rootWeight (monomialDegree a)) t = orderedMonomialScalar order a t := by
  rw [rootWeight_monomialDegree, integerWeightScalar_sum]
  simp_rw [integerWeightScalar_nsmul, integerWeightScalar_positiveRoot]
  unfold orderedMonomialScalar
  rw [← List.prod_toFinset _ order.nodup, rootOrder_toFinset]

def weightOfRootDegree (u : Composition n) (d : RootDegree n) : Weight n :=
  (fun i => (u i : ℤ)) + rootWeight d

theorem degreePiece_full_eigen (order : RootOrdering n) (hpbw : HasOrderedPBWBasis n)
    (d : RootDegree n) {x : Enveloping n} (hx : x ∈ envelopingDegreePiece order hpbw d)
    (t : DiagonalTorus n) :
    torusEnveloping t x = integerWeightScalar (rootWeight d) t • x := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    rw [envelopingBasis_apply, torusEnveloping_ordered, ← monomialScalar_fullWeight, ha]
  | zero => simp
  | add x y hx hy ihx ihy => simp only [map_add, ihx, ihy, smul_add]
  | smul c x hx ih => simp only [map_smul, ih, smul_comm c]

theorem jpDegreePiece_full_eigen (u : Composition n) (hpbw : HasOrderedPBWBasis n)
    (d : RootDegree n) {x : PresentationQuotient u} (hx : x ∈ jpDegreePiece u hpbw d) :
    x ∈ torusWeightSpace (jpTorusRepresentation u) (weightOfRootDegree u d) := by
  obtain ⟨a, ha, rfl⟩ := hx
  intro t
  change weightScalar u t • quotientScale (jpLeftIdeal u) _ t (Submodule.Quotient.mk a) = _
  rw [quotientScale_mk, degreePiece_full_eigen _ hpbw d ha,
    Submodule.Quotient.mk_smul, smul_smul]
  rw [weightOfRootDegree, integerWeightScalar_add, integerWeightScalar_nat]
  rfl

theorem linearDegreePiece_full_eigen (u : Composition n) (hpbw : HasOrderedPBWBasis n)
    (d : RootDegree n) {x : LinearPresentationQuotient u} (hx : x ∈ linearDegreePiece u hpbw d) :
    x ∈ torusWeightSpace (linearTorusRepresentation u) (weightOfRootDegree u d) := by
  obtain ⟨a, ha, rfl⟩ := hx
  intro t
  change weightScalar u t • quotientScale (linearLeftIdeal u) _ t (Submodule.Quotient.mk a) = _
  rw [quotientScale_mk, degreePiece_full_eigen _ hpbw d ha,
    Submodule.Quotient.mk_smul, smul_smul]
  rw [weightOfRootDegree, integerWeightScalar_add, integerWeightScalar_nat]
  rfl

theorem weightOfRootDegree_cut (u : Composition n) (d : RootDegree n) (k : Fin (n-1)) :
    integerWeightScalar (weightOfRootDegree u d) (cutTorus k) =
      weightScalar u (cutTorus k) * (2 : ℂ) ^ d k := by
  rw [weightOfRootDegree, integerWeightScalar_add, integerWeightScalar_nat,
    integerWeightScalar_cut, prefixWeight_rootWeight_cut]
  simp

theorem jpDegreePiece_eq_fullWeightSpace (u : Composition n) (hpbw : HasOrderedPBWBasis n)
    (d : RootDegree n) :
    jpDegreePiece u hpbw d = torusWeightSpace (jpTorusRepresentation u) (weightOfRootDegree u d) := by
  ext x
  constructor
  · exact jpDegreePiece_full_eigen u hpbw d
  · intro hx
    apply (mem_jpDegreePiece_iff_cut_eigen u hpbw d x).mpr
    intro k
    have h := hx (cutTorus k)
    rwa [weightOfRootDegree_cut] at h

theorem linearDegreePiece_eq_fullWeightSpace (u : Composition n) (hpbw : HasOrderedPBWBasis n)
    (d : RootDegree n) :
    linearDegreePiece u hpbw d = torusWeightSpace (linearTorusRepresentation u) (weightOfRootDegree u d) := by
  ext x
  constructor
  · exact linearDegreePiece_full_eigen u hpbw d
  · intro hx
    apply (mem_linearDegreePiece_iff_cut_eigen u hpbw d x).mpr
    intro k
    have h := hx (cutTorus k)
    rwa [weightOfRootDegree_cut] at h

theorem windowFullWeightSpace_finrank (u : Composition n) (hpbw : HasOrderedPBWBasis n)
    (β d : RootDegree n) (hd : d ≤ β)
    (hβ : ∀ r : PositiveRoot n, u r.val.1 < u r.val.2 →
      ¬ jpExponent u r • rootDegree r.val.1 r.val.2 ≤ β) :
    Module.finrank ℂ (torusWeightSpace (linearTorusRepresentation u) (weightOfRootDegree u d)) =
      Module.finrank ℂ (torusWeightSpace (jpTorusRepresentation u) (weightOfRootDegree u d)) := by
  rw [← linearDegreePiece_eq_fullWeightSpace u hpbw d, ← jpDegreePiece_eq_fullWeightSpace u hpbw d]
  exact windowDegree_finrank u hpbw β d hd hβ

end
end Schubert.RS
