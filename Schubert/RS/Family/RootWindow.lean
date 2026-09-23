import Schubert.RS.Family.RootPattern
import Schubert.RS.AtomExpansionCertificate
import Schubert.RS.Representation.CompositionFlag

/-! The coefficient window for arbitrary family parameters, under explicit
Joseph-Polo, Demazure character, and PBW hypotheses. -/

namespace Schubert.RS.Family
noncomputable section
open Representation

def targetDifference (P : Parameters) : Weight P.rank :=
  fun i => (c P i : ℤ)-a P i-b P i

def coefficientBox (P : Parameters) : RootDegree P.rank :=
  Finsupp.equivFunOnFinite.symm (fun k => beta P ⟨k.val+1,by omega⟩)

theorem coefficientBox_bound (P : Parameters) (k : Fin (P.rank-1)) :
    coefficientBox P k ≤ P.m+1 := beta_bound P _

theorem extended_coefficientBox (P : Parameters) (k : Fin (P.rank+1)) :
    extendedRootDegree (coefficientBox P) k=(beta P k : ℤ) := by
  unfold extendedRootDegree
  split_ifs with h
  · change (beta P ⟨k.val-1+1,by omega⟩ : ℤ)=(beta P k : ℤ)
    have he : (⟨k.val-1+1,by omega⟩ : Fin (P.rank+1))=k := by
      apply Fin.ext
      simp only [Fin.val_mk]
      omega
    rw [he]
  · have he : k=0 ∨ k=Fin.last P.rank := by
      have hk := k.isLt
      simp only [Fin.ext_iff,Fin.val_zero,Fin.val_last]
      omega
    rcases he with rfl | rfl
    · simp [beta_start]
    · simp [beta_finish]

theorem rootWeight_coefficientBox (P : Parameters) :
    rootWeight (coefficientBox P)=targetDifference P := by
  rw [rootWeight_discrete]
  funext j
  simp only [extended_coefficientBox]
  exact beta_recurrence P j

theorem beta_is_prefix (P : Parameters) (k : Fin (P.rank+1)) :
    prefixWeight (targetDifference P) k=(beta P k : ℤ) := by
  rw [← rootWeight_coefficientBox,prefixWeight_rootWeight,extended_coefficientBox]

theorem power_a_outside (P : Parameters) (i j : Fin P.rank)
    (hij : i<j) (h : a P i<a P j) :
    ¬(a P j-a P i+1) • rootDegree i j ≤ coefficientBox P :=
  root_power_outside_window i j hij _ _
    (lt_of_le_of_lt (coefficientBox_bound P _) (ascent_gap_a P i j h))

theorem power_b_outside (P : Parameters) (i j : Fin P.rank)
    (hij : i<j) (h : b P i<b P j) :
    ¬(b P j-b P i+1) • rootDegree i j ≤ coefficientBox P :=
  root_power_outside_window i j hij _ _
    (lt_of_le_of_lt (coefficientBox_bound P _) (ascent_gap_b P i j h))

theorem power_g_outside (P : Parameters) (i j : Fin P.rank)
    (hij : i<j) (h : g P i<g P j) :
    ¬(g P j-g P i+1) • rootDegree i j ≤ coefficientBox P :=
  root_power_outside_window i j hij _ _
    (lt_of_le_of_lt (coefficientBox_bound P _) (ascent_gap_g P i j h))

theorem rectangular_target (P : Parameters) :
    (fun i => (a P i : ℤ)+b P i+g P i)+rootWeight (coefficientBox P)=
      (fun _ => (P.rectangle : ℤ)) := by
  rw [rootWeight_coefficientBox]
  funext i
  have he : g P i+c P i=P.rectangle := Nat.sub_add_cancel (c_le P i)
  change (a P i : ℤ)+b P i+g P i+((c P i : ℤ)-a P i-b P i)=P.rectangle
  omega

theorem family_rectangle_eq_root_product (P : Parameters)
    (hJP : ∀ u : Composition P.rank, CompositionFlagJosephPolo u)
    (hDCF : ∀ u : Composition P.rank, CompositionFlagDemazureCharacter u) (hpbw : HasOrderedPBWBasis P.rank) :
    rectangleCoefficient P.rectangle (c P) (key (a P)*key (b P))=
      MvPowerSeries.coeff (coefficientBox P)
        (∏ r : PositiveRoot P.rank, familyRootFactor P r) := by
  have h := three_key_window_coefficient compositionFlagTorus compositionFlagGenerator
    hJP hDCF hpbw (a P) (b P) (g P) (coefficientBox P)
    (fun r hr => power_a_outside P r.val.1 r.val.2 r.property hr)
    (fun r hr => power_b_outside P r.val.1 r.val.2 r.property hr)
    (fun r hr => power_g_outside P r.val.1 r.val.2 r.property hr)
  rw [rectangular_target,family_root_series_eq_product] at h
  unfold rectangleCoefficient
  rw [map_mul]
  exact h

theorem family_expansion_root_coefficient (P : Parameters)
    (hJP : ∀ u : Composition P.rank, CompositionFlagJosephPolo u)
    (hDCF : ∀ u : Composition P.rank, CompositionFlagDemazureCharacter u) (hpbw : HasOrderedPBWBasis P.rank)
    (t : Composition P.rank →₀ ℤ)
    (ht : key (a P)*key (b P)=t.sum (fun u z => z • atom u)) :
    t (c P)=MvPowerSeries.coeff (coefficientBox P)
      (∏ r : PositiveRoot P.rank, familyRootFactor P r) := by
  rw [← rectangleCoefficient_expansion compositionFlagTorus compositionFlagGenerator
    hJP hDCF hpbw P.rectangle (c P) (c_le P) t,← ht]
  exact family_rectangle_eq_root_product P hJP hDCF hpbw

end
end Schubert.RS.Family

