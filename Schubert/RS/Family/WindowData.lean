import Schubert.RS.Family.Data

/-! Uniform residual, prefix and defining-power bounds for the exact family,
including the least allowed scale and empty middle blocks. -/

namespace Schubert.RS.Family

theorem rectangle_large (P : Parameters) : P.K+1 ≤ P.rectangle := by
  have hk := P.K_pos
  have hm := P.m_pos
  have hmul : P.K ≤ P.m*P.K := by
    simpa using Nat.mul_le_mul_right P.K (show 1 ≤ P.m by omega)
  unfold Parameters.rectangle
  rw [Nat.add_mul]
  omega

theorem c_le (P : Parameters) (i : Fin P.rank) : c P i ≤ P.rectangle := by
  unfold c
  split_ifs
  · exact rectangle_large P
  · exact le_rfl

theorem g_value (P : Parameters) (i : Fin P.rank) :
    g P i = if sourceClass P i then (P.m+2)*P.K-2 else 0 := by
  have hk := P.K_pos
  have hm := P.m_pos
  unfold g c Parameters.rectangle
  split_ifs <;> simp only [Nat.add_mul] <;> omega

theorem source_sum (P : Parameters) (i : Fin P.rank) (h : sourceClass P i) :
    a P i+b P i=P.K := by
  have hi : (coordinateClass P i).val=0 ∨ (coordinateClass P i).val=1 := by
    change (coordinateClass P i).val < 2 at h
    omega
  rcases hi with hi | hi <;> simp [a,b,hi]

theorem target_sum (P : Parameters) (i : Fin P.rank) (h : ¬sourceClass P i) :
    a P i+b P i=(P.m+3)*P.K := by
  have hc := (coordinateClass P i).isLt
  have hi : 2 ≤ (coordinateClass P i).val := by
    change ¬(coordinateClass P i).val < 2 at h
    omega
  simp only [a,b,show (coordinateClass P i).val ≠ 0 by omega,
    show (coordinateClass P i).val ≠ 1 by omega,if_false]
  rw [← Nat.add_mul]
  congr 1
  omega

theorem residual_pattern (P : Parameters) (i : Fin P.rank) :
    (c P i : ℤ)-a P i-b P i=if sourceClass P i then 1 else -1 := by
  by_cases h : sourceClass P i
  · have hs := source_sum P i h
    simp only [c,h,if_true]
    omega
  · have ht := target_sum P i h
    have hp : 0 < (P.m+3)*P.K := Nat.mul_pos (by omega) P.K_pos
    simp only [c,h,if_false,Parameters.rectangle]
    omega

def beta (P : Parameters) (i : Fin (P.rank+1)) : ℕ :=
  if i.val ≤ P.m+1 then i.val
  else if i.val ≤ 2*P.m+1 then 2*P.m+2-i.val
  else if i.val ≤ 3*P.m then i.val-2*P.m
  else 4*P.m-i.val

theorem beta_bound (P : Parameters) (i : Fin (P.rank+1)) : beta P i ≤ P.m+1 := by
  have hi := i.isLt
  change i.val < 4*P.m+1 at hi
  unfold beta
  split_ifs <;> omega

theorem beta_start (P : Parameters) : beta P 0=0 := by simp [beta]

theorem beta_finish (P : Parameters) : beta P (Fin.last P.rank)=0 := by
  have hm := P.m_pos
  unfold beta
  split_ifs <;> simp only [Fin.val_last,Parameters.rank] at * <;> omega

theorem beta_recurrence (P : Parameters) (i : Fin P.rank) :
    (beta P i.succ : ℤ)-beta P i.castSucc=(c P i : ℤ)-a P i-b P i := by
  rw [residual_pattern]
  simp only [sourceClass_iff,beta,Fin.val_succ,Fin.val_castSucc]
  have hi := i.isLt
  change i.val < 4*P.m at hi
  have hm := P.m_pos
  split_ifs <;> omega

theorem scaled_strict_gap (x y K : ℕ) (h : x*K<y*K) : K ≤ y*K-x*K := by
  have hxy : x<y := Nat.lt_of_mul_lt_mul_right h
  have he := Nat.mul_le_mul_right K (Nat.succ_le_of_lt hxy)
  simp only [Nat.succ_mul] at he
  omega

theorem ascent_gap_a (P : Parameters) (i j : Fin P.rank) (h : a P i<a P j) :
    P.m+1 < a P j-a P i+1 := by
  have he := scaled_strict_gap _ _ P.K h
  have hk := P.K_bound
  change P.K ≤ a P j-a P i at he
  omega

theorem ascent_gap_b (P : Parameters) (i j : Fin P.rank) (h : b P i<b P j) :
    P.m+1 < b P j-b P i+1 := by
  have he := scaled_strict_gap _ _ P.K h
  have hk := P.K_bound
  change P.K ≤ b P j-b P i at he
  omega

theorem ascent_gap_g (P : Parameters) (i j : Fin P.rank) (h : g P i<g P j) :
    P.m+1 < g P j-g P i+1 := by
  have hm := P.m_pos
  have hk := P.K_bound
  have hmul : P.K ≤ P.m*P.K := by
    simpa using Nat.mul_le_mul_right P.K (show 1 ≤ P.m by omega)
  rw [g_value P i,g_value P j] at h ⊢
  split_ifs at h ⊢ <;> (try simp_all only [Nat.add_mul]) <;> omega

theorem rank28_beta : beta rank28Parameters=Counterexample.beta := by
  apply funext
  change ∀ i : Fin 29, beta rank28Parameters i=Counterexample.beta i
  simp only [beta,rank28Parameters,Parameters.rank,Parameters.m]
  decide

end Schubert.RS.Family



