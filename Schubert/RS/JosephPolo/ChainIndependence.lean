import Schubert.RS.JosephPolo.DefiningChains

namespace Schubert.RS.Representation
noncomputable section
open FinPermutation
open scoped BigOperators
set_option maxHeartbeats 600000
universe u

/-- A relation among distinct chain-admissible products is detected on the
union of their chosen ambient orbits. The proof inducts on the number of
columns, not on a character formula or a straightening assertion. -/
theorem flagColumnProduct_relation_zero {n d : ℕ} :
    ∀ (h : Fin d → Fin n) {ι : Type u} [Fintype ι]
      (T : ι → (j : Fin d) → FlagMinorRowSet (h j))
      (hT : Function.Injective T) (W : ι → FinPermutation n)
      (hchain : ∀ i, HasFlagDefiningChain h (T i) (W i)) (c : ι → ℂ),
      (∀ i, flagOrbitRestriction (W i) (∑ j, c j • flagColumnProduct h (T j)) = 0) →
      ∀ i, c i = 0 := by
  classical
  induction d with
  | zero =>
    intro h ι inst T hT W hchain c hz i
    have hall (j : ι) : j = i := hT (funext fun k => Fin.elim0 k)
    have heq : (∑ j, c j • flagColumnProduct h (T j)) = c i • (1 : MatrixPolynomial n) := by
      rw [Finset.sum_eq_single i]
      · simp [flagColumnProduct]
      · intro j hj hji
        exact False.elim (hji (hall j))
      · simp
    have he := congrFun (hz i) []
    rw [heq,map_smul,map_one] at he
    simpa using he
  | succ d ih =>
    intro h ι inst T hT W hchain c hz
    by_contra hn
    push Not at hn
    obtain ⟨i₁,hi₁⟩ := hn
    let support : Finset ι := Finset.univ.filter fun i => c i ≠ 0
    have hs : support.Nonempty := ⟨i₁,by simp [support,hi₁]⟩
    obtain ⟨i₀,hi₀,hmin⟩ := support.exists_min_image
      (fun i => ∑ j, ((T i (Fin.last d)).rows j).val) hs
    have hc₀ : c i₀ ≠ 0 := (Finset.mem_filter.mp hi₀).2
    let C : FlagMinorRowSet (h (Fin.last d)) := T i₀ (Fin.last d)
    let J := {i : ι // c i ≠ 0 ∧ T i (Fin.last d) = C}
    let j₀ : J := ⟨i₀,hc₀,rfl⟩
    have houtside (i : ι) (hci : c i ≠ 0) (hCi : T i (Fin.last d) ≠ C) :
        ¬ ∀ j, (T i (Fin.last d)).rows j ≤ C.rows j := by
      intro hle
      apply hCi
      exact FlagMinorRowSet.eq_of_le_of_sum_le hle
        (hmin i (by simp [support,hci]))
    choose V hVW hVC hprefix using (fun i => (hchain i).last)
    have hrelmem : (∑ j, c j • flagColumnProduct h (T j)) ∈
        Submodule.span ℂ (Set.range (flagColumnProduct h)) := by
      apply Submodule.sum_mem
      intro j hj
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨T j,rfl⟩)
    have hwhole (i : J) : flagOrbitRestriction (V i.val)
        (∑ j : J, c j.val • flagColumnProduct h (T j.val)) = 0 := by
      have hres := flagOrbitRestriction_zero_of_bruhat_columns h (hVW i.val)
        (∑ j, c j • flagColumnProduct h (T j)) hrelmem (hz i.val)
      have heq : flagOrbitRestriction (V i.val)
          (∑ j : J, c j.val • flagColumnProduct h (T j.val)) =
          flagOrbitRestriction (V i.val) (∑ j, c j • flagColumnProduct h (T j)) := by
        simp only [map_sum,map_smul]
        apply Fintype.sum_of_injective (fun j : J => j.val) Subtype.val_injective
        · intro j hj
          by_cases hcj : c j = 0
          · rw [hcj,zero_smul]
          · have hCj : T j (Fin.last d) ≠ C := by
              intro he
              exact hj ⟨⟨j,hcj,he⟩,rfl⟩
            have hm : flagOrbitRestriction (V i.val)
                (flagRowMinor (h (Fin.last d)) (T j (Fin.last d)).rows) = 0 := by
              apply flagOrbitRestriction_minor_zero
              rw [hVC i.val,i.property.2]
              exact houtside j hcj hCj
            rw [flagColumnProduct_fin_succ,map_mul,hm,mul_zero,smul_zero]
        · intro j
          rfl
      exact heq.trans hres
    have hfactor : (∑ j : J, c j.val • flagColumnProduct h (T j.val)) =
        (∑ j : J, c j.val • flagColumnProduct (fun k => h k.castSucc)
          (fun k => T j.val k.castSucc)) * flagRowMinor (h (Fin.last d)) C.rows := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      rw [flagColumnProduct_fin_succ,j.property.2,smul_mul_assoc]
    have htailzero (i : J) : flagOrbitRestriction (V i.val)
        (∑ j : J, c j.val • flagColumnProduct (fun k => h k.castSucc)
          (fun k => T j.val k.castSucc)) = 0 := by
      have he := hwhole i
      rw [hfactor,map_mul] at he
      funext z
      have hp := congrFun he z
      have hm : flagOrbitRestriction (V i.val) (flagRowMinor (h (Fin.last d)) C.rows) z ≠ 0 := by
        have heC : flagPrefixRows (V i.val) (h (Fin.last d)) = C := (hVC i.val).trans i.property.2
        simpa only [heC] using
          flagOrbitRestriction_prefix_minor_ne_zero (V i.val) (h (Fin.last d)) z
      exact (mul_eq_zero.mp hp).resolve_right hm
    have htailinj : Function.Injective (fun i : J => fun k : Fin d => T i.val k.castSucc) := by
      intro i j he
      apply Subtype.ext
      apply hT
      funext k
      refine Fin.lastCases ?_ (fun a => ?_) k
      · exact i.property.2.trans j.property.2.symm
      · exact congrFun he a
    have hresult := ih (fun k => h k.castSucc)
      (fun i : J => fun k => T i.val k.castSucc) htailinj
      (fun i : J => V i.val) (fun i => hprefix i.val) (fun i => c i.val) htailzero
    exact hc₀ (hresult j₀)

end
end Schubert.RS.Representation
