import Schubert.FlagVarieties.Charts.AdaptedBasis
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Every complete flag over a field lies in a big cell

Let `V₀ ⊆ V₁ ⊆ ⋯ ⊆ Vₙ = Kⁿ` be a complete flag over a field `K` (`dim Vⱼ = j`). Then there is a
permutation `v` with `Vⱼ ⊕ span(e_{v(j)}, …, e_{v(n-1)}) = Kⁿ` for every `j`
(`exists_perm_isCompl_tailSpan`).

The proof chooses `v(n-1), v(n-2), …` in turn: if `T` is a complement of `V_{j+1}` spanned by
coordinate vectors, then `V_j ⊔ T` is a hyperplane, and any coordinate vector outside it extends
`T` to a complement of `V_j`.
-/

noncomputable section

namespace FlagVarieties

variable {K : Type*} [Field K] {n : ℕ}

/-- The span of the coordinate vectors `e_{t(i)}` for the indices `i ≥ k`. -/
def coordSpanFrom {m : ℕ} (t : Fin m → Fin n) (k : ℕ) : Submodule K (Fin n → K) :=
  Submodule.span K ((fun i => Pi.single (t i) (1 : K)) '' {i : Fin m | k ≤ i.val})

theorem coordSpanFrom_cons_succ {m : ℕ} (c : Fin n) (t : Fin m → Fin n) (k : ℕ) :
    coordSpanFrom (K := K) (Fin.cons c t : Fin (m + 1) → Fin n) (k + 1) = coordSpanFrom t k := by
  unfold coordSpanFrom
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨i, hi, rfl⟩
    cases i using Fin.cases with
    | zero => simp at hi
    | succ i => exact ⟨i, by simpa using hi, by simp⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i.succ, by simpa using hi, by simp⟩

theorem coordSpanFrom_cons_zero {m : ℕ} (c : Fin n) (t : Fin m → Fin n) :
    coordSpanFrom (K := K) (Fin.cons c t : Fin (m + 1) → Fin n) 0 =
      coordSpanFrom t 0 ⊔ Submodule.span K {Pi.single c (1 : K)} := by
  unfold coordSpanFrom
  rw [← Submodule.span_union]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_ofPred_eq, zero_le, true_and, Set.mem_union,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    cases i using Fin.cases with
    | zero => exact Or.inr (by simp)
    | succ i => exact Or.inl ⟨i, by simp⟩
  · rintro (⟨i, rfl⟩ | rfl)
    · exact ⟨i.succ, by simp⟩
    · exact ⟨0, by simp⟩

variable (V : ℕ → Submodule K (Fin n → K)) (hmono : Monotone V)
  (hdim : ∀ j, j ≤ n → Module.finrank K (V j) = j)

include hmono hdim in
theorem exists_coordSpan_complements (m : ℕ) (hm : m ≤ n) :
    ∃ t : Fin m → Fin n, Function.Injective t ∧
      ∀ k, k ≤ m → IsCompl (V (n - (m - k))) (coordSpanFrom (K := K) t k) := by
  induction m with
  | zero =>
    refine ⟨Fin.elim0, fun i => i.elim0, fun k hk => ?_⟩
    have hk0 : k = 0 := Nat.le_zero.mp hk
    subst hk0
    have htop : V n = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [hdim n le_rfl, Module.finrank_fin_fun]
    have hbot : coordSpanFrom (K := K) (Fin.elim0 : Fin 0 → Fin n) 0 = ⊥ := by
      unfold coordSpanFrom
      rw [Submodule.span_eq_bot]
      rintro _ ⟨i, _, rfl⟩
      exact i.elim0
    simp only [Nat.sub_zero]
    rw [htop, hbot]
    exact isCompl_top_bot
  | succ m ih =>
    obtain ⟨t, ht, hc⟩ := ih (Nat.le_of_succ_le hm)
    set W := V (n - (m + 1)) with hW
    set T := coordSpanFrom (K := K) t 0 with hT
    have hTc : IsCompl (V (n - m)) T := by
      simpa using hc 0 (Nat.zero_le _)
    have hWV : W ≤ V (n - m) := hmono (by omega)
    have hdimW : Module.finrank K W = n - (m + 1) := hdim _ (by omega)
    have hdimV : Module.finrank K (V (n - m)) = n - m := hdim _ (by omega)
    have hdimT : Module.finrank K T = m := by
      have := Submodule.finrank_sup_add_finrank_inf_eq (V (n - m)) T
      rw [hTc.sup_eq_top, hTc.inf_eq_bot, finrank_top, finrank_bot, Module.finrank_fin_fun,
        hdimV] at this
      omega
    -- the hyperplane `W ⊔ T`
    have hH : W ⊔ T ≠ ⊤ := by
      intro h
      have h1 := Submodule.finrank_sup_add_finrank_inf_eq W T
      have hinf : W ⊓ T = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        have := hTc.inf_eq_bot
        rw [← this]
        exact ⟨hWV hx.1, hx.2⟩
      rw [h, hinf, finrank_top, finrank_bot, Module.finrank_fin_fun, hdimW, hdimT] at h1
      omega
    obtain ⟨c, hcH⟩ : ∃ c : Fin n, Pi.single c (1 : K) ∉ W ⊔ T := by
      by_contra hall
      simp only [not_exists, not_not] at hall
      apply hH
      rw [eq_top_iff, ← (Pi.basisFun K (Fin n)).span_eq, Submodule.span_le]
      rintro _ ⟨c, rfl⟩
      simpa [Pi.basisFun_apply] using hall c
    have hcT : ∀ i, t i ≠ c := by
      intro i hi
      apply hcH
      apply Submodule.mem_sup_right
      rw [← hi]
      exact Submodule.subset_span ⟨i, Nat.zero_le _, rfl⟩
    refine ⟨Fin.cons c t, ?_, fun k hk => ?_⟩
    · rw [Fin.cons_injective_iff]
      exact ⟨fun ⟨i, hi⟩ => hcT i hi, ht⟩
    · rcases Nat.eq_zero_or_pos k with rfl | hkpos
      · -- the new complement `T ⊔ ⟨e_c⟩` of `W`
        rw [coordSpanFrom_cons_zero, ← hT]
        simp only [Nat.sub_zero]
        have hdisj : Disjoint W (T ⊔ Submodule.span K {Pi.single c (1 : K)}) := by
          rw [Submodule.disjoint_def]
          intro x hxW hx
          obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
          obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hz
          by_cases ha : a = 0
          · subst ha
            rw [zero_smul, add_zero] at hxW ⊢
            have := hTc.inf_eq_bot
            have hy0 : y ∈ V (n - m) ⊓ T := ⟨hWV hxW, hy⟩
            rw [this] at hy0
            exact hy0
          · exfalso
            apply hcH
            have : Pi.single c (1 : K) = a⁻¹ • ((y + a • Pi.single c 1) - y) := by
              rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ ha, one_smul]
            rw [this]
            exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.mem_sup_left hxW)
              (Submodule.mem_sup_right hy))
        refine ⟨hdisj, ?_⟩
        rw [codisjoint_iff]
        apply Submodule.eq_top_of_finrank_eq
        have hcT' : Disjoint T (Submodule.span K {Pi.single c (1 : K)}) := by
          rw [Submodule.disjoint_span_singleton' (by simp)]
          exact fun h => hcH (Submodule.mem_sup_right h)
        have h1 := Submodule.finrank_sup_add_finrank_inf_eq W
          (T ⊔ Submodule.span K {Pi.single c (1 : K)})
        have h2 := Submodule.finrank_sup_add_finrank_inf_eq T
          (Submodule.span K {Pi.single c (1 : K)})
        rw [hdisj.eq_bot, finrank_bot] at h1
        rw [hcT'.eq_bot, finrank_bot, finrank_span_singleton (by simp), hdimT] at h2
        rw [Module.finrank_fin_fun, ← hW]
        omega
      · obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hkpos)
        rw [coordSpanFrom_cons_succ]
        have := hc k' (by omega)
        have he : n - (m + 1 - (k' + 1)) = n - (m - k') := by omega
        rwa [he]

include hmono hdim in
/-- Every complete flag over a field is in good position for some permutation. -/
theorem exists_perm_isCompl_tailSpan :
    ∃ v : Equiv.Perm (Fin n), ∀ j, j ≤ n → IsCompl (V j) (tailSpan v j) := by
  obtain ⟨t, ht, hc⟩ := exists_coordSpan_complements V hmono hdim n le_rfl
  have hbij : Function.Bijective t := (Finite.injective_iff_bijective).mp ht
  refine ⟨Equiv.ofBijective t hbij, fun j hj => ?_⟩
  have h := hc j hj
  have he : n - (n - j) = j := by omega
  rw [he] at h
  convert h using 1
  unfold tailSpan coordSpanFrom
  rfl

end FlagVarieties
