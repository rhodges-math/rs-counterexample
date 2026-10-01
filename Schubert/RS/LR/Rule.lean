import Schubert.RS.LR.Involution

/-!
# The Littlewood–Richardson rule

For a weakly decreasing integer weight `κ` (a rational weight of `GL_d`) and a Young diagram `ν`,

  `a_{κ + δ} · s_ν = ∑_T a_{κ + wt(T) + δ}`,

the sum running over the semistandard tableaux `T` of shape `ν` in the letters `0, …, d − 1`
that are lattice from `κ` (`Schubert.RS.LR.alternant_mul_schur`). Here `a` is the alternant and
`δ = (d − 1, …, 0)` the staircase (`Schubert.RS.Quiver.Schur`).

Proof: `s_ν = ∑_T x^{wt T}` is symmetric, so `a_{κ+δ} s_ν = ∑_T a_{κ + δ + wt T}`
(`Schubert.RS.Quiver.Schur.alternant_mul_sum_single`). On the tableaux that are not lattice, the
involution of `Schubert/RS/LR/Involution.lean` reverses the sign: it replaces `κ + δ + wt T` by
its image under the transposition of `i` and `i + 1` (`Schubert.RS.LR.weight_lrSwapB`).

## Main results

* `Schubert.RS.LR.alternant_mul_schur`: the Littlewood–Richardson rule, alternant form.
* `Schubert.RS.LR.coeff_alternant_mul_schur`: the coefficient of `a_{λ + δ}` counts LR tableaux.
* `Schubert.RS.LR.alternant_mul_shiftedSchur`: the same with a determinant twist `det^k`.
* `Schubert.RS.LR.weylProjector_ratSchur_mul_schur`: in projector form, the multiplicity of `s_λ`
  in `s_κ · s_ν` is the number of tableaux of shape `ν` lattice from `κ` with `κ + wt T = λ`.
-/

namespace Schubert.RS.LR

noncomputable section

open SemistandardYoungTableau Schubert.RS.Quiver.Schur Equiv

variable {d : ℕ} {ν : YoungDiagram} {κ : Weight d}

/-! ### The involution on bounded tableaux -/

/-- The involution, on tableaux in the letters `0, …, d − 1`. -/
def lrSwapB (hκ : Antitone κ) (T : TauCeti.BoundedSSYT d ν) {r i : ℕ}
    (h : IsFirstViolation κ T.1 r i) : TauCeti.BoundedSSYT d ν :=
  ⟨lrSwap hκ h, fun a c hac => by
    have hlt := h.lt
    rw [lrSwap, recut_apply]
    split_ifs
    · omega
    · omega
    · exact T.2 a c hac⟩

theorem lrSwapB_val (hκ : Antitone κ) (T : TauCeti.BoundedSSYT d ν) {r i : ℕ}
    (h : IsFirstViolation κ T.1 r i) : (lrSwapB hκ T h).1 = lrSwap hκ h :=
  rfl

/-- **The sign-reversing property**: the involution replaces `κ + wt T + δ` by its image under the
transposition of the letters `i` and `i + 1`. -/
theorem weight_lrSwapB (hκ : Antitone κ) (T : TauCeti.BoundedSSYT d ν) {r i : ℕ}
    (h : IsFirstViolation κ T.1 r i) :
    κ + weightVec (lrSwapB hκ T h) + staircase d =
      (κ + weightVec T + staircase d) ∘ ⇑(swap (⟨i, by have := h.lt; omega⟩ : Fin d)
        ⟨i + 1, h.lt⟩) := by
  have hlt := h.lt
  have hadd := content_lrSwap_add hκ h
  have hpair := content_lrSwap_pair hκ h
  have he := eNat_eq hκ h
  rw [balance] at he
  have hki := kap_of_lt κ (i := i) (by omega)
  have hki' := kap_of_lt κ hlt
  have hz : ((content (lrSwap hκ h) i : ℕ) : ℤ) + (eNat κ T.1 r i : ℕ) + 1 +
      (countBelow T.1 r (i + 1) : ℕ) = (content T.1 (i + 1) : ℕ) + (countBelow T.1 r i : ℕ) := by
    exact_mod_cast hadd
  have hp : ((content (lrSwap hκ h) i : ℕ) : ℤ) + (content (lrSwap hκ h) (i + 1) : ℕ) =
      (content T.1 i : ℕ) + (content T.1 (i + 1) : ℕ) := by
    exact_mod_cast hpair
  rw [hki, hki'] at he
  funext x
  obtain ⟨x, hx⟩ := x
  simp only [Pi.add_apply, Function.comp_apply, weightVec, lrSwapB_val, staircase]
  by_cases hxi : x = i
  · subst hxi
    rw [swap_apply_left]
    simp only
    push_cast at *
    linarith
  · by_cases hxi' : x = i + 1
    · subst hxi'
      rw [swap_apply_right]
      simp only
      push_cast at *
      linarith
    · rw [swap_apply_of_ne_of_ne (fun e => hxi (congrArg Fin.val e))
        (fun e => hxi' (congrArg Fin.val e)), content_lrSwap_of_ne hκ h hxi hxi']

/-- An alternant changes sign under a transposition. -/
theorem alternant_comp_swap (β : Weight d) {a b : Fin d} (hab : a ≠ b) :
    alternant (β ∘ ⇑(swap a b)) = -alternant β := by
  rw [alternant_comp_perm, Perm.sign_swap hab]
  ext w
  rw [coeff_single_zero_mul]
  simp

/-- On a tableau that is not lattice, the involution reverses the sign of the alternant term. -/
theorem alternant_lrSwapB (hκ : Antitone κ) (T : TauCeti.BoundedSSYT d ν) {r i : ℕ}
    (h : IsFirstViolation κ T.1 r i) :
    alternant (κ + weightVec (lrSwapB hκ T h) + staircase d) =
      -alternant (κ + weightVec T + staircase d) := by
  rw [weight_lrSwapB hκ T h, alternant_comp_swap]
  intro e
  have := congrArg Fin.val e
  simp at this

theorem lrSwapB_lrSwapB (hκ : Antitone κ) (T : TauCeti.BoundedSSYT d ν) {r i r' i' : ℕ}
    (h : IsFirstViolation κ T.1 r i) (h' : IsFirstViolation κ (lrSwapB hκ T h).1 r' i') :
    lrSwapB hκ (lrSwapB hκ T h) h' = T := by
  obtain ⟨rfl, rfl⟩ := (isFirstViolation_lrSwap hκ h).unique h'
  exact Subtype.ext (lrSwap_lrSwap hκ h)

/-- The first violation of a tableau that is not lattice. -/
def firstViolation {T : _root_.SemistandardYoungTableau ν} (h : ¬ IsLattice κ T) : ℕ × ℕ :=
  Classical.choose (show ∃ p : ℕ × ℕ, IsFirstViolation κ T p.1 p.2 by
    obtain ⟨r, i, hri⟩ := exists_isFirstViolation h
    exact ⟨(r, i), hri⟩)

theorem isFirstViolation_firstViolation {T : _root_.SemistandardYoungTableau ν}
    (h : ¬ IsLattice κ T) :
    IsFirstViolation κ T (firstViolation h).1 (firstViolation h).2 :=
  Classical.choose_spec (show ∃ p : ℕ × ℕ, IsFirstViolation κ T p.1 p.2 by
    obtain ⟨r, i, hri⟩ := exists_isFirstViolation h
    exact ⟨(r, i), hri⟩)

/-- The involution on all bounded tableaux: the identity on the lattice ones. -/
def lrInv (hκ : Antitone κ) (T : TauCeti.BoundedSSYT d ν) : TauCeti.BoundedSSYT d ν :=
  if h : IsLattice κ T.1 then T else lrSwapB hκ T (isFirstViolation_firstViolation h)

theorem lrInv_of_not (hκ : Antitone κ) {T : TauCeti.BoundedSSYT d ν} (h : ¬ IsLattice κ T.1) :
    lrInv hκ T = lrSwapB hκ T (isFirstViolation_firstViolation h) :=
  dite_eq_right h

theorem not_isLattice_lrInv (hκ : Antitone κ) {T : TauCeti.BoundedSSYT d ν}
    (h : ¬ IsLattice κ T.1) : ¬ IsLattice κ (lrInv hκ T).1 := by
  rw [lrInv_of_not hκ h]
  exact (isFirstViolation_lrSwap hκ (isFirstViolation_firstViolation h)).not_isLattice

theorem lrInv_lrInv (hκ : Antitone κ) {T : TauCeti.BoundedSSYT d ν} (h : ¬ IsLattice κ T.1) :
    lrInv hκ (lrInv hκ T) = T := by
  have key : ∀ S : TauCeti.BoundedSSYT d ν,
      S = lrSwapB hκ T (isFirstViolation_firstViolation h) →
        ∀ {r' i' : ℕ} (h' : IsFirstViolation κ S.1 r' i'), lrSwapB hκ S h' = T := by
    rintro S rfl r' i' h'
    exact lrSwapB_lrSwapB hκ T _ h'
  rw [lrInv_of_not hκ (not_isLattice_lrInv hκ h)]
  exact key _ (lrInv_of_not hκ h) _

/-- **The terms of the tableaux that are not lattice cancel.** -/
theorem sum_not_isLattice (hκ : Antitone κ) :
    ∑ T ∈ Finset.univ.filter (fun T : TauCeti.BoundedSSYT d ν => ¬ IsLattice κ T.1),
      alternant (κ + weightVec T + staircase d) = 0 := by
  refine Finset.sum_involution (fun T _ => lrInv hκ T) (fun T hT => ?_) (fun T hT hne => ?_)
    (fun T hT => ?_) (fun T hT => ?_)
  · have hT' := (Finset.mem_filter.mp hT).2
    rw [lrInv_of_not hκ hT', alternant_lrSwapB, add_neg_cancel]
  · have hT' := (Finset.mem_filter.mp hT).2
    intro heq
    apply hne
    have h1 : alternant (κ + weightVec (lrInv hκ T) + staircase d) =
        -alternant (κ + weightVec T + staircase d) := by
      rw [lrInv_of_not hκ hT', alternant_lrSwapB]
    rw [heq] at h1
    ext w
    have h3 := congrArg (fun f : Laurent d => f.coeff w) h1
    simp only [AddMonoidAlgebra.coeff_neg] at h3
    have h4 : (alternant (κ + weightVec T + staircase d)).coeff w = 0 := by
      have h5 : (alternant (κ + weightVec T + staircase d)).coeff w =
          -(alternant (κ + weightVec T + staircase d)).coeff w := by simpa using h3
      linarith
    simpa using h4
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      not_isLattice_lrInv hκ (Finset.mem_filter.mp hT).2⟩
  · exact lrInv_lrInv hκ (Finset.mem_filter.mp hT).2

/-! ### The rule -/

/-- A Schur polynomial, as a Laurent polynomial, is the sum of the monomials of its tableaux. -/
theorem toLaurent_diagramSchurPoly (ν : YoungDiagram) :
    toLaurent (TauCeti.diagramSchurPoly d ℤ ν) =
      ∑ T : TauCeti.BoundedSSYT d ν, AddMonoidAlgebra.single (weightVec T) (1 : ℤ) := by
  rw [TauCeti.diagramSchurPoly_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [toLaurent_monomial]
  congr 1

/-- **The Littlewood–Richardson rule**, alternant form: for a weakly decreasing integer weight
`κ` and a Young diagram `ν`,
`a_{κ + δ} · s_ν = ∑_{T lattice from κ} a_{κ + wt(T) + δ}`, the sum over the semistandard
tableaux of shape `ν` in the letters `0, …, d − 1` whose reverse row word is lattice from `κ`. -/
theorem alternant_mul_schur (κ : Weight d) (hκ : Antitone κ) (ν : YoungDiagram) :
    alternant (κ + staircase d) * toLaurent (TauCeti.diagramSchurPoly d ℤ ν) =
      ∑ T ∈ Finset.univ.filter (fun T : TauCeti.BoundedSSYT d ν => IsLattice κ T.1),
        alternant (κ + weightVec T + staircase d) := by
  have hsym : IsSymmetric (∑ T ∈ (Finset.univ : Finset (TauCeti.BoundedSSYT d ν)),
      AddMonoidAlgebra.single (weightVec T) (1 : ℤ)) := by
    rw [← toLaurent_diagramSchurPoly]
    exact isSymmetric_toLaurent (TauCeti.isSymmetric_diagramSchurPoly d ℤ ν)
  rw [toLaurent_diagramSchurPoly, alternant_mul_sum_single _ _ _ hsym,
    ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun T : TauCeti.BoundedSSYT d ν =>
      IsLattice κ T.1)]
  have h0 := sum_not_isLattice hκ (ν := ν)
  have hc : ∀ T : TauCeti.BoundedSSYT d ν,
      κ + staircase d + weightVec T = κ + weightVec T + staircase d := fun T => add_right_comm _ _ _
  simp only [hc, h0, add_zero]

/-- **The coefficient form of the Littlewood–Richardson rule**: for weakly decreasing `κ` and `λ`,
the coefficient of `x^{λ + δ}` in `a_{κ + δ} s_ν` (the multiplicity of `a_{λ + δ}`) is the number
of tableaux of shape `ν` lattice from `κ` with `κ + wt(T) = λ`. -/
theorem coeff_alternant_mul_schur (κ lam : Weight d) (hκ : Antitone κ) (hlam : Antitone lam)
    (ν : YoungDiagram) :
    (alternant (κ + staircase d) * toLaurent (TauCeti.diagramSchurPoly d ℤ ν)).coeff
        (lam + staircase d) =
      ((Finset.univ.filter fun T : TauCeti.BoundedSSYT d ν =>
        IsLattice κ T.1 ∧ κ + weightVec T = lam).card : ℤ) := by
  classical
  rw [alternant_mul_schur κ hκ ν]
  simp only [AddMonoidAlgebra.coeff_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
  have hterm : ∀ T ∈ Finset.univ.filter (fun T : TauCeti.BoundedSSYT d ν => IsLattice κ T.1),
      (alternant (κ + weightVec T + staircase d)).coeff (lam + staircase d) =
        if κ + weightVec T = lam then 1 else 0 := by
    intro T hT
    rw [coeff_alternant_of_strictAnti
      (strictAnti_add_staircase (antitone_add_weightVec (Finset.mem_filter.mp hT).2))
      (strictAnti_add_staircase hlam)]
    by_cases he : κ + weightVec T = lam
    · simp [he]
    · have he' : κ + weightVec T + staircase d ≠ lam + staircase d :=
        fun e => he (add_right_cancel e)
      simp [he, he']
  rw [Finset.sum_congr rfl hterm, Finset.sum_boole, Finset.filter_filter]

theorem isLattice_add_const (κ : Weight d) (k : ℤ) (T : _root_.SemistandardYoungTableau ν) :
    IsLattice (κ + fun _ => k) T ↔ IsLattice κ T := by
  have hk : ∀ j, j < d → kap (κ + fun _ => k) j = kap κ j + k := by
    intro j hj
    rw [kap_of_lt _ hj, kap_of_lt _ hj]
    rfl
  refine forall_congr' fun r => forall_congr' fun i => forall_congr' fun hi => ?_
  rw [hk (i + 1) hi, hk i (by omega)]
  constructor <;> intro h <;> linarith

/-- **The Littlewood–Richardson rule with a determinant twist**:
`a_{κ + δ} · det^k s_ν = ∑_{T lattice from κ} a_{κ + wt(T) + k + δ}`. -/
theorem alternant_mul_shiftedSchur (κ : Weight d) (hκ : Antitone κ) (ν : YoungDiagram) (k : ℤ) :
    alternant (κ + staircase d) * shiftedSchur d ν k =
      ∑ T ∈ Finset.univ.filter (fun T : TauCeti.BoundedSSYT d ν => IsLattice κ T.1),
        alternant (κ + weightVec T + (fun _ => k) + staircase d) := by
  have hκ' : Antitone (κ + fun _ => k) := hκ.add antitone_const
  rw [shiftedSchur, ← mul_assoc, alternant_mul_single_const,
    show κ + staircase d + (fun _ => k) = (κ + fun _ => k) + staircase d by abel,
    alternant_mul_schur _ hκ' ν]
  refine Finset.sum_congr (Finset.filter_congr fun T _ => isLattice_add_const κ k T.1)
    fun T _ => ?_
  congr 1
  abel

theorem revPerm_comp_twice (u : Weight d) :
    (u ∘ ⇑(Fin.revPerm : Perm (Fin d))) ∘ ⇑(Fin.revPerm : Perm (Fin d)) = u := by
  funext i
  simp

/-- **The Littlewood–Richardson rule in projector form**: for dominant weights `κ` and `λ`, the
multiplicity of `s_λ` in `s_κ · s_ν` (the Weyl projector coefficient) is the number of tableaux of
shape `ν` lattice from `κ` with `κ + wt(T) = λ`. -/
theorem weylProjector_ratSchur_mul_schur (κ lam : TauCeti.DominantWeight d) (ν : YoungDiagram) :
    weylProjector (lam.1 ∘ ⇑(Fin.revPerm : Perm (Fin d)))
        (ratSchur κ * toLaurent (TauCeti.diagramSchurPoly d ℤ ν)) =
      ((Finset.univ.filter fun T : TauCeti.BoundedSSYT d ν =>
        IsLattice κ.1 T.1 ∧ κ.1 + weightVec T = lam.1).card : ℤ) := by
  have hsym : IsSymmetric (ratSchur κ * toLaurent (TauCeti.diagramSchurPoly d ℤ ν)) :=
    (isSymmetric_ratSchur κ).mul
      (isSymmetric_toLaurent (TauCeti.isSymmetric_diagramSchurPoly d ℤ ν))
  rw [weylProjector_eq_alternant hsym, revPerm_comp_twice, ← mul_assoc,
    alternant_mul_ratSchur, coeff_alternant_mul_schur κ.1 lam.1 κ.2 lam.2 ν]

end

end Schubert.RS.LR
