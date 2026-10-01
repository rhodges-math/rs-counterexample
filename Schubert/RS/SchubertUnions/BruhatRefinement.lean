import Schubert.RS.SchubertUnions.Coset
import Schubert.RS.SchubertUnions.RightKey
import Schubert.RS.KeyAction

/-!
# The Bruhat refinement of keys into Demazure atoms

For a weakly decreasing composition `λ` and a shortest coset representative `σ ∈ W^λ`,

  `κ_{σλ} = Σ_{u ∈ W^λ, u ≤ σ} 𝒜_{uλ}`,

which is equation (1.3) of the paper [Lascoux–Schützenberger] (`key_eq_sum_atom`).

The proof is by induction on the length of `σ`, peeling off a left descent `sᵢ` of `σ` and using
the action of the isobaric operator `πᵢ` on atoms (`isobaric_atom_of_gt`,
`isobaric_atom_of_eq`, `isobaric_atom_of_lt`) together with the lifting property of Bruhat order.
-/

namespace Schubert.RS.SchubertUnions

open FinPermutation Representation Schubert

noncomputable section

variable {n : ℕ}

/-! ### The isobaric operator on atoms -/

@[simp] theorem atomOperator_zero (i : AdjacentPosition n) : atomOperator i 0 = 0 := by
  simp [atomOperator]

/-- `π̄ᵢ 𝒜_a = 0` when `aᵢ = a_{i+1}`. -/
theorem atomOperator_atom_of_eq (a : Composition n) (i : AdjacentPosition n)
    (heq : a i.left = a i.right) : atomOperator i (atom a) = 0 := by
  induction a using (measure sortingMeasure).wf.induction generalizing i with
  | h a ih =>
    by_cases ha : (ascentSet a).Nonempty
    · let j := firstAscent a ha
      have hj : a j.left < a j.right := firstAscent_lt a ha
      have hjlt := sortingMeasure_swap_lt a j hj
      have hji : j ≠ i := by rintro rfl; omega
      by_cases hadj : i.right = j.left
      · have hxz : i.left ≠ j.right :=
          (i.left_lt_right.trans (hadj ▸ j.left_lt_right)).ne
        have hzy : j.right ≠ i.right := by rw [hadj]; exact j.left_ne_right.symm
        have h1 : (swapComposition a j) i.left < (swapComposition a j) i.right := by
          simpa [swapComposition, adjacentTransposition, ← hadj,
            Equiv.swap_apply_def, i.left_ne_right, hxz, heq] using hj
        have h2 : (swapComposition (swapComposition a j) i) j.left =
            (swapComposition (swapComposition a j) i) j.right := by
          simp [swapComposition, adjacentTransposition, ← hadj,
            Equiv.swap_apply_def, i.left_ne_right, hxz, hxz.symm, hzy, heq]
        have h2lt := (sortingMeasure_swap_lt (swapComposition a j) i h1).trans hjlt
        rw [atom_ascent a ha, atom_any_ascent _ i h1, atomOperator_braid i j hadj,
          ih _ h2lt j h2, atomOperator_zero, atomOperator_zero]
      · by_cases hadj' : j.right = i.left
        · have hxz : j.left ≠ i.right :=
            (j.left_lt_right.trans (hadj' ▸ i.left_lt_right)).ne
          have hzy : i.right ≠ j.right := by rw [hadj']; exact i.left_ne_right.symm
          have hxy : j.left ≠ i.left := by rw [← hadj']; exact j.left_ne_right
          have h1 : (swapComposition a j) i.left < (swapComposition a j) i.right := by
            simpa [swapComposition, adjacentTransposition, ← hadj',
              Equiv.swap_apply_of_ne_of_ne hxz.symm hzy, ← heq] using hj
          have h2 : (swapComposition (swapComposition a j) i) j.left =
              (swapComposition (swapComposition a j) i) j.right := by
            simp [swapComposition, adjacentTransposition, hadj',
              Equiv.swap_apply_def, hxy, hxz, hxz.symm,
              i.left_ne_right.symm, heq]
          have h2lt := (sortingMeasure_swap_lt (swapComposition a j) i h1).trans hjlt
          rw [atom_ascent a ha, atom_any_ascent _ i h1, ← atomOperator_braid j i hadj',
            ih _ h2lt j h2, atomOperator_zero, atomOperator_zero]
        · have hs : SeparatedAdjacentPositions i j := by
            have hn : i.left.val ≠ j.left.val := by
              intro h
              exact hji (AdjacentPosition.ext (Fin.ext h).symm)
            have hn1 : i.right.val ≠ j.left.val := fun h => hadj (Fin.ext h)
            have hn2 : j.right.val ≠ i.left.val := fun h => hadj' (Fin.ext h)
            have hi := i.right_val
            have hjr := j.right_val
            change i.right.val < j.left.val ∨ j.right.val < i.left.val
            omega
          obtain ⟨hll, hlr, hrl, hrr⟩ := separated_endpoint_ne i j hs
          have hi' : (swapComposition a j) i.left = (swapComposition a j) i.right := by
            simpa [swapComposition_other _ _ _ hll hlr,
              swapComposition_other _ _ _ hrl hrr] using heq
          rw [atom_ascent a ha, atomOperator_commute i j hs, ih _ hjlt i hi', atomOperator_zero]
    · rw [atom_of_no_ascent a ha, atomOperator,
        isobaric_of_symmetric i _ (compositionMonomial_symmetric a i heq), sub_self]

theorem isobaric_atom_of_eq (a : Composition n) (i : AdjacentPosition n)
    (heq : a i.left = a i.right) : isobaric i (atom a) = atom a := by
  have h := atomOperator_atom_of_eq a i heq
  rwa [atomOperator, sub_eq_zero] at h

theorem isobaric_atom_of_gt (a : Composition n) (i : AdjacentPosition n)
    (h : a i.right < a i.left) :
    isobaric i (atom a) = atom a + atom (swapComposition a i) := by
  have hb : (swapComposition a i) i.left < (swapComposition a i) i.right := by simpa using h
  have hs := atom_any_ascent (swapComposition a i) i hb
  rw [swapComposition_involutive, atomOperator] at hs
  rw [hs]
  abel

theorem isobaric_atom_of_lt (a : Composition n) (i : AdjacentPosition n)
    (h : a i.left < a i.right) : isobaric i (atom a) = 0 := by
  rw [atom_any_ascent a i h, atomOperator, isobaric_sub, isobaric_idempotent, sub_self]

/-! ### Shortest coset representatives and left multiplication -/

theorem permAct_leftAdjacentSwap (σ : FinPermutation n) (i : AdjacentPosition n)
    (dom : Composition n) :
    permAct (σ.leftAdjacentSwap i) dom = swapComposition (permAct σ dom) i := by
  funext j
  simp only [permAct, swapComposition, leftAdjacentSwap_symm_apply]

theorem adjacentTransposition_lt_of_lt {i : AdjacentPosition n} {x y : Fin n} (hxy : x < y)
    (h : ¬ (x = i.left ∧ y = i.right)) :
    adjacentTransposition i x < adjacentTransposition i y := by
  have hr := i.right_val
  simp only [adjacentTransposition, Equiv.swap_apply_def]
  rw [Fin.lt_def] at hxy
  simp only [Fin.ext_iff] at h
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 <;> simp only [Fin.ext_iff, Fin.lt_def] at * <;> omega

theorem isMinCosetRep_one (dom : Composition n) : IsMinCosetRep dom (Equiv.refl (Fin n)) :=
  fun _ _ hij _ => hij

/-- Left multiplication by `sᵢ` keeps `W^λ`, unless it breaks the order inside a block. -/
theorem isMinCosetRep_leftAdjacentSwap {dom : Composition n} {σ : FinPermutation n}
    (hσ : IsMinCosetRep dom σ) {i : AdjacentPosition n}
    (h : ¬ (σ.symm i.left < σ.symm i.right ∧ dom (σ.symm i.left) = dom (σ.symm i.right))) :
    IsMinCosetRep dom (σ.leftAdjacentSwap i) := by
  intro p q hpq hdom
  simp only [leftAdjacentSwap_apply]
  refine adjacentTransposition_lt_of_lt (hσ p q hpq hdom) fun hpair => h ?_
  obtain ⟨hp, hq⟩ := hpair
  rw [← hp, ← hq, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  exact ⟨hpq, hdom⟩

theorem permAct_lt_of_descent {dom : Composition n} (hdom : Antitone dom) {σ : FinPermutation n}
    (hσ : IsMinCosetRep dom σ) {i : AdjacentPosition n} (hd : σ.symm i.right < σ.symm i.left) :
    permAct σ dom i.left < permAct σ dom i.right := by
  simp only [permAct]
  refine lt_of_le_of_ne (hdom hd.le) fun he => ?_
  have := hσ _ _ hd he.symm
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this
  exact absurd this (not_lt.mpr i.left_lt_right.le)

theorem permAct_le_of_ascent {dom : Composition n} (hdom : Antitone dom) {τ : FinPermutation n}
    {i : AdjacentPosition n} (ha : τ.symm i.left < τ.symm i.right) :
    permAct τ dom i.right ≤ permAct τ dom i.left :=
  hdom ha.le

theorem symm_left_ne_symm_right (τ : FinPermutation n) (i : AdjacentPosition n) :
    τ.symm i.left ≠ τ.symm i.right := fun h => i.left_ne_right (τ.symm.injective h)

/-! ### The refinement -/

open Classical in
/-- `{u ∈ W^λ | u ≤ σ}`. -/
def minCosetInterval (dom : Composition n) (σ : FinPermutation n) : Finset (FinPermutation n) :=
  Finset.univ.filter fun τ => IsMinCosetRep dom τ ∧ τ ≤ᴮ σ

theorem mem_minCosetInterval {dom : Composition n} {σ τ : FinPermutation n} :
    τ ∈ minCosetInterval dom σ ↔ IsMinCosetRep dom τ ∧ τ ≤ᴮ σ := by
  classical
  unfold minCosetInterval
  simp

/-- The isobaric operator `πᵢ` as an additive map. -/
def isobaricHom (i : AdjacentPosition n) : Polynomial n →+ Polynomial n where
  toFun := isobaric i
  map_zero' := isobaric_zero i
  map_add' := isobaric_add i

theorem sum_isobaric_atom_step (dom : Composition n) (hdom : Antitone dom) (σ : FinPermutation n)
    (i : AdjacentPosition n) (hd : σ.symm i.right < σ.symm i.left) :
    ∑ τ ∈ minCosetInterval dom (σ.leftAdjacentSwap i), isobaric i (atom (permAct τ dom)) =
      ∑ τ ∈ minCosetInterval dom σ, atom (permAct τ dom) := by
  classical
  set σ' := σ.leftAdjacentSwap i with hσ'
  let v : FinPermutation n → Composition n := fun τ => permAct τ dom
  let D : FinPermutation n → Prop := fun τ => v τ i.left < v τ i.right
  let P : FinPermutation n → Prop := fun τ => v τ i.right < v τ i.left
  have hσ'asc : σ'.symm i.left < σ'.symm i.right := by
    rw [hσ', leftAdjacentSwap_symm_left, leftAdjacentSwap_symm_right]; exact hd
  have hσ'σ : σ' ≤ᴮ σ := left_reflection_le_of_descent i σ hd
  have hσσ' : σ'.leftAdjacentSwap i = σ := leftAdjacentSwap_leftAdjacentSwap σ i
  -- `D` is the descent condition on `W^λ`
  have hDdesc : ∀ τ, IsMinCosetRep dom τ → D τ → τ.symm i.right < τ.symm i.left := by
    intro τ _ hD
    rcases lt_or_gt_of_ne (symm_left_ne_symm_right τ i) with ha | ha
    · exact absurd hD (not_lt.mpr (permAct_le_of_ascent hdom ha))
    · exact ha
  have hPasc : ∀ τ, P τ → τ.symm i.left < τ.symm i.right := by
    intro τ hP
    rcases lt_or_gt_of_ne (symm_left_ne_symm_right τ i) with ha | ha
    · exact ha
    · exact absurd hP (not_lt.mpr (hdom ha.le))
  -- pointwise decomposition of `πᵢ 𝒜_{vτ}`
  have hpoint : ∀ τ, isobaric i (atom (v τ)) =
      (if ¬ D τ then atom (v τ) else 0) + (if P τ then atom (v (τ.leftAdjacentSwap i)) else 0) := by
    intro τ
    have hv : v (τ.leftAdjacentSwap i) = swapComposition (v τ) i := permAct_leftAdjacentSwap τ i dom
    rcases lt_trichotomy (v τ i.left) (v τ i.right) with hlt | heq | hgt
    · have hP : ¬ P τ := not_lt.mpr hlt.le
      rw [isobaric_atom_of_lt _ i hlt, ite_eq_right (not_not.mpr hlt), ite_eq_right hP, add_zero]
    · have hD : ¬ D τ := by simp [D, heq]
      have hP : ¬ P τ := by simp [P, heq]
      rw [isobaric_atom_of_eq _ i heq, ite_eq_left hD, ite_eq_right hP, add_zero]
    · have hD : ¬ D τ := not_lt.mpr hgt.le
      rw [isobaric_atom_of_gt _ i hgt, ite_eq_left hD, ite_eq_left hgt, hv]
  rw [Finset.sum_congr rfl fun τ _ => hpoint τ, Finset.sum_add_distrib, ← Finset.sum_filter,
    ← Finset.sum_filter, ← Finset.sum_filter_not_add_sum_filter (minCosetInterval dom σ) D]
  congr 1
  · -- the terms without a strict descent
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext τ
    simp only [Finset.mem_filter, mem_minCosetInterval]
    constructor
    · rintro ⟨⟨hτ, hτσ'⟩, hD⟩
      exact ⟨⟨hτ, strongBruhat_trans hτσ' hσ'σ⟩, hD⟩
    · rintro ⟨⟨hτ, hτσ⟩, hD⟩
      refine ⟨⟨hτ, ?_⟩, hD⟩
      have hasc : τ.symm i.left < τ.symm i.right := by
        rcases lt_or_gt_of_ne (symm_left_ne_symm_right τ i) with ha | ha
        · exact ha
        · exact absurd (permAct_lt_of_descent hdom hτ ha) hD
      exact left_lower_le_reflected_upper i hτσ hasc hd
  · -- the terms moved by `sᵢ`
    refine Finset.sum_nbij' (fun τ => τ.leftAdjacentSwap i) (fun τ => τ.leftAdjacentSwap i)
      ?_ ?_ ?_ ?_ ?_
    · intro τ hτ
      simp only [Finset.mem_filter, mem_minCosetInterval] at hτ ⊢
      obtain ⟨⟨hτW, hτσ'⟩, hP⟩ := hτ
      have hasc := hPasc τ hP
      refine ⟨⟨isMinCosetRep_leftAdjacentSwap hτW fun h => ?_, ?_⟩, ?_⟩
      · exact absurd (h.2 ▸ rfl : dom (τ.symm i.left) = dom (τ.symm i.right)) (by
          intro he
          simp only [P, v, permAct] at hP
          rw [he] at hP
          exact lt_irrefl _ hP)
      · have := left_reflections_le_of_both_ascent i hτσ' hasc hσ'asc
        rwa [hσσ'] at this
      · show permAct (τ.leftAdjacentSwap i) dom i.left < permAct (τ.leftAdjacentSwap i) dom i.right
        rw [permAct_leftAdjacentSwap]
        simpa using hP
    · intro ρ hρ
      simp only [Finset.mem_filter, mem_minCosetInterval] at hρ ⊢
      obtain ⟨⟨hρW, hρσ⟩, hD⟩ := hρ
      have hdesc := hDdesc ρ hρW hD
      refine ⟨⟨isMinCosetRep_leftAdjacentSwap hρW fun h => ?_, ?_⟩, ?_⟩
      · exact absurd h.1 (not_lt.mpr hdesc.le)
      · exact left_reflections_le_of_both_descent i hρσ hdesc hd
      · show permAct (ρ.leftAdjacentSwap i) dom i.right < permAct (ρ.leftAdjacentSwap i) dom i.left
        rw [permAct_leftAdjacentSwap]
        simpa using hD
    · intro τ _
      exact leftAdjacentSwap_leftAdjacentSwap τ i
    · intro ρ _
      exact leftAdjacentSwap_leftAdjacentSwap ρ i
    · intro τ _
      rfl

open Classical in
/-- **The Bruhat refinement (1.3).** For `λ` weakly decreasing and `σ ∈ W^λ`,
`κ_{σλ} = Σ_{u ∈ W^λ, u ≤ σ} 𝒜_{uλ}`. -/
theorem key_eq_sum_atom (dom : Composition n) (hdom : Antitone dom) (σ : FinPermutation n)
    (hσ : IsMinCosetRep dom σ) :
    key (permAct σ dom) = ∑ τ ∈ minCosetInterval dom σ, atom (permAct τ dom) := by
  generalize hl : σ.length = l
  induction l using Nat.strong_induction_on generalizing σ with
  | h l ih =>
    by_cases hσ1 : σ = Equiv.refl (Fin n)
    · subst hσ1
      have hA : minCosetInterval dom (Equiv.refl (Fin n)) = {Equiv.refl (Fin n)} := by
        ext τ
        rw [mem_minCosetInterval, Finset.mem_singleton]
        constructor
        · rintro ⟨-, hτ⟩
          exact strongBruhat_antisymm hτ (refl_strongBruhatLE τ)
        · rintro rfl
          exact ⟨isMinCosetRep_one dom, strongBruhat_refl _⟩
      have hv : permAct (Equiv.refl (Fin n)) dom = dom := rfl
      rw [hA, Finset.sum_singleton, hv, key_of_antitone dom hdom, atom_of_antitone dom hdom]
    · have hsymm : σ.symm ≠ Equiv.refl (Fin n) := fun h => hσ1 (by
        rw [← Equiv.symm_symm σ, h]; rfl)
      obtain ⟨a, b, hb, hdesc⟩ := exists_descent_of_ne_refl (σ.symm : FinPermutation n) hsymm
      let i : AdjacentPosition n := ⟨a, by rw [← hb]; exact b.isLt⟩
      have hib : i.right = b := Fin.ext (by rw [AdjacentPosition.right_val]; exact hb.symm)
      have hd : σ.symm i.right < σ.symm i.left := by rw [hib]; exact hdesc
      have hD : HasDescent (σ.symm : FinPermutation n) i.left := ⟨b, hb, hdesc⟩
      obtain ⟨hle, hne⟩ := leftAdjacentSwap_lt_of_inverseDescent σ i hD
      have hlen : (σ.leftAdjacentSwap i).length < l := by
        rw [← hl]
        refine lt_of_le_of_ne (length_le_of_strongBruhatLE hle) fun he => hne ?_
        exact eq_of_strongBruhatLE_of_length_eq hle he
      have hσ' : IsMinCosetRep dom (σ.leftAdjacentSwap i) :=
        isMinCosetRep_leftAdjacentSwap hσ fun h => absurd h.1 (not_lt.mpr hd.le)
      have hasc := permAct_lt_of_descent hdom hσ hd
      rw [key_any_ascent _ i hasc, ← permAct_leftAdjacentSwap,
        ih _ hlen (σ.leftAdjacentSwap i) hσ' rfl]
      change isobaricHom i (∑ τ ∈ minCosetInterval dom (σ.leftAdjacentSwap i),
        atom (permAct τ dom)) = _
      rw [map_sum]
      exact sum_isobaric_atom_step dom hdom σ i hd

end

end Schubert.RS.SchubertUnions
