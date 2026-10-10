import RSCounterexample.QuiverInvariants.NormalForm

/-!
# Schofield's formula for general extensions

Let `K` be an infinite field, `Q` a forward quiver and `ι`, `κ` vertex families of dimension
vectors `α` and `β`. Write `ext(α, β)` for the smallest value of `extDim V W` (`genericExt`), and
`β ↠ β″` when a general representation on `κ` has a quotient of dimension `β″`
(`FQuiver.GeneralQuot`). Schofield's formula is

  `ext(α, β) = max {−⟨α, β″⟩ : β ↠ β″}`.

The inequality `≥` holds because `ext(V, −)` is right exact on quotients: for a general pair
`(V, W)` and a quotient `W ↠ W″` of dimension `β″`, `ext(V, W) ≥ ext(V, W″) ≥ −⟨α, β″⟩`.

The inequality `≤` (`FQuiver.exists_generalQuot_euler_add_extDim_nonpos`) is proved by induction
on `dim κ`. If `hom(α, β) = 0`, take `β″ = β`. Otherwise a general homomorphism `V → W` has a
nonzero rank `γ`; by the quotient lemma, dividing `W` by its image does not change `ext(V, −)`,
so `ext(α, β) = ext(α, β − γ)`, and a general quotient dimension of `β − γ` is one of `β`
(`FQuiver.exists_cokernelStep`). The argument uses only polynomial identities, ranks and minors,
and Zariski density, and no assumption on the characteristic.

## Main results

* `FQuiver.exists_generalQuot_euler_add_extDim_nonpos`: there is `β″` with `β ↠ β″` and
  `⟨α, β″⟩ + ext(V, W) ≤ 0` for some pair `(V, W)`, that is, `⟨α, β″⟩ ≤ −ext(α, β)`.
* `FQuiver.exists_extDim_eq_zero`: if `⟨α, β″⟩ ≥ 0` whenever `β ↠ β″`, some Ringel map `d_{V,W}`
  is onto.
* `FQuiver.neg_genericExt_le_euler`: `−ext(α, β) ≤ ⟨α, β″⟩` whenever `β ↠ β″`.
* `FQuiver.isGreatest_genericExt`: **Schofield's formula**.
-/

namespace QuiverInvariants

noncomputable section

namespace FQuiver

variable (Q : FQuiver) {K : Type*} [Field K] [Infinite K]

/-- **Schofield's bound.** For vertex families `ι` and `κ` there is a dimension vector `β` such
that a general representation on `κ` has a quotient of dimension `β` and
`⟨dim ι, β⟩ + ext(V, W) ≤ 0` for some pair `(V, W)`; equivalently
`⟨dim ι, β⟩ ≤ −ext(dim ι, dim κ)`. -/
theorem exists_generalQuot_euler_add_extDim_nonpos (ι κ : Fin Q.s → Type)
    [∀ p, Fintype (ι p)] [∀ p, DecidableEq (ι p)] [∀ p, Fintype (κ p)]
    [∀ p, DecidableEq (κ p)] :
    ∃ β : Fin Q.s → ℕ, Q.GeneralQuot K κ β ∧
      ∃ (V : Q.Rep K ι) (W : Q.Rep K κ),
        Q.euler (fun p => (Fintype.card (ι p) : ℤ)) (fun p => (β p : ℤ)) + Q.extDim V W ≤ 0 := by
  suffices h : ∀ (n : ℕ) (κ : Fin Q.s → Type) [∀ p, Fintype (κ p)] [∀ p, DecidableEq (κ p)],
      ∑ p, Fintype.card (κ p) = n → ∃ β : Fin Q.s → ℕ, Q.GeneralQuot K κ β ∧
        ∃ (V : Q.Rep K ι) (W : Q.Rep K κ),
          Q.euler (fun p => (Fintype.card (ι p) : ℤ)) (fun p => (β p : ℤ)) + Q.extDim V W ≤ 0 from
    h _ κ rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro κ _ _ hn
  by_cases h0 : Q.genericHom K ι κ = 0
  · obtain ⟨V, W, hVW⟩ := Q.exists_isHomGeneric (K := K) (ι := ι) (κ := κ)
    refine ⟨dimVec κ, Q.generalQuot_dimVec, V, W, ?_⟩
    have hh := Q.isHomGeneric_iff_homDim.mp hVW
    have he := Q.homDim_sub_extDim V W
    rw [hh, h0] at he
    simp only [dimVec_apply]
    push_cast at he
    linarith
  · obtain ⟨γ, ⟨p₀, hp₀⟩, hγ, hstep⟩ := Q.exists_cokernelStep (Nat.pos_of_ne_zero h0)
    set ιC : Fin Q.s → Type := finFam fun p => Fintype.card (κ p) - γ p
    have hC : ∀ p, γ p + Fintype.card (ιC p) = Fintype.card (κ p) := fun p => by
      simp only [ιC, finFam, Fintype.card_fin]
      have := hγ p
      omega
    obtain ⟨htrans, V, W, hVW⟩ := hstep ιC hC
    have hlt : ∑ p, Fintype.card (ιC p) < n := by
      rw [← hn]
      refine Finset.sum_lt_sum (fun p _ => ?_) ⟨p₀, Finset.mem_univ _, ?_⟩
      · have := hC p
        omega
      · have := hC p₀
        omega
    obtain ⟨β, hβ, V', C', hVC⟩ := ih _ hlt ιC rfl
    refine ⟨β, htrans β hβ, V, W, ?_⟩
    have := hVW V' C'
    have : (Q.extDim V W : ℤ) ≤ Q.extDim V' C' := by exact_mod_cast this
    linarith

/-- **Vanishing of `ext`.** If `⟨dim ι, β⟩ ≥ 0` for every dimension vector `β` of a general
quotient of the representations on `κ`, then some Ringel map `d_{V,W}` is onto: `ext(V, W) = 0`
for some pair. -/
theorem exists_extDim_eq_zero (ι κ : Fin Q.s → Type) [∀ p, Fintype (ι p)]
    [∀ p, DecidableEq (ι p)] [∀ p, Fintype (κ p)] [∀ p, DecidableEq (κ p)]
    (h : ∀ β : Fin Q.s → ℕ, Q.GeneralQuot K κ β →
      0 ≤ Q.euler (fun p => (Fintype.card (ι p) : ℤ)) (fun p => (β p : ℤ))) :
    ∃ (V : Q.Rep K ι) (W : Q.Rep K κ), Q.extDim V W = 0 := by
  obtain ⟨β, hβ, V, W, hle⟩ := Q.exists_generalQuot_euler_add_extDim_nonpos (K := K) ι κ
  have := h β hβ
  exact ⟨V, W, by omega⟩

variable {Q} {ι κ : Fin Q.s → Type} [∀ p, Fintype (ι p)] [∀ p, DecidableEq (ι p)]
  [∀ p, Fintype (κ p)] [∀ p, DecidableEq (κ p)]

/-- **The easy inequality.** If a general representation on `κ` has a quotient of dimension `β`,
then `−ext(dim ι, dim κ) ≤ ⟨dim ι, β⟩`. -/
theorem neg_genericExt_le_euler {β : Fin Q.s → ℕ} (hβ : Q.GeneralQuot K κ β) :
    -(Q.genericExt K ι κ : ℤ) ≤
      Q.euler (fun p => (Fintype.card (ι p) : ℤ)) (fun p => (β p : ℤ)) := by
  obtain ⟨z, hz, hgen⟩ :=
    (hβ.preimage_comp (Sum.inr_injective (α := Q.Entry ι))).exists_of_eventually
      (Q.eventually_isHomGeneric (K := K) (ι := ι) (κ := κ))
  obtain ⟨W, ⟨S, hS, hdim⟩, hW⟩ := hz
  have hWz : Q.pairSnd z = W := by rw [pairSnd, ← hW, ofCoord_coord]
  rw [hWz] at hgen
  obtain ⟨P, A, y, C, hP⟩ := hS.exists_transport_eq_blockRep Q
    (ι₁ := finFam fun p => Module.finrank K (S p)) (ι₂ := finFam β) (fun p => by simp)
    (fun p => by simp [hdim])
  have hext : Q.genericExt K ι κ = Q.extDim (Q.pairFst z) W :=
    (Q.isHomGeneric_iff_extDim.mp hgen).symm
  have hle : Q.extDim (Q.pairFst z) C ≤ Q.genericExt K ι κ := by
    rw [hext, ← Q.extDim_transport (VertexIso.refl K ι) P (Q.pairFst z) W, transport_refl, hP]
    exact Q.extDim_le_extDim_blockRep _ _ _ _
  have hC := Q.extDim_eq_homDim_sub_euler (Q.pairFst z) C
  simp only [finFam, Fintype.card_fin] at hC
  have : (Q.extDim (Q.pairFst z) C : ℤ) ≤ Q.genericExt K ι κ := by exact_mod_cast hle
  have : (0 : ℤ) ≤ Q.homDim (Q.pairFst z) C := Int.natCast_nonneg _
  linarith

/-- The bound of `FQuiver.exists_generalQuot_euler_add_extDim_nonpos` in terms of the generic
`ext`: some general quotient dimension `β` has `⟨dim ι, β⟩ = −ext(dim ι, dim κ)`. -/
theorem exists_generalQuot_euler_eq_neg_genericExt :
    ∃ β : Fin Q.s → ℕ, Q.GeneralQuot K κ β ∧
      Q.euler (fun p => (Fintype.card (ι p) : ℤ)) (fun p => (β p : ℤ)) =
        -(Q.genericExt K ι κ : ℤ) := by
  obtain ⟨β, hβ, V, W, hle⟩ := Q.exists_generalQuot_euler_add_extDim_nonpos (K := K) ι κ
  refine ⟨β, hβ, le_antisymm ?_ (neg_genericExt_le_euler hβ)⟩
  have : (Q.genericExt K ι κ : ℤ) ≤ Q.extDim V W := by exact_mod_cast Q.genericExt_le_extDim V W
  linarith

/-- **Schofield's formula.** `ext(dim ι, dim κ)` is the largest value of `−⟨dim ι, β⟩` over the
dimension vectors `β` of general quotients of the representations on `κ`. -/
theorem isGreatest_genericExt :
    IsGreatest {e : ℤ | ∃ β : Fin Q.s → ℕ, Q.GeneralQuot K κ β ∧
      e = -Q.euler (fun p => (Fintype.card (ι p) : ℤ)) (fun p => (β p : ℤ))}
      (Q.genericExt K ι κ) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨β, hβ, h⟩ := exists_generalQuot_euler_eq_neg_genericExt (K := K) (ι := ι) (κ := κ)
    exact ⟨β, hβ, by rw [h, neg_neg]⟩
  · rintro _ ⟨β, hβ, rfl⟩
    have := neg_genericExt_le_euler (ι := ι) hβ
    linarith

end FQuiver

end

end QuiverInvariants
