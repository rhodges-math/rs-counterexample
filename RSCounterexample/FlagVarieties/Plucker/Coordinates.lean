import RSCounterexample.FlagVarieties.Normality.Fulton.ParabolicChart
import RSCounterexample.FlagVarieties.PointModel.SectionBasis

/-!
# Plücker coordinates (ring and point level)

Over a field `K` (namespace `FlagVarieties.PointModel`).

* `pluckerVector k g : FlagMinorRowSet k → K`: the Plücker coordinates `Δ_T(g)`, `|T| = k + 1`, of
  the `(k+1)`-dimensional step `V_{k+1} = span(g e_0, …, g e_k)` of the flag of `g`; there are
  `n.choose (k + 1)` of them (`card_flagMinorRowSet`), not all zero (`pluckerVector_ne_zero`).
* **`pluckerVector_proportional_iff`**: the Plücker vectors of `g` and `g'` are proportional in
  every height iff `g' ∈ g B`. So the Plücker map `GL_n(K)/B → ∏_k ℙ(∧^{k+1} Kⁿ)` is well
  defined and **injective**: the point-level Plücker embedding of `Fl_n(K)`. The proof recovers
  the chart representative `L(g)` from ratios of Plücker coordinates (Cramer's rule,
  `chartMatrix_apply`).
* **`𝒪(1) ↔ 𝓛(-ϖ_k)`**: the Plücker coordinates are a basis of the degree-one part
  `A_{ϖ_k}` of the flag-minor algebra (`pluckerBasis`, characteristic `0`), and, through the
  restriction `A_{ϖ_k} ≅ H⁰(Fl_n, 𝓛(-ϖ_k))` (Borel–Weil, `pluckerSectionsEquiv`, with
  `GlobalSectionsConstant` as a hypothesis), a basis of the sections of `𝓛(-ϖ_k)`: the hyperplane
  sections of `ℙ(∧^{k+1} Kⁿ)` pull back to the sections of `𝓛(-ϖ_k)`, and
  `dim H⁰(Fl_n, 𝓛(-ϖ_k)) = n.choose (k + 1)`.
-/

open Schubert Demazure.FlagModule Demazure.SchubertUnions FinPermutation

namespace FlagVarieties.PointModel

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {K : Type*} [Field K] {n : ℕ}

/-! ### Plücker vectors -/

/-- The Plücker coordinates of height `k` of a matrix: its flag minors `Δ_T`, `|T| = k + 1`. -/
def pluckerVector (k : Fin n) (g : Matrix (Fin n) (Fin n) K) : FlagMinorRowSet k → K :=
  fun T => evalAt g (rowMinor K k T.rows)

theorem card_flagMinorRowSet (k : Fin n) :
    Fintype.card (FlagMinorRowSet k) = n.choose (k.val + 1) := by
  rw [Fintype.card_coe, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

theorem pluckerVector_ne_zero (k : Fin n) (g : GL (Fin n) K) :
    pluckerVector k (g : Matrix (Fin n) (Fin n) K) ≠ 0 := by
  obtain ⟨S, hS⟩ := exists_rowMinor_ne_zero k g
  exact fun h => hS (congrFun h S)

theorem columnMultiplicity_one (k : Fin n) :
    columnMultiplicity (fun _ : Fin 1 => k) = Pi.single k 1 := by
  rw [columnMultiplicity_const, one_smul]

/-- Proportional Plücker vectors are proportional on all of `A_{ϖ_k}`. -/
theorem evalAt_eq_mul_of_pluckerVector {k : Fin n} {g g' : Matrix (Fin n) (Fin n) K} {c : K}
    (h : pluckerVector k g' = c • pluckerVector k g) {p : MatrixEntryPolynomial K n}
    (hp : p ∈ minorSpan K (Pi.single k 1)) : evalAt g' p = c * evalAt g p := by
  rw [← columnMultiplicity_one, minorSpan_columnMultiplicity] at hp
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨T, rfl⟩ := hp
    have := congrFun h (T 0)
    simpa [colProd, pluckerVector] using this
  | zero => simp
  | add p q _ _ hp hq => rw [map_add, map_add, hp, hq, mul_add]
  | smul a p _ hp => rw [map_smul, map_smul, hp, smul_eq_mul, smul_eq_mul, mul_left_comm]

/-- With proportional Plücker vectors, the chart representatives agree. -/
theorem chartMatrix_eq_of_pluckerVector {v : Equiv.Perm (Fin n)}
    {g g' : Matrix (Fin n) (Fin n) K}
    (hc : ∀ k, ∃ c : K, pluckerVector k g' = c • pluckerVector k g)
    (hg' : ∀ k, evalAt g' (chartMinor K v k) ≠ 0) :
    chartMatrix K v g' = chartMatrix K v g := by
  ext r c
  obtain ⟨d, hd⟩ := hc c
  have hD := evalAt_eq_mul_of_pluckerVector hd (p := chartMinor K v c) (rowMinor_mem_minorSpan c _)
  have hN := evalAt_eq_mul_of_pluckerVector hd (p := numMinor K v r c) (rowMinor_mem_minorSpan c _)
  have hd0 : d ≠ 0 := fun h0 => hg' c (by rw [hD, h0, zero_mul])
  rw [chartMatrix_apply, chartMatrix_apply, hD, hN]
  exact mul_div_mul_left _ _ hd0

private theorem diag_ne_zero_of_upper_det {b : Matrix (Fin n) (Fin n) K}
    (hb : b.IsUpperTriangular) (hdet : b.det ≠ 0) (i : Fin n) : b i i ≠ 0 := by
  rw [Matrix.det_of_isUpperTriangular hb] at hdet
  exact Finset.prod_ne_zero_iff.mp hdet i (Finset.mem_univ _)

/-- **The Plücker embedding is injective on `GL_n(K)/B`**: the Plücker vectors of `g` and `g'` are
proportional in every height iff `g' ∈ g B`. -/
theorem pluckerVector_proportional_iff (g g' : GL (Fin n) K) :
    (∀ k, ∃ c : K, c ≠ 0 ∧
      pluckerVector k (g' : Matrix (Fin n) (Fin n) K) =
        c • pluckerVector k (g : Matrix (Fin n) (Fin n) K)) ↔
      ∃ b : Matrix (Fin n) (Fin n) K, b.IsUpperTriangular ∧
        (g' : Matrix (Fin n) (Fin n) K) = (g : Matrix (Fin n) (Fin n) K) * b := by
  constructor
  · intro hc
    obtain ⟨v, hv⟩ := exists_chartMinor_ne_zero g
    have hv' : ∀ k, evalAt (g' : Matrix (Fin n) (Fin n) K) (chartMinor K v k) ≠ 0 := by
      intro k
      obtain ⟨c, hc0, hck⟩ := hc k
      rw [evalAt_eq_mul_of_pluckerVector hck (p := chartMinor K v k) (rowMinor_mem_minorSpan k _)]
      exact mul_ne_zero hc0 (hv k)
    have hL := chartMatrix_eq_of_pluckerVector (fun k => (hc k).imp fun _ h => h.2) hv'
    refine ⟨chartBeta K v g * chartInvBeta K v g',
      (chartBeta_isUpperTriangular v _).mul fun i j hij => chartInvBeta_blockTriangular hv' hij, ?_⟩
    calc (g' : Matrix (Fin n) (Fin n) K) = chartMatrix K v g' * chartInvBeta K v g' :=
          (chartMatrix_mul_chartInvBeta hv').symm
      _ = chartMatrix K v g * chartInvBeta K v g' := by rw [hL]
      _ = (g : Matrix (Fin n) (Fin n) K) * (chartBeta K v g * chartInvBeta K v g') := by
          rw [chartMatrix, Matrix.mul_assoc]
  · rintro ⟨b, hb, hg'⟩ k
    have hgdet : (g' : Matrix (Fin n) (Fin n) K).det ≠ 0 :=
      ((Matrix.isUnit_iff_isUnit_det _).mp g'.isUnit).ne_zero
    have hbdet : b.det ≠ 0 := fun h => hgdet (by rw [hg', Matrix.det_mul, h, mul_zero])
    refine ⟨diagPow (shapeWeight (Pi.single k 1)) b,
      diagPow_ne_zero (diag_ne_zero_of_upper_det hb hbdet) _, ?_⟩
    funext T
    rw [Pi.smul_apply, smul_eq_mul, pluckerVector, pluckerVector, hg',
      evalAt_mul_of_mem_minorSpan (rowMinor_mem_minorSpan k _) _ _ hb]

/-! ### Plücker coordinates as sections -/

/-- Every row set of size `k + 1` is the prefix set `v{0..k}` of a permutation. -/
theorem exists_flagPrefixRows_eq {k : Fin n} (T : FlagMinorRowSet k) :
    ∃ v : Equiv.Perm (Fin n), flagPrefixRows v k = T := by
  classical
  have hT : T.val.card = k.val + 1 := (Finset.mem_powersetCard.mp T.property).2
  have h1 : Fintype.card {i : Fin n // i ≤ k} = Fintype.card {x : Fin n // x ∈ T.val} := by
    rw [← Fintype.card_congr (lowEquiv k), Fintype.card_fin, Fintype.card_coe, hT]
  set e₁ := Fintype.equivOfCardEq h1
  set v := e₁.extendSubtype
  have hv : ∀ i (hi : i ≤ k), v i = (e₁ ⟨i, hi⟩ : Fin n) := fun i hi =>
    Equiv.extendSubtype_apply_of_mem e₁ i hi
  refine ⟨v, Subtype.ext ?_⟩
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    change x ∈ Finset.univ.image (fun j => v (prefixIndex k j)) at hx
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hx
    have hj : prefixIndex k j ≤ k := by
      change (prefixIndex k j).val ≤ k.val
      have := j.isLt
      simp only [prefixIndex]
      omega
    rw [hv _ hj]
    exact (e₁ ⟨_, hj⟩).2
  · rw [hT]
    exact ((Finset.mem_powersetCard.mp (flagPrefixRows v k).property).2).ge

theorem mem_chainSet_single {k : Fin n} (T : (j : Fin 1) → FlagMinorRowSet ((fun _ => k) j)) :
    T ∈ chainSet (fun _ : Fin 1 => k) Finset.univ := by
  obtain ⟨v, hv⟩ := exists_flagPrefixRows_eq (T 0)
  refine mem_chainSet.mpr ⟨v, Finset.mem_univ v, fun _ => v, fun _ _ _ => strongBruhat_refl v,
    fun j => ?_, fun _ => strongBruhat_refl v⟩
  rw [Subsingleton.elim j 0]
  exact hv

/-- **The Plücker coordinates are linearly independent** (characteristic `0`). -/
theorem linearIndependent_plucker [CharZero K] (k : Fin n) :
    LinearIndependent K (fun T : FlagMinorRowSet k => rowMinor K k T.rows) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc T
  let e : {T' // T' ∈ chainSet (fun _ : Fin 1 => k) Finset.univ} ≃ FlagMinorRowSet k :=
    { toFun := fun T' => T'.1 0
      invFun := fun T => ⟨fun _ => T, mem_chainSet_single _⟩
      left_inv := fun T' => Subtype.ext (funext fun j => by rw [Subsingleton.elim j 0])
      right_inv := fun _ => rfl }
  have hsum : ∑ T' : {T' // T' ∈ chainSet (fun _ : Fin 1 => k) Finset.univ},
      c (e T') • colProd K (fun _ : Fin 1 => k) T'.1 = 0 := by
    rw [← hc, ← e.sum_comp]
    refine Finset.sum_congr rfl fun T' _ => ?_
    simp [e, colProd]
  have h0 := eq_zero_of_sum_mem_vanishSpan (fun _ : Fin 1 => k) Finset.univ (fun T' => c (e T'))
    (by rw [hsum]; exact Submodule.zero_mem _)
  have := congrFun h0 (e.symm T)
  simpa using this

theorem rowMinor_mem_minorSpan_single (k : Fin n) (T : FlagMinorRowSet k) :
    rowMinor K k T.rows ∈ minorSpan K (Pi.single k 1) :=
  rowMinor_mem_minorSpan k _

/-- The Plücker coordinates span `A_{ϖ_k}`. -/
theorem span_plucker (k : Fin n) :
    Submodule.span K (Set.range fun T : FlagMinorRowSet k => rowMinor K k T.rows) =
      minorSpan K (Pi.single k 1) := by
  apply le_antisymm
  · exact Submodule.span_le.mpr (by rintro _ ⟨T, rfl⟩; exact rowMinor_mem_minorSpan_single k T)
  · rw [← columnMultiplicity_one, minorSpan_columnMultiplicity]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨T, rfl⟩
    exact Submodule.subset_span ⟨T 0, by simp [colProd]⟩

/-- **The Plücker coordinates are a basis of `A_{ϖ_k}`** (characteristic `0`). -/
def pluckerBasis [CharZero K] (k : Fin n) :
    Module.Basis (FlagMinorRowSet k) K (minorSpan K (Pi.single k 1)) :=
  (Module.Basis.span (linearIndependent_plucker (K := K) k)).map
    (LinearEquiv.ofEq _ _ (span_plucker k))

theorem pluckerBasis_apply [CharZero K] (k : Fin n) (T : FlagMinorRowSet k) :
    (pluckerBasis (K := K) k T : MatrixEntryPolynomial K n) = rowMinor K k T.rows := by
  simp [pluckerBasis]

theorem finrank_minorSpan_single [CharZero K] (k : Fin n) :
    Module.finrank K (minorSpan K (Pi.single k 1)) = n.choose (k.val + 1) := by
  rw [Module.finrank_eq_card_basis (pluckerBasis (K := K) k), card_flagMinorRowSet]

/-- **`𝒪(1) ↔ 𝓛(-ϖ_k)`**: restriction identifies `A_{ϖ_k}` (the span of the Plücker
coordinates) with `H⁰(Fl_n, 𝓛(-ϖ_k))` (Borel–Weil, with `GlobalSectionsConstant` as a hypothesis).
-/
def pluckerSectionsEquivOfGlobalSectionsConstant [IsAlgClosed K] [CharZero K]
    (hglobalSections : ∀ w : Equiv.Perm (Fin n), GlobalSectionsConstant K w) (k : Fin n) :
    minorSpan K (Pi.single k 1) ≃ₗ[K]
      sectionSpace K Finset.univ (shapeWeightZ (Pi.single k 1)) :=
  LinearEquiv.ofBijective (minorRestriction K Finset.univ (Pi.single k 1))
    ⟨by
      rw [← LinearMap.ker_eq_bot, ker_minorRestriction, vanishSpan_univ, Submodule.comap_bot,
        Submodule.ker_subtype],
      minorRestriction_surjective_of_globalSectionsConstant (standardMonomialTheory_of_charZero K)
          hglobalSections bruhatLower_univ _⟩

/-- **The Plücker coordinates are a basis of `H⁰(Fl_n, 𝓛(-ϖ_k))`.** -/
def pluckerSectionBasisOfGlobalSectionsConstant [IsAlgClosed K] [CharZero K]
    (hglobalSections : ∀ w : Equiv.Perm (Fin n), GlobalSectionsConstant K w) (k : Fin n) :
    Module.Basis (FlagMinorRowSet k) K
      (sectionSpace K Finset.univ (shapeWeightZ (Pi.single k 1))) :=
  (pluckerBasis k).map (pluckerSectionsEquivOfGlobalSectionsConstant hglobalSections k)

theorem finrank_sections_single_of_globalSectionsConstant [IsAlgClosed K] [CharZero K]
    (hglobalSections : ∀ w : Equiv.Perm (Fin n), GlobalSectionsConstant K w) (k : Fin n) :
    Module.finrank K (sectionSpace K Finset.univ (shapeWeightZ (Pi.single k 1))) =
      n.choose (k.val + 1) := by
  rw [Module.finrank_eq_card_basis
      (pluckerSectionBasisOfGlobalSectionsConstant hglobalSections k),
      card_flagMinorRowSet]

end

end FlagVarieties.PointModel
