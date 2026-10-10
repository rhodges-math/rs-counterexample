import RSCounterexample.FlagVarieties.PointModel.Complex.Basic

/-!
# The flag-minor algebra, graded by column shape

`A_m ⊆ ℂ[x_ij]` is the span of the products of flag minors with column multiplicities `m`; the
minors may have arbitrary rows. We write it `minorSpan m`, and show that it equals the Demazure
library's span of ordered standard products `flagSpan h = span {flagColumnProduct h T}` for every
ordered column sequence `h` with `columnMultiplicity h = m` (`minorSpan_columnMultiplicity`).

The graded pieces multiply: `A_m · A_{m'} ⊆ A_{m + m'}` (`mul_mem_minorSpan`).
-/

open Schubert Demazure.FlagModule

namespace FlagVarieties.PointModel.Complex

noncomputable section

variable {n : ℕ}

/-- A flag minor: a height `k` and an ordered list of `k + 1` rows; the columns are `0, …, k`. -/
abbrev _root_.FlagVarieties.PointModel.MinorDatum (n : ℕ) := Σ k : Fin n, (Fin (k.val + 1) → Fin n)

/-- The polynomial of a minor datum. -/
def _root_.FlagVarieties.PointModel.MinorDatum.poly (x : MinorDatum n) : MatrixPolynomial n :=
    flagRowMinor x.1 x.2

theorem _root_.FlagVarieties.PointModel.MinorDatum.exists_poly_eq (x : MinorDatum n) {k : Fin n}
    (hx : x.1 = k) :
    ∃ s : Fin (k.val + 1) → Fin n, x.poly = flagRowMinor k s := by
  rcases x with ⟨k', s'⟩
  change k' = k at hx
  subst hx
  exact ⟨s', rfl⟩

/-- The product of a finite family of flag minors. -/
def familyProd {d : ℕ} (x : Fin d → MinorDatum n) : MatrixPolynomial n := ∏ j, (x j).poly

/-- The column multiplicities of a finite family of flag minors. -/
def _root_.FlagVarieties.PointModel.familyShape {d : ℕ} (x : Fin d → MinorDatum n) :
    ColumnShape n :=
  columnMultiplicity fun j => (x j).1

-- The field-free notions live in `FlagVarieties.PointModel`; they are also names here.
export PointModel (MinorDatum familyShape)

/-- **The flag-minor algebra in column shape `m`**: the span of all products of flag minors
with column multiplicities `m`. -/
def minorSpan (m : ColumnShape n) : Submodule ℂ (MatrixPolynomial n) :=
  Submodule.span ℂ {p | ∃ (d : ℕ) (x : Fin d → MinorDatum n), familyShape x = m ∧ familyProd x = p}

/-- The Demazure library's span of the ordered flag-minor products with column sequence `h`. -/
def flagSpan {d : ℕ} (h : Fin d → Fin n) : Submodule ℂ (MatrixPolynomial n) :=
  Submodule.span ℂ (Set.range (flagColumnProduct h))

theorem familyProd_mem_minorSpan {d : ℕ} (x : Fin d → MinorDatum n) :
    familyProd x ∈ minorSpan (familyShape x) :=
  Submodule.subset_span ⟨d, x, rfl, rfl⟩

/-! ### Column multiplicities -/

theorem _root_.FlagVarieties.PointModel.columnMultiplicity_apply {d : ℕ} (h : Fin d → Fin n)
    (k : Fin n) :
    columnMultiplicity h k = ∑ j, if h j = k then 1 else 0 := by
  classical
  rw [columnMultiplicity, Fintype.card_subtype, Finset.card_filter]

theorem columnMultiplicity_append {d d' : ℕ} (h : Fin d → Fin n) (h' : Fin d' → Fin n) :
    columnMultiplicity (Fin.append h h') = columnMultiplicity h + columnMultiplicity h' := by
  funext k
  simp only [columnMultiplicity_apply, Fin.sum_univ_add, Fin.append_left, Fin.append_right,
    Pi.add_apply]

theorem _root_.FlagVarieties.PointModel.columnMultiplicity_castSucc {d : ℕ}
    (h : Fin (d + 1) → Fin n) :
    columnMultiplicity h =
      columnMultiplicity (fun j => h j.castSucc) + Pi.single (h (Fin.last d)) 1 := by
  funext k
  simp only [columnMultiplicity_apply, Fin.sum_univ_castSucc, Pi.add_apply, Pi.single_apply]
  congr 1
  by_cases hk : h (Fin.last d) = k
  · simp [hk]
  · simp [hk, Ne.symm hk]

theorem _root_.FlagVarieties.PointModel.columnMultiplicity_zero (h : Fin 0 → Fin n) :
    columnMultiplicity h = 0 := by
  funext k
  simp [columnMultiplicity_apply]

theorem sum_columnMultiplicity {d : ℕ} (h : Fin d → Fin n) : ∑ k, columnMultiplicity h k = d := by
  simp only [columnMultiplicity]
  rw [← Fintype.card_sigma, Fintype.card_congr (Equiv.sigmaFiberEquiv h), Fintype.card_fin]

/-- Two column sequences with the same multiplicities differ by a bijection of positions. -/
theorem _root_.FlagVarieties.PointModel.exists_equiv_of_columnMultiplicity_eq {d d' : ℕ}
    {h : Fin d → Fin n} {h' : Fin d' → Fin n}
    (hm : columnMultiplicity h = columnMultiplicity h') :
    ∃ σ : Fin d ≃ Fin d', ∀ j, h' (σ j) = h j :=
  ⟨Equiv.ofFiberEquiv fun k => Fintype.equivOfCardEq (congrFun hm k),
    Equiv.ofFiberEquiv_map _⟩

/-! ### Products in the graded flag-minor algebra -/

theorem _root_.FlagVarieties.PointModel.familyShape_append {d d' : ℕ} (x : Fin d → MinorDatum n)
    (y : Fin d' → MinorDatum n) :
    familyShape (Fin.append x y) = familyShape x + familyShape y := by
  have : (fun j => (Fin.append x y j).1) = Fin.append (fun j => (x j).1) (fun j => (y j).1) := by
    funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp
  rw [familyShape, this, columnMultiplicity_append]
  rfl

theorem familyProd_append {d d' : ℕ} (x : Fin d → MinorDatum n) (y : Fin d' → MinorDatum n) :
    familyProd (Fin.append x y) = familyProd x * familyProd y := by
  simp only [familyProd, Fin.prod_univ_add, Fin.append_left, Fin.append_right]

theorem mul_mem_minorSpan {m m' : ColumnShape n} {p q : MatrixPolynomial n}
    (hp : p ∈ minorSpan m) (hq : q ∈ minorSpan m') : p * q ∈ minorSpan (m + m') := by
  have hle : minorSpan m * minorSpan m' ≤ minorSpan (m + m') := by
    rw [minorSpan, minorSpan, Submodule.span_mul_span]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨_, ⟨d, x, hx, rfl⟩, _, ⟨d', y, hy, rfl⟩, rfl⟩
    exact Submodule.subset_span ⟨d + d', Fin.append x y, by rw [familyShape_append, hx, hy],
      familyProd_append x y⟩
  exact hle (Submodule.mul_mem_mul hp hq)

theorem one_mem_minorSpan : (1 : MatrixPolynomial n) ∈ minorSpan 0 :=
  Submodule.subset_span ⟨0, Fin.elim0, by funext k; simp [familyShape, columnMultiplicity_apply],
    by simp [familyProd]⟩

theorem pow_mem_minorSpan {m : ColumnShape n} {p : MatrixPolynomial n} (hp : p ∈ minorSpan m)
    (k : ℕ) : p ^ k ∈ minorSpan (k • m) := by
  induction k with
  | zero => simpa using one_mem_minorSpan
  | succ k ih =>
    rw [pow_succ, succ_nsmul]
    exact mul_mem_minorSpan ih hp

theorem poly_mem_minorSpan (x : MinorDatum n) : x.poly ∈ minorSpan (Pi.single x.1 1) := by
  have h := familyProd_mem_minorSpan (fun _ : Fin 1 => x)
  have hs : familyShape (fun _ : Fin 1 => x) = Pi.single x.1 1 := by
    funext k
    simp [familyShape, columnMultiplicity_apply, Pi.single_apply, eq_comm]
  rw [hs] at h
  simpa [familyProd] using h

theorem flagRowMinor_mem_minorSpan (k : Fin n) (s : Fin (k.val + 1) → Fin n) :
    flagRowMinor k s ∈ minorSpan (Pi.single k 1) :=
  poly_mem_minorSpan ⟨k, s⟩

/-! ### Comparison with the ordered standard products -/

/-- A flag minor with arbitrary rows lies in the span of the flag minors with sorted rows. -/
theorem flagRowMinor_eq_sum (k : Fin n) (s : Fin (k.val + 1) → Fin n) :
    flagRowMinor k s =
      ∑ S : FlagMinorRowSet k, ((1 : Square n).submatrix S.rows s).det • flagRowMinor k S.rows := by
  have h := rowAction_flagRowMinor_sum (1 : Square n) k s
  simpa [rowAction_one] using h

/-- Every product of flag minors with column sequence `h` lies in `flagSpan h`. -/
theorem prod_flagRowMinor_mem_flagSpan {d : ℕ} (h : Fin d → Fin n)
    (s : (j : Fin d) → Fin ((h j).val + 1) → Fin n) :
    ∏ j, flagRowMinor (h j) (s j) ∈ flagSpan h := by
  classical
  rw [Finset.prod_congr rfl fun j _ => flagRowMinor_eq_sum (h j) (s j), Fintype.prod_sum]
  refine Submodule.sum_mem _ fun T _ => ?_
  rw [Finset.prod_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨T, rfl⟩)

theorem prod_poly_mem_flagSpan {d : ℕ} (h : Fin d → Fin n) (z : Fin d → MinorDatum n)
    (hz : ∀ j, (z j).1 = h j) : ∏ j, (z j).poly ∈ flagSpan h := by
  choose s hs using fun j => (z j).exists_poly_eq (hz j)
  simp_rw [hs]
  exact prod_flagRowMinor_mem_flagSpan h s

theorem flagSpan_le_minorSpan {d : ℕ} (h : Fin d → Fin n) :
    flagSpan h ≤ minorSpan (columnMultiplicity h) := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨T, rfl⟩
  exact Submodule.subset_span ⟨d, fun j => ⟨h j, (T j).rows⟩, rfl, rfl⟩

theorem minorSpan_le_flagSpan {d : ℕ} (h : Fin d → Fin n) :
    minorSpan (columnMultiplicity h) ≤ flagSpan h := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨d', x, hx, rfl⟩
  obtain ⟨σ, hσ⟩ := exists_equiv_of_columnMultiplicity_eq hx
  change ∏ j, (x j).poly ∈ flagSpan h
  rw [← Equiv.prod_comp σ.symm (fun j => (x j).poly)]
  exact prod_poly_mem_flagSpan h _ fun i => by rw [← hσ (σ.symm i), Equiv.apply_symm_apply]

/-- **The graded flag-minor algebra is the Demazure library's span of standard products.** -/
theorem minorSpan_columnMultiplicity {d : ℕ} (h : Fin d → Fin n) :
    minorSpan (columnMultiplicity h) = flagSpan h :=
  le_antisymm (minorSpan_le_flagSpan h) (flagSpan_le_minorSpan h)

theorem flagSpan_congr {d d' : ℕ} {h : Fin d → Fin n} {h' : Fin d' → Fin n}
    (hm : columnMultiplicity h = columnMultiplicity h') : flagSpan h = flagSpan h' := by
  rw [← minorSpan_columnMultiplicity, ← minorSpan_columnMultiplicity, hm]

/-- Multiplying `flagSpan` of the first `d` columns by a minor of the last height lands in
`flagSpan h`. -/
theorem mul_flagRowMinor_mem_flagSpan {d : ℕ} (h : Fin (d + 1) → Fin n) {q : MatrixPolynomial n}
    (hq : q ∈ flagSpan fun j => h j.castSucc) (s : Fin ((h (Fin.last d)).val + 1) → Fin n) :
    q * flagRowMinor (h (Fin.last d)) s ∈ flagSpan h := by
  rw [← minorSpan_columnMultiplicity, columnMultiplicity_castSucc]
  rw [← minorSpan_columnMultiplicity] at hq
  exact mul_mem_minorSpan hq (flagRowMinor_mem_minorSpan _ s)

end

end FlagVarieties.PointModel.Complex
