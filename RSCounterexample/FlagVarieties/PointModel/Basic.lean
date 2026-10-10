import RSCounterexample.FlagVarieties.LineBundle.Model
import RSCounterexample.GLRep.Borel.Evaluation
import RSCounterexample.FlagVarieties.PointModel.Complex.ChainCount

/-!
# The ring model of Schubert unions over an arbitrary field

This is the field-general version of `PointModel.Complex.Basic`, `PointModel.Complex.MinorSpan` and
`PointModel.Complex.MinorEval`. Fix a field `K`.

* `MatrixEntryPolynomial K n = K[x_ij]`, `GLCoord K n = 𝒪(GL_n) = K[x_ij][det⁻¹]` (Tau Ceti),
  evaluation `evalAt g`, `glEval g` at `g ∈ GL_n(K)`.
* `IsBorel`, `permMat K w` (`ẇ e_j = e_{w j}`), `bruhatCell K w = B ẇ B`, `orbitSet K S`,
  `orbitIdeal K S`, `IsSemiInvOn`, `GlobalSectionsConstant K w`.
* The graded flag-minor algebra `minorSpan K m = A_λ` and the standard products `flagSpan K h`
  (`minorSpan_columnMultiplicity`).
* Right `B`-semi-invariance of `A_λ` (`evalAt_mul_of_mem_minorSpan`), and the reduction of vanishing
  on `B ẇ B` to vanishing on `U ẇ` (`forall_mem_orbitSet_iff`).

Field-free notions (`lowerSet`, `shapeWeightZ`, `MinorDatum`, column multiplicities,
`hyperplaneSectionSet`, chain sets) are declared in this namespace, in the files of
`PointModel/Complex/` and in `PointModel/Unitriangular`.
-/

open Schubert Demazure.FlagModule Demazure.SchubertUnions FinPermutation
open GLRep (glEval)

namespace FlagVarieties.PointModel

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {K : Type*} [Field K] {n : ℕ}

/-! ### Polynomials, `𝒪(GL_n)` and evaluation -/

/-- The polynomial ring `K[x_ij]` of the matrix entries. -/
abbrev MatrixEntryPolynomial (K : Type*) [Field K] (n : ℕ) := MvPolynomial (Fin n × Fin n) K

/-- The generic determinant. -/
abbrev genericDetPoly (K : Type*) [Field K] (n : ℕ) : MatrixEntryPolynomial K n :=
  (Matrix.mvPolynomialX (Fin n) (Fin n) K).det

/-- Evaluation at a matrix. -/
def evalAt (g : Matrix (Fin n) (Fin n) K) : MatrixEntryPolynomial K n →ₐ[K] K :=
  MvPolynomial.aeval fun rc => g rc.1 rc.2

@[simp]
theorem evalAt_X (g : Matrix (Fin n) (Fin n) K) (r c : Fin n) :
    evalAt g (MvPolynomial.X (r, c)) = g r c :=
  MvPolynomial.aeval_X _ _

theorem evalAt_genericDetPoly (g : Matrix (Fin n) (Fin n) K) : evalAt g (genericDetPoly K n) =
    g.det := by
  rw [AlgHom.map_det]
  congr 1
  ext i j
  simp [AlgHom.mapMatrix_apply, Matrix.mvPolynomialX_apply]

theorem isUnit_evalAt_genericDetPoly (g : GL (Fin n) K) :
    IsUnit (evalAt (g : Matrix (Fin n) (Fin n) K) (genericDetPoly K n)) := by
  rw [evalAt_genericDetPoly]
  exact (Matrix.isUnit_iff_isUnit_det _).mp g.isUnit

theorem glEval_algebraMap_eq_evalAt (g : GL (Fin n) K) (f : MatrixEntryPolynomial K n) :
    glEval g (algebraMap (MatrixEntryPolynomial K n) (GLCoord K n) f) = evalAt
        (g : Matrix (Fin n) (Fin n) K) f := by
  exact GLRep.glEval_algebraMap g f

theorem exists_mul_det_pow (t : GLCoord K n) :
    ∃ (f : MatrixEntryPolynomial K n) (k : ℕ),
      t * algebraMap (MatrixEntryPolynomial K n) (GLCoord K n) (genericDetPoly K n ^ k) =
        algebraMap (MatrixEntryPolynomial K n) (GLCoord K n) f := by
  obtain ⟨⟨f, ⟨_, k, rfl⟩⟩, hf⟩ := IsLocalization.surj (Submonoid.powers (genericDetPoly K n)) t
  exact ⟨f, k, hf⟩

/-! ### Borel subgroup, permutation matrices, Bruhat cells -/

/-- `b` is upper triangular. -/
def IsBorel (b : GL (Fin n) K) : Prop := (b : Matrix (Fin n) (Fin n) K).IsUpperTriangular

theorem IsBorel.mul {b b' : GL (Fin n) K} (hb : IsBorel b) (hb' : IsBorel b') :
    IsBorel (b * b') := by
  unfold IsBorel at *
  rw [Units.val_mul]
  exact Matrix.BlockTriangular.mul hb hb'

theorem isBorel_one : IsBorel (1 : GL (Fin n) K) := by
  unfold IsBorel
  rw [Units.val_one]
  exact Matrix.blockTriangular_one

/-- The permutation matrix `ẇ`, with `ẇ e_j = e_{w j}`. -/
def permMat (K : Type*) [Field K] (w : Equiv.Perm (Fin n)) : Matrix (Fin n) (Fin n) K :=
  fun i j => if i = w j then 1 else 0

theorem mul_permMat (g : Matrix (Fin n) (Fin n) K) (w : Equiv.Perm (Fin n)) (i j : Fin n) :
    (g * permMat K w) i j = g i (w j) := by
  classical
  simp [Matrix.mul_apply, permMat]

theorem permMat_one : permMat K (1 : Equiv.Perm (Fin n)) = 1 := by
  ext i j
  simp [permMat, Matrix.one_apply]

theorem permMat_mul (v w : Equiv.Perm (Fin n)) :
    permMat K (v * w) = permMat K v * permMat K w := by
  ext i j
  rw [mul_permMat]
  simp [permMat, Equiv.Perm.mul_apply]

/-- The permutation matrix as an invertible matrix. -/
def permGL (K : Type*) [Field K] (w : Equiv.Perm (Fin n)) : GL (Fin n) K where
  val := permMat K w
  inv := permMat K w⁻¹
  val_inv := by rw [← permMat_mul, mul_inv_cancel, permMat_one]
  inv_val := by rw [← permMat_mul, inv_mul_cancel, permMat_one]

@[simp]
theorem coe_permGL (w : Equiv.Perm (Fin n)) :
    (permGL K w : Matrix (Fin n) (Fin n) K) = permMat K w := rfl

/-- The Bruhat cell `B ẇ B`. -/
def bruhatCell (K : Type*) [Field K] (w : Equiv.Perm (Fin n)) : Set (GL (Fin n) K) :=
  {g | ∃ b₁ b₂ : GL (Fin n) K, IsBorel b₁ ∧ IsBorel b₂ ∧ g = b₁ * permGL K w * b₂}

/-- `⋃_{w ∈ S} B ẇ B`, the preimage of `X_S` for a Bruhat ideal `S`. -/
def orbitSet (K : Type*) [Field K] (S : Finset (Equiv.Perm (Fin n))) : Set (GL (Fin n) K) :=
  ⋃ w ∈ S, bruhatCell K w

theorem mem_orbitSet {S : Finset (Equiv.Perm (Fin n))} {g : GL (Fin n) K} :
    g ∈ orbitSet K S ↔ ∃ w ∈ S, g ∈ bruhatCell K w := by
  simp [orbitSet]

theorem orbitSet_mono {S S' : Finset (Equiv.Perm (Fin n))} (h : S ⊆ S') :
    orbitSet K S ⊆ orbitSet K S' := fun _ hg => by
  obtain ⟨w, hw, hg⟩ := mem_orbitSet.mp hg
  exact mem_orbitSet.mpr ⟨w, h hw, hg⟩

theorem orbitSet_union (S S' : Finset (Equiv.Perm (Fin n))) :
    orbitSet K (S ∪ S') = orbitSet K S ∪ orbitSet K S' := by
  ext g
  simp only [Set.mem_union, mem_orbitSet, Finset.mem_union]
  constructor
  · rintro ⟨w, hw | hw, hg⟩
    · exact Or.inl ⟨w, hw, hg⟩
    · exact Or.inr ⟨w, hw, hg⟩
  · rintro (⟨w, hw, hg⟩ | ⟨w, hw, hg⟩)
    · exact ⟨w, Or.inl hw, hg⟩
    · exact ⟨w, Or.inr hw, hg⟩

theorem bruhatCell_mul_borel {w : Equiv.Perm (Fin n)} {g b : GL (Fin n) K}
    (hg : g ∈ bruhatCell K w) (hb : IsBorel b) : g * b ∈ bruhatCell K w := by
  obtain ⟨b₁, b₂, h₁, h₂, rfl⟩ := hg
  exact ⟨b₁, b₂ * b, h₁, h₂.mul hb, by simp only [mul_assoc]⟩

theorem orbitSet_mul_borel {S : Finset (Equiv.Perm (Fin n))} {g b : GL (Fin n) K}
    (hg : g ∈ orbitSet K S) (hb : IsBorel b) : g * b ∈ orbitSet K S := by
  obtain ⟨w, hw, hg⟩ := mem_orbitSet.mp hg
  exact mem_orbitSet.mpr ⟨w, hw, bruhatCell_mul_borel hg hb⟩

/-- The ideal of functions vanishing on `orbitSet K S`. -/
def orbitIdeal (K : Type*) [Field K] (S : Finset (Equiv.Perm (Fin n))) :
    Ideal (GLCoord K n) where
  carrier := {t | ∀ g ∈ orbitSet K S, glEval g t = 0}
  add_mem' {a b} ha hb g hg := by rw [map_add, ha g hg, hb g hg, add_zero]
  zero_mem' g _ := map_zero _
  smul_mem' c a ha g hg := by rw [smul_eq_mul, map_mul, ha g hg, mul_zero]

theorem mem_orbitIdeal {S : Finset (Equiv.Perm (Fin n))} {t : GLCoord K n} :
    t ∈ orbitIdeal K S ↔ ∀ g ∈ orbitSet K S, glEval g t = 0 :=
  Iff.rfl

/-- `η(b) = ∏ᵢ b_ii^{ηᵢ}`. -/
def borelCharValue (η : Fin n → ℤ) (b : Matrix (Fin n) (Fin n) K) : K := ∏ i, b i i ^ η i

/-- Right semi-invariance of weight `η` on `Z`. -/
def IsSemiInvOn (Z : Set (GL (Fin n) K)) (η : Fin n → ℤ) (t : GLCoord K n) : Prop :=
  ∀ g ∈ Z, ∀ b : GL (Fin n) K, IsBorel b →
    glEval (g * b) t = borelCharValue η (b : Matrix (Fin n) (Fin n) K) * glEval g t

theorem IsSemiInvOn.mono {Z Z' : Set (GL (Fin n) K)} {η : Fin n → ℤ} {t : GLCoord K n}
    (h : IsSemiInvOn Z' η t) (hZ : Z ⊆ Z') : IsSemiInvOn Z η t :=
  fun g hg b hb => h g (hZ hg) b hb

theorem IsSemiInvOn.sub {Z : Set (GL (Fin n) K)} {η : Fin n → ℤ} {t t' : GLCoord K n}
    (h : IsSemiInvOn Z η t) (h' : IsSemiInvOn Z η t') : IsSemiInvOn Z η (t - t') :=
  fun g hg b hb => by rw [map_sub, map_sub, h g hg b hb, h' g hg b hb, mul_sub]

/-- **Constant global sections**: `Γ(X_w, 𝒪) = K` in ring form. -/
def GlobalSectionsConstant (K : Type*) [Field K] (w : Equiv.Perm (Fin n)) : Prop :=
  ∀ t : GLCoord K n, IsSemiInvOn (orbitSet K (lowerSet w)) 0 t →
    ∃ c : K, t - algebraMap K (GLCoord K n) c ∈ orbitIdeal K (lowerSet w)

/-! ### Flag minors and the graded flag-minor algebra -/

/-- The flag minor with rows `s` (in order) and columns `0, …, k`. -/
def rowMinor (K : Type*) [Field K] (k : Fin n) (s : Fin (k.val + 1) → Fin n) :
    MatrixEntryPolynomial K n :=
  (Matrix.of fun i j => (MvPolynomial.X (s i, prefixIndex k j) : MatrixEntryPolynomial K n)).det

/-- The polynomial of a minor datum. -/
def MinorDatum.toPoly (K : Type*) [Field K] (x : MinorDatum n) : MatrixEntryPolynomial K n :=
    rowMinor K x.1 x.2

theorem toPoly_eq_rowMinor (x : MinorDatum n) {k : Fin n} (hx : x.1 = k) :
    ∃ s : Fin (k.val + 1) → Fin n, MinorDatum.toPoly K x = rowMinor K k s := by
  rcases x with ⟨k', s'⟩
  change k' = k at hx
  subst hx
  exact ⟨s', rfl⟩

/-- The product of a finite family of flag minors. -/
def familyProd (K : Type*) [Field K] {d : ℕ} (x : Fin d → MinorDatum n) :
    MatrixEntryPolynomial K n :=
  ∏ j, MinorDatum.toPoly K (x j)

/-- The graded flag-minor algebra `A_λ` in column shape `m`. -/
def minorSpan (K : Type*) [Field K] (m : ColumnShape n) : Submodule K (MatrixEntryPolynomial K n) :=
  Submodule.span K
    {p | ∃ (d : ℕ) (x : Fin d → MinorDatum n), familyShape x = m ∧ familyProd K x = p}

/-- An ordered product of flag minors with sorted rows. -/
def colProd (K : Type*) [Field K] {d : ℕ} (h : Fin d → Fin n)
    (T : (j : Fin d) → FlagMinorRowSet (h j)) : MatrixEntryPolynomial K n :=
  ∏ j, rowMinor K (h j) (T j).rows

/-- The span of the ordered standard products with column sequence `h`. -/
def flagSpan (K : Type*) [Field K] {d : ℕ} (h : Fin d → Fin n) :
    Submodule K (MatrixEntryPolynomial K n) :=
  Submodule.span K (Set.range (colProd K h))

theorem familyProd_mem_minorSpan {d : ℕ} (x : Fin d → MinorDatum n) :
    familyProd K x ∈ minorSpan K (familyShape x) :=
  Submodule.subset_span ⟨d, x, rfl, rfl⟩

theorem familyProd_append {d d' : ℕ} (x : Fin d → MinorDatum n) (y : Fin d' → MinorDatum n) :
    familyProd K (Fin.append x y) = familyProd K x * familyProd K y := by
  simp only [familyProd, Fin.prod_univ_add, Fin.append_left, Fin.append_right]

theorem mul_mem_minorSpan {m m' : ColumnShape n} {p q : MatrixEntryPolynomial K n}
    (hp : p ∈ minorSpan K m) (hq : q ∈ minorSpan K m') : p * q ∈ minorSpan K (m + m') := by
  have hle : minorSpan K m * minorSpan K m' ≤ minorSpan K (m + m') := by
    rw [minorSpan, minorSpan, Submodule.span_mul_span]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨_, ⟨d, x, hx, rfl⟩, _, ⟨d', y, hy, rfl⟩, rfl⟩
    exact Submodule.subset_span ⟨d + d', Fin.append x y, by rw [familyShape_append, hx, hy],
      familyProd_append x y⟩
  exact hle (Submodule.mul_mem_mul hp hq)

theorem one_mem_minorSpan : (1 : MatrixEntryPolynomial K n) ∈ minorSpan K 0 :=
  Submodule.subset_span ⟨0, Fin.elim0, by funext k; simp [familyShape, columnMultiplicity_apply],
    by simp [familyProd]⟩

theorem pow_mem_minorSpan {m : ColumnShape n} {p : MatrixEntryPolynomial K n}
    (hp : p ∈ minorSpan K m)
    (k : ℕ) : p ^ k ∈ minorSpan K (k • m) := by
  induction k with
  | zero => simpa using one_mem_minorSpan
  | succ k ih =>
    rw [pow_succ, succ_nsmul]
    exact mul_mem_minorSpan ih hp

theorem toPoly_mem_minorSpan (x : MinorDatum n) : MinorDatum.toPoly K x ∈ minorSpan K
    (Pi.single x.1 1) := by
  have h := familyProd_mem_minorSpan (K := K) (fun _ : Fin 1 => x)
  have hs : familyShape (fun _ : Fin 1 => x) = Pi.single x.1 1 := by
    funext k
    simp [familyShape, columnMultiplicity_apply, Pi.single_apply, eq_comm]
  rw [hs] at h
  simpa [familyProd] using h

theorem rowMinor_mem_minorSpan (k : Fin n) (s : Fin (k.val + 1) → Fin n) :
    rowMinor K k s ∈ minorSpan K (Pi.single k 1) :=
  toPoly_mem_minorSpan ⟨k, s⟩

/-- Sorting the rows of a flag minor. -/
theorem exists_sorted_rows (k : Fin n) (s : Fin (k.val + 1) → Fin n) (hs : Function.Injective s) :
    ∃ (S : FlagMinorRowSet k) (σ : Equiv.Perm (Fin (k.val + 1))), ∀ i, S.rows (σ i) = s i := by
  classical
  let S : FlagMinorRowSet k := ⟨Finset.univ.image s, by
    refine Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, ?_⟩
    rw [Finset.card_image_of_injective _ hs, Finset.card_univ, Fintype.card_fin]⟩
  have hcard : S.val.card = k.val + 1 := (Finset.mem_powersetCard.mp S.property).2
  let f : Fin (k.val + 1) → Fin (k.val + 1) := fun i =>
    (S.val.orderIsoOfFin hcard).symm ⟨s i, Finset.mem_image_of_mem s (Finset.mem_univ i)⟩
  have hf : ∀ i, S.rows (f i) = s i := fun i => by
    change ((S.val.orderIsoOfFin hcard) ((S.val.orderIsoOfFin hcard).symm _) : Fin n) = s i
    rw [OrderIso.apply_symm_apply]
  have hinj : Function.Injective f := fun i j hij => hs (by rw [← hf i, ← hf j, hij])
  exact ⟨S, Equiv.ofBijective f hinj.bijective_of_finite, hf⟩

/-- A flag minor with arbitrary rows lies in the span of the flag minors with sorted rows. -/
theorem rowMinor_mem_span_sorted (k : Fin n) (s : Fin (k.val + 1) → Fin n) :
    rowMinor K k s ∈ Submodule.span K (Set.range fun S : FlagMinorRowSet k =>
        rowMinor K k S.rows) := by
  classical
  by_cases hs : Function.Injective s
  · obtain ⟨S, σ, hσ⟩ := exists_sorted_rows k s hs
    have h : rowMinor K k s = (Equiv.Perm.sign σ : K) • rowMinor K k S.rows := by
      have hM :
          (Matrix.of fun i j =>
          (MvPolynomial.X (s i, prefixIndex k j) : MatrixEntryPolynomial K n)) =
          (Matrix.of fun i j =>
              (MvPolynomial.X (S.rows i, prefixIndex k j) : MatrixEntryPolynomial K n)).submatrix
            σ id := by
        ext i j
        simp [hσ]
      rw [rowMinor, rowMinor, hM, Matrix.det_permute, Algebra.smul_def, map_intCast]
    rw [h]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨S, rfl⟩)
  · simp only [Function.Injective, not_forall] at hs
    obtain ⟨i, j, hij, hne⟩ := hs
    have : rowMinor K k s = 0 := by
      rw [rowMinor]
      refine Matrix.det_zero_of_row_eq (i := i) (j := j) hne ?_
      funext c
      simp [hij]
    rw [this]
    exact Submodule.zero_mem _

/-- Every product of flag minors with column sequence `h` lies in `flagSpan K h`. -/
theorem prod_rowMinor_mem_flagSpan {d : ℕ} (h : Fin d → Fin n)
    (s : (j : Fin d) → Fin ((h j).val + 1) → Fin n) :
    ∏ j, rowMinor K (h j) (s j) ∈ flagSpan K h := by
  classical
  have hmem : ∀ j, ∃ c : FlagMinorRowSet (h j) → K,
      rowMinor K (h j) (s j) = ∑ S, c S • rowMinor K (h j) S.rows := fun j => by
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp
      (rowMinor_mem_span_sorted (K := K) (h j) (s j))
    exact ⟨c, hc.symm⟩
  choose c hc using hmem
  rw [Finset.prod_congr rfl fun j _ => hc j, Fintype.prod_sum]
  refine Submodule.sum_mem _ fun T _ => ?_
  rw [Finset.prod_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨T, rfl⟩)

theorem prod_toPoly_mem_flagSpan {d : ℕ} (h : Fin d → Fin n) (z : Fin d → MinorDatum n)
    (hz : ∀ j, (z j).1 = h j) : ∏ j, MinorDatum.toPoly K (z j) ∈ flagSpan K h := by
  choose s hs using fun j => toPoly_eq_rowMinor (K := K) (z j) (hz j)
  simp_rw [hs]
  exact prod_rowMinor_mem_flagSpan h s

theorem flagSpan_le_minorSpan {d : ℕ} (h : Fin d → Fin n) :
    flagSpan K h ≤ minorSpan K (columnMultiplicity h) := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨T, rfl⟩
  exact Submodule.subset_span ⟨d, fun j => ⟨h j, (T j).rows⟩, rfl, rfl⟩

theorem minorSpan_le_flagSpan {d : ℕ} (h : Fin d → Fin n) :
    minorSpan K (columnMultiplicity h) ≤ flagSpan K h := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨d', x, hx, rfl⟩
  obtain ⟨σ, hσ⟩ := exists_equiv_of_columnMultiplicity_eq hx
  change ∏ j, MinorDatum.toPoly K (x j) ∈ flagSpan K h
  rw [← Equiv.prod_comp σ.symm (fun j => MinorDatum.toPoly K (x j))]
  exact prod_toPoly_mem_flagSpan h _ fun i => by rw [← hσ (σ.symm i), Equiv.apply_symm_apply]

/-- **The graded flag-minor algebra is the span of the standard products.** -/
theorem minorSpan_columnMultiplicity {d : ℕ} (h : Fin d → Fin n) :
    minorSpan K (columnMultiplicity h) = flagSpan K h :=
  le_antisymm (minorSpan_le_flagSpan h) (flagSpan_le_minorSpan h)

theorem colProd_mem_minorSpan {d : ℕ} (h : Fin d → Fin n)
    (T : (j : Fin d) → FlagMinorRowSet (h j)) :
    colProd K h T ∈ minorSpan K (columnMultiplicity h) := by
  rw [minorSpan_columnMultiplicity]
  exact Submodule.subset_span ⟨T, rfl⟩

instance finiteDimensional_flagSpan {d : ℕ} (h : Fin d → Fin n) :
    FiniteDimensional K (flagSpan K h) :=
  FiniteDimensional.span_of_finite K (Set.finite_range _)

instance finiteDimensional_minorSpan (m : ColumnShape n) : FiniteDimensional K (minorSpan K m) := by
  obtain ⟨d, h, rfl⟩ := exists_columnMultiplicity m
  rw [minorSpan_columnMultiplicity]
  infer_instance

/-! ### Evaluation and right `B`-semi-invariance -/

theorem evalAt_rowMinor (g : Matrix (Fin n) (Fin n) K) (k : Fin n) (s : Fin (k.val + 1) → Fin n) :
    evalAt g (rowMinor K k s) = (g.submatrix s (prefixIndex k)).det := by
  rw [rowMinor, AlgHom.map_det]
  congr 1
  ext i j
  simp [AlgHom.mapMatrix_apply]

theorem submatrix_mul_upper (g b : Matrix (Fin n) (Fin n) K) (hb : b.IsUpperTriangular)
    (k : Fin n) (s : Fin (k.val + 1) → Fin n) :
    (g * b).submatrix s (prefixIndex k) =
      g.submatrix s (prefixIndex k) * b.submatrix (prefixIndex k) (prefixIndex k) := by
  classical
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  have hsub : ∑ l, g (s i) l * b l (prefixIndex k j) =
      ∑ l ∈ Finset.univ.image (prefixIndex k), g (s i) l * b l (prefixIndex k j) := by
    symm
    refine Finset.sum_subset (Finset.subset_univ _) fun l _ hl => ?_
    have hlk : k.val < l.val := by
      by_contra hle
      exact hl (Finset.mem_image.mpr ⟨⟨l.val, by omega⟩, Finset.mem_univ _, Fin.ext rfl⟩)
    have hlt : prefixIndex k j < l := by
      change (prefixIndex k j).val < l.val
      simp only [prefixIndex]
      omega
    rw [hb (i := l) (j := prefixIndex k j) hlt, mul_zero]
  rw [hsub, Finset.sum_image (fun a _ b _ h => prefixIndex_injective k h)]

theorem prod_diag_prefixIndex (b : Matrix (Fin n) (Fin n) K) (k : Fin n) :
    ∏ i : Fin (k.val + 1), b (prefixIndex k i) (prefixIndex k i) =
      ∏ i : Fin n, b i i ^ (if i ≤ k then 1 else 0) := by
  classical
  have h1 : ∏ i ∈ Finset.univ.image (prefixIndex k), b i i =
      ∏ i : Fin (k.val + 1), b (prefixIndex k i) (prefixIndex k i) :=
    Finset.prod_image fun a _ c _ h => prefixIndex_injective k h
  rw [← h1]
  have himg : Finset.univ.image (prefixIndex k) = Finset.univ.filter fun i : Fin n => i ≤ k := by
    ext i
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
    constructor
    · rintro ⟨j, rfl⟩
      change (prefixIndex k j).val ≤ k.val
      simp only [prefixIndex]
      omega
    · intro hi
      exact ⟨⟨i.val, by have : i.val ≤ k.val := hi; omega⟩, Fin.ext rfl⟩
  rw [himg, Finset.prod_filter]
  refine Finset.prod_congr rfl fun i _ => ?_
  split_ifs <;> simp

theorem evalAt_mul_rowMinor (g b : Matrix (Fin n) (Fin n) K) (hb : b.IsUpperTriangular)
    (k : Fin n) (s : Fin (k.val + 1) → Fin n) :
    evalAt (g * b) (rowMinor K k s) =
      (∏ i : Fin n, b i i ^ (if i ≤ k then 1 else 0)) * evalAt g (rowMinor K k s) := by
  have hbu : (b.submatrix (prefixIndex k) (prefixIndex k)).IsUpperTriangular := fun i j hij =>
    hb (show prefixIndex k j < prefixIndex k i from by
      change (prefixIndex k j).val < (prefixIndex k i).val
      simpa only [prefixIndex, id_eq, Fin.lt_def] using hij)
  rw [evalAt_rowMinor, evalAt_rowMinor, submatrix_mul_upper g b hb, Matrix.det_mul,
    Matrix.det_of_isUpperTriangular hbu]
  simp only [Matrix.submatrix_apply]
  rw [prod_diag_prefixIndex, mul_comm]

/-- `∏ᵢ b_ii^{μᵢ}`. -/
def diagPow (μ : Fin n → ℕ) (b : Matrix (Fin n) (Fin n) K) : K := ∏ i, b i i ^ μ i

theorem diagPow_add (μ ν : Fin n → ℕ) (b : Matrix (Fin n) (Fin n) K) :
    diagPow (μ + ν) b = diagPow μ b * diagPow ν b := by
  simp only [diagPow, Pi.add_apply, pow_add, Finset.prod_mul_distrib]

theorem diagPow_nsmul (k : ℕ) (μ : Fin n → ℕ) (b : Matrix (Fin n) (Fin n) K) :
    diagPow (k • μ) b = diagPow μ b ^ k := by
  induction k with
  | zero => simp [diagPow]
  | succ k ih => rw [succ_nsmul, diagPow_add, ih, pow_succ]

theorem borelCharValue_shapeWeightZ (m : ColumnShape n) (b : Matrix (Fin n) (Fin n) K) :
    borelCharValue (shapeWeightZ m) b = diagPow (shapeWeight m) b := by
  simp only [borelCharValue, shapeWeightZ, diagPow, zpow_natCast]

theorem evalAt_mul_toPoly (g b : Matrix (Fin n) (Fin n) K) (hb : b.IsUpperTriangular)
    (x : MinorDatum n) :
    evalAt (g * b) (MinorDatum.toPoly K x) =
      diagPow (shapeWeight (Pi.single x.1 1)) b * evalAt g (MinorDatum.toPoly K x) := by
  rw [shapeWeight_single, MinorDatum.toPoly, evalAt_mul_rowMinor g b hb]
  rfl

theorem evalAt_mul_familyProd (g b : Matrix (Fin n) (Fin n) K) (hb : b.IsUpperTriangular) :
    ∀ {d : ℕ} (x : Fin d → MinorDatum n),
      evalAt (g * b) (familyProd K x) =
        diagPow (shapeWeight (familyShape x)) b * evalAt g (familyProd K x)
  | 0, x => by
    simp [familyProd, familyShape, columnMultiplicity_zero, shapeWeight_zero, diagPow]
  | d + 1, x => by
    have ih := evalAt_mul_familyProd g b hb (fun j => x j.castSucc)
    have hshape : familyShape x =
        familyShape (fun j => x j.castSucc) + Pi.single (x (Fin.last d)).1 1 :=
      columnMultiplicity_castSucc fun j => (x j).1
    have hprod : familyProd K x = familyProd K (fun j => x j.castSucc) * MinorDatum.toPoly K
        (x (Fin.last d)) :=
      Fin.prod_univ_castSucc _
    rw [hprod, map_mul, map_mul, ih, evalAt_mul_toPoly g b hb, hshape, shapeWeight_add, diagPow_add]
    ring

/-- **Elements of `A_λ` are semi-invariant of weight `λ`.** -/
theorem evalAt_mul_of_mem_minorSpan {m : ColumnShape n} {p : MatrixEntryPolynomial K n}
    (hp : p ∈ minorSpan K m) (g b : Matrix (Fin n) (Fin n) K) (hb : b.IsUpperTriangular) :
    evalAt (g * b) p = diagPow (shapeWeight m) b * evalAt g p := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨d, x, hx, rfl⟩ := hp
    rw [← hx]
    exact evalAt_mul_familyProd g b hb x
  | zero => simp
  | add p q _ _ hp hq => rw [map_add, map_add, hp, hq, mul_add]
  | smul c p _ hp => rw [map_smul, map_smul, hp, smul_eq_mul, smul_eq_mul, mul_left_comm]

theorem isSemiInvOn_of_mem_minorSpan {m : ColumnShape n} {p : MatrixEntryPolynomial K n}
    (hp : p ∈ minorSpan K m) (Z : Set (GL (Fin n) K)) :
    IsSemiInvOn Z (shapeWeightZ m) (algebraMap (MatrixEntryPolynomial K n) (GLCoord K n) p) := by
  intro g _ b hb
  rw [glEval_algebraMap_eq_evalAt, glEval_algebraMap_eq_evalAt, Units.val_mul,
      evalAt_mul_of_mem_minorSpan hp _ _ hb,
    borelCharValue_shapeWeightZ]

/-! ### Points of Bruhat cells -/

/-- An invertible matrix from a matrix with unit determinant. -/
def unitOfDet (u : Matrix (Fin n) (Fin n) K) (hu : IsUnit u.det) : GL (Fin n) K :=
  ((Matrix.isUnit_iff_isUnit_det u).mpr hu).unit

@[simp]
theorem coe_unitOfDet (u : Matrix (Fin n) (Fin n) K) (hu : IsUnit u.det) :
    (unitOfDet u hu : Matrix (Fin n) (Fin n) K) = u :=
  IsUnit.unit_spec _

theorem det_of_isUnitriangular {u : Matrix (Fin n) (Fin n) K} (hu : IsUnitriangular u) :
    u.det = 1 := by
  rw [Matrix.det_of_isUpperTriangular hu.1]
  exact Finset.prod_eq_one fun i _ => hu.2 i

theorem unitriangular_mul_mem_bruhatCell (w : Equiv.Perm (Fin n)) {u : Matrix (Fin n) (Fin n) K}
    (hu : IsUnitriangular u) :
    unitOfDet u (by rw [det_of_isUnitriangular hu]; exact isUnit_one) * permGL K w ∈
      bruhatCell K w :=
  ⟨unitOfDet u (by rw [det_of_isUnitriangular hu]; exact isUnit_one), 1,
    by unfold IsBorel; rw [coe_unitOfDet]; exact hu.1, isBorel_one, by simp⟩

theorem diagonal_mul_permMat (d : Fin n → K) (w : Equiv.Perm (Fin n)) :
    Matrix.diagonal d * permMat K w = permMat K w * Matrix.diagonal (d ∘ w) := by
  ext i j
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, permMat, Function.comp_apply]
  split_ifs with h <;> simp [h]

theorem diag_ne_zero_of_isBorel {b : GL (Fin n) K} (hb : IsBorel b) (i : Fin n) :
    (b : Matrix (Fin n) (Fin n) K) i i ≠ 0 := by
  have hdet : (b : Matrix (Fin n) (Fin n) K).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp b.isUnit).ne_zero
  rw [Matrix.det_of_isUpperTriangular hb] at hdet
  exact Finset.prod_ne_zero_iff.mp hdet i (Finset.mem_univ _)

/-- A point of `B ẇ B` is `u ẇ b` with `u` upper unitriangular and `b` upper triangular. -/
theorem exists_unitriangular_of_mem_bruhatCell {w : Equiv.Perm (Fin n)} {g : GL (Fin n) K}
    (hg : g ∈ bruhatCell K w) :
    ∃ u b : Matrix (Fin n) (Fin n) K, IsUnitriangular u ∧ b.IsUpperTriangular ∧
      (∀ i, b i i ≠ 0) ∧ (g : Matrix (Fin n) (Fin n) K) = u * permMat K w * b := by
  obtain ⟨b₁, b₂, h₁, h₂, rfl⟩ := hg
  let d : Fin n → K := fun i => (b₁ : Matrix (Fin n) (Fin n) K) i i
  have hd : ∀ i, d i ≠ 0 := diag_ne_zero_of_isBorel h₁
  refine ⟨(b₁ : Matrix (Fin n) (Fin n) K) * Matrix.diagonal (fun i => (d i)⁻¹),
    Matrix.diagonal (d ∘ w) * (b₂ : Matrix (Fin n) (Fin n) K), ⟨?_, fun i => ?_⟩,
    (Matrix.blockTriangular_diagonal _).mul h₂, fun i => ?_, ?_⟩
  · exact Matrix.BlockTriangular.mul h₁ (Matrix.blockTriangular_diagonal _)
  · simp [Matrix.mul_diagonal, d, hd i]
  · rw [Matrix.diagonal_mul]
    exact mul_ne_zero (hd (w i)) (diag_ne_zero_of_isBorel h₂ i)
  · have hb₁ : (b₁ : Matrix (Fin n) (Fin n) K) =
        ((b₁ : Matrix (Fin n) (Fin n) K) * Matrix.diagonal (fun i => (d i)⁻¹)) *
          Matrix.diagonal d := by
      rw [Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]
      have hone : (fun i => (d i)⁻¹ * d i) = fun _ => (1 : K) :=
        funext fun i => inv_mul_cancel₀ (hd i)
      rw [hone, Matrix.diagonal_one, Matrix.mul_one]
    rw [Units.val_mul, Units.val_mul, coe_permGL]
    conv_lhs => rw [hb₁]
    rw [Matrix.mul_assoc _ (Matrix.diagonal d), diagonal_mul_permMat]
    simp only [Matrix.mul_assoc]

/-- **Vanishing on `B ẇ B` reduces to vanishing on `U ẇ`** for elements of `A_λ`. -/
theorem forall_mem_orbitSet_iff {m : ColumnShape n} {p : MatrixEntryPolynomial K n}
    (hp : p ∈ minorSpan K m)
    (S : Finset (Equiv.Perm (Fin n))) :
    (∀ g ∈ orbitSet K S, evalAt (g : Matrix (Fin n) (Fin n) K) p = 0) ↔
      ∀ w ∈ S, ∀ u : Matrix (Fin n) (Fin n) K, IsUnitriangular u →
        evalAt (u * permMat K w) p = 0 := by
  constructor
  · intro h w hw u hu
    have := h _ (mem_orbitSet.mpr ⟨w, hw, unitriangular_mul_mem_bruhatCell w hu⟩)
    simpa using this
  · intro h g hg
    obtain ⟨w, hw, hg⟩ := mem_orbitSet.mp hg
    obtain ⟨u, b, hu, hb, -, hgub⟩ := exists_unitriangular_of_mem_bruhatCell hg
    rw [hgub, evalAt_mul_of_mem_minorSpan hp _ _ hb, h w hw u hu, mul_zero]

end

end FlagVarieties.PointModel
