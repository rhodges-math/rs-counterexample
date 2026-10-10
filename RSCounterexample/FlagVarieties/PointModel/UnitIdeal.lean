import RSCounterexample.FlagVarieties.PointModel.Chart
import RSCounterexample.FlagVarieties.Foundations.TypeA.MatrixBruhatDecomposition
import Mathlib.RingTheory.Nullstellensatz

/-!
# The big cells cover `GL_n`

* `exists_mem_bruhatCell`: the Bruhat decomposition `GL_n = ⋃_w B ẇ B` (from the type-A
  Bruhat decomposition of invertible matrices).
* `evalAt_chartPoly_ne_zero_of_mem_bruhatCell`: on `B ẇ B` the chart polynomial `f_w` does not
  vanish; hence every `g ∈ GL_n(K)` lies in some big cell `G_v`.
* `exists_partition_of_unity` (**unit ideal**): for every `N`, there are `c_v ∈ 𝒪(GL_n)` with
  `∑_v c_v f_v^N = 1`. The proof is Hilbert's Nullstellensatz: `det` vanishes on the common zero
  locus of the `f_v`.
-/

open Schubert Demazure.FlagModule Demazure.SchubertUnions FinPermutation

namespace FlagVarieties.PointModel

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {K : Type*} [Field K] {n : ℕ}

/-- **Bruhat decomposition**: every invertible matrix lies in a Bruhat cell. -/
theorem exists_mem_bruhatCell (g : GL (Fin n) K) : ∃ w, g ∈ bruhatCell K w := by
  obtain ⟨B, C, w, hB, hC, huB, huC, hg⟩ :=
    FlagVarieties.Foundations.TypeA.exists_upper_perm_upper_of_isUnit
      (g : Matrix (Fin n) (Fin n) K) g.isUnit
  refine ⟨w, unitOfDet B ((Matrix.isUnit_iff_isUnit_det B).mp huB),
    unitOfDet C ((Matrix.isUnit_iff_isUnit_det C).mp huC), ?_, ?_, ?_⟩
  · unfold IsBorel
    rw [coe_unitOfDet]
    exact hB
  · unfold IsBorel
    rw [coe_unitOfDet]
    exact hC
  · apply Units.ext
    rw [Units.val_mul, Units.val_mul, coe_unitOfDet, coe_unitOfDet, coe_permGL, hg]
    congr 2
    ext i c
    by_cases h : i = w c <;>
      simp [FlagVarieties.Foundations.pivotMatrix, permMat, h,
        eq_comm]

/-- On `u ẇ` with `u` upper unitriangular, the chart minors of `w` are `1`. -/
theorem evalAt_unitriangular_mul_chartMinor {u : Matrix (Fin n) (Fin n) K} (hu : IsUnitriangular u)
    (w : Equiv.Perm (Fin n)) (c : Fin n) :
    evalAt (u * permMat K w) (chartMinor K w c) = 1 := by
  rw [chartMinor, evalAt_rowMinor]
  have hsub : (u * permMat K w).submatrix (leadRows w c) (prefixIndex c) =
      (u.submatrix (flagPrefixRows w c).rows (flagPrefixRows w c).rows).submatrix
        (flagPrefixPermutation w c) (flagPrefixPermutation w c) := by
    ext a b
    simp only [Matrix.submatrix_apply, mul_permMat, leadRows,
      flagPrefixPermutation_spec]
  rw [hsub, Matrix.det_submatrix_equiv_self]
  have hup : (u.submatrix (flagPrefixRows w c).rows (flagPrefixRows w c).rows).IsUpperTriangular :=
    fun i j hij => hu.1 ((flagPrefixRows w c).rows.strictMono hij)
  rw [Matrix.det_of_isUpperTriangular hup]
  exact Finset.prod_eq_one fun i _ => hu.2 _

theorem diagPow_ne_zero {b : Matrix (Fin n) (Fin n) K} (hb : ∀ i, b i i ≠ 0) (μ : Fin n → ℕ) :
    diagPow μ b ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (hb i)

theorem evalAt_chartMinor_ne_zero_of_mem_bruhatCell {w : Equiv.Perm (Fin n)} {g : GL (Fin n) K}
    (hg : g ∈ bruhatCell K w) (c : Fin n) :
    evalAt (g : Matrix (Fin n) (Fin n) K) (chartMinor K w c) ≠ 0 := by
  obtain ⟨u, b, hu, hb, hbd, hgub⟩ := exists_unitriangular_of_mem_bruhatCell hg
  have hmem : chartMinor K w c ∈ minorSpan K (Pi.single c 1) :=
    rowMinor_mem_minorSpan c (leadRows w c)
  rw [hgub, evalAt_mul_of_mem_minorSpan hmem _ _ hb, evalAt_unitriangular_mul_chartMinor hu,
    mul_one]
  exact diagPow_ne_zero hbd _

theorem evalAt_chartPoly_ne_zero_of_mem_bruhatCell {w : Equiv.Perm (Fin n)} {g : GL (Fin n) K}
    (hg : g ∈ bruhatCell K w) : evalAt (g : Matrix (Fin n) (Fin n) K) (chartPoly K w) ≠ 0 := by
  rw [chartPoly, map_prod]
  exact Finset.prod_ne_zero_iff.mpr fun c _ => evalAt_chartMinor_ne_zero_of_mem_bruhatCell hg c

/-- **The big cells cover `GL_n(K)`.** -/
theorem exists_chartPoly_ne_zero (g : GL (Fin n) K) :
    ∃ v, evalAt (g : Matrix (Fin n) (Fin n) K) (chartPoly K v) ≠ 0 := by
  obtain ⟨w, hw⟩ := exists_mem_bruhatCell g
  exact ⟨w, evalAt_chartPoly_ne_zero_of_mem_bruhatCell hw⟩

theorem exists_chartMinor_ne_zero (g : GL (Fin n) K) :
    ∃ v, ∀ c, evalAt (g : Matrix (Fin n) (Fin n) K) (chartMinor K v c) ≠ 0 := by
  obtain ⟨w, hw⟩ := exists_mem_bruhatCell g
  exact ⟨w, evalAt_chartMinor_ne_zero_of_mem_bruhatCell hw⟩

/-- The determinant vanishes on the common zeros of the chart polynomials. -/
theorem detPoly_mem_radical [IsAlgClosed K] :
    genericDetPoly K n ∈ (Ideal.span (Set.range (chartPoly K (n := n)))).radical := by
  rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := K),
    MvPolynomial.mem_vanishingIdeal_iff]
  intro x hx
  rw [MvPolynomial.mem_zeroLocus_iff] at hx
  let g : Matrix (Fin n) (Fin n) K := Matrix.of fun i j => x (i, j)
  have hev : ∀ p : MatrixEntryPolynomial K n, MvPolynomial.aeval x p = evalAt g p := fun _ => rfl
  rw [hev, evalAt_genericDetPoly]
  by_contra hdet
  let gu : GL (Fin n) K := unitOfDet g (isUnit_iff_ne_zero.mpr hdet)
  obtain ⟨w, hw⟩ := exists_chartPoly_ne_zero gu
  apply hw
  have h0 := hx (chartPoly K w) (Ideal.subset_span ⟨w, rfl⟩)
  rw [hev] at h0
  simpa [gu] using h0

/-- **Unit ideal**: the powers `f_v^N` generate the unit ideal of `𝒪(GL_n)`. -/
theorem exists_partition_of_unity [IsAlgClosed K] (N : ℕ) :
    ∃ c : Equiv.Perm (Fin n) → GLCoord K n,
      ∑ v, c v * algebraMap (MatrixEntryPolynomial K n) (GLCoord K n) (chartPoly K v) ^ N = 1 := by
  obtain ⟨M, hN⟩ := detPoly_mem_radical (K := K) (n := n)
  let J : Ideal (GLCoord K n) :=
    Ideal.span (Set.range fun v => algebraMap (MatrixEntryPolynomial K n) (GLCoord K n)
                                     (chartPoly K v))
  have hJ : J = ⊤ := by
    have hmem : algebraMap (MatrixEntryPolynomial K n) (GLCoord K n) (genericDetPoly K n ^ M) ∈
        J := by
      have := Ideal.mem_map_of_mem (algebraMap (MatrixEntryPolynomial K n) (GLCoord K n)) hN
      rwa [Ideal.map_span, ← Set.range_comp] at this
    have hunit : IsUnit (algebraMap (MatrixEntryPolynomial K n) (GLCoord K n)
        (genericDetPoly K n ^ M)) := by
      rw [map_pow]
      exact (IsLocalization.Away.algebraMap_isUnit (genericDetPoly K n)).pow M
    exact Ideal.eq_top_of_isUnit_mem _ hmem hunit
  have hJK := Ideal.span_pow_eq_top _ hJ N
  rw [← Set.range_comp] at hJK
  have h1 : (1 : GLCoord K n) ∈ Ideal.span (Set.range ((fun x => x ^ N) ∘
      fun v => algebraMap (MatrixEntryPolynomial K n) (GLCoord K n) (chartPoly K v))) := by
    rw [hJK]
    exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp h1
  exact ⟨c, by simpa [smul_eq_mul] using hc⟩

end

end FlagVarieties.PointModel
