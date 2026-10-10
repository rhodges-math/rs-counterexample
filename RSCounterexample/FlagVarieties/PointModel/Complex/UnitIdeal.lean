import RSCounterexample.FlagVarieties.PointModel.Complex.Chart
import RSCounterexample.FlagVarieties.Foundations.TypeA.MatrixBruhatDecomposition
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# The big cells cover `GL_n`

* `exists_mem_bruhatCell`: the Bruhat decomposition `GL_n = ⋃_w B ẇ B` (from the type-A
  Bruhat decomposition of invertible matrices).
* `evalAt_chartPoly_ne_zero_of_mem_bruhatCell`: on `B ẇ B` the chart polynomial `f_w` does not
  vanish; hence every `g ∈ GL_n(ℂ)` lies in some big cell `G_v`.
* `exists_partition_of_unity` (**unit ideal**): for every `K`, there are `c_v ∈ 𝒪(GL_n)` with
  `∑_v c_v f_v^K = 1`. The proof is Hilbert's Nullstellensatz: `det` vanishes on the common zero
  locus of the `f_v`.
-/

open Schubert Demazure.FlagModule Demazure.SchubertUnions FinPermutation

namespace FlagVarieties.PointModel.Complex

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

/-- **Bruhat decomposition**: every invertible matrix lies in a Bruhat cell. -/
theorem exists_mem_bruhatCell (g : GL (Fin n) ℂ) : ∃ w, g ∈ bruhatCell w := by
  obtain ⟨B, C, w, hB, hC, huB, huC, hg⟩ :=
    FlagVarieties.Foundations.TypeA.exists_upper_perm_upper_of_isUnit
      (g : Matrix (Fin n) (Fin n) ℂ) g.isUnit
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
      simp [FlagVarieties.Foundations.pivotMatrix, rowPermutationMatrix, h,
        eq_comm]

/-- On `u ẇ` with `u` upper unitriangular, the chart minors of `w` are `1`. -/
theorem evalAt_unitriangular_mul_chartMinor {u : Matrix (Fin n) (Fin n) ℂ} (hu : IsUnitriangular u)
    (w : Equiv.Perm (Fin n)) (c : Fin n) :
    evalAt (u * rowPermutationMatrix w) (chartMinor w c) = 1 := by
  rw [chartMinor, evalAt_flagRowMinor]
  have hsub : (u * rowPermutationMatrix w).submatrix (leadRows w c) (prefixIndex c) =
      (u.submatrix (flagPrefixRows w c).rows (flagPrefixRows w c).rows).submatrix
        (flagPrefixPermutation w c) (flagPrefixPermutation w c) := by
    ext a b
    simp only [Matrix.submatrix_apply, mul_rowPermutationMatrix, leadRows,
      flagPrefixPermutation_spec]
  rw [hsub, Matrix.det_submatrix_equiv_self]
  have hup : (u.submatrix (flagPrefixRows w c).rows (flagPrefixRows w c).rows).IsUpperTriangular :=
    fun i j hij => hu.1 ((flagPrefixRows w c).rows.strictMono hij)
  rw [Matrix.det_of_isUpperTriangular hup]
  exact Finset.prod_eq_one fun i _ => hu.2 _

theorem diagPow_ne_zero {b : Matrix (Fin n) (Fin n) ℂ} (hb : ∀ i, b i i ≠ 0) (μ : Fin n → ℕ) :
    diagPow μ b ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (hb i)

theorem evalAt_chartMinor_ne_zero_of_mem_bruhatCell {w : Equiv.Perm (Fin n)} {g : GL (Fin n) ℂ}
    (hg : g ∈ bruhatCell w) (c : Fin n) :
    evalAt (g : Matrix (Fin n) (Fin n) ℂ) (chartMinor w c) ≠ 0 := by
  obtain ⟨u, b, hu, hb, hbd, hgub⟩ := exists_unitriangular_of_mem_bruhatCell hg
  have hmem : chartMinor w c ∈ minorSpan (Pi.single c 1) :=
    flagRowMinor_mem_minorSpan c (leadRows w c)
  rw [hgub, evalAt_mul_of_mem_minorSpan hmem _ _ hb, evalAt_unitriangular_mul_chartMinor hu,
    mul_one]
  exact diagPow_ne_zero hbd _

theorem evalAt_chartPoly_ne_zero_of_mem_bruhatCell {w : Equiv.Perm (Fin n)} {g : GL (Fin n) ℂ}
    (hg : g ∈ bruhatCell w) : evalAt (g : Matrix (Fin n) (Fin n) ℂ) (chartPoly w) ≠ 0 := by
  rw [chartPoly, map_prod]
  exact Finset.prod_ne_zero_iff.mpr fun c _ => evalAt_chartMinor_ne_zero_of_mem_bruhatCell hg c

/-- **The big cells cover `GL_n(ℂ)`.** -/
theorem exists_chartPoly_ne_zero (g : GL (Fin n) ℂ) :
    ∃ v, evalAt (g : Matrix (Fin n) (Fin n) ℂ) (chartPoly v) ≠ 0 := by
  obtain ⟨w, hw⟩ := exists_mem_bruhatCell g
  exact ⟨w, evalAt_chartPoly_ne_zero_of_mem_bruhatCell hw⟩

theorem exists_chartMinor_ne_zero (g : GL (Fin n) ℂ) :
    ∃ v, ∀ c, evalAt (g : Matrix (Fin n) (Fin n) ℂ) (chartMinor v c) ≠ 0 := by
  obtain ⟨w, hw⟩ := exists_mem_bruhatCell g
  exact ⟨w, evalAt_chartMinor_ne_zero_of_mem_bruhatCell hw⟩

/-- The determinant vanishes on the common zeros of the chart polynomials. -/
theorem detPoly_mem_radical :
    detPoly n ∈ (Ideal.span (Set.range (chartPoly (n := n)))).radical := by
  rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := ℂ),
    MvPolynomial.mem_vanishingIdeal_iff]
  intro x hx
  rw [MvPolynomial.mem_zeroLocus_iff] at hx
  let g : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j => x (i, j)
  have hev : ∀ p : MatrixPolynomial n, MvPolynomial.aeval x p = evalAt g p := fun _ => rfl
  rw [hev, evalAt_detPoly]
  by_contra hdet
  let gu : GL (Fin n) ℂ := unitOfDet g (isUnit_iff_ne_zero.mpr hdet)
  obtain ⟨w, hw⟩ := exists_chartPoly_ne_zero gu
  apply hw
  have h0 := hx (chartPoly w) (Ideal.subset_span ⟨w, rfl⟩)
  rw [hev] at h0
  simpa [gu] using h0

/-- **Unit ideal**: the powers `f_v^K` generate the unit ideal of `𝒪(GL_n)`. -/
theorem exists_partition_of_unity (K : ℕ) :
    ∃ c : Equiv.Perm (Fin n) → GLCoord ℂ n,
      ∑ v, c v * algebraMap (MatrixPolynomial n) (GLCoord ℂ n) (chartPoly v) ^ K = 1 := by
  obtain ⟨N, hN⟩ := detPoly_mem_radical (n := n)
  let J : Ideal (GLCoord ℂ n) :=
    Ideal.span (Set.range fun v => algebraMap (MatrixPolynomial n) (GLCoord ℂ n) (chartPoly v))
  have hJ : J = ⊤ := by
    have hmem : algebraMap (MatrixPolynomial n) (GLCoord ℂ n) (detPoly n ^ N) ∈ J := by
      have := Ideal.mem_map_of_mem (algebraMap (MatrixPolynomial n) (GLCoord ℂ n)) hN
      rwa [Ideal.map_span, ← Set.range_comp] at this
    have hunit : IsUnit (algebraMap (MatrixPolynomial n) (GLCoord ℂ n) (detPoly n ^ N)) := by
      rw [map_pow]
      exact (IsLocalization.Away.algebraMap_isUnit (detPoly n)).pow N
    exact Ideal.eq_top_of_isUnit_mem _ hmem hunit
  have hJK := Ideal.span_pow_eq_top _ hJ K
  rw [← Set.range_comp] at hJK
  have h1 : (1 : GLCoord ℂ n) ∈ Ideal.span (Set.range ((fun x => x ^ K) ∘
      fun v => algebraMap (MatrixPolynomial n) (GLCoord ℂ n) (chartPoly v))) := by
    rw [hJK]
    exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp h1
  exact ⟨c, by simpa [smul_eq_mul] using hc⟩

end

end FlagVarieties.PointModel.Complex
