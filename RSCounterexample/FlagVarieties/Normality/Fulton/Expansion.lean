import RSCounterexample.FlagVarieties.PointModel.BorelWeil
import RSCounterexample.FlagVarieties.PointModel.UnitIdeal
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Chart descent in `𝒪(GL_n)`

Tools for the scheme-theoretic results of `Normality/Fulton`.

* `shapeExpand bl r`: `r(x · p)` for a generic block-upper-triangular matrix `p` (blocks given by
  `bl : Fin n → ℕ`), as a polynomial in the entries of `p` with coefficients in `K[x_ij]`. If `r`
  vanishes on a set `Z` stable under right multiplication by such invertible `p`, so do all its
  coefficients (`coeff_shapeExpand_eq_zero`).
* `IsRegularOn D ψ` and `IsGoodOn D 𝔟 ψ`: a function `ψ` on `GL_n(K)` agrees, where `D ≠ 0`, with
  `Q / D^M` for some polynomial `Q`, resp. for some `Q` in the ideal `𝔟`.
* `exists_partition_of_unity_of_cover`: polynomials without common zero on `GL_n(K)` generate the
  unit ideal of `𝒪(GL_n)` (Nullstellensatz).
* `isGoodOn_of_chart`: on a chart `g = L(g) p(g)` with `p(g)` block-upper-triangular and regular,
  a polynomial vanishing on `Z` is good as soon as polynomials vanishing on `Z` are good at `L(g)`;
  `algebraMap_mem_of_isGoodOn`: good on a cover implies membership in the extended ideal.
-/

open Schubert Demazure.FlagModule Demazure.SchubertUnions FinPermutation
open GLRep (glEval)

namespace FlagVarieties.PointModel

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {K : Type*} [Field K] {n : ℕ}

/-! ### Expansion along block-upper-triangular matrices -/

/-- The block-upper-triangular part of an assignment `y`, for the blocks `bl`. -/
def shapePart (bl : Fin n → ℕ) (y : Fin n × Fin n → K) : Matrix (Fin n) (Fin n) K :=
  fun k j => if bl j < bl k then 0 else y (k, j)

theorem shapePart_blockTriangular (bl : Fin n → ℕ) (y : Fin n × Fin n → K) :
    (shapePart bl y).BlockTriangular bl := by
  intro k j hjk
  simp [shapePart, hjk]

theorem shapePart_of_blockTriangular {bl : Fin n → ℕ} {p : Matrix (Fin n) (Fin n) K}
    (hp : p.BlockTriangular bl) : shapePart bl (fun ij => p ij.1 ij.2) = p := by
  ext k j
  simp only [shapePart]
  split_ifs with h
  · exact (hp h).symm
  · rfl

/-- The generic block-upper-triangular entry `p_kj`. -/
def shapeVar (bl : Fin n → ℕ) (k j : Fin n) : MvPolynomial (Fin n × Fin n)
    (MatrixEntryPolynomial K n) :=
  if bl j < bl k then 0 else MvPolynomial.X (k, j)

/-- `r(x · p)`, as a polynomial in the entries of a block-upper-triangular `p`, with coefficients in
`K[x_ij]`. -/
def shapeExpand (bl : Fin n → ℕ) (r : MatrixEntryPolynomial K n) : MvPolynomial (Fin n × Fin n)
    (MatrixEntryPolynomial K n) :=
  MvPolynomial.aeval (fun ij : Fin n × Fin n =>
    ∑ k, MvPolynomial.C (MvPolynomial.X (ij.1, k)) * shapeVar bl k ij.2) r

theorem eval_map_shapeExpand (bl : Fin n → ℕ) (X : Matrix (Fin n) (Fin n) K)
    (y : Fin n × Fin n → K) (r : MatrixEntryPolynomial K n) :
    MvPolynomial.eval y (MvPolynomial.map (evalAt X).toRingHom (shapeExpand bl r)) =
      evalAt (X * shapePart bl y) r := by
  induction r using MvPolynomial.induction_on with
  | C a => simp [shapeExpand, evalAt]
  | add p q hp hq => rw [shapeExpand, map_add, ← shapeExpand, ← shapeExpand, map_add, map_add, hp,
      hq, map_add]
  | mul_X p ij hp =>
    rw [shapeExpand, map_mul, ← shapeExpand, map_mul, map_mul, hp, map_mul, evalAt_X,
      MvPolynomial.aeval_X, Matrix.mul_apply, map_sum, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [shapeVar, shapePart, map_mul, MvPolynomial.map_C, MvPolynomial.eval_C]
    split_ifs <;> simp [evalAt]

/-- The determinant of the generic block-upper-triangular matrix. -/
def shapeDet (K : Type*) [Field K] (bl : Fin n → ℕ) : MvPolynomial (Fin n × Fin n) K :=
  (Matrix.of fun k j : Fin n =>
    if bl j < bl k then (0 : MvPolynomial (Fin n × Fin n) K) else MvPolynomial.X (k, j)).det

theorem eval_shapeDet (bl : Fin n → ℕ) (y : Fin n × Fin n → K) :
    MvPolynomial.eval y (shapeDet K bl) = (shapePart bl y).det := by
  rw [shapeDet, RingHom.map_det]
  congr 1
  ext k j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, shapePart]
  split_ifs <;> simp

theorem shapeDet_ne_zero (bl : Fin n → ℕ) : shapeDet K bl ≠ 0 := by
  classical
  intro h
  have h1 := eval_shapeDet (K := K) bl (fun ij => if ij.1 = ij.2 then 1 else 0)
  have hone : shapePart bl (fun ij : Fin n × Fin n => if ij.1 = ij.2 then (1 : K) else 0) = 1 := by
    ext k j
    by_cases hkj : k = j
    · subst hkj
      simp [shapePart]
    · simp [shapePart, hkj, Matrix.one_apply_ne hkj]
  rw [h, map_zero, hone, Matrix.det_one] at h1
  exact zero_ne_one h1

/-- **The coefficients of the expansion vanish on `Z`** if `r` does and `Z` is stable under right
multiplication by invertible block-upper-triangular matrices. -/
theorem coeff_shapeExpand_eq_zero [Infinite K] (bl : Fin n → ℕ) {Z : Set (GL (Fin n) K)}
    (hZ : ∀ g ∈ Z, ∀ p : GL (Fin n) K, (p : Matrix (Fin n) (Fin n) K).BlockTriangular bl →
      g * p ∈ Z)
    {r : MatrixEntryPolynomial K n} (hr : ∀ g ∈ Z, evalAt (g : Matrix (Fin n) (Fin n) K) r = 0)
    (α : (Fin n × Fin n) →₀ ℕ) {g : GL (Fin n) K} (hg : g ∈ Z) :
    evalAt (g : Matrix (Fin n) (Fin n) K) ((shapeExpand bl r).coeff α) = 0 := by
  have hq : MvPolynomial.map (evalAt (g : Matrix (Fin n) (Fin n) K)).toRingHom (shapeExpand bl r) *
      shapeDet K bl = 0 := by
    apply MvPolynomial.funext
    intro y
    rw [map_mul, map_zero, eval_shapeDet]
    by_cases hd : (shapePart bl y).det = 0
    · rw [hd, mul_zero]
    · have hp : IsUnit (shapePart bl y).det := isUnit_iff_ne_zero.mpr hd
      have h1 := hr _ (hZ g hg (unitOfDet _ hp)
        (by rw [coe_unitOfDet]; exact shapePart_blockTriangular bl y))
      rw [Units.val_mul, coe_unitOfDet] at h1
      rw [eval_map_shapeExpand, h1, zero_mul]
  have hq0 := (mul_eq_zero.mp hq).resolve_right (shapeDet_ne_zero bl)
  have := congrArg (fun q : MvPolynomial (Fin n × Fin n) K => q.coeff α) hq0
  simpa [MvPolynomial.coeff_map] using this

/-! ### Regular and good functions on a chart -/

/-- `ψ` agrees, where `D ≠ 0`, with `Q / D^M` for a polynomial `Q`. -/
def IsRegularOn (D : MatrixEntryPolynomial K n) (ψ : GL (Fin n) K → K) : Prop :=
  ∃ (M : ℕ) (Q : MatrixEntryPolynomial K n), ∀ g : GL (Fin n) K,
    evalAt (g : Matrix (Fin n) (Fin n) K) D ≠ 0 →
      evalAt (g : Matrix (Fin n) (Fin n) K) Q = evalAt (g : Matrix (Fin n) (Fin n) K) D ^ M * ψ g

/-- `ψ` agrees, where `D ≠ 0`, with `x / D^M` for some `x` in the ideal `𝔟`. -/
def IsGoodOn (D : MatrixEntryPolynomial K n) (𝔟 : Ideal (MatrixEntryPolynomial K n))
    (ψ : GL (Fin n) K → K) : Prop :=
  ∃ (M : ℕ), ∃ x ∈ 𝔟, ∀ g : GL (Fin n) K,
    evalAt (g : Matrix (Fin n) (Fin n) K) D ≠ 0 →
      evalAt (g : Matrix (Fin n) (Fin n) K) x = evalAt (g : Matrix (Fin n) (Fin n) K) D ^ M * ψ g

section Regular

variable {D : MatrixEntryPolynomial K n}

theorem IsRegularOn.congr {ψ φ : GL (Fin n) K → K} (h : IsRegularOn D ψ)
    (hψφ : ∀ g : GL (Fin n) K, evalAt (g : Matrix (Fin n) (Fin n) K) D ≠ 0 → ψ g = φ g) :
    IsRegularOn D φ := by
  obtain ⟨M, Q, hQ⟩ := h
  exact ⟨M, Q, fun g hg => by rw [hQ g hg, hψφ g hg]⟩

theorem isRegularOn_poly (P : MatrixEntryPolynomial K n) :
    IsRegularOn D fun g => evalAt (g : Matrix (Fin n) (Fin n) K) P :=
  ⟨0, P, fun g _ => by rw [pow_zero, one_mul]⟩

theorem isRegularOn_const (c : K) : IsRegularOn D fun _ => c :=
  ⟨0, MvPolynomial.C c, fun g _ => by simp [evalAt]⟩

theorem IsRegularOn.add {ψ φ : GL (Fin n) K → K} (hψ : IsRegularOn D ψ) (hφ : IsRegularOn D φ) :
    IsRegularOn D fun g => ψ g + φ g := by
  obtain ⟨M₁, Q₁, h₁⟩ := hψ
  obtain ⟨M₂, Q₂, h₂⟩ := hφ
  refine ⟨M₁ + M₂, Q₁ * D ^ M₂ + Q₂ * D ^ M₁, fun g hg => ?_⟩
  rw [map_add, map_mul, map_mul, map_pow, map_pow, h₁ g hg, h₂ g hg]
  ring

theorem IsRegularOn.mul {ψ φ : GL (Fin n) K → K} (hψ : IsRegularOn D ψ) (hφ : IsRegularOn D φ) :
    IsRegularOn D fun g => ψ g * φ g := by
  obtain ⟨M₁, Q₁, h₁⟩ := hψ
  obtain ⟨M₂, Q₂, h₂⟩ := hφ
  refine ⟨M₁ + M₂, Q₁ * Q₂, fun g hg => ?_⟩
  rw [map_mul, h₁ g hg, h₂ g hg]
  ring

theorem IsRegularOn.sub {ψ φ : GL (Fin n) K → K} (hψ : IsRegularOn D ψ) (hφ : IsRegularOn D φ) :
    IsRegularOn D fun g => ψ g - φ g :=
  (hψ.add ((isRegularOn_const (-1)).mul hφ)).congr fun g _ => by ring

theorem IsRegularOn.pow {ψ : GL (Fin n) K → K} (hψ : IsRegularOn D ψ) (e : ℕ) :
    IsRegularOn D fun g => ψ g ^ e := by
  induction e with
  | zero => simpa using isRegularOn_const (D := D) (1 : K)
  | succ e ih => simpa [pow_succ] using ih.mul hψ

theorem IsRegularOn.sum {ι : Type*} (s : Finset ι) (ψ : ι → GL (Fin n) K → K)
    (h : ∀ i ∈ s, IsRegularOn D (ψ i)) : IsRegularOn D fun g => ∑ i ∈ s, ψ i g := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isRegularOn_const (D := D) (0 : K)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem IsRegularOn.prod {ι : Type*} (s : Finset ι) (ψ : ι → GL (Fin n) K → K)
    (h : ∀ i ∈ s, IsRegularOn D (ψ i)) : IsRegularOn D fun g => ∏ i ∈ s, ψ i g := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isRegularOn_const (D := D) (1 : K)
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end Regular

section Good

variable {D : MatrixEntryPolynomial K n} {𝔟 : Ideal (MatrixEntryPolynomial K n)}

theorem IsGoodOn.congr {ψ φ : GL (Fin n) K → K} (h : IsGoodOn D 𝔟 ψ)
    (hψφ : ∀ g : GL (Fin n) K, evalAt (g : Matrix (Fin n) (Fin n) K) D ≠ 0 → ψ g = φ g) :
    IsGoodOn D 𝔟 φ := by
  obtain ⟨M, x, hx, hxe⟩ := h
  exact ⟨M, x, hx, fun g hg => by rw [hxe g hg, hψφ g hg]⟩

theorem isGoodOn_zero : IsGoodOn D 𝔟 fun _ => 0 :=
  ⟨0, 0, Submodule.zero_mem _, fun g _ => by simp⟩

theorem IsGoodOn.add {ψ φ : GL (Fin n) K → K} (hψ : IsGoodOn D 𝔟 ψ) (hφ : IsGoodOn D 𝔟 φ) :
    IsGoodOn D 𝔟 fun g => ψ g + φ g := by
  obtain ⟨M₁, x₁, hx₁, h₁⟩ := hψ
  obtain ⟨M₂, x₂, hx₂, h₂⟩ := hφ
  refine ⟨M₁ + M₂, x₁ * D ^ M₂ + x₂ * D ^ M₁,
    Submodule.add_mem _ (Ideal.mul_mem_right _ _ hx₁) (Ideal.mul_mem_right _ _ hx₂), fun g hg => ?_⟩
  rw [map_add, map_mul, map_mul, map_pow, map_pow, h₁ g hg, h₂ g hg]
  ring

theorem IsGoodOn.mul {ψ φ : GL (Fin n) K → K} (hψ : IsGoodOn D 𝔟 ψ) (hφ : IsRegularOn D φ) :
    IsGoodOn D 𝔟 fun g => ψ g * φ g := by
  obtain ⟨M₁, x, hx, h₁⟩ := hψ
  obtain ⟨M₂, Q, h₂⟩ := hφ
  refine ⟨M₁ + M₂, x * Q, Ideal.mul_mem_right _ _ hx, fun g hg => ?_⟩
  rw [map_mul, h₁ g hg, h₂ g hg]
  ring

theorem IsGoodOn.sum {ι : Type*} (s : Finset ι) (ψ : ι → GL (Fin n) K → K)
    (h : ∀ i ∈ s, IsGoodOn D 𝔟 (ψ i)) : IsGoodOn D 𝔟 fun g => ∑ i ∈ s, ψ i g := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isGoodOn_zero (D := D) (𝔟 := 𝔟)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- A good polynomial function: some `D^M r` lies in the extended ideal. -/
theorem IsGoodOn.exists_algebraMap_mem [Infinite K] {r : MatrixEntryPolynomial K n}
    (h : IsGoodOn D 𝔟 fun g => evalAt (g : Matrix (Fin n) (Fin n) K) r) :
    ∃ M : ℕ, algebraMap (MatrixEntryPolynomial K n) (GLCoord K n) (D ^ M * r) ∈
      𝔟.map (algebraMap (MatrixEntryPolynomial K n) (GLCoord K n)) := by
  obtain ⟨M, x, hx, hxe⟩ := h
  refine ⟨M + 1, ?_⟩
  have heq : algebraMap (MatrixEntryPolynomial K n) (GLCoord K n) (D ^ (M + 1) * r) =
      algebraMap (MatrixEntryPolynomial K n) (GLCoord K n) (D * x) := by
    rw [← sub_eq_zero, ← map_sub]
    apply eq_zero_of_glEval_eq_zero
    intro g
    rw [glEval_algebraMap_eq_evalAt, map_sub, map_mul, map_mul, map_pow]
    by_cases hD : evalAt (g : Matrix (Fin n) (Fin n) K) D = 0
    · simp [hD]
    · rw [hxe g hD]
      ring
  rw [heq]
  exact Ideal.mem_map_of_mem _ (Ideal.mul_mem_left _ _ hx)

end Good

/-! ### Clearing the determinant -/

theorem evalAt_eq_zero_of_mul_det_pow {t : GLCoord K n} {r : MatrixEntryPolynomial K n} {e : ℕ}
    (hre : t * algebraMap (MatrixEntryPolynomial K n) (GLCoord K n) (genericDetPoly K n ^ e) =
      algebraMap (MatrixEntryPolynomial K n) (GLCoord K n) r)
    {g : GL (Fin n) K} (hg : glEval g t = 0) : evalAt (g : Matrix (Fin n) (Fin n) K) r = 0 := by
  have := congrArg (glEval g) hre
  rw [map_mul, glEval_algebraMap_eq_evalAt, glEval_algebraMap_eq_evalAt, hg, zero_mul] at this
  exact this.symm

theorem mem_of_mul_det_pow {𝔞 : Ideal (GLCoord K n)} {t : GLCoord K n}
    {r : MatrixEntryPolynomial K n}
    {e : ℕ}
    (hre : t * algebraMap (MatrixEntryPolynomial K n) (GLCoord K n) (genericDetPoly K n ^ e) =
      algebraMap (MatrixEntryPolynomial K n) (GLCoord K n) r)
    (hr : algebraMap (MatrixEntryPolynomial K n) (GLCoord K n) r ∈ 𝔞) : t ∈ 𝔞 := by
  have hu : IsUnit (algebraMap (MatrixEntryPolynomial K n) (GLCoord K n)
      (genericDetPoly K n ^ e)) := by
    rw [map_pow]
    exact (IsLocalization.Away.algebraMap_isUnit (genericDetPoly K n)).pow e
  have ht : t = algebraMap (MatrixEntryPolynomial K n) (GLCoord K n) r * ↑hu.unit⁻¹ := by
    rw [← hre, mul_assoc, IsUnit.mul_val_inv, mul_one]
  rw [ht]
  exact Ideal.mul_mem_right _ _ hr

/-! ### Partitions of unity -/

/-- **Polynomials without common zero on `GL_n(K)` generate the unit ideal of `𝒪(GL_n)`**, also
after raising them to any power `N`. -/
theorem exists_partition_of_unity_of_cover [IsAlgClosed K] {ι : Type*} [Fintype ι]
    (D : ι → MatrixEntryPolynomial K n)
    (hD : ∀ g : GL (Fin n) K, ∃ i, evalAt (g : Matrix (Fin n) (Fin n) K) (D i) ≠ 0) (N : ℕ) :
    ∃ c : ι → GLCoord K n,
      ∑ i, c i * algebraMap (MatrixEntryPolynomial K n) (GLCoord K n) (D i) ^ N = 1 := by
  have hrad : genericDetPoly K n ∈ (Ideal.span (Set.range D)).radical := by
    rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := K),
      MvPolynomial.mem_vanishingIdeal_iff]
    intro x hx
    rw [MvPolynomial.mem_zeroLocus_iff] at hx
    let g : Matrix (Fin n) (Fin n) K := Matrix.of fun i j => x (i, j)
    have hev : ∀ p : MatrixEntryPolynomial K n, MvPolynomial.aeval x p = evalAt g p := fun _ => rfl
    rw [hev, evalAt_genericDetPoly]
    by_contra hdet
    let gu : GL (Fin n) K := unitOfDet g (isUnit_iff_ne_zero.mpr hdet)
    obtain ⟨i, hi⟩ := hD gu
    apply hi
    have h0 := hx (D i) (Ideal.subset_span ⟨i, rfl⟩)
    rw [hev] at h0
    simpa [gu] using h0
  obtain ⟨M, hM⟩ := hrad
  let J : Ideal (GLCoord K n) :=
    Ideal.span (Set.range fun i => algebraMap (MatrixEntryPolynomial K n) (GLCoord K n) (D i))
  have hJ : J = ⊤ := by
    have hmem : algebraMap (MatrixEntryPolynomial K n) (GLCoord K n) (genericDetPoly K n ^ M) ∈
        J := by
      have := Ideal.mem_map_of_mem (algebraMap (MatrixEntryPolynomial K n) (GLCoord K n)) hM
      rwa [Ideal.map_span, ← Set.range_comp] at this
    have hunit : IsUnit (algebraMap (MatrixEntryPolynomial K n) (GLCoord K n)
        (genericDetPoly K n ^ M)) := by
      rw [map_pow]
      exact (IsLocalization.Away.algebraMap_isUnit (genericDetPoly K n)).pow M
    exact Ideal.eq_top_of_isUnit_mem _ hmem hunit
  have hJK := Ideal.span_pow_eq_top _ hJ N
  rw [← Set.range_comp] at hJK
  have h1 : (1 : GLCoord K n) ∈ Ideal.span (Set.range ((fun x => x ^ N) ∘
      fun i => algebraMap (MatrixEntryPolynomial K n) (GLCoord K n) (D i))) := by
    rw [hJK]
    exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp h1
  exact ⟨c, by simpa [smul_eq_mul] using hc⟩

/-- **Descent along a cover**: if `r` is good on every chart of a cover, then `r` lies in the
ideal of `𝒪(GL_n)` generated by `𝔟`. -/
theorem algebraMap_mem_of_isGoodOn [IsAlgClosed K] {ι : Type*} [Fintype ι]
    (D : ι → MatrixEntryPolynomial K n)
    (hD : ∀ g : GL (Fin n) K, ∃ i, evalAt (g : Matrix (Fin n) (Fin n) K) (D i) ≠ 0)
    {𝔟 : Ideal (MatrixEntryPolynomial K n)} {r : MatrixEntryPolynomial K n}
    (h : ∀ i, IsGoodOn (D i) 𝔟 fun g => evalAt (g : Matrix (Fin n) (Fin n) K) r) :
    algebraMap (MatrixEntryPolynomial K n) (GLCoord K n) r ∈
      𝔟.map (algebraMap (MatrixEntryPolynomial K n) (GLCoord K n)) := by
  classical
  choose M hM using fun i => (h i).exists_algebraMap_mem
  let N := Finset.univ.sup M
  obtain ⟨c, hc⟩ := exists_partition_of_unity_of_cover D hD N
  have hNi : ∀ i, algebraMap (MatrixEntryPolynomial K n) (GLCoord K n) (D i ^ N * r) ∈
      𝔟.map (algebraMap (MatrixEntryPolynomial K n) (GLCoord K n)) := by
    intro i
    have hle : M i ≤ N := Finset.le_sup (Finset.mem_univ i)
    rw [← Nat.sub_add_cancel hle, pow_add, mul_assoc, map_mul]
    exact Ideal.mul_mem_left _ _ (hM i)
  have hr : algebraMap (MatrixEntryPolynomial K n) (GLCoord K n) r =
      ∑ i, c i * algebraMap (MatrixEntryPolynomial K n) (GLCoord K n) (D i ^ N * r) := by
    simp only [map_mul, map_pow, ← mul_assoc, ← Finset.sum_mul, hc, one_mul]
  rw [hr]
  exact Submodule.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (hNi i)

/-! ### The chart lemma -/

/-- **Chart lemma.** Let `Z` be stable under right multiplication by invertible
block-upper-triangular matrices, and `r` vanish on `Z`. Suppose that where `D ≠ 0`,
`g = L(g) p(g)` with `p(g)` block-upper-triangular with regular entries, and that every polynomial
vanishing on `Z` is good at `L(g)`. Then `r` is good. -/
theorem isGoodOn_of_chart [Infinite K] (bl : Fin n → ℕ) {Z : Set (GL (Fin n) K)}
    (hZ : ∀ g ∈ Z, ∀ p : GL (Fin n) K, (p : Matrix (Fin n) (Fin n) K).BlockTriangular bl →
      g * p ∈ Z)
    {r : MatrixEntryPolynomial K n} (hr : ∀ g ∈ Z, evalAt (g : Matrix (Fin n) (Fin n) K) r = 0)
    (D : MatrixEntryPolynomial K n) (𝔟 : Ideal (MatrixEntryPolynomial K n))
        (L p : GL (Fin n) K → Matrix (Fin n) (Fin n) K)
    (hLp : ∀ g : GL (Fin n) K, evalAt (g : Matrix (Fin n) (Fin n) K) D ≠ 0 →
      (g : Matrix (Fin n) (Fin n) K) = L g * p g ∧ (p g).BlockTriangular bl)
    (hp : ∀ i j, IsRegularOn D fun g => p g i j)
    (hL : ∀ P : MatrixEntryPolynomial K n, (∀ g ∈ Z, evalAt (g : Matrix (Fin n) (Fin n) K) P = 0) →
      IsGoodOn D 𝔟 fun g => evalAt (L g) P) :
    IsGoodOn D 𝔟 fun g => evalAt (g : Matrix (Fin n) (Fin n) K) r := by
  classical
  have hsum : IsGoodOn D 𝔟 fun g => ∑ α ∈ (shapeExpand bl r).support,
      evalAt (L g) ((shapeExpand bl r).coeff α) * ∏ ij ∈ α.support, p g ij.1 ij.2 ^ α ij :=
    IsGoodOn.sum _ _ fun α _ =>
      (hL _ fun g hg => coeff_shapeExpand_eq_zero bl hZ hr α hg).mul
        (IsRegularOn.prod _ _ fun ij _ => (hp ij.1 ij.2).pow _)
  refine hsum.congr fun g hg => ?_
  obtain ⟨hgLp, hpt⟩ := hLp g hg
  have key : evalAt (L g * p g) r = ∑ α ∈ (shapeExpand bl r).support,
      evalAt (L g) ((shapeExpand bl r).coeff α) * ∏ ij ∈ α.support, p g ij.1 ij.2 ^ α ij := by
    conv_lhs => rw [← shapePart_of_blockTriangular hpt]
    rw [← eval_map_shapeExpand, MvPolynomial.eval_map, MvPolynomial.eval₂_eq]
    rfl
  rw [hgLp, key]

end

end FlagVarieties.PointModel
