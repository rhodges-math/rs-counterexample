import RSCounterexample.FlagVarieties.Schubert.SimpleSchubertSections

/-!
# Flags of points of `Pᵢ`

Matrix computations for `X_{sᵢ} ≅ ℙ¹`:

* `FlagVarieties.orbitMap_point_eq_of_blockTriangular`: two points of `GLₙ` with `g⁻¹ h ∈ B` have
  the same image in `Flₙ`;
* `blockTriangular_transvection_inv_mul`, `blockTriangular_transvection_perm_inv_mul`: a point
  `p ∈ Pᵢ(A)` lies in `(1 + τ E_{i+1,i}) B` when `τ pᵢᵢ = p_{i+1,i}`, and in
  `(1 + σ E_{i,i+1}) sᵢ B` when `σ p_{i+1,i} = pᵢᵢ`;
* `parabolicSection_proj_eq`: points of `Pᵢ` in the same coset of `B` have the same image in
  `X_{sᵢ}`; `spec_map_parabolicSection`: naturality of `parabolicSection`.
-/

noncomputable section

namespace FlagVarieties

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Foundations Foundations.QuotientCharts

universe u

variable {R : Type u} [CommRing R] {n : ℕ}

/-! ### Points of `GLₙ` with the same flag -/

theorem orbitMap_point_eq_of_blockTriangular {A : Type u} [CommRing A] [Algebra R A]
    (k k' : GLCoord R n →ₐ[R] A)
    (h : ((GLScheme.pointMatrix R n k)⁻¹ * GLScheme.pointMatrix R n k').BlockTriangular id) :
    GLScheme.point R n k ≫ FlagScheme.orbitMap R n =
      GLScheme.point R n k' ≫ FlagScheme.orbitMap R n := by
  rw [FlagScheme.orbitMap_point, FlagScheme.orbitMap_point]
  congr 1
  exact (matrixFlag_eq_iff _ _
    ((Matrix.isUnit_iff_isUnit_det _).mp (generalLinearMatrixAt_isUnit R _ n _))
    ((Matrix.isUnit_iff_isUnit_det _).mp (generalLinearMatrixAt_isUnit R _ n _))).mpr h

/-! ### Matrix computations in `Pᵢ` -/

variable (i : ℕ) (hi : i + 1 < n)

theorem permMatrix_mul_apply {A : Type*} [CommRing A] (w : Equiv.Perm (Fin n))
    (M : Matrix (Fin n) (Fin n) A) (r c : Fin n) :
    (permMatrix (A := A) n w * M) r c = M (w.symm r) c := by
  simp only [Matrix.mul_apply, permMatrix_apply]
  rw [Finset.sum_eq_single (w.symm r)]
  · simp
  · intro q _ hq
    have hne : ¬ r = w q := fun h => hq (by rw [h, Equiv.symm_apply_apply])
    rw [ite_eq_right_of_eq_false _ _ (eq_false hne)]
    simp
  · simp

theorem transvection_inv {A : Type*} [CommRing A] {a b : Fin n} (hab : a ≠ b) (x : A) :
    (Matrix.transvection a b x)⁻¹ = Matrix.transvection a b (-x) :=
  Matrix.inv_eq_left_inv (by
    rw [Matrix.transvection_mul_transvection_same a b hab, neg_add_cancel,
      Matrix.transvection_zero])

theorem transvection_mul_apply {A : Type*} [CommRing A] {a b : Fin n} (x : A)
    (M : Matrix (Fin n) (Fin n) A) (r c : Fin n) :
    (Matrix.transvection a b x * M) r c = M r c + (if r = a then x * M b c else 0) := by
  rw [Matrix.transvection, add_mul, one_mul, Matrix.add_apply]
  split_ifs with hr
  · rw [hr, Matrix.single_mul_apply_same]
  · rw [Matrix.single_mul_apply_of_ne _ _ _ _ _ hr, add_zero]

/-- **`p ∈ (1 + τ E_{i+1,i}) B`** when `τ pᵢᵢ = p_{i+1,i}`. -/
theorem blockTriangular_transvection_inv_mul {A : Type*} [CommRing A]
    (P : Matrix (Fin n) (Fin n) A) (hP : P.BlockTriangular (parabolicBlock n i)) (τ : A)
    (hτ : τ * P (rowA n i hi) (rowA n i hi) = P (rowB n i hi) (rowA n i hi)) :
    ((Matrix.transvection (rowB n i hi) (rowA n i hi) τ)⁻¹ * P).BlockTriangular id := by
  rw [transvection_inv (rowA_ne_rowB n i hi).symm]
  intro r c hrc
  rw [transvection_mul_apply]
  have hrc' : c.val < r.val := hrc
  have hA : (rowA n i hi).val = i := rfl
  have hB : (rowB n i hi).val = i + 1 := rfl
  have hz : ∀ r' c' : Fin n, c'.val < r'.val → ¬(r'.val = i + 1 ∧ c'.val = i) → P r' c' = 0 :=
    fun r' c' h1 h2 => hP ((parabolicBlock_lt_iff i r' c').mpr ⟨h1, h2⟩)
  by_cases hr : r = rowB n i hi
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hr), hr]
    have hr' : r.val = i + 1 := by rw [hr]
    by_cases hc : c.val = i
    · have hc' : c = rowA n i hi := Fin.ext hc
      rw [hc', ← hτ]
      ring
    · rw [hz _ c (by omega) (by omega), hz _ c (by omega) (by omega)]
      ring
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hr), add_zero]
    have hr' : r.val ≠ i + 1 := fun h => hr (Fin.ext h)
    exact hz r c hrc' (by omega)

/-- **`p ∈ (1 + σ E_{i,i+1}) sᵢ B`** when `σ p_{i+1,i} = pᵢᵢ`. -/
theorem blockTriangular_transvection_perm_inv_mul {A : Type*} [CommRing A]
    (P : Matrix (Fin n) (Fin n) A) (hP : P.BlockTriangular (parabolicBlock n i)) (σ : A)
    (hσ : σ * P (rowB n i hi) (rowA n i hi) = P (rowA n i hi) (rowA n i hi)) :
    ((Matrix.transvection (rowA n i hi) (rowB n i hi) σ *
      permMatrix n (simpleReflection n i hi))⁻¹ * P).BlockTriangular id := by
  have hw : (permMatrix (A := A) n (simpleReflection n i hi))⁻¹ =
      permMatrix n (simpleReflection n i hi) :=
    Matrix.inv_eq_left_inv (permMatrix_simpleReflection_mul_self n i hi)
  rw [Matrix.mul_inv_rev, hw, transvection_inv (rowA_ne_rowB n i hi), Matrix.mul_assoc]
  intro r c hrc
  rw [permMatrix_mul_apply, transvection_mul_apply]
  have hrc' : c.val < r.val := hrc
  have hA : (rowA n i hi).val = i := rfl
  have hB : (rowB n i hi).val = i + 1 := rfl
  have hz : ∀ r' c' : Fin n, c'.val < r'.val → ¬(r'.val = i + 1 ∧ c'.val = i) → P r' c' = 0 :=
    fun r' c' h1 h2 => hP ((parabolicBlock_lt_iff i r' c').mpr ⟨h1, h2⟩)
  have hsymm : (simpleReflection n i hi).symm = simpleReflection n i hi := Equiv.symm_swap _ _
  rw [hsymm]
  by_cases hra : r = rowA n i hi
  · rw [hra, simpleReflection, Equiv.swap_apply_left,
      ite_eq_right_of_eq_false _ _ (eq_false (rowA_ne_rowB n i hi).symm), add_zero]
    have hc : c.val < i := by rw [hra] at hrc'; exact hrc'
    exact hz _ c (by simp only at *; omega) (by omega)
  · by_cases hrb : r = rowB n i hi
    · rw [hrb, simpleReflection, Equiv.swap_apply_right,
        ite_eq_left_of_eq_true _ _ (eq_self _)]
      have hc : c.val ≤ i := by rw [hrb] at hrc'; simp at hrc'; omega
      by_cases hci : c.val = i
      · have hc' : c = rowA n i hi := Fin.ext hci
        rw [hc', ← hσ]
        ring
      · rw [hz _ c (by simp only at *; omega) (by omega), hz _ c (by omega) (by omega)]
        ring
    · rw [simpleReflection, Equiv.swap_apply_of_ne_of_ne hra hrb,
        ite_eq_right_of_eq_false _ _ (eq_false hra), add_zero]
      have h1 : r.val ≠ i := fun h => hra (Fin.ext h)
      have h2 : r.val ≠ i + 1 := fun h => hrb (Fin.ext h)
      exact hz r c hrc' (by omega)

/-! ### Points of `Pᵢ` and their images in `X_{sᵢ}` -/

variable {i hi}

theorem spec_map_parabolicSection {A B : Type u} [CommRing A] [Algebra R A] [CommRing B]
    [Algebra R B] (φ : A →ₐ[R] B) (g : Matrix (Fin n) (Fin n) A) (hg : IsUnit g.det)
    (hb : g.BlockTriangular (parabolicBlock n i)) :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ parabolicSection (R := R) (hi := hi) g hg hb =
      parabolicSection (R := R) (hi := hi) (g.map φ) (isUnit_det_map_algHom (R := R) φ hg)
        (fun r c h => by simp [Matrix.map_apply, hb h]) := by
  unfold parabolicSection
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 3
  apply Ideal.Quotient.ringHom_ext
  have h : φ.comp (glPointOfMatrix R g hg) =
      glPointOfMatrix R (g.map φ) (isUnit_det_map_algHom (R := R) φ hg) := by
    apply glCoord_algHom_ext R
    rw [pointMatrix_comp, pointMatrix_glPointOfMatrix, pointMatrix_glPointOfMatrix]
  exact congrArg AlgHom.toRingHom h

/-- **Points of `Pᵢ` in the same coset of `B` have the same image in `X_{sᵢ}`.** -/
theorem parabolicSection_proj_eq {A : Type u} [CommRing A] [Algebra R A]
    (g h : Matrix (Fin n) (Fin n) A) (hg : IsUnit g.det) (hh : IsUnit h.det)
    (hbg : g.BlockTriangular (parabolicBlock n i)) (hbh : h.BlockTriangular (parabolicBlock n i))
    (hflag : (g⁻¹ * h).BlockTriangular id) :
    parabolicSection (R := R) (hi := hi) g hg hbg ≫ preimageProj R n _ =
      parabolicSection (R := R) (hi := hi) h hh hbh ≫ preimageProj R n _ := by
  rw [← cancel_mono (simpleSchubert R n i hi).subschemeι, Category.assoc, Category.assoc,
    ← pullback.condition, parabolicSection_ι_assoc, parabolicSection_ι_assoc]
  apply orbitMap_point_eq_of_blockTriangular
  rw [pointMatrix_glPointOfMatrix, pointMatrix_glPointOfMatrix]
  exact hflag

end FlagVarieties
