import Schubert.FlagVarieties.PointModel.Complex.MinorSpan

/-!
# Flag minors at points of `GL_n(ℂ)`

* `evalAt_mul_flagRowMinor`: for `b` upper triangular,
  `Δ_s(g b) = Δ_s(g) · ∏_{i ≤ k} b_ii` for a flag minor of height `k` with rows `s`.
* `evalAt_mul_of_mem_minorSpan`: hence every element of the flag-minor algebra `A_m` is
  semi-invariant of weight `λ = shapeWeight m` under right translation by `B`.
* `evalAt_eq_zero_iff_unionRestriction`: an element of `A_m` vanishes on `orbitSet S` exactly when
  its restriction to the union of orbits `U · ẇ` (`w ∈ S`) in the Demazure library vanishes. This
  identifies the kernel `I_S^A` of the Demazure library with the pointwise vanishing ideal.
-/

open Schubert Demazure.FlagModule Demazure.SchubertUnions

namespace FlagVarieties.PointModel.Complex

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

theorem evalAt_flagRowMinor (g : Matrix (Fin n) (Fin n) ℂ) (k : Fin n)
    (s : Fin (k.val + 1) → Fin n) :
    evalAt g (flagRowMinor k s) = (g.submatrix s (prefixIndex k)).det := by
  rw [flagRowMinor, AlgHom.map_det]
  congr 1
  ext i j
  simp [Matrix.submatrix_apply]

/-- The `(k+1) × (k+1)` leading block of an upper-triangular matrix splits off a product of the
first `k+1` columns. -/
theorem submatrix_mul_upper (g b : Matrix (Fin n) (Fin n) ℂ) (hb : b.IsUpperTriangular)
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

theorem prod_diag_prefixIndex (b : Matrix (Fin n) (Fin n) ℂ) (k : Fin n) :
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

/-- **Right translation by an upper-triangular matrix** multiplies a flag minor of height `k` by
the product of the first `k + 1` diagonal entries. -/
theorem evalAt_mul_flagRowMinor (g b : Matrix (Fin n) (Fin n) ℂ) (hb : b.IsUpperTriangular)
    (k : Fin n) (s : Fin (k.val + 1) → Fin n) :
    evalAt (g * b) (flagRowMinor k s) =
      (∏ i : Fin n, b i i ^ (if i ≤ k then 1 else 0)) * evalAt g (flagRowMinor k s) := by
  have hbu : (b.submatrix (prefixIndex k) (prefixIndex k)).IsUpperTriangular := fun i j hij =>
    hb (show prefixIndex k j < prefixIndex k i from by
      change (prefixIndex k j).val < (prefixIndex k i).val
      simpa only [prefixIndex, id_eq, Fin.lt_def] using hij)
  rw [evalAt_flagRowMinor, evalAt_flagRowMinor, submatrix_mul_upper g b hb, Matrix.det_mul,
    Matrix.det_of_isUpperTriangular hbu]
  simp only [Matrix.submatrix_apply]
  rw [prod_diag_prefixIndex, mul_comm]

/-- The diagonal character `∏ᵢ b_ii^{μᵢ}` for a natural exponent vector. -/
def diagPow (μ : Fin n → ℕ) (b : Matrix (Fin n) (Fin n) ℂ) : ℂ := ∏ i, b i i ^ μ i

theorem diagPow_add (μ ν : Fin n → ℕ) (b : Matrix (Fin n) (Fin n) ℂ) :
    diagPow (μ + ν) b = diagPow μ b * diagPow ν b := by
  simp only [diagPow, Pi.add_apply, pow_add, Finset.prod_mul_distrib]

theorem borelCharValue_shapeWeightZ (m : ColumnShape n) (b : Matrix (Fin n) (Fin n) ℂ) :
    borelCharValue (shapeWeightZ m) b = diagPow (shapeWeight m) b := by
  simp only [borelCharValue, shapeWeightZ, diagPow, zpow_natCast]

theorem _root_.FlagVarieties.PointModel.shapeWeight_add (m m' : ColumnShape n) :
    shapeWeight (m + m') = shapeWeight m + shapeWeight m' := by
  funext i
  simp only [shapeWeight, Pi.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> simp

theorem _root_.FlagVarieties.PointModel.shapeWeight_single (k : Fin n) :
    shapeWeight (Pi.single k 1) = fun i => if i ≤ k then 1 else 0 := by
  classical
  funext i
  simp only [shapeWeight, Pi.single_apply]
  rw [Finset.sum_eq_single k]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

theorem _root_.FlagVarieties.PointModel.shapeWeight_zero : shapeWeight (0 : ColumnShape n) = 0 := by
  funext i
  simp [shapeWeight]

theorem evalAt_mul_poly (g b : Matrix (Fin n) (Fin n) ℂ) (hb : b.IsUpperTriangular)
    (x : MinorDatum n) :
    evalAt (g * b) x.poly = diagPow (shapeWeight (Pi.single x.1 1)) b * evalAt g x.poly := by
  rw [shapeWeight_single, MinorDatum.poly, evalAt_mul_flagRowMinor g b hb]
  rfl

theorem evalAt_mul_familyProd (g b : Matrix (Fin n) (Fin n) ℂ) (hb : b.IsUpperTriangular) :
    ∀ {d : ℕ} (x : Fin d → MinorDatum n),
      evalAt (g * b) (familyProd x) =
        diagPow (shapeWeight (familyShape x)) b * evalAt g (familyProd x)
  | 0, x => by
    simp [familyProd, familyShape, columnMultiplicity_zero, shapeWeight_zero, diagPow]
  | d + 1, x => by
    have ih := evalAt_mul_familyProd g b hb (fun j => x j.castSucc)
    have hshape : familyShape x =
        familyShape (fun j => x j.castSucc) + Pi.single (x (Fin.last d)).1 1 :=
      columnMultiplicity_castSucc fun j => (x j).1
    have hprod : familyProd x = familyProd (fun j => x j.castSucc) * (x (Fin.last d)).poly :=
      Fin.prod_univ_castSucc _
    rw [hprod, map_mul, map_mul, ih, evalAt_mul_poly g b hb, hshape, shapeWeight_add, diagPow_add]
    ring

/-- **Elements of `A_m` are semi-invariant of weight `shapeWeight m`.** -/
theorem evalAt_mul_of_mem_minorSpan {m : ColumnShape n} {p : MatrixPolynomial n}
    (hp : p ∈ minorSpan m) (g b : Matrix (Fin n) (Fin n) ℂ) (hb : b.IsUpperTriangular) :
    evalAt (g * b) p = diagPow (shapeWeight m) b * evalAt g p := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨d, x, hx, rfl⟩ := hp
    rw [← hx]
    exact evalAt_mul_familyProd g b hb x
  | zero => simp
  | add p q _ _ hp hq => rw [map_add, map_add, hp, hq, mul_add]
  | smul c p _ hp => rw [map_smul, map_smul, hp, smul_eq_mul, smul_eq_mul, mul_left_comm]

theorem isSemiInvOn_of_mem_minorSpan {m : ColumnShape n} {p : MatrixPolynomial n}
    (hp : p ∈ minorSpan m) (Z : Set (GL (Fin n) ℂ)) :
    IsSemiInvOn Z (shapeWeightZ m) (algebraMap (MatrixPolynomial n) (GLCoord ℂ n) p) := by
  intro g _ b hb
  rw [glEval_algebraMap_eq_evalAt, glEval_algebraMap_eq_evalAt, Units.val_mul,
      evalAt_mul_of_mem_minorSpan hp _ _ hb,
    borelCharValue_shapeWeightZ]

/-! ### Orbit points and the Demazure library's restriction maps -/

theorem flagOrbitRestriction_eq_evalAt (w : Equiv.Perm (Fin n)) (p : MatrixPolynomial n)
    (z : List (PositiveRoot n × ℂ)) :
    flagOrbitRestriction w p z = evalAt (upperRowMatrix z * rowPermutationMatrix w) p :=
  rfl

theorem det_upperRowMatrix (z : List (PositiveRoot n × ℂ)) : (upperRowMatrix z).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (upperRowMatrix_upper z)]
  simp [upperRowMatrix_diag]

/-- An invertible matrix from a matrix with unit determinant. -/
def unitOfDet (u : Matrix (Fin n) (Fin n) ℂ) (hu : IsUnit u.det) : GL (Fin n) ℂ :=
  ((Matrix.isUnit_iff_isUnit_det u).mpr hu).unit

@[simp]
theorem coe_unitOfDet (u : Matrix (Fin n) (Fin n) ℂ) (hu : IsUnit u.det) :
    (unitOfDet u hu : Matrix (Fin n) (Fin n) ℂ) = u :=
  IsUnit.unit_spec _

theorem upperRowMatrix_mul_mem_bruhatCell (w : Equiv.Perm (Fin n)) (z : List (PositiveRoot n × ℂ)) :
    unitOfDet (upperRowMatrix z) (by rw [det_upperRowMatrix]; exact isUnit_one) * permGL w ∈
      bruhatCell w :=
  ⟨unitOfDet (upperRowMatrix z) (by rw [det_upperRowMatrix]; exact isUnit_one), 1,
    by unfold IsBorel; rw [coe_unitOfDet]; exact upperRowMatrix_upper z, isBorel_one, by simp⟩

theorem exists_upperRowMatrix_eq :
    ∀ l : List ((Fin n × Fin n) × ℂ), (∀ x ∈ l, x.1.1 < x.1.2) →
      ∃ z : List (PositiveRoot n × ℂ), upperRowMatrix z = (l.map elemMatrix).prod
  | [], _ => ⟨[], by simp [upperRowMatrix]⟩
  | x :: l, hl => by
    obtain ⟨z, hz⟩ := exists_upperRowMatrix_eq l fun y hy => hl y (List.mem_cons_of_mem _ hy)
    refine ⟨(⟨x.1, hl x List.mem_cons_self⟩, x.2) :: z, ?_⟩
    rw [upperRowMatrix, hz, List.map_cons, List.prod_cons]
    rfl

/-- Every upper unitriangular matrix is an orbit word of the Demazure library. -/
theorem _root_.FlagVarieties.PointModel.IsUnitriangular.exists_upperRowMatrix
    {u : Matrix (Fin n) (Fin n) ℂ}
    (hu : IsUnitriangular u) : ∃ z : List (PositiveRoot n × ℂ), upperRowMatrix z = u := by
  obtain ⟨l, hl, rfl⟩ := hu.exists_elemList
  exact exists_upperRowMatrix_eq l hl

theorem diagonal_mul_rowPermutationMatrix (d : Fin n → ℂ) (w : Equiv.Perm (Fin n)) :
    Matrix.diagonal d * rowPermutationMatrix w =
      rowPermutationMatrix w * Matrix.diagonal (d ∘ w) := by
  ext i j
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, rowPermutationMatrix, Function.comp_apply]
  split_ifs with h <;> simp [h]

theorem diag_ne_zero_of_isBorel {b : GL (Fin n) ℂ} (hb : IsBorel b) (i : Fin n) :
    (b : Matrix (Fin n) (Fin n) ℂ) i i ≠ 0 := by
  have hdet : (b : Matrix (Fin n) (Fin n) ℂ).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp b.isUnit).ne_zero
  rw [Matrix.det_of_isUpperTriangular hb] at hdet
  exact Finset.prod_ne_zero_iff.mp hdet i (Finset.mem_univ _)

/-- A point of `B ẇ B` is `u ẇ b` with `u` upper unitriangular and `b` upper triangular. -/
theorem exists_unitriangular_of_mem_bruhatCell {w : Equiv.Perm (Fin n)} {g : GL (Fin n) ℂ}
    (hg : g ∈ bruhatCell w) :
    ∃ u b : Matrix (Fin n) (Fin n) ℂ, IsUnitriangular u ∧ b.IsUpperTriangular ∧
      (∀ i, b i i ≠ 0) ∧ (g : Matrix (Fin n) (Fin n) ℂ) = u * rowPermutationMatrix w * b := by
  obtain ⟨b₁, b₂, h₁, h₂, rfl⟩ := hg
  let d : Fin n → ℂ := fun i => (b₁ : Matrix (Fin n) (Fin n) ℂ) i i
  have hd : ∀ i, d i ≠ 0 := diag_ne_zero_of_isBorel h₁
  refine ⟨(b₁ : Matrix (Fin n) (Fin n) ℂ) * Matrix.diagonal (fun i => (d i)⁻¹),
    Matrix.diagonal (d ∘ w) * (b₂ : Matrix (Fin n) (Fin n) ℂ), ⟨?_, fun i => ?_⟩,
    (Matrix.blockTriangular_diagonal _).mul h₂, fun i => ?_, ?_⟩
  · exact Matrix.BlockTriangular.mul h₁ (Matrix.blockTriangular_diagonal _)
  · simp [Matrix.mul_diagonal, d, hd i]
  · rw [Matrix.diagonal_mul]
    exact mul_ne_zero (hd (w i)) (diag_ne_zero_of_isBorel h₂ i)
  · have hb₁ : (b₁ : Matrix (Fin n) (Fin n) ℂ) =
        ((b₁ : Matrix (Fin n) (Fin n) ℂ) * Matrix.diagonal (fun i => (d i)⁻¹)) *
          Matrix.diagonal d := by
      rw [Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]
      have hone : (fun i => (d i)⁻¹ * d i) = fun _ => (1 : ℂ) :=
        funext fun i => inv_mul_cancel₀ (hd i)
      rw [hone, Matrix.diagonal_one, Matrix.mul_one]
    rw [Units.val_mul, Units.val_mul, coe_permGL]
    conv_lhs => rw [hb₁]
    rw [Matrix.mul_assoc _ (Matrix.diagonal d), diagonal_mul_rowPermutationMatrix]
    simp only [Matrix.mul_assoc]

/-- **The orbit restriction kernel of the Demazure library is the pointwise vanishing ideal.** An
element of `A_m` vanishes on `orbitSet S` iff its restriction to the union of the orbits `U · ẇ`
(`w ∈ S`) is zero.
-/
theorem forall_evalAt_eq_zero_iff {m : ColumnShape n} {p : MatrixPolynomial n}
    (hp : p ∈ minorSpan m) (S : Finset (Equiv.Perm (Fin n))) :
    (∀ g ∈ orbitSet S, evalAt (g : Matrix (Fin n) (Fin n) ℂ) p = 0) ↔ unionRestriction S p = 0 := by
  constructor
  · intro h
    funext x
    change flagOrbitRestriction x.1 p x.2 = 0
    rw [flagOrbitRestriction_eq_evalAt]
    have := h _ (mem_orbitSet.mpr ⟨x.1.1, x.1.2, upperRowMatrix_mul_mem_bruhatCell x.1.1 x.2⟩)
    simpa using this
  · intro h g hg
    obtain ⟨w, hw, hg⟩ := mem_orbitSet.mp hg
    obtain ⟨u, b, hu, hb, -, hgub⟩ := exists_unitriangular_of_mem_bruhatCell hg
    obtain ⟨z, rfl⟩ := hu.exists_upperRowMatrix
    rw [hgub, evalAt_mul_of_mem_minorSpan hp _ _ hb, ← flagOrbitRestriction_eq_evalAt]
    have := congrFun h ⟨⟨w, hw⟩, z⟩
    change flagOrbitRestriction w p z = 0 at this
    rw [this, mul_zero]

end

end FlagVarieties.PointModel.Complex
