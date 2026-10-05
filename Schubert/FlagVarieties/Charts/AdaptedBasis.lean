import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.StdBasis

/-!
# Coordinate spans and adapted bases

Linear algebra over a commutative ring `A` behind the big cells of the flag scheme.

* `FlagVarieties.stdSpan A n m`: the span of the first `m` standard basis vectors of `Aⁿ`; a
  vector lies in it iff its coordinates from `m` on vanish.
* `FlagVarieties.map_stdSpan_eq_iff`: an invertible matrix maps every `stdSpan` onto itself iff
  it is upper triangular. Hence two invertible matrices have the same initial column spans iff
  they differ by an invertible upper triangular matrix on the right (`map_stdSpan_eq_map_iff`).
* `FlagVarieties.tailSpan v j`: for a permutation `v`, the span of `e_{v(j)}, …, e_{v(n-1)}`.
* `FlagVarieties.adaptedMatrix`: if `Vⱼ ⊕ tailSpan v j = Aⁿ` for every `j` and the `Vⱼ` increase,
  the vectors `w_k ∈ V_{k+1}` with `w_k - e_{v(k)} ∈ tailSpan v (k+1)` are the columns of a matrix
  `v · u` with `u` lower unitriangular, and the first `j` columns span `Vⱼ`
  (`span_adaptedMatrix_cols`).
-/

noncomputable section

namespace FlagVarieties

open Matrix

variable (A : Type*) [CommRing A] (n : ℕ)

/-! ### Initial standard spans -/

/-- The span of the first `m` standard basis vectors of `Aⁿ`. -/
def stdSpan (m : ℕ) : Submodule A (Fin n → A) :=
  Submodule.span A (Pi.basisFun A (Fin n) '' {i | i.val < m})

variable {A n}

theorem mem_stdSpan_iff {m : ℕ} {x : Fin n → A} :
    x ∈ stdSpan A n m ↔ ∀ i : Fin n, m ≤ i.val → x i = 0 := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, hj, rfl⟩ := hy
      intro i hi
      have hij : i ≠ j := by
        rintro rfl
        exact absurd hj (not_lt.mpr hi)
      simp [Pi.basisFun_apply, hij]
    | zero => intro i _; rfl
    | add x y _ _ hx hy => intro i hi; simp [hx i hi, hy i hi]
    | smul a x _ hx => intro i hi; simp [hx i hi]
  · intro h
    have hx : x = ∑ i, x i • Pi.basisFun A (Fin n) i := by
      simpa using ((Pi.basisFun A (Fin n)).sum_repr x).symm
    rw [hx]
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases hi : i.val < m
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
    · rw [h i (not_lt.mp hi), zero_smul]
      exact Submodule.zero_mem _

theorem map_stdSpan_le_iff (g : Matrix (Fin n) (Fin n) A) :
    (∀ m, (stdSpan A n m).map (Matrix.toLin' g) ≤ stdSpan A n m) ↔ g.BlockTriangular id := by
  constructor
  · intro h i j hji
    have hm := h (j.val + 1) (Submodule.mem_map_of_mem
      (Submodule.subset_span ⟨j, Nat.lt_succ_self _, rfl⟩))
    rw [mem_stdSpan_iff] at hm
    have := hm i (Nat.succ_le_of_lt (Fin.lt_def.mp hji))
    simpa [Pi.basisFun_apply, Matrix.toLin'_apply, Matrix.mulVec_single_one] using this
  · intro hg m
    rw [stdSpan, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
    change _ ∈ stdSpan A n m
    rw [mem_stdSpan_iff]
    intro i hi
    simpa [Pi.basisFun_apply, Matrix.toLin'_apply, Matrix.mulVec_single_one] using
      hg (show id j < id i from Fin.lt_def.mpr (lt_of_lt_of_le hj hi))

theorem map_stdSpan_eq_iff (g : Matrix (Fin n) (Fin n) A) [Invertible g] :
    (∀ m, (stdSpan A n m).map (Matrix.toLin' g) = stdSpan A n m) ↔ g.BlockTriangular id := by
  constructor
  · intro h
    exact (map_stdSpan_le_iff g).mp fun m => (h m).le
  · intro hg m
    apply le_antisymm ((map_stdSpan_le_iff g).mpr hg m)
    have hinv : (⅟g).BlockTriangular id := by
      rw [Matrix.invOf_eq_nonsing_inv]
      exact Matrix.blockTriangular_inv_of_blockTriangular hg
    have h2 := Submodule.map_mono (f := Matrix.toLin' g) ((map_stdSpan_le_iff (⅟g)).mpr hinv m)
    rwa [← Submodule.map_comp, ← Matrix.toLin'_mul, mul_invOf_self, Matrix.toLin'_one,
      Submodule.map_id] at h2

/-- Two invertible matrices have the same initial column spans iff they differ on the right by an
upper triangular matrix. -/
theorem map_stdSpan_eq_map_iff (g h : Matrix (Fin n) (Fin n) A) [Invertible g] [Invertible h] :
    (∀ m, (stdSpan A n m).map (Matrix.toLin' g) = (stdSpan A n m).map (Matrix.toLin' h)) ↔
      (⅟g * h).BlockTriangular id := by
  let : Invertible (⅟g * h) := invertibleMul _ _
  rw [← map_stdSpan_eq_iff]
  refine forall_congr' fun m => ?_
  rw [Matrix.toLin'_mul, Submodule.map_comp]
  constructor
  · intro e
    rw [← e, ← Submodule.map_comp, ← Matrix.toLin'_mul, invOf_mul_self, Matrix.toLin'_one,
      Submodule.map_id]
  · intro e
    conv_lhs => rw [← e, ← Submodule.map_comp, ← Matrix.toLin'_mul, mul_invOf_self,
      Matrix.toLin'_one,
      Submodule.map_id]

/-! ### Tail spans of a permutation -/

/-- The span of `e_{v(j)}, …, e_{v(n-1)}`. -/
def tailSpan (v : Equiv.Perm (Fin n)) (j : ℕ) : Submodule A (Fin n → A) :=
  Submodule.span A ((fun i => Pi.single (v i) (1 : A)) '' {i : Fin n | j ≤ i.val})

theorem mem_tailSpan_iff {v : Equiv.Perm (Fin n)} {j : ℕ} {x : Fin n → A} :
    x ∈ tailSpan v j ↔ ∀ i : Fin n, i.val < j → x (v i) = 0 := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨k, hk, rfl⟩ := hy
      intro i hi
      have hik : v i ≠ v k := by
        intro h
        rw [v.injective h] at hi
        exact absurd hk (not_le.mpr hi)
      simp [hik]
    | zero => intro i _; rfl
    | add x y _ _ hx hy => intro i hi; simp [hx i hi, hy i hi]
    | smul a x _ hx => intro i hi; simp [hx i hi]
  · intro h
    have hx : x = ∑ i, x (v i) • Pi.single (v i) (1 : A) := by
      rw [Equiv.sum_comp v (fun i => x i • Pi.single i (1 : A))]
      simpa [Pi.basisFun_apply] using ((Pi.basisFun A (Fin n)).sum_repr x).symm
    rw [hx]
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases hi : i.val < j
    · rw [h i hi, zero_smul]
      exact Submodule.zero_mem _
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, not_lt.mp hi, rfl⟩)

theorem tailSpan_antitone (v : Equiv.Perm (Fin n)) {j k : ℕ} (h : j ≤ k) :
    tailSpan (A := A) v k ≤ tailSpan v j := by
  intro x hx
  rw [mem_tailSpan_iff] at hx ⊢
  exact fun i hi => hx i (lt_of_lt_of_le hi h)

/-! ### The adapted matrix of a flag in good position -/

variable (v : Equiv.Perm (Fin n)) (V : ℕ → Submodule A (Fin n → A))
  (hV : ∀ j, IsCompl (V j) (tailSpan v j))

/-- The adapted vector `w_k ∈ V_{k+1}` with `w_k - e_{v(k)} ∈ tailSpan v (k+1)`. -/
def adaptedVector (k : Fin n) : Fin n → A :=
  (V (k.val + 1)).projection (tailSpan v (k.val + 1)) (hV (k.val + 1)) (Pi.single (v k) 1)

theorem adaptedVector_mem (k : Fin n) : adaptedVector v V hV k ∈ V (k.val + 1) :=
  Submodule.projection_apply_mem _ _

theorem single_sub_adaptedVector_mem (k : Fin n) :
    Pi.single (v k) 1 - adaptedVector v V hV k ∈ tailSpan v (k.val + 1) :=
  Submodule.sub_projection_mem _ _

theorem adaptedVector_apply_self (k : Fin n) : adaptedVector v V hV k (v k) = 1 := by
  have h := (mem_tailSpan_iff.mp (single_sub_adaptedVector_mem v V hV k)) k (Nat.lt_succ_self _)
  rw [Pi.sub_apply, Pi.single_eq_same, sub_eq_zero] at h
  exact h.symm

theorem adaptedVector_apply_of_lt {i k : Fin n} (hik : i < k) :
    adaptedVector v V hV k (v i) = 0 := by
  have h := (mem_tailSpan_iff.mp (single_sub_adaptedVector_mem v V hV k)) i
    (Nat.lt_succ_of_lt hik)
  have hne : v i ≠ v k := fun e => (ne_of_lt hik) (v.injective e)
  rw [Pi.sub_apply, Pi.single_eq_of_ne hne, zero_sub, neg_eq_zero] at h
  exact h

/-- The matrix whose columns are the adapted vectors. -/
def adaptedMatrix : Matrix (Fin n) (Fin n) A :=
  Matrix.of fun i k => adaptedVector v V hV k i

/-- The rows of the adapted matrix, reordered by `v`: a lower unitriangular matrix. -/
def adaptedUnipotent : Matrix (Fin n) (Fin n) A :=
  Matrix.of fun i k => adaptedVector v V hV k (v i)

theorem adaptedUnipotent_blockTriangular :
    (adaptedUnipotent v V hV).BlockTriangular OrderDual.toDual := by
  intro i k hik
  exact adaptedVector_apply_of_lt v V hV hik

theorem det_adaptedUnipotent : (adaptedUnipotent v V hV).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular _ (adaptedUnipotent_blockTriangular v V hV)]
  exact Finset.prod_eq_one fun k _ => adaptedVector_apply_self v V hV k

theorem adaptedMatrix_eq : adaptedMatrix v V hV =
    (v.symm.toPEquiv.toMatrix : Matrix (Fin n) (Fin n) A) * adaptedUnipotent v V hV := by
  ext i k
  simp [PEquiv.toMatrix_toPEquiv_mul, Matrix.submatrix_apply, adaptedMatrix, adaptedUnipotent]

theorem isUnit_det_adaptedMatrix : IsUnit (adaptedMatrix v V hV).det := by
  rw [adaptedMatrix_eq, Matrix.det_mul, det_adaptedUnipotent, mul_one, Matrix.det_permutation]
  exact (Equiv.Perm.sign v.symm).isUnit.map (Int.castRingHom A)

theorem adaptedVector_mem_tailSpan {j : ℕ} {k : Fin n} (hk : j ≤ k.val) :
    adaptedVector v V hV k ∈ tailSpan v j := by
  rw [mem_tailSpan_iff]
  intro i hi
  exact adaptedVector_apply_of_lt v V hV (Fin.lt_def.mpr (lt_of_lt_of_le hi hk))

variable {V} in
/-- The first `j` adapted vectors span `Vⱼ`. -/
theorem span_adaptedVector (hmono : Monotone V) (j : ℕ) :
    Submodule.span A (adaptedVector v V hV '' {k | k.val < j}) = V j := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨k, hk, rfl⟩
    exact hmono (Nat.succ_le_of_lt hk) (adaptedVector_mem v V hV k)
  · intro x hx
    have hu := isUnit_det_adaptedMatrix v V hV
    -- write `x` in the basis of adapted vectors
    set W := adaptedMatrix v V hV
    set c := W⁻¹ *ᵥ x
    have hxc : x = ∑ k, c k • adaptedVector v V hV k := by
      have h1 : W *ᵥ c = x := by
        simp only [c, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
      rw [← h1]
      funext i
      simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, W,
        adaptedMatrix, Matrix.of_apply]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    set y := ∑ k ∈ Finset.univ.filter (fun k : Fin n => j ≤ k.val),
      c k • adaptedVector v V hV k with hy_def
    set z := ∑ k ∈ Finset.univ.filter (fun k : Fin n => ¬ j ≤ k.val),
      c k • adaptedVector v V hV k with hz_def
    have hyz : x = z + y := by
      rw [hxc, hy_def, hz_def, add_comm]
      exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm
    have hz : z ∈ Submodule.span A (adaptedVector v V hV '' {k | k.val < j}) :=
      Submodule.sum_mem _ fun k hk => Submodule.smul_mem _ _
        (Submodule.subset_span ⟨k, not_le.mp (Finset.mem_filter.mp hk).2, rfl⟩)
    have hzV : z ∈ V j := by
      refine Submodule.sum_mem _ fun k hk => Submodule.smul_mem _ _ ?_
      exact hmono (Nat.succ_le_of_lt (not_le.mp (Finset.mem_filter.mp hk).2))
        (adaptedVector_mem v V hV k)
    have hyT : y ∈ tailSpan v j :=
      Submodule.sum_mem _ fun k hk => Submodule.smul_mem _ _
        (adaptedVector_mem_tailSpan v V hV (Finset.mem_filter.mp hk).2)
    have hyV : y ∈ V j := by
      have : y = x - z := by rw [hyz]; abel
      rw [this]
      exact Submodule.sub_mem _ hx hzV
    have hy0 : y = 0 := by
      have := (hV j).disjoint
      rw [Submodule.disjoint_def] at this
      exact this y hyV hyT
    rw [hyz, hy0, add_zero]
    exact hz

end FlagVarieties
