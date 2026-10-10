import RSCounterexample.FlagVarieties.Bruhat.Cells

/-!
# Points of opposite Schubert and Richardson varieties

In the ring model over a field `K` (namespace `FlagVarieties.PointModel`):

* `oppBruhatCell K w = B⁻ ẇ B` (`B⁻` lower triangular), the preimage of the opposite cell
  `C^w = B⁻ ẇ B / B`; `oppOrbitSet K S`, the preimage of `X^S`; `upperSet v = {u | v ≤ u}`;
  `richardsonSet K w v = π⁻¹(X_w ∩ X^v)(K)`, the intersection of `⋃_{u ≤ w} B u̇ B` and
  `⋃_{u ≥ v} B⁻ u̇ B`.
* `le_of_mem_bruhatCell_of_mem_oppBruhatCell`: `B u̇ B ∩ B⁻ u̇' B ≠ ∅ → u' ≤ u` (flag minors);
  `eq_of_mem_oppBruhatCell`: the opposite cells are disjoint.
* **`richardsonSet_nonempty_iff`**: `X_w ∩ X^v ≠ ∅ ⟺ v ≤ w`.
* **Torus-fixed points** (`K` of characteristic `0`): `isTorusFixed_iff`: the `T`-fixed points of
  `GL_n / B` are the cosets `u̇ B` (via the normal form of the cells);
  `isTorusFixed_mem_richardsonSet_iff`: those in `X_w ∩ X^v` are the `u̇ B` with `v ≤ u ≤ w`.
-/

open Schubert Demazure.FlagModule Demazure.SchubertUnions FinPermutation

namespace FlagVarieties.PointModel

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {K : Type*} [Field K] {n : ℕ}

/-! ### Opposite cells -/

/-- `b` is lower triangular: a point of the opposite Borel subgroup `B⁻`. -/
def IsOppBorel (b : GL (Fin n) K) : Prop := (b : Matrix (Fin n) (Fin n) K).IsLowerTriangular

theorem isOppBorel_one : IsOppBorel (1 : GL (Fin n) K) := by
  unfold IsOppBorel
  rw [Units.val_one]
  exact Matrix.blockTriangular_one

/-- The opposite Bruhat cell `B⁻ ẇ B`. -/
def oppBruhatCell (K : Type*) [Field K] (w : Equiv.Perm (Fin n)) : Set (GL (Fin n) K) :=
  {g | ∃ b₁ b₂ : GL (Fin n) K, IsOppBorel b₁ ∧ IsBorel b₂ ∧ g = b₁ * permGL K w * b₂}

/-- `⋃_{w ∈ S} B⁻ ẇ B`, the preimage of the opposite Schubert union `X^S`. -/
def oppOrbitSet (K : Type*) [Field K] (S : Finset (Equiv.Perm (Fin n))) : Set (GL (Fin n) K) :=
  ⋃ w ∈ S, oppBruhatCell K w

/-- The Bruhat interval `{u | v ≤ u}`. -/
def upperSet (v : Equiv.Perm (Fin n)) : Finset (Equiv.Perm (Fin n)) := by
  classical exact Finset.univ.filter fun u => v ≤ᴮ u

theorem mem_upperSet {u v : Equiv.Perm (Fin n)} : u ∈ upperSet v ↔ v ≤ᴮ u := by
  classical
  simp [upperSet]

/-- `π⁻¹(X_w ∩ X^v)(K)`. -/
def richardsonSet (K : Type*) [Field K] (w v : Equiv.Perm (Fin n)) : Set (GL (Fin n) K) :=
  orbitSet K (lowerSet w) ∩ oppOrbitSet K (upperSet v)

theorem mem_oppOrbitSet {S : Finset (Equiv.Perm (Fin n))} {g : GL (Fin n) K} :
    g ∈ oppOrbitSet K S ↔ ∃ w ∈ S, g ∈ oppBruhatCell K w := by
  simp [oppOrbitSet]

theorem permGL_mem_oppBruhatCell (v : Equiv.Perm (Fin n)) : permGL K v ∈ oppBruhatCell K v :=
  ⟨1, 1, isOppBorel_one, isBorel_one, by simp⟩

/-- A minor of a lower triangular matrix vanishes unless the columns are entrywise below the
rows. -/
theorem lowerTriangular_minor_zero {k : ℕ} (b : Matrix (Fin n) (Fin n) K)
    (hb : b.IsLowerTriangular) (s t : Fin k ↪o Fin n) (h : ¬ ∀ i, t i ≤ s i) :
    (b.submatrix s t).det = 0 := by
  rw [← Matrix.det_transpose, Matrix.transpose_submatrix]
  refine upperTriangular_minor_zero b.transpose (fun i j hij => ?_) t s h
  exact hb (show OrderDual.toDual i < OrderDual.toDual j from hij)

theorem diag_ne_zero_of_isOppBorel {b : GL (Fin n) K} (hb : IsOppBorel b) (i : Fin n) :
    (b : Matrix (Fin n) (Fin n) K) i i ≠ 0 := by
  have hdet : (b : Matrix (Fin n) (Fin n) K).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp b.isUnit).ne_zero
  rw [Matrix.det_of_isLowerTriangular _ hb] at hdet
  exact Finset.prod_ne_zero_iff.mp hdet i (Finset.mem_univ _)

/-- Flag minors on `b₁ ẇ b₂`. -/
theorem evalAt_mul_permMat_mul_rowMinor (b₁ b₂ : Matrix (Fin n) (Fin n) K)
    (hb₂ : b₂.IsUpperTriangular) (w : Equiv.Perm (Fin n)) (k : Fin n) (T : FlagMinorRowSet k) :
    evalAt (b₁ * permMat K w * b₂) (rowMinor K k T.rows) =
      diagPow (shapeWeight (Pi.single k 1)) b₂ *
        ((Equiv.Perm.sign (flagPrefixPermutation w k) : K) *
          (b₁.submatrix T.rows (flagPrefixRows w k).rows).det) := by
  rw [evalAt_mul_of_mem_minorSpan (rowMinor_mem_minorSpan k _) _ _ hb₂,
    evalAt_unitriangular_mul_rowMinor]

/-- On `B⁻ ẇ B`, a nonzero flag minor `Δ_T` has `w{0..k} ≤ T`. -/
theorem galeLE_of_mem_oppBruhatCell {w : Equiv.Perm (Fin n)} {g : GL (Fin n) K}
    (hg : g ∈ oppBruhatCell K w) {k : Fin n} {T : FlagMinorRowSet k}
    (h : evalAt (g : Matrix (Fin n) (Fin n) K) (rowMinor K k T.rows) ≠ 0) :
    galeLE (flagPrefixRows w k) T := by
  obtain ⟨b₁, b₂, h₁, h₂, rfl⟩ := hg
  rw [Units.val_mul, Units.val_mul, coe_permGL, evalAt_mul_permMat_mul_rowMinor _ _ h₂] at h
  apply galeLE_of_rows_le
  by_contra hle
  apply h
  rw [lowerTriangular_minor_zero _ h₁ T.rows (flagPrefixRows w k).rows hle, mul_zero, mul_zero]

theorem sign_ne_zero {m : ℕ} (σ : Equiv.Perm (Fin m)) : (Equiv.Perm.sign σ : K) ≠ 0 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

/-- On `B⁻ ẇ B`, the prefix minors of `w` do not vanish. -/
theorem evalAt_prefix_ne_zero_of_mem_oppBruhatCell {w : Equiv.Perm (Fin n)} {g : GL (Fin n) K}
    (hg : g ∈ oppBruhatCell K w) (k : Fin n) :
    evalAt (g : Matrix (Fin n) (Fin n) K) (rowMinor K k (flagPrefixRows w k).rows) ≠ 0 := by
  obtain ⟨b₁, b₂, h₁, h₂, rfl⟩ := hg
  rw [Units.val_mul, Units.val_mul, coe_permGL, evalAt_mul_permMat_mul_rowMinor _ _ h₂]
  refine mul_ne_zero (diagPow_ne_zero (diag_ne_zero_of_isBorel h₂) _)
    (mul_ne_zero (sign_ne_zero _) ?_)
  set S := flagPrefixRows w k
  have hlow : ((b₁ : Matrix (Fin n) (Fin n) K).submatrix S.rows S.rows).IsLowerTriangular :=
    fun i j hij => h₁ (show OrderDual.toDual (S.rows j) < OrderDual.toDual (S.rows i) from
      S.rows.strictMono hij)
  rw [Matrix.det_of_isLowerTriangular _ hlow]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => diag_ne_zero_of_isOppBorel h₁ _

/-- **`B u̇ B ∩ B⁻ u̇' B ≠ ∅ → u' ≤ u`.** -/
theorem le_of_mem_bruhatCell_of_mem_oppBruhatCell {u u' : Equiv.Perm (Fin n)} {g : GL (Fin n) K}
    (hu : g ∈ bruhatCell K u) (hu' : g ∈ oppBruhatCell K u') : u' ≤ᴮ u :=
  strongBruhat_iff_galeLE.mpr fun k => by
    by_contra hk
    exact evalAt_prefix_ne_zero_of_mem_oppBruhatCell hu' k
      (evalAt_rowMinor_eq_zero_of_mem_orbitSet hk (mem_orbitSet_grassSet_of_mem_bruhatCell hu k))

/-- **The opposite cells are disjoint.** -/
theorem eq_of_mem_oppBruhatCell {v w : Equiv.Perm (Fin n)} {g : GL (Fin n) K}
    (hv : g ∈ oppBruhatCell K v) (hw : g ∈ oppBruhatCell K w) : v = w :=
  strongBruhat_antisymm
    (strongBruhat_iff_galeLE.mpr fun k =>
      galeLE_of_mem_oppBruhatCell hv (evalAt_prefix_ne_zero_of_mem_oppBruhatCell hw k))
    (strongBruhat_iff_galeLE.mpr fun k =>
      galeLE_of_mem_oppBruhatCell hw (evalAt_prefix_ne_zero_of_mem_oppBruhatCell hv k))

/-! ### Nonemptiness of Richardson varieties -/

/-- **`X_w ∩ X^v ≠ ∅ ⟺ v ≤ w`.** -/
theorem richardsonSet_nonempty_iff (w v : Equiv.Perm (Fin n)) :
    (richardsonSet K w v).Nonempty ↔ v ≤ᴮ w := by
  constructor
  · rintro ⟨g, hg₁, hg₂⟩
    obtain ⟨u, hu, hgu⟩ := mem_orbitSet.mp hg₁
    obtain ⟨u', hu', hgu'⟩ := mem_oppOrbitSet.mp hg₂
    exact strongBruhat_trans (mem_upperSet.mp hu')
      (strongBruhat_trans (le_of_mem_bruhatCell_of_mem_oppBruhatCell hgu hgu')
        (mem_lowerSet.mp hu))
  · intro hvw
    exact ⟨permGL K w, mem_orbitSet.mpr ⟨w, mem_lowerSet_self w, permGL_mem_bruhatCell w⟩,
      mem_oppOrbitSet.mpr ⟨w, mem_upperSet.mpr hvw, permGL_mem_oppBruhatCell w⟩⟩

/-! ### Torus-fixed points -/

/-- `g B` is fixed by the diagonal torus: `t g ∈ g B` for every invertible diagonal `t`. -/
def IsTorusFixed (g : GL (Fin n) K) : Prop :=
  ∀ t : Fin n → K, (∀ i, t i ≠ 0) →
    ∃ b : Matrix (Fin n) (Fin n) K, b.IsUpperTriangular ∧
      Matrix.diagonal t * (g : Matrix (Fin n) (Fin n) K) = (g : Matrix (Fin n) (Fin n) K) * b

theorem diag_ne_zero_of_det_ne_zero {b : Matrix (Fin n) (Fin n) K} (hb : b.IsUpperTriangular)
    (hdet : b.det ≠ 0) (i : Fin n) : b i i ≠ 0 := by
  rw [Matrix.det_of_isUpperTriangular hb] at hdet
  exact Finset.prod_ne_zero_iff.mp hdet i (Finset.mem_univ _)

theorem cellPoint_zero (w : Equiv.Perm (Fin n)) : cellPoint w (fun _ => (0 : K)) = permMat K w := by
  ext r c
  simp only [cellPoint, kazhdanLusztigPoint, permMat]
  by_cases h : ∀ j ≤ c, w j ≠ r
  · have hrc : r ≠ w c := fun e => h c le_rfl e.symm
    simp [hrc]
  · simp [h]

/-- The torus acts on the cell coordinates by characters. -/
theorem diagonal_mul_cellPoint (w : Equiv.Perm (Fin n)) (t : Fin n → K) (ht : ∀ i, t i ≠ 0)
    (y : CellVar w → K) :
    Matrix.diagonal t * cellPoint w y =
      cellPoint w (fun x => t x.1.1.1 / t (w x.1.1.2) * y x) * Matrix.diagonal (t ∘ w) := by
  ext r c
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal, Function.comp_apply]
  simp only [cellPoint, kazhdanLusztigPoint]
  by_cases h : ∀ j ≤ c, w j ≠ r
  · rw [dite_eq_left h, dite_eq_left h]
    by_cases hlt : r < w c
    · rw [dite_eq_left hlt, dite_eq_left hlt]
      field_simp [ht (w c)]
    · rw [dite_eq_right hlt, dite_eq_right hlt, mul_zero, zero_mul]
  · rw [dite_eq_right h, dite_eq_right h]
    by_cases hr : r = w c
    · subst hr
      simp
    · simp [hr]

/-- **The torus-fixed points of `GL_n / B` are the cosets `u̇ B`.** -/
theorem isTorusFixed_iff [CharZero K] (g : GL (Fin n) K) :
    IsTorusFixed g ↔ ∃ (u : Equiv.Perm (Fin n)) (b : Matrix (Fin n) (Fin n) K),
      b.IsUpperTriangular ∧ (g : Matrix (Fin n) (Fin n) K) = permMat K u * b := by
  constructor
  · intro hT
    obtain ⟨u, hu⟩ := exists_mem_bruhatCell g
    obtain ⟨y, b₀, hb₀, hg⟩ := exists_cellPoint_mul hu
    -- a torus element with distinct entries
    let t : Fin n → K := fun i => (i.val : K) + 1
    have ht : ∀ i, t i ≠ 0 := fun i => by
      simp only [t]
      exact_mod_cast Nat.succ_ne_zero i.val
    have htinj : Function.Injective t := fun i j h => by
      simp only [t, add_left_inj, Nat.cast_inj] at h
      exact Fin.ext h
    obtain ⟨b, hb, htg⟩ := hT t ht
    have hgdet : (g : Matrix (Fin n) (Fin n) K).det ≠ 0 :=
      ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit).ne_zero
    have hb₀det : b₀.det ≠ 0 := fun h => hgdet (by rw [hg, Matrix.det_mul, h, mul_zero])
    have hbdet : b.det ≠ 0 := by
      have := congrArg Matrix.det htg
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal] at this
      intro h
      rw [h, mul_zero] at this
      exact (mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => ht i) hgdet) this
    have := Matrix.invertibleOfIsUnitDet _ (isUnit_iff_ne_zero.mpr hb₀det)
    have hb₀inv : (b₀⁻¹).IsUpperTriangular := Matrix.blockTriangular_inv_of_blockTriangular hb₀
    set D' : Matrix (Fin n) (Fin n) K := Matrix.diagonal fun i => (t (u i))⁻¹
    set B := b₀ * b * b₀⁻¹ * D'
    have hBup : B.IsUpperTriangular :=
      ((hb₀.mul hb).mul hb₀inv).mul (Matrix.blockTriangular_diagonal _)
    have hBdet : B.det ≠ 0 := by
      simp only [B, D', Matrix.det_mul, Matrix.det_diagonal, Matrix.det_nonsing_inv]
      refine mul_ne_zero (mul_ne_zero (mul_ne_zero hb₀det hbdet) ?_) ?_
      · exact (Ring.inverse_eq_inv b₀.det).symm ▸ inv_ne_zero hb₀det
      · exact Finset.prod_ne_zero_iff.mpr fun i _ => inv_ne_zero (ht _)
    have hDD : Matrix.diagonal (t ∘ u) * D' = 1 := by
      simp only [D', Matrix.diagonal_mul_diagonal, Function.comp_apply]
      rw [← Matrix.diagonal_one]
      congr 1
      funext i
      exact mul_inv_cancel₀ (ht _)
    have hkey : cellPoint u y * B =
        cellPoint u (fun x => t x.1.1.1 / t (u x.1.1.2) * y x) := by
      have h1 : cellPoint u y * B = Matrix.diagonal t * cellPoint u y * D' := by
        calc cellPoint u y * B = cellPoint u y * b₀ * b * b₀⁻¹ * D' := by
              simp only [B, Matrix.mul_assoc]
          _ = Matrix.diagonal t * (cellPoint u y * b₀) * b₀⁻¹ * D' := by rw [← hg, ← htg]
          _ = Matrix.diagonal t * cellPoint u y * (b₀ * b₀⁻¹) * D' := by
              simp only [Matrix.mul_assoc]
          _ = Matrix.diagonal t * cellPoint u y * D' := by
              rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hb₀det), Matrix.mul_one]
      rw [h1, diagonal_mul_cellPoint u t ht, Matrix.mul_assoc, hDD, Matrix.mul_one]
    have hy := eq_of_cellPoint_mul hBup (diag_ne_zero_of_det_ne_zero hBup hBdet) hkey
    have hy0 : y = fun _ => 0 := by
      funext x
      have hx := congrFun hy x
      have hne : t x.1.1.1 ≠ t (u x.1.1.2) := fun h => ne_of_chartVar u x.1 (htinj h)
      have hratio : t x.1.1.1 / t (u x.1.1.2) ≠ 1 := fun h =>
        hne ((div_eq_one_iff_eq (ht _)).mp h)
      by_contra hyx
      apply hratio
      have := hx.symm
      rw [mul_eq_right₀ hyx] at this
      exact this
    refine ⟨u, b₀, hb₀, ?_⟩
    rw [hg, hy0, cellPoint_zero]
  · rintro ⟨u, b, hb, hg⟩ t ht
    have hgdet : (g : Matrix (Fin n) (Fin n) K).det ≠ 0 :=
      ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit).ne_zero
    have hbdet : b.det ≠ 0 := fun h => hgdet (by rw [hg, Matrix.det_mul, h, mul_zero])
    have := Matrix.invertibleOfIsUnitDet _ (isUnit_iff_ne_zero.mpr hbdet)
    refine ⟨b⁻¹ * Matrix.diagonal (t ∘ u) * b,
      ((Matrix.blockTriangular_inv_of_blockTriangular hb).mul
        (Matrix.blockTriangular_diagonal _)).mul hb, ?_⟩
    rw [hg]
    calc Matrix.diagonal t * (permMat K u * b) = permMat K u * Matrix.diagonal (t ∘ u) * b := by
          rw [← Matrix.mul_assoc, diagonal_mul_permMat]
      _ = permMat K u * (b * b⁻¹) * Matrix.diagonal (t ∘ u) * b := by
          rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hbdet), Matrix.mul_one]
      _ = permMat K u * b * (b⁻¹ * Matrix.diagonal (t ∘ u) * b) := by
          simp only [Matrix.mul_assoc]

/-- **The torus-fixed points of `X_w ∩ X^v`** are the `u̇ B` with `v ≤ u ≤ w`. -/
theorem isTorusFixed_mem_richardsonSet_iff [CharZero K] (w v : Equiv.Perm (Fin n))
    (g : GL (Fin n) K) :
    (IsTorusFixed g ∧ g ∈ richardsonSet K w v) ↔
      ∃ (u : Equiv.Perm (Fin n)) (b : Matrix (Fin n) (Fin n) K), v ≤ᴮ u ∧ u ≤ᴮ w ∧
        b.IsUpperTriangular ∧ (g : Matrix (Fin n) (Fin n) K) = permMat K u * b := by
  constructor
  · rintro ⟨hT, hg₁, hg₂⟩
    obtain ⟨u, b, hb, hg⟩ := (isTorusFixed_iff g).mp hT
    have hgdet : (g : Matrix (Fin n) (Fin n) K).det ≠ 0 :=
      ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit).ne_zero
    have hbdet : IsUnit b.det := isUnit_iff_ne_zero.mpr fun h =>
      hgdet (by rw [hg, Matrix.det_mul, h, mul_zero])
    have hgu : g = permGL K u * unitOfDet b hbdet := by
      apply Units.ext
      rw [Units.val_mul, coe_unitOfDet, coe_permGL, hg]
    have hcell : g ∈ bruhatCell K u :=
      ⟨1, unitOfDet b hbdet, isBorel_one, by unfold IsBorel; rw [coe_unitOfDet]; exact hb,
        by rw [hgu, one_mul]⟩
    have hopp : g ∈ oppBruhatCell K u :=
      ⟨1, unitOfDet b hbdet, isOppBorel_one, by unfold IsBorel; rw [coe_unitOfDet]; exact hb,
        by rw [hgu, one_mul]⟩
    obtain ⟨u₁, hu₁, hgu₁⟩ := mem_orbitSet.mp hg₁
    obtain ⟨u₂, hu₂, hgu₂⟩ := mem_oppOrbitSet.mp hg₂
    refine ⟨u, b, ?_, ?_, hb, hg⟩
    · rw [eq_of_mem_oppBruhatCell hopp hgu₂]
      exact mem_upperSet.mp hu₂
    · rw [eq_of_mem_bruhatCell hcell hgu₁]
      exact mem_lowerSet.mp hu₁
  · rintro ⟨u, b, hvu, huw, hb, hg⟩
    have hgdet : (g : Matrix (Fin n) (Fin n) K).det ≠ 0 :=
      ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit).ne_zero
    have hbdet : IsUnit b.det := isUnit_iff_ne_zero.mpr fun h =>
      hgdet (by rw [hg, Matrix.det_mul, h, mul_zero])
    have hgu : g = 1 * permGL K u * unitOfDet b hbdet := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, Units.val_one, Matrix.one_mul, coe_unitOfDet, coe_permGL,
        hg]
    have hbB : IsBorel (unitOfDet b hbdet) := by
      unfold IsBorel
      rw [coe_unitOfDet]
      exact hb
    refine ⟨(isTorusFixed_iff g).mpr ⟨u, b, hb, hg⟩,
      mem_orbitSet.mpr ⟨u, mem_lowerSet.mpr huw, 1, _, isBorel_one, hbB, hgu⟩,
      mem_oppOrbitSet.mpr ⟨u, mem_upperSet.mpr hvu, 1, _, isOppBorel_one, hbB, hgu⟩⟩

end

end FlagVarieties.PointModel
