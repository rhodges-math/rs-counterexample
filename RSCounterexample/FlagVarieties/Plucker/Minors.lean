import RSCounterexample.Demazure.JosephPolo.PrefixMinors
import RSCounterexample.FlagVarieties.Charts.BigCellPoints

/-!
# Flag minors over a commutative ring

For a square matrix `M` over a commutative ring and a row set `T` of size `k + 1`, `minor M T` is
the flag minor `Δ_T(M)` on the rows `T` and the columns `0, …, k`.

* `minor_map`: naturality in the ring.
* `minor_mul_upper`: right multiplication by an upper triangular matrix `B` multiplies `Δ_T` by
  `∏_{i ≤ k} B_{ii}`.
* `isUnit_minor_perm_mul`: on `ẇ u` (`u` lower unitriangular), the minor on `v{0..k}` is a unit.
* `inBigCell_matrixFlag_iff_minor`: **the flag of an invertible matrix `g` lies in the big cell of
  `v` iff all the minors `Δ_{v{0..k}}(g)` are units** (the criterion via `bigCellBlock`, whose
  determinant is `±Δ_{v{0..k}}(g)`, `det_bigCellBlock_succ`).
* `rowSet ρ`, `exists_minor_rowSet`: the row set of an injective `ρ`; reordering the rows changes
  the minor by a sign.
* `entry_eq_minor`: for `u` lower unitriangular and `j < i`, `u_{ij} = ±Δ_T(ẇ u)` with
  `T = v{0..j-1} ∪ {v(i)}`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace FlagVarieties.Plucker

open Matrix Demazure.FlagModule

variable {n : ℕ} {A : Type*} [CommRing A]

/-- **The flag minor `Δ_T(M)`**: the minor of `M` on the rows `T` (`|T| = k + 1`) and the
columns `0, …, k`. -/
def minor {k : Fin n} (M : Matrix (Fin n) (Fin n) A) (T : FlagMinorRowSet k) : A :=
  (M.submatrix T.rows (prefixIndex k)).det

theorem minor_map {B : Type*} [CommRing B] (f : A →+* B) {k : Fin n}
    (M : Matrix (Fin n) (Fin n) A) (T : FlagMinorRowSet k) :
    minor (M.map f) T = f (minor M T) := by
  rw [minor, minor, RingHom.map_det, RingHom.mapMatrix_apply, Matrix.submatrix_map]

theorem prefixIndex_strictMono (k : Fin n) : StrictMono (prefixIndex k) :=
  fun _ _ h => h

theorem isUnit_sign_cast {m : Type*} [Fintype m] [DecidableEq m] (σ : Equiv.Perm m) :
    IsUnit ((Equiv.Perm.sign σ : ℤ) : A) :=
  (Equiv.Perm.sign σ).isUnit.map (Int.castRingHom A)

theorem sign_cast_mul_self {m : Type*} [Fintype m] [DecidableEq m] (σ : Equiv.Perm m) :
    ((Equiv.Perm.sign σ : ℤ) : A) * ((Equiv.Perm.sign σ : ℤ) : A) = 1 := by
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]

/-! ### Upper triangular scaling -/

theorem submatrix_prefix_mul_upper (g b : Matrix (Fin n) (Fin n) A) (hb : b.IsUpperTriangular)
    {k : Fin n} (s : Fin (k.val + 1) → Fin n) :
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

/-- Right multiplication by an upper triangular matrix scales the flag minors. -/
theorem minor_mul_upper (M B : Matrix (Fin n) (Fin n) A) (hB : B.IsUpperTriangular)
    {k : Fin n} (T : FlagMinorRowSet k) :
    minor (M * B) T =
      minor M T * ∏ i : Fin (k.val + 1), B (prefixIndex k i) (prefixIndex k i) := by
  rw [minor, minor, submatrix_prefix_mul_upper M B hB, Matrix.det_mul]
  congr 1
  exact Matrix.det_of_isUpperTriangular (fun i j h => hB (prefixIndex_strictMono k h))

theorem isUnit_diag_of_upper {B : Matrix (Fin n) (Fin n) A} (hB : B.IsUpperTriangular)
    (hdet : IsUnit B.det) (i : Fin n) : IsUnit (B i i) := by
  rw [Matrix.det_of_isUpperTriangular hB, IsUnit.prod_univ_iff] at hdet
  exact hdet i

/-- The scaling factor of `minor_mul_upper` is a unit. -/
theorem isUnit_prod_prefix_diag {B : Matrix (Fin n) (Fin n) A} (hB : B.IsUpperTriangular)
    (hdet : IsUnit B.det) (k : Fin n) :
    IsUnit (∏ i : Fin (k.val + 1), B (prefixIndex k i) (prefixIndex k i)) :=
  IsUnit.prod_univ_iff.mpr fun _ => isUnit_diag_of_upper hB hdet _

/-! ### The minors on `v{0..k}` -/

/-- The minor on `v{0..k}`, with its rows in the order `v(0), …, v(k)`. -/
theorem minor_flagPrefixRows (v : Equiv.Perm (Fin n)) (k : Fin n)
    (M : Matrix (Fin n) (Fin n) A) :
    ((Equiv.Perm.sign (flagPrefixPermutation v k) : ℤ) : A) * minor M (flagPrefixRows v k) =
      (M.submatrix (fun j => v (prefixIndex k j)) (prefixIndex k)).det := by
  rw [minor, ← Matrix.det_permute]
  congr 1
  ext i j
  simp only [Matrix.submatrix_apply, id, flagPrefixPermutation_spec]

theorem perm_mul_eq_submatrix (v : Equiv.Perm (Fin n)) (u : Matrix (Fin n) (Fin n) A) :
    (v.symm.toPEquiv.toMatrix : Matrix (Fin n) (Fin n) A) * u = u.submatrix v.symm id :=
  PEquiv.toMatrix_toPEquiv_mul v.symm u

theorem det_prefix_perm_mul (v : Equiv.Perm (Fin n)) {u : Matrix (Fin n) (Fin n) A}
    (hu : IsLowerUnitriangular u) (k : Fin n) :
    (((v.symm.toPEquiv.toMatrix : Matrix (Fin n) (Fin n) A) * u).submatrix
      (fun j => v (prefixIndex k j)) (prefixIndex k)).det = 1 := by
  rw [perm_mul_eq_submatrix, Matrix.submatrix_submatrix]
  have : (v.symm ∘ fun j => v (prefixIndex k j)) = prefixIndex k := by
    funext j
    simp
  rw [this, Function.id_comp, Matrix.det_of_isLowerTriangular
    (u.submatrix (prefixIndex k) (prefixIndex k)) (fun i j hij => hu.1 hij)]
  exact Finset.prod_eq_one fun i _ => hu.2 _

/-- **On `ẇ u` the minor on `v{0..k}` is a unit** (it is `±1`). -/
theorem isUnit_minor_perm_mul (v : Equiv.Perm (Fin n)) {u : Matrix (Fin n) (Fin n) A}
    (hu : IsLowerUnitriangular u) (k : Fin n) :
    IsUnit (minor ((v.symm.toPEquiv.toMatrix : Matrix (Fin n) (Fin n) A) * u)
      (flagPrefixRows v k)) := by
  have h := minor_flagPrefixRows v k ((v.symm.toPEquiv.toMatrix : Matrix (Fin n) (Fin n) A) * u)
  rw [det_prefix_perm_mul v hu k] at h
  exact IsUnit.of_mul_eq_one_right _ h

/-! ### The big cell criterion -/

/-- The determinant of `bigCellBlock v (k + 1) g` is `±Δ_{v{0..k}}(g)`. -/
theorem det_bigCellBlock_succ (v : Equiv.Perm (Fin n)) (k : Fin n)
    (g : Matrix (Fin n) (Fin n) A) :
    ((Equiv.Perm.sign v : ℤ) : A) * (bigCellBlock v (k.val + 1) g).det =
      (g.submatrix (fun j => v (prefixIndex k j)) (prefixIndex k)).det := by
  classical
  rw [← Matrix.det_permute]
  rw [Matrix.twoBlockTriangular_det _ (fun c : Fin n => k.val + 1 ≤ c.val)]
  · have h1 : ((bigCellBlock v (k.val + 1) g).submatrix v id).toSquareBlockProp
        (fun c : Fin n => k.val + 1 ≤ c.val) = 1 := by
      ext a b
      have ha := a.2
      have hb := b.2
      simp only [Matrix.toSquareBlockProp_def, Matrix.of_apply, Matrix.submatrix_apply, id,
        bigCellBlock, Matrix.one_apply, Pi.single_apply, v.injective.eq_iff, Subtype.ext_iff]
      rw [ite_eq_right (by omega)]
    rw [h1, Matrix.det_one, one_mul]
    let e : Fin (k.val + 1) ≃ {c : Fin n // ¬ (k.val + 1 ≤ c.val)} :=
      { toFun := fun i => ⟨prefixIndex k i, by simp only [prefixIndex]; omega⟩
        invFun := fun c => ⟨c.val.val, by omega⟩
        left_inv := fun i => rfl
        right_inv := fun c => rfl }
    rw [← Matrix.det_submatrix_equiv_self e]
    congr 1
    ext i j
    have hj : (prefixIndex k j).val < k.val + 1 := by simp only [prefixIndex]; omega
    simp only [Matrix.submatrix_apply, Matrix.toSquareBlockProp_def, Matrix.of_apply, id,
      bigCellBlock, e, Equiv.coe_fn_mk]
    rw [ite_eq_left hj]
  · intro i hi j hj
    simp only [Matrix.submatrix_apply, id, bigCellBlock, Matrix.of_apply, Pi.single_apply,
      v.injective.eq_iff]
    rw [ite_eq_right (by omega), ite_eq_right (fun h => by subst h; omega)]

theorem isUnit_det_bigCellBlock_succ_iff (v : Equiv.Perm (Fin n)) (k : Fin n)
    (g : Matrix (Fin n) (Fin n) A) :
    IsUnit (bigCellBlock v (k.val + 1) g).det ↔ IsUnit (minor g (flagPrefixRows v k)) := by
  have h := (det_bigCellBlock_succ v k g).trans (minor_flagPrefixRows v k g).symm
  constructor
  · intro hb
    have := (isUnit_sign_cast v).mul hb
    rw [h] at this
    exact (IsUnit.mul_iff.mp this).2
  · intro hm
    have := (isUnit_sign_cast (flagPrefixPermutation v k)).mul hm
    rw [← h] at this
    exact (IsUnit.mul_iff.mp this).2

theorem isUnit_det_bigCellBlock_zero (v : Equiv.Perm (Fin n)) (g : Matrix (Fin n) (Fin n) A) :
    IsUnit (bigCellBlock v 0 g).det := by
  classical
  have h1 : (bigCellBlock v 0 g).submatrix v id = 1 := by
    ext i j
    simp only [Matrix.submatrix_apply, id, bigCellBlock, Matrix.of_apply, Pi.single_apply,
      v.injective.eq_iff, Matrix.one_apply]
    rw [ite_eq_right (Nat.not_lt_zero _)]
  have h := Matrix.det_permute v (bigCellBlock v 0 g)
  rw [h1, Matrix.det_one] at h
  exact IsUnit.of_mul_eq_one_right _ h.symm

/-- **The big cell criterion**: the flag of an invertible matrix `g` lies in the big cell of `v`
iff the minors `Δ_{v{0..k}}(g)` are units. -/
theorem inBigCell_matrixFlag_iff_minor (v : Equiv.Perm (Fin n)) (g : Matrix (Fin n) (Fin n) A)
    (hg : IsUnit g.det) :
    InBigCell v (matrixFlag g hg) ↔ ∀ k : Fin n, IsUnit (minor g (flagPrefixRows v k)) := by
  rw [inBigCell_matrixFlag_iff]
  constructor
  · intro h k
    exact (isUnit_det_bigCellBlock_succ_iff v k g).mp (h k.succ)
  · intro h j
    refine Fin.cases ?_ (fun k => ?_) j
    · simp only [Fin.val_zero]
      exact isUnit_det_bigCellBlock_zero v g
    · exact (isUnit_det_bigCellBlock_succ_iff v k g).mpr (h k)

/-! ### Row sets of injective maps -/

/-- The row set `ρ(0), …, ρ(k)` of an injective map. -/
def rowSet {k : Fin n} (ρ : Fin (k.val + 1) → Fin n) (hρ : Function.Injective ρ) :
    FlagMinorRowSet k :=
  ⟨Finset.univ.image ρ, by
    apply Finset.mem_powersetCard.mpr
    refine ⟨Finset.subset_univ _, ?_⟩
    rw [Finset.card_image_of_injective _ hρ, Finset.card_univ, Fintype.card_fin]⟩

theorem exists_perm_rowSet {k : Fin n} (ρ : Fin (k.val + 1) → Fin n)
    (hρ : Function.Injective ρ) :
    ∃ π : Equiv.Perm (Fin (k.val + 1)), ∀ j, (rowSet ρ hρ).rows (π j) = ρ j := by
  have hmem : ∀ j, ρ j ∈ (rowSet ρ hρ).val := fun j =>
    Finset.mem_image_of_mem ρ (Finset.mem_univ j)
  let e := (rowSet ρ hρ).val.orderIsoOfFin (Finset.mem_powersetCard.mp (rowSet ρ hρ).property).2
  let pos : Fin (k.val + 1) → Fin (k.val + 1) := fun j => e.symm ⟨ρ j, hmem j⟩
  have hpos : ∀ j, (rowSet ρ hρ).rows (pos j) = ρ j := fun j =>
    congrArg Subtype.val (e.apply_symm_apply _)
  have hinj : Function.Injective pos := fun i j hij => hρ (by rw [← hpos i, ← hpos j, hij])
  exact ⟨Equiv.ofBijective pos hinj.bijective_of_finite, hpos⟩

/-- Reordering the rows of a minor changes it by a sign. -/
theorem exists_minor_rowSet {k : Fin n} (ρ : Fin (k.val + 1) → Fin n)
    (hρ : Function.Injective ρ) :
    ∃ ε : ℤˣ, ∀ M : Matrix (Fin n) (Fin n) A,
      ((ε : ℤ) : A) * minor M (rowSet ρ hρ) = (M.submatrix ρ (prefixIndex k)).det := by
  obtain ⟨π, hπ⟩ := exists_perm_rowSet ρ hρ
  refine ⟨Equiv.Perm.sign π, fun M => ?_⟩
  rw [minor, ← Matrix.det_permute]
  congr 1
  ext i j
  simp only [Matrix.submatrix_apply, id, hπ]

/-! ### Entries of `u` as minors of `ẇ u` -/

/-- The rows `0, …, j - 1, i`. -/
def hookRows (j i : Fin n) : Fin (j.val + 1) → Fin n :=
  fun m => if m.val < j.val then prefixIndex j m else i

theorem hookRows_injective {j i : Fin n} (hji : j < i) : Function.Injective (hookRows j i) := by
  intro a b hab
  have hi : j.val < i.val := hji
  simp only [hookRows] at hab
  split_ifs at hab with ha hb hb
  · exact prefixIndex_injective j hab
  · have := congrArg Fin.val hab
    simp only [prefixIndex] at this
    omega
  · have := congrArg Fin.val hab
    simp only [prefixIndex] at this
    omega
  · have ha' := a.isLt
    have hb' := b.isLt
    exact Fin.ext (by omega)

/-- For `u` lower unitriangular and `j < i`, the minor of `u` on the rows `0, …, j - 1, i` and the
columns `0, …, j` is `u_{ij}`. -/
theorem det_hookRows {u : Matrix (Fin n) (Fin n) A} (hu : IsLowerUnitriangular u) {j i : Fin n}
    (hji : j < i) : (u.submatrix (hookRows j i) (prefixIndex j)).det = u i j := by
  have hi : j.val < i.val := hji
  have hlow : (u.submatrix (hookRows j i) (prefixIndex j)).IsLowerTriangular := by
    intro a b hab
    have hab' : a.val < b.val := hab
    have ha : a.val < j.val := by have := b.isLt; omega
    simp only [Matrix.submatrix_apply, hookRows, ite_eq_left ha]
    exact hu.1 (show prefixIndex j a < prefixIndex j b from hab')
  rw [Matrix.det_of_isLowerTriangular _ hlow, Fin.prod_univ_castSucc]
  have h1 : ∀ m : Fin j.val,
      u.submatrix (hookRows j i) (prefixIndex j) m.castSucc m.castSucc = 1 := by
    intro m
    have hm : (m.castSucc : Fin (j.val + 1)).val < j.val := m.isLt
    simp only [Matrix.submatrix_apply, hookRows, ite_eq_left hm]
    exact hu.2 _
  have h2 : prefixIndex j (Fin.last j.val) = j := Fin.ext rfl
  have h3 : hookRows j i (Fin.last j.val) = i := by simp [hookRows]
  rw [Finset.prod_eq_one fun m _ => h1 m, one_mul]
  change u (hookRows j i (Fin.last j.val)) (prefixIndex j (Fin.last j.val)) = u i j
  rw [h2, h3]

/-- **The entries of `u` are minors of `ẇ u`**: for `j < i`, `u_{ij} = ±Δ_T(ẇ u)` with
`T = v{0..j-1} ∪ {v(i)}`. -/
theorem entry_eq_minor (v : Equiv.Perm (Fin n)) {u : Matrix (Fin n) (Fin n) A}
    (hu : IsLowerUnitriangular u) {j i : Fin n} (hji : j < i) :
    ∃ ε : ℤˣ, u i j = ((ε : ℤ) : A) *
      minor ((v.symm.toPEquiv.toMatrix : Matrix (Fin n) (Fin n) A) * u)
        (rowSet (v ∘ hookRows j i) (v.injective.comp (hookRows_injective hji))) := by
  obtain ⟨ε, hε⟩ := exists_minor_rowSet (A := A) (v ∘ hookRows j i)
    (v.injective.comp (hookRows_injective hji))
  refine ⟨ε, ?_⟩
  rw [hε, perm_mul_eq_submatrix, Matrix.submatrix_submatrix]
  have : (v.symm ∘ v ∘ hookRows j i) = hookRows j i := by
    funext m
    simp
  rw [this, Function.id_comp, det_hookRows hu hji]

end FlagVarieties.Plucker
