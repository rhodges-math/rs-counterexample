import Schubert.FlagVarieties.LineBundle.BigCellData
import Schubert.FlagVarieties.Schubert.Preimage

/-!
# Semi-invariant minors

The factors `m_j = det (bigCellBlock v j X)` of `f_v` (`± ` the minors of `g` with columns
`0, …, j-1` and rows `v(0), …, v(j-1)`) are semi-invariant functions on `GLₙ`:
`m_j(g b) = m_j(g) · ∏_{c < j} b_cc` (`FlagVarieties.map_bigCellMinor_mul`). Their ratios give,
for every weight `η`, a semi-invariant unit `τ_η` of weight `η` on `π⁻¹(bigCell v)`.
-/

noncomputable section

namespace FlagVarieties

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

universe u

section Matrix

variable {A : Type*} [CommRing A] {n : ℕ}

/-- `b` on the first `j` rows and columns, completed by the identity. -/
def blockUpper (j : ℕ) (b : Matrix (Fin n) (Fin n) A) : Matrix (Fin n) (Fin n) A :=
  Matrix.of fun r c => if c.val < j then (if r.val < j then b r c else 0) else
    (if r = c then 1 else 0)

theorem blockUpper_blockTriangular (j : ℕ) {b : Matrix (Fin n) (Fin n) A}
    (hb : b.BlockTriangular id) : (blockUpper j b).BlockTriangular id := by
  intro r c h
  simp only [blockUpper, Matrix.of_apply]
  split_ifs with h1 h2 h3
  · exact hb h
  · rfl
  · exact absurd h3 (ne_of_gt h)
  · rfl

theorem det_blockUpper (j : ℕ) {b : Matrix (Fin n) (Fin n) A} (hb : b.BlockTriangular id) :
    (blockUpper j b).det = ∏ c, if c.val < j then b c c else 1 := by
  rw [Matrix.det_of_isUpperTriangular (blockUpper_blockTriangular j hb)]
  refine Finset.prod_congr rfl fun c _ => ?_
  by_cases hc : c.val < j <;> simp [blockUpper, hc]

theorem bigCellBlock_mul_upper (v : Equiv.Perm (Fin n)) (j : ℕ) (g b : Matrix (Fin n) (Fin n) A)
    (hb : b.BlockTriangular id) :
    bigCellBlock v j (g * b) = bigCellBlock v j g * blockUpper j b := by
  ext r c
  simp only [bigCellBlock, blockUpper, Matrix.of_apply, Matrix.mul_apply]
  by_cases hc : c.val < j
  · simp only [hc, ite_true]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : k.val < j
    · simp [hk]
    · have hck : c < k := by
        rw [Fin.lt_def]
        omega
      simp [hk, hb hck]
  · simp only [hc, ite_false, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq']
    simp [hc]

theorem det_bigCellBlock_mul_upper (v : Equiv.Perm (Fin n)) (j : ℕ)
    (g b : Matrix (Fin n) (Fin n) A) (hb : b.BlockTriangular id) :
    (bigCellBlock v j (g * b)).det =
      (bigCellBlock v j g).det * ∏ c, if c.val < j then b c c else 1 := by
  rw [bigCellBlock_mul_upper v j g b hb, Matrix.det_mul, det_blockUpper j hb]

end Matrix

section Points

variable {R : Type u} [CommRing R] {n : ℕ}

variable (R) in
/-- The minor `m_j = det (bigCellBlock v j X)` of the generic matrix. -/
def bigCellMinor (v : Equiv.Perm (Fin n)) (j : ℕ) : GLCoord R n :=
  (bigCellBlock v j (genericMatrix R n)).det

theorem map_bigCellMinor {A : Type u} [CommRing A] [Algebra R A] (v : Equiv.Perm (Fin n))
    (j : ℕ) (k : GLCoord R n →ₐ[R] A) :
    k (bigCellMinor R v j) = (bigCellBlock v j (GLScheme.pointMatrix R n k)).det := by
  rw [bigCellMinor, ← AlgHom.coe_toRingHom, ← det_map_ringHom, bigCellBlock_map]
  rfl

variable (R n) in
/-- `∏_{c < j} b_cc`. -/
def borelMinor (j : ℕ) : BorelCoord R n :=
  ∏ c, if c.val < j then borelMatrix R n c c else 1

/-- **The minors are semi-invariant**: `m_j(g b) = m_j(g) · ∏_{c < j} b_cc`. -/
theorem map_bigCellMinor_mul {A : Type u} [CommRing A] [Algebra R A] (v : Equiv.Perm (Fin n))
    (j : ℕ) (k : GLCoord R n →ₐ[R] A) (b : BorelCoord R n →ₐ[R] A) :
    glPointOfMatrix R (GLScheme.pointMatrix R n k * (borelMatrix R n).map b)
        (isUnit_det_pointMatrix_mul k b) (bigCellMinor R v j) =
      k (bigCellMinor R v j) * b (borelMinor R n j) := by
  rw [map_bigCellMinor, pointMatrix_glPointOfMatrix,
    det_bigCellBlock_mul_upper _ _ _ _ (borelMatrix_map_blockTriangular b), ← map_bigCellMinor,
    borelMinor, map_prod]
  congr 1
  refine Finset.prod_congr rfl fun c _ => ?_
  split_ifs <;> simp [Matrix.map_apply]

end Points

section Weights

variable (R : Type u) [CommRing R] (n : ℕ)

theorem borelCharacterUnit_add (η η' : Fin n → ℤ) :
    borelCharacterUnit R n (η + η') = borelCharacterUnit R n η * borelCharacterUnit R n η' := by
  simp only [borelCharacterUnit, Pi.add_apply, zpow_add, Finset.prod_mul_distrib]

theorem borelCharacterUnit_zero : borelCharacterUnit R n 0 = 1 := by
  simp [borelCharacterUnit]

theorem borelCharacterUnit_neg (η : Fin n → ℤ) :
    borelCharacterUnit R n (-η) = (borelCharacterUnit R n η)⁻¹ :=
  eq_inv_of_mul_eq_one_left
      (by rw [← borelCharacterUnit_add, neg_add_cancel, borelCharacterUnit_zero])

variable {n} in
/-- The weight of the minor `m_j`: `-1` on the first `j` coordinates. -/
def minorWeight (j : ℕ) : Fin n → ℤ :=
  fun i => if i.val < j then -1 else 0

theorem borelCharacterUnit_minorWeight_inv (j : ℕ) :
    (((borelCharacterUnit R n (minorWeight j))⁻¹ : (BorelCoord R n)ˣ) : BorelCoord R n) =
      borelMinor R n j := by
  rw [← borelCharacterUnit_neg, borelCharacterUnit, Units.coe_prod, borelMinor]
  refine Finset.prod_congr rfl fun c _ => ?_
  by_cases hc : c.val < j
  · simp [minorWeight, hc, borelDiag]
  · simp [minorWeight, hc]

end Weights

namespace BorelAction

variable {R : Type u} [CommRing R] {n : ℕ} {T : Scheme.{u}} (E : BorelAction R n T)

theorem twist_add (η η' : Fin n → ℤ) : E.twist (η + η') = E.twist η * E.twist η' := by
  rw [twist, twist, twist, borelCharacterUnit_add, mul_inv_rev, Units.val_mul, map_mul, map_mul,
    mul_comm]

theorem twistOn_add (η η' : Fin n → ℤ) (W : E.actionDomain.Opens) :
    E.twistOn (η + η') W = E.twistOn η W * E.twistOn η' W := by
  rw [twistOn, twistOn, twistOn, twist_add, map_mul]

theorem twist_neg_mul (η : Fin n → ℤ) : E.twist (-η) * E.twist η = 1 := by
  rw [← twist_add, neg_add_cancel, twist, borelCharacterUnit_zero, inv_one, Units.val_one, map_one,
    map_one]

theorem twistOn_neg_mul (η : Fin n → ℤ) (W : E.actionDomain.Opens) :
    E.twistOn (-η) W * E.twistOn η W = 1 := by
  rw [twistOn, twistOn, ← map_mul, twist_neg_mul, map_one]

/-- Products of semi-invariant functions are semi-invariant, with the sum of the weights. -/
theorem IsSemiInvariant.mul {η η' : Fin n → ℤ} {W : T.Opens} {f g : Γ(E.P, E.q ⁻¹ᵁ W)}
    (hf : E.IsSemiInvariant η f) (hg : E.IsSemiInvariant η' g) :
    E.IsSemiInvariant (η + η') (f * g) := by
  unfold IsSemiInvariant at hf hg ⊢
  rw [map_mul, map_mul, hf, hg, twistOn_add]
  ring

/-- The inverse of a semi-invariant unit is semi-invariant, with the opposite weight. -/
theorem IsSemiInvariant.inv {η : Fin n → ℤ} {W : T.Opens} {u : (Γ(E.P, E.q ⁻¹ᵁ W))ˣ}
    (hu : E.IsSemiInvariant η (u : Γ(E.P, E.q ⁻¹ᵁ W))) :
    E.IsSemiInvariant (-η) ((u⁻¹ : (Γ(E.P, E.q ⁻¹ᵁ W))ˣ) : Γ(E.P, E.q ⁻¹ᵁ W)) := by
  unfold IsSemiInvariant at hu ⊢
  have h1 := congrArg (E.act.appLE _ _ (E.actionFst_preimage_le W)).hom u.inv_mul
  have h2 := congrArg (E.actionFst.app (E.q ⁻¹ᵁ W)).hom u.inv_mul
  rw [map_mul, map_one, hu] at h1
  rw [map_mul, map_one] at h2
  have ht := E.twistOn_neg_mul η (E.actionFst ⁻¹ᵁ E.q ⁻¹ᵁ W)
  linear_combination (E.twistOn (-η) _ * (E.actionFst.app (E.q ⁻¹ᵁ W)).hom ↑u⁻¹) * h1 -
    ((E.act.appLE _ _ (E.actionFst_preimage_le W)).hom ↑u⁻¹) * ht -
    ((E.act.appLE _ _ (E.actionFst_preimage_le W)).hom ↑u⁻¹ * E.twistOn (-η) _ * E.twistOn η _) * h2

theorem _root_.FlagVarieties.appLE_top_top {X Y : Scheme.{u}} (f : X ⟶ Y) (e : ⊤ ≤ f ⁻¹ᵁ ⊤) :
    f.appLE ⊤ ⊤ e = f.appTop :=
  Scheme.Hom.appLE_eq_app (f := f) (U := ⊤)

theorem twistOn_top (η : Fin n → ℤ) : E.twistOn η ⊤ = E.twist η := by
  rw [twistOn, Subsingleton.elim (homOfLE le_top) (𝟙 _), op_id, CategoryTheory.Functor.map_id]
  rfl

theorem isSemiInvariant_top_iff (η : Fin n → ℤ) (f : Γ(E.P, E.q ⁻¹ᵁ ⊤)) :
    E.IsSemiInvariant η (W := ⊤) f ↔ E.act.appTop.hom f = E.twist η * E.actionFst.appTop.hom f := by
  unfold IsSemiInvariant
  exact Eq.congr (congrArg (fun φ => CommRingCat.Hom.hom φ f) (appLE_top_top E.act _))
    (congrArg (· * _) (E.twistOn_top η))

/-- Semi-invariance of a global function can be tested after pulling back along an isomorphism
`τ : Y ≅ P ×_R B`. -/
theorem isSemiInvariant_top_iff_of_isIso {Y : Scheme.{u}} (τ : Y ⟶ E.actionDomain) (hτ : IsIso τ)
    (η : Fin n → ℤ) (f : Γ(E.P, E.q ⁻¹ᵁ ⊤)) :
    E.IsSemiInvariant η (W := ⊤) f ↔
      (τ ≫ E.act).appTop.hom f = (τ ≫ E.actionSnd).appTop.hom
          ((Scheme.ΓSpecIso (CommRingCat.of (BorelCoord R n))).inv
            (((borelCharacterUnit R n η)⁻¹ : (BorelCoord R n)ˣ) : BorelCoord R n)) *
        (τ ≫ E.actionFst).appTop.hom f := by
  have hinj : Function.Injective (τ.app ⊤).hom :=
    (ConcreteCategory.bijective_of_isIso (τ.app ⊤)).1
  rw [isSemiInvariant_top_iff, ← hinj.eq_iff, map_mul]
  rfl

theorem twist_zero : E.twist 0 = 1 := by
  rw [twist, borelCharacterUnit_zero, inv_one, Units.val_one, map_one, map_one]

theorem IsSemiInvariant.one (W : T.Opens) : E.IsSemiInvariant 0 (W := W) 1 := by
  unfold IsSemiInvariant
  rw [map_one, map_one, twistOn, twist_zero, map_one, one_mul]

/-- Integer powers of semi-invariant units. -/
theorem IsSemiInvariant.zpow {η : Fin n → ℤ} {W : T.Opens} {u : (Γ(E.P, E.q ⁻¹ᵁ W))ˣ}
    (hu : E.IsSemiInvariant η (u : Γ(E.P, E.q ⁻¹ᵁ W))) (k : ℤ) :
    E.IsSemiInvariant (k • η) ((u ^ k : (Γ(E.P, E.q ⁻¹ᵁ W))ˣ) : Γ(E.P, E.q ⁻¹ᵁ W)) := by
  induction k using Int.induction_on with
  | zero => simpa using IsSemiInvariant.one E W
  | succ k ih =>
    rw [zpow_add_one, Units.val_mul, add_smul, one_smul]
    exact ih.mul E hu
  | pred k ih =>
    rw [sub_eq_add_neg, zpow_add, zpow_neg_one, Units.val_mul, add_smul, neg_one_smul]
    exact ih.mul E hu.inv

/-- Finite products of semi-invariant units. -/
theorem IsSemiInvariant.prod {ι : Type*} (s : Finset ι) {W : T.Opens} (η : ι → Fin n → ℤ)
    (u : ι → (Γ(E.P, E.q ⁻¹ᵁ W))ˣ)
    (hu : ∀ i ∈ s, E.IsSemiInvariant (η i) (u i : Γ(E.P, E.q ⁻¹ᵁ W))) :
    E.IsSemiInvariant (∑ i ∈ s, η i) ((∏ i ∈ s, u i : (Γ(E.P, E.q ⁻¹ᵁ W))ˣ) :
      Γ(E.P, E.q ⁻¹ᵁ W)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IsSemiInvariant.one E W
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, Units.val_mul]
    exact (hu a (Finset.mem_insert_self a s)).mul E
      (ih fun i hi => hu i (Finset.mem_insert_of_mem hi))

end BorelAction

section GLPoints

variable {R : Type u} [CommRing R] {n : ℕ}

variable (R n) in
/-- `𝒪(GLₙ) ⊗_R 𝒪(B)`, the coordinate ring of `GLₙ ×_R B`. -/
def GLBorelCoord : Type u :=
  GLCoord R n ⊗[R] BorelCoord R n

instance : CommRing (GLBorelCoord R n) :=
  inferInstanceAs (CommRing (GLCoord R n ⊗[R] BorelCoord R n))

instance : Algebra R (GLBorelCoord R n) :=
  inferInstanceAs (Algebra R (GLCoord R n ⊗[R] BorelCoord R n))

variable (R n) in
/-- The first factor `𝒪(GLₙ) → 𝒪(GLₙ) ⊗ 𝒪(B)`. -/
def GLBorelCoord.inl : GLCoord R n →ₐ[R] GLBorelCoord R n :=
  Algebra.TensorProduct.includeLeft

variable (R n) in
/-- The second factor `𝒪(B) → 𝒪(GLₙ) ⊗ 𝒪(B)`. -/
def GLBorelCoord.inr : BorelCoord R n →ₐ[R] GLBorelCoord R n :=
  Algebra.TensorProduct.includeRight

variable (R n) in
/-- The universal point `Spec (𝒪(GLₙ) ⊗ 𝒪(B)) ≅ GLₙ ×_R B`. -/
def glBorelUniversalPoint : Spec (CommRingCat.of (GLBorelCoord R n)) ⟶ GLBorel R n :=
  (glBorelSpecIso R n).inv

instance : IsIso (glBorelUniversalPoint R n) :=
  inferInstanceAs (IsIso (glBorelSpecIso R n).inv)

theorem glBorelUniversalPoint_fst : glBorelUniversalPoint R n ≫ pullback.fst _ _ =
    GLScheme.point R n (GLBorelCoord.inl R n) :=
  glBorelSpecIso_inv_fst R n

theorem glBorelUniversalPoint_snd :
    glBorelUniversalPoint R n ≫ pullback.snd _ _ = Spec.map
        (CommRingCat.ofHom (GLBorelCoord.inr R n).toRingHom) :=
  glBorelSpecIso_inv_snd R n

theorem glBorelUniversalPoint_eq : glBorelUniversalPoint R n = pullback.lift
    (GLScheme.point R n (GLBorelCoord.inl R n))
    (Spec.map (CommRingCat.ofHom (GLBorelCoord.inr R n).toRingHom))
        (point_borel_condition _ _) := by
  apply pullback.hom_ext
  · rw [glBorelUniversalPoint_fst, pullback.lift_fst]
  · rw [glBorelUniversalPoint_snd, pullback.lift_snd]

/-- A global function `F` on `GLₙ` with `F(g b) = η(b)⁻¹ F(g)` (tested on the universal point of
`GLₙ ×_R B`) is semi-invariant of weight `η`. -/
theorem isSemiInvariant_glCoordToGlobal (η : Fin n → ℤ) (F : GLCoord R n)
    (hF : glPointOfMatrix R
        (GLScheme.pointMatrix R n (GLBorelCoord.inl R n) * (borelMatrix R n).map
            (GLBorelCoord.inr R n))
          (isUnit_det_pointMatrix_mul _ _) F =
      GLBorelCoord.inr R n (((borelCharacterUnit R n η)⁻¹ : (BorelCoord R n)ˣ) : BorelCoord R n) *
        GLBorelCoord.inl R n F) :
    (glBorelAction R n).IsSemiInvariant η (W := ⊤) (glCoordToGlobal R n F) := by
  refine ((glBorelAction R n).isSemiInvariant_top_iff_of_isIso (glBorelUniversalPoint R n)
    (inferInstanceAs (IsIso (glBorelUniversalPoint R n))) η _).mpr ?_
  change (glBorelUniversalPoint R n ≫ mulRight R n).appTop.hom _ =
    (glBorelUniversalPoint R n ≫ pullback.snd _ _).appTop.hom _ *
      (glBorelUniversalPoint R n ≫ pullback.fst _ _).appTop.hom _
  rw [glBorelUniversalPoint_eq, lift_mulRight, ← glBorelUniversalPoint_eq,
      glBorelUniversalPoint_fst, glBorelUniversalPoint_snd,
    point_appTop_glCoordToGlobal, point_appTop_glCoordToGlobal, hF, map_mul]
  congr 1
  rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

/-- **The minors `m_j` are semi-invariant**, of weight `-1` on the first `j` coordinates. -/
theorem isSemiInvariant_bigCellMinor (v : Equiv.Perm (Fin n)) (j : ℕ) :
    (glBorelAction R n).IsSemiInvariant (minorWeight j) (W := ⊤)
      (glCoordToGlobal R n (bigCellMinor R v j)) := by
  apply isSemiInvariant_glCoordToGlobal
  rw [map_bigCellMinor_mul, borelCharacterUnit_minorWeight_inv, mul_comm]

end GLPoints

section Units

variable {R : Type u} [CommRing R] {n : ℕ} (v : Equiv.Perm (Fin n))

variable (R) in
/-- Restriction of global functions on `GLₙ` to `π⁻¹(bigCell v)`. -/
def restrictBigCell :
    Γ(GLScheme R n, ⊤) ⟶ Γ(GLScheme R n, FlagScheme.orbitMap R n ⁻¹ᵁ bigCell R v) :=
  (GLScheme R n).presheaf.map (homOfLE le_top).op

theorem isUnit_restrictBigCell_bigCellFunction :
    IsUnit ((restrictBigCell R v).hom (glCoordToGlobal R n (bigCellFunction R v))) := by
  set O := FlagScheme.orbitMap R n ⁻¹ᵁ bigCell R v
  set x := glCoordToGlobal R n (bigCellFunction R v)
  have h1 : IsUnit ((preimageChart R v).appTop.hom x) := by
    rw [point_appTop_glCoordToGlobal]
    exact (IsLocalization.Away.algebraMap_isUnit (bigCellFunction R v)).map _
  have h2 : preimageChart R v = (preimageIso R v).inv ≫ O.ι := by
    rw [Iso.eq_inv_comp, preimageIso_hom_chart]
  have h3 : IsUnit (O.ι.appTop.hom x) := by
    rw [h2] at h1
    have : IsIso ((preimageIso R v).inv.app ⊤) := inferInstance
    exact (isUnit_map_iff (asIso ((preimageIso R v).inv.app ⊤)).commRingCatIsoToRingEquiv _).mp h1
  have e : O.ι.appTop.hom x = ((GLScheme R n).presheaf.map
      (homOfLE (Scheme.Opens.ι_image_le O ⊤)).op).hom ((restrictBigCell R v).hom x) := by
    rw [Scheme.Opens.ι_appTop, restrictBigCell, ← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl
  rw [e] at h3
  have := isIso_presheaf_map_of_eq (homOfLE (Scheme.Opens.ι_image_le O ⊤))
    (Scheme.Opens.ι_image_top O)
  exact (isUnit_map_iff (asIso ((GLScheme R n).presheaf.map
    (homOfLE (Scheme.Opens.ι_image_le O ⊤)).op)).commRingCatIsoToRingEquiv _).mp h3

theorem isUnit_restrictBigCell_bigCellMinor (j : Fin (n + 1)) :
    IsUnit ((restrictBigCell R v).hom (glCoordToGlobal R n (bigCellMinor R v j))) := by
  have h := isUnit_restrictBigCell_bigCellFunction (R := R) v
  have e : bigCellFunction R v = ∏ j : Fin (n + 1), bigCellMinor R v j := rfl
  rw [e, map_prod, map_prod, IsUnit.prod_univ_iff] at h
  exact h j

theorem isSemiInvariant_restrictBigCell_bigCellMinor (j : ℕ) :
    (glBorelAction R n).IsSemiInvariant (minorWeight j) (W := bigCell R v)
      ((restrictBigCell R v).hom (glCoordToGlobal R n (bigCellMinor R v j))) :=
  BorelAction.IsSemiInvariant.map _ le_top (isSemiInvariant_bigCellMinor v j)

variable (R) in
/-- The unit `m_j` on `π⁻¹(bigCell v)`. -/
def minorUnit (j : Fin (n + 1)) :
    (Γ(GLScheme R n, FlagScheme.orbitMap R n ⁻¹ᵁ bigCell R v))ˣ :=
  (isUnit_restrictBigCell_bigCellMinor v j).unit

variable (R) in
/-- **A semi-invariant unit of weight `η` on `π⁻¹(bigCell v)`**: `∏ᵢ (m_i / m_{i+1})^{ηᵢ}`. -/
def bigCellTwistUnit (η : Fin n → ℤ) :
    (Γ(GLScheme R n, FlagScheme.orbitMap R n ⁻¹ᵁ bigCell R v))ˣ :=
  ∏ i : Fin n, (minorUnit R v i.castSucc * (minorUnit R v i.succ)⁻¹) ^ η i

theorem minorWeight_sub (i : Fin n) :
    minorWeight (n := n) i.castSucc.val + -minorWeight i.succ.val = Pi.single i 1 := by
  funext c
  simp only [minorWeight, Fin.val_castSucc, Fin.val_succ, Pi.add_apply, Pi.neg_apply]
  by_cases h : c = i
  · subst h
    simp
  · rw [Pi.single_eq_of_ne h]
    have : c.val ≠ i.val := fun e => h (Fin.ext e)
    by_cases h1 : c.val < i.val
    · simp [h1, show c.val < i.val + 1 by omega]
    · simp [h1, show ¬ c.val < i.val + 1 by omega]

theorem isSemiInvariant_bigCellTwistUnit (η : Fin n → ℤ) :
    (glBorelAction R n).IsSemiInvariant η (W := bigCell R v)
      ((bigCellTwistUnit R v η : (Γ(GLScheme R n, FlagScheme.orbitMap R n ⁻¹ᵁ bigCell R v))ˣ) :
        Γ(GLScheme R n, FlagScheme.orbitMap R n ⁻¹ᵁ bigCell R v)) := by
  have hη : ∑ i : Fin n, η i • (Pi.single i (1 : ℤ) : Fin n → ℤ) = η := by
    funext c
    simp [Finset.sum_apply, Pi.single_apply]
  have h := BorelAction.IsSemiInvariant.prod (glBorelAction R n) Finset.univ
    (fun i : Fin n => η i • (Pi.single i (1 : ℤ) : Fin n → ℤ))
    (fun i => (minorUnit R v i.castSucc * (minorUnit R v i.succ)⁻¹) ^ η i) (fun i _ => by
      refine BorelAction.IsSemiInvariant.zpow _ ?_ (η i)
      rw [← minorWeight_sub, Units.val_mul]
      exact (isSemiInvariant_restrictBigCell_bigCellMinor v _).mul _
        (BorelAction.IsSemiInvariant.inv _ (isSemiInvariant_restrictBigCell_bigCellMinor v _)))
  rw [hη] at h
  exact h

end Units

end FlagVarieties
