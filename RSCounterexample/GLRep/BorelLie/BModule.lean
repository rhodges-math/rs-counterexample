import RSCounterexample.GLRep.BorelLie.Brackets
import RSCounterexample.Demazure.BModules.Basic

/-!
# Rational `B`-representations as `BModule`s

Over `ℂ`, a rational representation `ρ` of the Borel subgroup `B ⊆ GL_n(ℂ)` on a
finite-dimensional space `W` gives a `BModule` of the Demazure library
(`Demazure.BModules.BModule n`, **`GLRep.IsRationalBorelRep.toBModule`**):

* `𝔫⁺` acts through the differentials: `nil X = Σ_{a<b} X_ab D_ab`; this is a Lie algebra map
  `upperNilpotent n →ₗ⁅ℂ⁆ End W` by the bracket relations of `Brackets.lean` (`nil`);
* the torus acts through `B` (`ρ ∘ borelTorus`), compatibly with `𝔫⁺` (`conj_borelLie`), and `W`
  is the sum of its integral weight spaces.

The dictionary (the full `B ↔ (𝔫⁺, T)` correspondence, for every rational
`B`-representation):

* **subspaces**: `forall_mem_iff_bModule`: a subspace is `B`-stable iff it is a `B`-submodule of
  `toBModule` (stable under `nil` and the torus); `subrepresentationOrderIso :
  Subrepresentation ρ ≃o BSubmodule hρ.toBModule`;
* **maps**: `forall_intertwining_iff_bModule`; `homEquiv : ρ.IntertwiningMap σ ≃
  BModule.Hom hρ.toBModule hσ.toBModule`;
* **isomorphisms**: `isoEquiv : ρ.Equiv σ ≃ (hρ.toBModule ≃ᴮ hσ.toBModule)`.
-/

namespace GLRep

open Module Demazure.FlagModule Demazure.BModules

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : ℕ}

/-! ### Strictly upper triangular matrices as combinations of root vectors -/

theorem rootVector_val_apply (r : PositiveRoot n) (i j : Fin n) :
    (rootVector r).val i j = if r.val.1 = i ∧ r.val.2 = j then 1 else 0 := by
  change Matrix.single r.val.1 r.val.2 (1 : ℂ) i j = _
  rw [Matrix.single_apply]

theorem upperNilpotent_val_eq_sum (X : upperNilpotent n) (i j : Fin n) :
    X.val i j = ∑ p : PositiveRoot n, X.val p.val.1 p.val.2 * (rootVector p).val i j := by
  by_cases hij : i < j
  · rw [Finset.sum_eq_single ⟨(i, j), hij⟩]
    · rw [rootVector_val_apply, ite_eq_left ⟨rfl, rfl⟩, mul_one]
    · intro p _ hp
      rw [rootVector_val_apply, ite_eq_right, mul_zero]
      rintro ⟨h1, h2⟩
      exact hp (Subtype.ext (Prod.ext h1 h2))
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [X.property i j hij]
    refine (Finset.sum_eq_zero fun p _ => ?_).symm
    rw [rootVector_val_apply, ite_eq_right, mul_zero]
    rintro ⟨h1, h2⟩
    exact hij (h1 ▸ h2 ▸ p.property)

/-- **Every `X ∈ 𝔫⁺` is `Σ_{a<b} X_ab E_ab`.** -/
theorem upperNilpotent_eq_sum (X : upperNilpotent n) :
    X = ∑ p : PositiveRoot n, X.val p.val.1 p.val.2 • rootVector p := by
  apply Subtype.ext
  ext i j
  rw [upperNilpotent_val_eq_sum X i j]
  change _ = ((upperNilpotent n).incl (∑ p : PositiveRoot n, X.val p.val.1 p.val.2 •
    rootVector p)) i j
  rw [map_sum, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_smul, Matrix.smul_apply, smul_eq_mul]
  rfl

/-- Two linear maps out of `𝔫⁺` agreeing on the root vectors are equal. -/
theorem upperNilpotent_linearMap_ext {E : Type*} [AddCommGroup E] [Module ℂ E]
    {f g : upperNilpotent n →ₗ[ℂ] E} (h : ∀ r, f (rootVector r) = g (rootVector r)) : f = g := by
  refine LinearMap.ext fun X => ?_
  rw [upperNilpotent_eq_sum X, map_sum, map_sum]
  exact Finset.sum_congr rfl fun p _ => by rw [map_smul, map_smul, h]

/-! ### The weight spaces -/

theorem integerWeightScalar_eq (μ : Fin n → ℤ) (t : DiagonalTorus n) :
    integerWeightScalar μ t = TauCeti.weightCharHom ℂ μ t := by
  rw [TauCeti.weightCharHom_apply, TauCeti.weightChar_apply, TauCeti.torusCharacter_def,
    Units.coe_prod, integerWeightScalar]
  exact Finset.prod_congr rfl fun i _ => (Units.val_zpow_eq_zpow_val _ _).symm

theorem torusWeightSpace_eq {E : Type*} [AddCommGroup E] [Module ℂ E]
    (π : DiagonalTorus n →* Module.End ℂ E) (μ : Fin n → ℤ) :
    Demazure.FlagModule.torusWeightSpace π μ = GLRep.torusWeightSpace π μ := by
  ext x
  rw [GLRep.mem_torusWeightSpace]
  change (∀ t, π t x = integerWeightScalar μ t • x) ↔ _
  simp only [integerWeightScalar_eq]

/-! ### The `𝔫⁺`-action -/

namespace IsRationalBorelRep

variable {W : Type} [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ (borel ℂ n) W}
variable (hρ : IsRationalBorelRep ρ)

/-- `X ↦ Σ_{a<b} X_ab D_ab`, as a linear map. -/
def nilLinear : upperNilpotent n →ₗ[ℂ] Module.End ℂ W where
  toFun X := ∑ p : PositiveRoot n, X.val p.val.1 p.val.2 • hρ.borelLie p.property
  map_add' X Y := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← add_smul]
    rfl
  map_smul' c X := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [smul_smul]
    rfl

theorem nilLinear_apply (X : upperNilpotent n) :
    hρ.nilLinear X = ∑ p : PositiveRoot n, X.val p.val.1 p.val.2 • hρ.borelLie p.property :=
  rfl

theorem nilLinear_rootVector (r : PositiveRoot n) :
    hρ.nilLinear (rootVector r) = hρ.borelLie r.property := by
  rw [nilLinear_apply, Finset.sum_eq_single r]
  · rw [rootVector_val_apply, ite_eq_left ⟨rfl, rfl⟩, one_smul]
  · intro p _ hp
    rw [rootVector_val_apply, ite_eq_right, zero_smul]
    rintro ⟨h1, h2⟩
    exact hp (Subtype.ext (Prod.ext h1.symm h2.symm))
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem nilLinear_of_val_eq (X : upperNilpotent n) (r : PositiveRoot n)
    (h : X.val = Matrix.single r.val.1 r.val.2 1) :
    hρ.nilLinear X = hρ.borelLie r.property := by
  have : X = rootVector r := Subtype.ext h
  rw [this, nilLinear_rootVector]

/-- The bracket of two root vectors acts by the bracket of the differentials. -/
theorem nilLinear_lie_rootVector (p q : PositiveRoot n) :
    hρ.nilLinear ⁅rootVector p, rootVector q⁆ =
      ⁅hρ.nilLinear (rootVector p), hρ.nilLinear (rootVector q)⁆ := by
  obtain ⟨⟨a, b⟩, hab⟩ := p
  obtain ⟨⟨c, d⟩, hcd⟩ := q
  simp only at hab hcd
  rw [nilLinear_rootVector, nilLinear_rootVector, Ring.lie_def]
  have hval : (⁅rootVector ⟨(a, b), hab⟩, rootVector ⟨(c, d), hcd⟩⁆ : upperNilpotent n).val =
      Matrix.single a b (1 : ℂ) * Matrix.single c d 1 -
        Matrix.single c d (1 : ℂ) * Matrix.single a b 1 := by
    rw [LieSubalgebra.coe_bracket, Ring.lie_def]
    rfl
  by_cases hbc : b = c
  · subst hbc
    have hda : d ≠ a := (hab.trans hcd).ne'
    have h1 : (⁅rootVector ⟨(a, b), hab⟩, rootVector ⟨(b, d), hcd⟩⁆ : upperNilpotent n).val =
        Matrix.single a d 1 := by
      rw [hval, Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne _ _ _ _ hda,
        sub_zero, mul_one]
    rw [hρ.nilLinear_of_val_eq _ ⟨(a, d), hab.trans hcd⟩ h1]
    exact (hρ.borelLie_bracket hab hcd).symm
  · by_cases hda : d = a
    · subst hda
      have h1 : (-⁅rootVector ⟨(d, b), hab⟩, rootVector ⟨(c, d), hcd⟩⁆ : upperNilpotent n).val =
          Matrix.single c b 1 := by
        rw [show (-⁅rootVector ⟨(d, b), hab⟩, rootVector ⟨(c, d), hcd⟩⁆ : upperNilpotent n).val =
          -(⁅rootVector ⟨(d, b), hab⟩, rootVector ⟨(c, d), hcd⟩⁆ : upperNilpotent n).val from rfl,
          hval, Matrix.single_mul_single_of_ne _ _ _ _ hbc,
          Matrix.single_mul_single_same, zero_sub, neg_neg, mul_one]
      have h2 := hρ.nilLinear_of_val_eq _ ⟨(c, b), hcd.trans hab⟩ h1
      rw [map_neg, neg_eq_iff_eq_neg] at h2
      rw [h2, ← hρ.borelLie_bracket hcd hab, neg_sub]
    · have h1 : (⁅rootVector ⟨(a, b), hab⟩, rootVector ⟨(c, d), hcd⟩⁆ :
          upperNilpotent n) = 0 := by
        apply Subtype.ext
        rw [hval, Matrix.single_mul_single_of_ne _ _ _ _ hbc,
          Matrix.single_mul_single_of_ne _ _ _ _ hda, sub_zero]
        rfl
      rw [h1, map_zero, hρ.borelLie_comm hab hcd hbc (Ne.symm hda), sub_self]

/-- **The `𝔫⁺`-action** `X ↦ Σ_{a<b} X_ab D_ab`, a Lie algebra map. -/
def nil : upperNilpotent n →ₗ⁅ℂ⁆ Module.End ℂ W :=
  { hρ.nilLinear with
    map_lie' := fun {X Y} => by
      change hρ.nilLinear ⁅X, Y⁆ = ⁅hρ.nilLinear X, hρ.nilLinear Y⁆
      rw [upperNilpotent_eq_sum X, upperNilpotent_eq_sum Y]
      simp only [sum_lie, lie_sum, smul_lie, lie_smul, map_sum, map_smul]
      refine Finset.sum_congr rfl fun p _ => congrArg _ (Finset.sum_congr rfl fun q _ => ?_)
      rw [hρ.nilLinear_lie_rootVector q p] }

theorem nil_apply (X : upperNilpotent n) : hρ.nil X = hρ.nilLinear X :=
  rfl

theorem nil_rootVector (r : PositiveRoot n) : hρ.nil (rootVector r) = hρ.borelLie r.property :=
  hρ.nilLinear_rootVector r

/-! ### The associated `BModule` -/

theorem rho_borelTorus_borelLie (t : DiagonalTorus n) (r : PositiveRoot n) (w : W) :
    ρ (borelTorus ℂ n t) (hρ.borelLie r.property w) =
      rootScalar t r.val.1 r.val.2 • hρ.borelLie r.property (ρ (borelTorus ℂ n t) w) := by
  have h := congrArg (fun T : Module.End ℂ W => T (ρ (borelTorus ℂ n t) w))
    (hρ.conj_borelLie r.property t)
  simp only [Module.End.mul_apply, ← Module.End.mul_apply (ρ (borelTorus ℂ n t)⁻¹),
    ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply, LinearMap.smul_apply] at h
  exact h

/-- **The `BModule` of a rational representation of `B`**. -/
def toBModule : BModule n where
  carrier := W
  instFiniteDimensional := hρ.finiteDimensional
  nil := hρ.nil
  torus := ρ.comp (borelTorus ℂ n)
  torus_nil t X v := by
    change ρ (borelTorus ℂ n t) (hρ.nilLinear X v) =
      hρ.nilLinear (torusLie t X) (ρ (borelTorus ℂ n t) v)
    rw [nilLinear_apply, nilLinear_apply, LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [LinearMap.smul_apply, LinearMap.smul_apply, map_smul, rho_borelTorus_borelLie, smul_smul,
      mul_comm]
    rfl
  weightDiagonal := by
    rw [IsWeightDiagonal]
    simp only [torusWeightSpace_eq]
    exact hρ.iSup_borelWeightSpace_eq_top

@[simp] theorem toBModule_nil (X : upperNilpotent n) (w : W) :
    hρ.toBModule.nil X w = hρ.nilLinear X w :=
  rfl

@[simp] theorem toBModule_torus (t : DiagonalTorus n) (w : W) :
    hρ.toBModule.torus t w = ρ (borelTorus ℂ n t) w :=
  rfl

theorem toBModule_nil_rootVector (r : PositiveRoot n) (w : W) :
    hρ.toBModule.nil (rootVector r) w = hρ.borelLie r.property w := by
  rw [toBModule_nil, nilLinear_rootVector]

/-! ### Subspaces -/

theorem forall_nil_mem_iff (U : Submodule ℂ W) :
    (∀ X, ∀ u ∈ U, hρ.toBModule.nil X u ∈ U) ↔
      ∀ (a b : Fin n) (hab : a < b), ∀ u ∈ U, hρ.borelLie hab u ∈ U := by
  constructor
  · intro h a b hab u hu
    have := h (rootVector ⟨(a, b), hab⟩) u hu
    rwa [toBModule_nil_rootVector] at this
  · intro h X u hu
    rw [toBModule_nil, nilLinear_apply, LinearMap.sum_apply]
    exact U.sum_mem fun p _ => U.smul_mem _ (h _ _ p.property u hu)

/-- **`B`-stable subspaces are the `B`-submodules of the `BModule`.** -/
theorem forall_mem_iff_bModule (U : Submodule ℂ W) :
    (∀ g, ∀ u ∈ U, ρ g u ∈ U) ↔
      (∀ X, ∀ u ∈ U, hρ.toBModule.nil X u ∈ U) ∧ (∀ t, ∀ u ∈ U, hρ.toBModule.torus t u ∈ U) := by
  rw [hρ.forall_mem_iff, forall_nil_mem_iff, and_comm]
  rfl

/-- The `B`-submodule of a subrepresentation. -/
def toBSubmodule (U : Subrepresentation ρ) : BSubmodule hρ.toBModule where
  toSubmodule := U.toSubmodule
  nil_mem := ((hρ.forall_mem_iff_bModule U.toSubmodule).mp
    fun g _ hu => U.apply_mem_toSubmodule g hu).1
  torus_mem := ((hρ.forall_mem_iff_bModule U.toSubmodule).mp
    fun g _ hu => U.apply_mem_toSubmodule g hu).2

/-- The subrepresentation of a `B`-submodule. -/
def ofBSubmodule (S : BSubmodule hρ.toBModule) : Subrepresentation ρ where
  toSubmodule := S.toSubmodule
  apply_mem_toSubmodule g _ hv :=
    (hρ.forall_mem_iff_bModule S.toSubmodule).mpr ⟨S.nil_mem, S.torus_mem⟩ g _ hv

/-- **Subrepresentations of `ρ` are the `B`-submodules of its `BModule`.** -/
def subrepresentationOrderIso : Subrepresentation ρ ≃o BSubmodule hρ.toBModule where
  toFun := hρ.toBSubmodule
  invFun := hρ.ofBSubmodule
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

/-! ### Maps -/

variable {V : Type} [AddCommGroup V] [Module ℂ V] {σ : Representation ℂ (borel ℂ n) V}
  (hσ : IsRationalBorelRep σ)

theorem map_nilLinear_of (f : W →ₗ[ℂ] V)
    (h : ∀ (a b : Fin n) (hab : a < b) (w : W), f (hρ.borelLie hab w) = hσ.borelLie hab (f w))
    (X : upperNilpotent n) (w : W) : f (hρ.nilLinear X w) = hσ.nilLinear X (f w) := by
  rw [nilLinear_apply, nilLinear_apply, LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun p _ => by
    rw [LinearMap.smul_apply, LinearMap.smul_apply, map_smul, h _ _ p.property]

/-- **`B`-intertwiners are the `B`-module homomorphisms.** -/
theorem forall_intertwining_iff_bModule (f : W →ₗ[ℂ] V) :
    (∀ g w, f (ρ g w) = σ g (f w)) ↔
      (∀ X w, f (hρ.toBModule.nil X w) = hσ.toBModule.nil X (f w)) ∧
        ∀ t w, f (hρ.toBModule.torus t w) = hσ.toBModule.torus t (f w) := by
  rw [hρ.forall_intertwining_iff hσ, and_comm]
  refine and_congr ⟨fun h X w => ?_, fun h a b hab w => ?_⟩ Iff.rfl
  · exact hρ.map_nilLinear_of hσ f h X w
  · have := h (rootVector ⟨(a, b), hab⟩) w
    rwa [toBModule_nil_rootVector, toBModule_nil_rootVector] at this

/-- The `B`-module homomorphism of an intertwining map. -/
def toHom (f : ρ.IntertwiningMap σ) : BModule.Hom hρ.toBModule hσ.toBModule where
  toLinearMap := f.toLinearMap
  map_nil := ((hρ.forall_intertwining_iff_bModule hσ f.toLinearMap).mp
    fun g w => LinearMap.congr_fun (f.isIntertwining' g) w).1
  map_torus := ((hρ.forall_intertwining_iff_bModule hσ f.toLinearMap).mp
    fun g w => LinearMap.congr_fun (f.isIntertwining' g) w).2

/-- The intertwining map of a `B`-module homomorphism. -/
def ofHom (φ : BModule.Hom hρ.toBModule hσ.toBModule) : ρ.IntertwiningMap σ where
  toLinearMap := φ.toLinearMap
  isIntertwining' g := LinearMap.ext fun w =>
    (hρ.forall_intertwining_iff_bModule hσ φ.toLinearMap).mpr ⟨φ.map_nil, φ.map_torus⟩ g w

/-- **Intertwining maps of rational `B`-representations are the `BModule`
homomorphisms.** -/
def homEquiv : ρ.IntertwiningMap σ ≃ BModule.Hom hρ.toBModule hσ.toBModule where
  toFun := hρ.toHom hσ
  invFun := hρ.ofHom hσ
  left_inv f := by cases f; rfl
  right_inv φ := by cases φ; rfl

theorem homEquiv_toLinearMap (f : ρ.IntertwiningMap σ) :
    (hρ.homEquiv hσ f).toLinearMap = f.toLinearMap :=
  rfl

/-- The `B`-module isomorphism of an equivalence of representations. -/
def toIso (e : ρ.Equiv σ) : hρ.toBModule ≃ᴮ hσ.toBModule where
  toLinearEquiv := e.toLinearEquiv
  map_nil := (hρ.toHom hσ e.toIntertwiningMap).map_nil
  map_torus := (hρ.toHom hσ e.toIntertwiningMap).map_torus

/-- The equivalence of representations of a `B`-module isomorphism. -/
def ofIso (e : hρ.toBModule ≃ᴮ hσ.toBModule) : ρ.Equiv σ where
  toLinearMap := e.toLinearEquiv.toLinearMap
  isIntertwining' g := LinearMap.ext fun w =>
    (hρ.forall_intertwining_iff_bModule hσ e.toLinearEquiv.toLinearMap).mpr
      ⟨e.map_nil, e.map_torus⟩ g w
  invFun := e.toLinearEquiv.symm
  left_inv := e.toLinearEquiv.left_inv
  right_inv := e.toLinearEquiv.right_inv

/-- **Equivalences of rational `B`-representations are the `BModule` isomorphisms.** -/
def isoEquiv : ρ.Equiv σ ≃ (hρ.toBModule ≃ᴮ hσ.toBModule) where
  toFun := hρ.toIso hσ
  invFun := hρ.ofIso hσ
  left_inv e := by cases e; rfl
  right_inv e := by cases e; rfl

end IsRationalBorelRep

end

end GLRep
