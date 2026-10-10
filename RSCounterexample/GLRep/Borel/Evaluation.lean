import RSCounterexample.GLRep.Borel.Regular

/-!
# Evaluation of regular functions on `GL_n` and vanishing ideals

An element `f` of the coordinate ring `𝒪(GL_n) = K[x_ij][det⁻¹]` (`FlagVarieties.GLCoord K n`) is
evaluated at a point `g ∈ GL_n(K)` by `GLRep.glEval g`, a `K`-algebra homomorphism with
`x_ij ↦ g_ij`. Translations become translations of the argument:

* `glEval g (leftTranslHom h f) = glEval (h⁻¹ g) f` (`GLRep.glEval_leftTranslHom`);
* `glEval g (rightTranslHom h f) = glEval (g h) f` (`GLRep.glEval_rightTranslHom`).

Over an infinite field a regular function is determined by its values
(`GLRep.glEvalFun_injective`).

The **vanishing ideal** of a set `Z ⊆ GL_n(K)` (`GLRep.vanishingIdeal Z`) is stable under left
or right translation by `B` when `Z` is (`GLRep.isLeftBorelStable_vanishingIdeal`,
`GLRep.isRightBorelStable_vanishingIdeal`). A class `[t] ∈ 𝒪(GL_n)/I(Z)` is `(B, η)`-semi-invariant
exactly when `t(g b) = η(b)⁻¹ t(g)` for all `g ∈ Z` and `b ∈ B`
(`GLRep.mk_mem_borelSemiInvariants_vanishingIdeal_iff`). For `Z` the preimage in `GL_n(K)` of a
union of Schubert varieties, this describes the sections of `𝓛(η)` over the union by values.
-/

namespace GLRep

open MvPolynomial TauCeti

noncomputable section

/-! ### Evaluation at a point -/

section Eval

variable {K : Type*} [CommRing K] {n : ℕ}

theorem isUnit_aeval_genericDet (g : GL (Fin n) K) :
    IsUnit ((aeval fun p : Fin n × Fin n => (g : Matrix (Fin n) (Fin n) K) p.1 p.2)
      (genericDet K n)) := by
  rw [AlgHom.map_det, Matrix.mvPolynomialX_mapMatrix_aeval K]
  exact Matrix.isUnits_det_units g

/-- **Evaluation** of regular functions on `GL_n` at a point `g ∈ GL_n(K)`: `x_ij ↦ g_ij`. -/
def glEval (g : GL (Fin n) K) : GLCoord K n →ₐ[K] K :=
  IsLocalization.Away.liftAlgHom (genericDet K n) (isUnit_aeval_genericDet g)

theorem glEval_algebraMap (g : GL (Fin n) K) (p : MvPolynomial (Fin n × Fin n) K) :
    glEval g (algebraMap _ _ p) =
      aeval (fun q : Fin n × Fin n => (g : Matrix (Fin n) (Fin n) K) q.1 q.2) p :=
  IsLocalization.Away.lift_eq (genericDet K n) (isUnit_aeval_genericDet g) p

@[simp]
theorem glEval_glX (g : GL (Fin n) K) (i j : Fin n) :
    glEval g (glX i j) = (g : Matrix (Fin n) (Fin n) K) i j := by
  rw [glX, glEval_algebraMap, aeval_X]

theorem glEval_genericDet (g : GL (Fin n) K) :
    glEval g (algebraMap _ _ (genericDet K n)) = (g : Matrix (Fin n) (Fin n) K).det := by
  rw [glEval_algebraMap, AlgHom.map_det, Matrix.mvPolynomialX_mapMatrix_aeval K]

/-- Two algebra homomorphisms out of `𝒪(GL_n)` agreeing on the coordinates `x_ij` are equal. -/
theorem algHom_ext_glX {T : Type*} [CommRing T] [Algebra K T]
    {φ ψ : GLCoord K n →ₐ[K] T} (h : ∀ i j, φ (glX i j) = ψ (glX i j)) : φ = ψ := by
  apply GeneralLinear.algHom_ext_away
  apply MvPolynomial.algHom_ext
  rintro ⟨i, j⟩
  exact h i j

/-- **Evaluation after left translation**: `(h · f)(g) = f(h⁻¹ g)`. -/
theorem glEval_leftTranslHom (g h : GL (Fin n) K) (f : GLCoord K n) :
    glEval g (leftTranslHom K n h f) = glEval (h⁻¹ * g) f := by
  have : (glEval g).comp (leftTranslHom K n h) = glEval (h⁻¹ * g) := by
    refine algHom_ext_glX fun i j => ?_
    rw [AlgHom.comp_apply, leftTranslHom_glX, map_sum, glEval_glX, Units.val_mul,
      Matrix.mul_apply]
    simp only [map_smul, glEval_glX, smul_eq_mul]
  exact AlgHom.congr_fun this f

/-- **Evaluation after right translation**: `(h · f)(g) = f(g h)`. -/
theorem glEval_rightTranslHom (g h : GL (Fin n) K) (f : GLCoord K n) :
    glEval g (rightTranslHom K n h f) = glEval (g * h) f := by
  have : (glEval g).comp (rightTranslHom K n h) = glEval (g * h) := by
    refine algHom_ext_glX fun i j => ?_
    rw [AlgHom.comp_apply, rightTranslHom_glX, map_sum, glEval_glX, Units.val_mul,
      Matrix.mul_apply]
    simp only [map_smul, glEval_glX, smul_eq_mul, mul_comm]
  exact AlgHom.congr_fun this f

variable (K n) in
/-- Regular functions on `GL_n` as functions on `GL_n(K)`. -/
def glEvalFun : GLCoord K n →ₐ[K] (GL (Fin n) K → K) :=
  AlgHom.pi fun g => glEval g

@[simp]
theorem glEvalFun_apply (f : GLCoord K n) (g : GL (Fin n) K) :
    glEvalFun K n f g = glEval g f :=
  rfl

end Eval

/-! ### Torus weights of the coordinates -/

section TorusWeights

variable {K : Type*} [Field K] {n : ℕ}

/-- Left translation by `t ∈ T` scales `x_ij` by `tᵢ⁻¹`: the coordinate `x_ij` has weight
`−eᵢ`. -/
theorem leftTranslHom_borelTorus_glX (t : Fin n → Kˣ) (i j : Fin n) :
    leftTranslHom K n (borelTorus K n t : GL (Fin n) K) (glX i j) =
      (((t i)⁻¹ : Kˣ) : K) • glX i j := by
  rw [leftTranslHom_glX, coe_borelTorus, ← map_inv,
    Finset.sum_eq_single i
      (fun k _ hk => by rw [diagGL_apply, ite_eq_right (Ne.symm hk), zero_smul]) (by simp),
    diagGL_apply, ite_eq_left rfl, Pi.inv_apply]

/-- Right translation by `t ∈ T` scales `x_ij` by `tⱼ`. -/
theorem rightTranslHom_borelTorus_glX (t : Fin n → Kˣ) (i j : Fin n) :
    rightTranslHom K n (borelTorus K n t : GL (Fin n) K) (glX i j) =
      ((t j : Kˣ) : K) • glX i j := by
  rw [rightTranslHom_glX, coe_borelTorus,
    Finset.sum_eq_single j
      (fun k _ hk => by rw [diagGL_apply, ite_eq_right hk, zero_smul]) (by simp),
    diagGL_apply, ite_eq_left rfl]

/-- Left translation by `t ∈ T` scales `det⁻¹` by `t₁ ⋯ tₙ`. -/
theorem leftTranslHom_borelTorus_glDetInv (t : Fin n → Kˣ) :
    leftTranslHom K n (borelTorus K n t : GL (Fin n) K) (glDetInv K n) =
      ((∏ i, t i : Kˣ) : K) • glDetInv K n := by
  rw [leftTranslHom_glDetInv, ← Matrix.GeneralLinearGroup.val_det_apply, det_borel,
    borelDiag_borelTorus]

end TorusWeights

/-! ### Regular functions are determined by their values -/

section Injective

variable {K : Type*} [Field K] [Infinite K] {n : ℕ}

/-- **Over an infinite field, a regular function on `GL_n` vanishing on `GL_n(K)` is zero.** -/
theorem eq_zero_of_forall_glEval_eq_zero {f : GLCoord K n}
    (hf : ∀ g : GL (Fin n) K, glEval g f = 0) : f = 0 := by
  obtain ⟨m, a, hz⟩ := IsLocalization.Away.surj (genericDet K n) f
  have ha : a = 0 := by
    refine isZariskiDense_glCoord K n a fun g => ?_
    have := congrArg (glEval g) hz
    rw [map_mul, hf g, zero_mul, glEval_algebraMap] at this
    exact this.symm
  have hunit : IsUnit (algebraMap _ (GLCoord K n) (genericDet K n) ^ m) :=
    (IsLocalization.Away.algebraMap_isUnit _).pow m
  rw [ha, map_zero] at hz
  exact (hunit.mul_left_eq_zero).mp hz

/-- **Over an infinite field, regular functions on `GL_n` are determined by their values on
`GL_n(K)`.** -/
theorem glEvalFun_injective : Function.Injective (glEvalFun K n) := by
  refine (injective_iff_map_eq_zero (glEvalFun K n)).mpr fun f hf => ?_
  exact eq_zero_of_forall_glEval_eq_zero fun g => congrFun hf g

end Injective

/-! ### Vanishing ideals -/

section Vanishing

variable {K : Type*} [Field K] {n : ℕ}

/-- The **vanishing ideal** of a set `Z ⊆ GL_n(K)`: the regular functions vanishing on `Z`. -/
def vanishingIdeal (Z : Set (GL (Fin n) K)) : Ideal (GLCoord K n) where
  carrier := {f | ∀ g ∈ Z, glEval g f = 0}
  add_mem' {f f'} hf hf' g hg := by rw [map_add, hf g hg, hf' g hg, add_zero]
  zero_mem' g _ := map_zero _
  smul_mem' c f hf g hg := by rw [smul_eq_mul, map_mul, hf g hg, mul_zero]

theorem mem_vanishingIdeal {Z : Set (GL (Fin n) K)} {f : GLCoord K n} :
    f ∈ vanishingIdeal Z ↔ ∀ g ∈ Z, glEval g f = 0 :=
  Iff.rfl

/-- The vanishing ideal of a set stable under left multiplication by `B` is stable under left
translation by `B`. -/
theorem isLeftBorelStable_vanishingIdeal {Z : Set (GL (Fin n) K)}
    (hZ : ∀ g ∈ Z, ∀ b ∈ borel K n, b * g ∈ Z) : IsLeftBorelStable (vanishingIdeal Z) :=
  fun b hb f hf g hg => by
    rw [glEval_leftTranslHom]
    exact hf _ (hZ g hg _ ((borel K n).inv_mem hb))

/-- The vanishing ideal of a set stable under right multiplication by `B` is stable under right
translation by `B`. -/
theorem isRightBorelStable_vanishingIdeal {Z : Set (GL (Fin n) K)}
    (hZ : ∀ g ∈ Z, ∀ b ∈ borel K n, g * b ∈ Z) : IsRightBorelStable (vanishingIdeal Z) :=
  fun b hb f hf g hg => by
    rw [glEval_rightTranslHom]
    exact hf _ (hZ g hg b hb)

/-- **Semi-invariants modulo a vanishing ideal are described by values**: the class of `t` in
`𝒪(GL_n)/I(Z)` lies in `(𝒪(GL_n)/I(Z))^{(B, η)}` exactly when `t(g b) = η(b)⁻¹ t(g)` for all
`g ∈ Z` and `b ∈ B`. -/
theorem mk_mem_borelSemiInvariants_vanishingIdeal_iff {Z : Set (GL (Fin n) K)}
    (hR : IsRightBorelStable (vanishingIdeal Z)) (η : Fin n → ℤ) (t : GLCoord K n) :
    Ideal.Quotient.mk _ t ∈ borelSemiInvariants (vanishingIdeal Z) hR η ↔
      ∀ g ∈ Z, ∀ b : borel K n,
        glEval (g * (b : GL (Fin n) K)) t = (((borelChar K n η b)⁻¹ : Kˣ) : K) * glEval g t := by
  rw [mem_borelSemiInvariants]
  have key : ∀ b : borel K n,
      quotRightTranslHom (vanishingIdeal Z) hR b (Ideal.Quotient.mk _ t) =
          (((borelChar K n η b)⁻¹ : Kˣ) : K) • Ideal.Quotient.mk (vanishingIdeal Z) t ↔
        ∀ g ∈ Z, glEval (g * (b : GL (Fin n) K)) t =
          (((borelChar K n η b)⁻¹ : Kˣ) : K) * glEval g t := by
    intro b
    change Ideal.Quotient.mk _ (rightTranslHom K n b t) = _ ↔ _
    rw [← Ideal.Quotient.mkₐ_eq_mk K, ← map_smul, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq,
      mem_vanishingIdeal]
    refine forall₂_congr fun g _ => ?_
    rw [map_sub, glEval_rightTranslHom, map_smul, smul_eq_mul, sub_eq_zero]
  simp only [key]
  exact ⟨fun h g hg b => h b g hg, fun h b g hg => h g hg b⟩

end Vanishing

end

end GLRep
