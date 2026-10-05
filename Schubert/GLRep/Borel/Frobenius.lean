import Schubert.GLRep.Borel.GLRegular

/-!
# Frobenius reciprocity for `ind_B^G(η)`

Over an infinite field, evaluation identifies the coordinate ring `𝒪(GL_n)` with the regular
functions on `GL_n(K)` (`GLRep.glEvalEquiv`). For a rational representation `V` of `GL_n(K)` and a
weight `η`, **Frobenius reciprocity** identifies the `GL_n(K)`-maps `V → ind_B^G(η)` with the
`B`-maps `V → K_η` (`GLRep.indBorelFrobeniusEquiv`): a `B`-map `φ` corresponds to
`v ↦ (g ↦ φ(g⁻¹ · v))`, and a `GL_n(K)`-map to its composite with evaluation at `1`
(`GLRep.indBorelEvalOne`). Here `ind_B^G(η) = 𝒪(GL_n)^{(B, η)}` is the space of global sections
of `𝓛(η)` on `G/B` (`GLRep.indBorelRep`).
-/

namespace GLRep

open MvPolynomial TauCeti

noncomputable section

/-! ### Evaluation is an isomorphism onto the regular functions -/

section Equiv

variable {K : Type*} [Field K] {n : ℕ}

theorem glEval_glDetInv (g : GL (Fin n) K) :
    glEval g (glDetInv K n) = (((Matrix.GeneralLinearGroup.det g)⁻¹ : Kˣ) : K) := by
  have h := congrArg (glEval g) (algebraMap_genericDet_mul_glDetInv (K := K) (n := n))
  rw [map_mul, glEval_genericDet, map_one, ← Matrix.GeneralLinearGroup.val_det_apply] at h
  rw [← one_mul (glEval g _), ← Units.inv_mul (Matrix.GeneralLinearGroup.det g), mul_assoc, h,
    mul_one]

/-- **The values of the elements of `𝒪(GL_n)` are exactly the regular functions.** -/
theorem range_glEvalFun : (glEvalFun K n).range = glRegularFunctions K n := by
  apply le_antisymm
  · rw [← Algebra.map_top, ← adjoin_glX_glDetInv, AlgHom.map_adjoin, Algebra.adjoin_le_iff]
    rintro _ ⟨r, (⟨p, rfl⟩ | hr), rfl⟩
    · have : glEvalFun K n (glX p.1 p.2) =
          fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K) p.1 p.2 :=
        funext fun g => glEval_glX g p.1 p.2
      rw [this]
      exact entry_mem_glRegularFunctions p.1 p.2
    · rw [Set.mem_singleton_iff] at hr
      subst hr
      have : glEvalFun K n (glDetInv K n) =
          fun g : GL (Fin n) K => (((Matrix.GeneralLinearGroup.det g)⁻¹ : Kˣ) : K) :=
        funext fun g => glEval_glDetInv g
      rw [this]
      exact detInv_mem_glRegularFunctions
  · refine coordFunctions_le fun s => ?_
    rcases s with p | u
    · exact ⟨glX p.1 p.2, funext fun g => glEval_glX g p.1 p.2⟩
    · exact ⟨glDetInv K n, funext fun g => glEval_glDetInv g⟩

variable [Infinite K]

variable (K n) in
/-- **`𝒪(GL_n)` is the algebra of regular functions on `GL_n(K)`**, over an infinite field. -/
def glEvalEquiv : GLCoord K n ≃ₐ[K] glRegularFunctions K n :=
  (AlgEquiv.ofInjective (glEvalFun K n) glEvalFun_injective).trans
    (Subalgebra.equivOfEq _ _ range_glEvalFun)

@[simp]
theorem glEvalEquiv_apply_apply (f : GLCoord K n) (g : GL (Fin n) K) :
    (glEvalEquiv K n f : GL (Fin n) K → K) g = glEval g f :=
  rfl

theorem glEval_glEvalEquiv_symm (F : glRegularFunctions K n) (g : GL (Fin n) K) :
    glEval g ((glEvalEquiv K n).symm F) = (F : GL (Fin n) K → K) g := by
  rw [← glEvalEquiv_apply_apply, AlgEquiv.apply_symm_apply]

/-- Two elements of `𝒪(GL_n)` with the same values are equal. -/
theorem glCoord_ext {f f' : GLCoord K n} (h : ∀ g, glEval g f = glEval g f') : f = f' :=
  glEvalFun_injective (funext h)

omit [Infinite K] in
/-- Inversion maps regular functions to regular functions. -/
theorem comp_inv_mem_glRegularFunctions {F : GL (Fin n) K → K}
    (hF : F ∈ glRegularFunctions K n) : (fun g => F g⁻¹) ∈ glRegularFunctions K n := by
  refine comp_mem_of_forall_coord_mem (fun g : GL (Fin n) K => g⁻¹) (fun s => ?_) hF
  rcases s with p | u
  · exact inv_apply_mem_glRegularFunctions p.1 p.2
  · have : (fun g : GL (Fin n) K => glRationalCoord K n g⁻¹ (Sum.inr u)) =
        fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K).det := by
      funext g
      change (((Matrix.GeneralLinearGroup.det g⁻¹)⁻¹ : Kˣ) : K) = _
      rw [map_inv, inv_inv, Matrix.GeneralLinearGroup.val_det_apply]
    rw [this]
    exact det_mem_glRegularFunctions

end Equiv

/-! ### Frobenius reciprocity -/

section Frobenius

variable {K : Type*} [Field K] {n : ℕ} (η : Fin n → ℤ)

theorem glEval_mul_of_mem_indBorelSubrep {f : GLCoord K n}
    (hf : f ∈ (indBorelSubrep K n η).toSubmodule) (g : GL (Fin n) K) (b : borel K n) :
    glEval (g * (b : GL (Fin n) K)) f = (((borelChar K n η b)⁻¹ : Kˣ) : K) * glEval g f := by
  rw [← glEval_rightTranslHom, (mem_indBorelSubrep.mp hf) b, map_smul, smul_eq_mul]

/-- **Evaluation at `1`**, a `B`-map `ind_B^G(η) → K_η`. -/
def indBorelEvalOne :
    Representation.IntertwiningMap ((indBorelRep K n η).comp (borel K n).subtype)
      (borelCharRep K n η) where
  toFun f := glEval 1 (f : GLCoord K n)
  map_add' f f' := map_add _ _ _
  map_smul' c f := map_smul _ _ _
  isIntertwining' b := LinearMap.ext fun f => by
    change glEval 1 (leftTranslHom K n (b : GL (Fin n) K) f) =
      (borelChar K n η b : K) * glEval 1 (f : GLCoord K n)
    rw [glEval_leftTranslHom, mul_one, ← one_mul ((b : GL (Fin n) K)⁻¹), ← Subgroup.coe_inv,
      glEval_mul_of_mem_indBorelSubrep η f.2, map_inv, inv_inv]

variable [Infinite K]
variable {V : Type*} [AddCommGroup V] [Module K V] {ρ : Representation K (GL (Fin n) K) V}

/-- The function `g ↦ φ(g⁻¹ · v)` attached to `v` by a `B`-map `φ : V → K_η`, as an element of
`ind_B^G(η)`. -/
def indBorelFrobeniusMap (hρ : IsRationalRep ρ)
    (φ : Representation.IntertwiningMap (ρ.comp (borel K n).subtype) (borelCharRep K n η))
    (v : V) : (indBorelSubrep K n η).toSubmodule :=
  ⟨(glEvalEquiv K n).symm ⟨fun g => φ (ρ g⁻¹ v), comp_inv_mem_glRegularFunctions
      (hρ.hasCoeffsIn_glRegularFunctions.coeff_mem (φ.toLinearMap) v)⟩, by
    refine mem_indBorelSubrep.mpr fun b => glCoord_ext fun g => ?_
    rw [glEval_rightTranslHom, map_smul, smul_eq_mul, glEval_glEvalEquiv_symm,
      glEval_glEvalEquiv_symm]
    change φ (ρ (g * b)⁻¹ v) = _ * φ (ρ g⁻¹ v)
    have := φ.isIntertwining _ _ b⁻¹ (ρ g⁻¹ v)
    change φ (ρ (b⁻¹ : borel K n) (ρ g⁻¹ v)) = (borelChar K n η b⁻¹ : K) * φ (ρ g⁻¹ v) at this
    rw [mul_inv_rev, map_mul, Module.End.mul_apply, ← Subgroup.coe_inv, this, map_inv]⟩

theorem glEval_indBorelFrobeniusMap (hρ : IsRationalRep ρ)
    (φ : Representation.IntertwiningMap (ρ.comp (borel K n).subtype) (borelCharRep K n η))
    (v : V) (g : GL (Fin n) K) :
    glEval g (indBorelFrobeniusMap η hρ φ v : GLCoord K n) = φ (ρ g⁻¹ v) :=
  glEval_glEvalEquiv_symm _ g

omit [Infinite K] in
theorem coe_indBorelRep_apply (g : GL (Fin n) K) (f : (indBorelSubrep K n η).toSubmodule) :
    (indBorelRep K n η g f : GLCoord K n) = leftTranslHom K n g f :=
  rfl

/-- The `GL_n(K)`-map `V → ind_B^G(η)` attached to a `B`-map `φ : V → K_η`. -/
def indBorelFrobeniusInverse (hρ : IsRationalRep ρ)
    (φ : Representation.IntertwiningMap (ρ.comp (borel K n).subtype) (borelCharRep K n η)) :
    ρ.IntertwiningMap (indBorelRep K n η) where
  toFun := indBorelFrobeniusMap η hρ φ
  map_add' v w := Subtype.ext <| glCoord_ext fun g => by
    simp only [glEval_indBorelFrobeniusMap, Submodule.coe_add, map_add]
  map_smul' c v := Subtype.ext <| glCoord_ext fun g => by
    simp only [glEval_indBorelFrobeniusMap, Submodule.coe_smul, map_smul, RingHom.id_apply]
  isIntertwining' h := LinearMap.ext fun v => Subtype.ext <| glCoord_ext fun g => by
    change glEval g (indBorelFrobeniusMap η hρ φ (ρ h v) : GLCoord K n) =
      glEval g (leftTranslHom K n h (indBorelFrobeniusMap η hρ φ v : GLCoord K n))
    rw [glEval_leftTranslHom, glEval_indBorelFrobeniusMap, glEval_indBorelFrobeniusMap,
      mul_inv_rev, inv_inv, map_mul, Module.End.mul_apply]

theorem glEval_indBorelFrobeniusInverse (hρ : IsRationalRep ρ)
    (φ : Representation.IntertwiningMap (ρ.comp (borel K n).subtype) (borelCharRep K n η))
    (v : V) (g : GL (Fin n) K) :
    glEval g (indBorelFrobeniusInverse η hρ φ v : GLCoord K n) = φ (ρ g⁻¹ v) :=
  glEval_indBorelFrobeniusMap η hρ φ v g

/-- The `B`-map `V → K_η` attached to a `GL_n(K)`-map `Φ : V → ind_B^G(η)`: evaluation at `1`. -/
def indBorelFrobeniusForward (Φ : ρ.IntertwiningMap (indBorelRep K n η)) :
    Representation.IntertwiningMap (ρ.comp (borel K n).subtype) (borelCharRep K n η) :=
  (indBorelEvalOne η).comp ⟨Φ.toLinearMap, fun b => Φ.isIntertwining' (b : GL (Fin n) K)⟩

omit [Infinite K] in
theorem indBorelFrobeniusForward_apply (Φ : ρ.IntertwiningMap (indBorelRep K n η)) (v : V) :
    indBorelFrobeniusForward η Φ v = glEval 1 (Φ v : GLCoord K n) :=
  rfl

/-- **Frobenius reciprocity**: for a rational representation `V` of `GL_n(K)`, the
`GL_n(K)`-maps `V → ind_B^G(η)` are the `B`-maps `V → K_η`, by evaluation at `1`. -/
def indBorelFrobeniusEquiv (hρ : IsRationalRep ρ) :
    ρ.IntertwiningMap (indBorelRep K n η) ≃ₗ[K]
      Representation.IntertwiningMap (ρ.comp (borel K n).subtype) (borelCharRep K n η) where
  toFun := indBorelFrobeniusForward η
  map_add' Φ Ψ := Representation.IntertwiningMap.ext (LinearMap.ext fun v => by
    change glEval 1 ((Φ v + Ψ v : (indBorelSubrep K n η).toSubmodule) : GLCoord K n) =
      glEval 1 (Φ v : GLCoord K n) + glEval 1 (Ψ v : GLCoord K n)
    rw [Submodule.coe_add, map_add])
  map_smul' c Φ := Representation.IntertwiningMap.ext (LinearMap.ext fun v => by
    change glEval 1 ((c • Φ) v : GLCoord K n) = c • glEval 1 (Φ v : GLCoord K n)
    rw [Representation.IntertwiningMap.smul_apply, Submodule.coe_smul, map_smul])
  invFun := indBorelFrobeniusInverse η hρ
  left_inv Φ := by
    refine Representation.IntertwiningMap.ext (LinearMap.ext fun v => ?_)
    refine Subtype.ext (glCoord_ext fun g => ?_)
    change glEval g (indBorelFrobeniusInverse η hρ (indBorelFrobeniusForward η Φ) v : GLCoord K n) =
      glEval g (Φ v : GLCoord K n)
    rw [glEval_indBorelFrobeniusInverse, indBorelFrobeniusForward_apply, Φ.isIntertwining,
      coe_indBorelRep_apply, glEval_leftTranslHom, inv_inv, mul_one]
  right_inv φ := by
    refine Representation.IntertwiningMap.ext (LinearMap.ext fun v => ?_)
    change indBorelFrobeniusForward η (indBorelFrobeniusInverse η hρ φ) v = φ v
    rw [indBorelFrobeniusForward_apply, glEval_indBorelFrobeniusInverse, inv_one, map_one,
      Module.End.one_apply]

end Frobenius

end

end GLRep
