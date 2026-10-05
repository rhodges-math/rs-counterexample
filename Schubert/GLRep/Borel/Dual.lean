import Schubert.GLRep.Borel.Frobenius

/-!
# Duals and the inverse-transpose twist

For a representation `ρ` of `GL_n(K)`:

* `GLRep.inverseTranspose : g ↦ (g⁻¹)ᵀ` is an automorphism of `GL_n(K)` inverting the diagonal
  torus; the twist `ρ ∘ θ` has the weights of `ρ` negated
  (`GLRep.ratCharacter_comp_inverseTranspose`), is rational when `ρ` is, and is irreducible
  exactly when `ρ` is;
* the dual representation `ρ^∨` (`Representation.dual`) is rational when `ρ` is, with the weights
  of `ρ` negated (`GLRep.IsRationalRep.ratCharacter_dual`), and irreducible when `ρ` is
  (`GLRep.isIrreducible_dual`);
* consequently, in characteristic zero, `ρ ∘ θ ≅ ρ^∨` for irreducible rational `ρ`
  (`GLRep.nonempty_equiv_comp_inverseTranspose_dual`).

The weight negation of Laurent polynomials is `GLRep.laurentNeg : x^μ ↦ x^{−μ}`.
-/

namespace GLRep

open Module TauCeti

open scoped Matrix

noncomputable section

/-! ### Negating weights -/

section Laurent

variable {κ : Type*}

/-- The ring involution `x^μ ↦ x^{−μ}` of the Laurent polynomials. -/
def laurentNeg : TorusLaurent κ ≃+* TorusLaurent κ :=
  AddMonoidAlgebra.mapDomainRingEquiv ℤ (AddEquiv.neg (κ → ℤ))

theorem coeff_laurentNeg (f : TorusLaurent κ) (μ : κ → ℤ) :
    (laurentNeg f).coeff μ = f.coeff (-μ) := by
  rw [laurentNeg, AddMonoidAlgebra.coeff_mapDomainRingEquiv, Finsupp.equivMapDomain_apply]
  rfl

@[simp]
theorem laurentNeg_single (μ : κ → ℤ) (c : ℤ) :
    laurentNeg (AddMonoidAlgebra.single μ c) = AddMonoidAlgebra.single (-μ) c := by
  rw [laurentNeg, AddMonoidAlgebra.mapDomainRingEquiv_single, AddEquiv.neg_apply]

theorem weightCharHom_inv_apply {K : Type*} [Field K] [Fintype κ] (μ : κ → ℤ) (t : κ → Kˣ) :
    weightCharHom K μ t⁻¹ = weightCharHom K (-μ) t := by
  simp only [weightCharHom_apply, weightChar_apply, torusCharacter_def, Pi.inv_apply,
    Pi.neg_apply, zpow_neg, inv_zpow, Finset.prod_inv_distrib]

theorem laurentEval_laurentNeg {K : Type*} [Field K] [Fintype κ] (t : κ → Kˣ)
    (f : TorusLaurent κ) : laurentEval K t (laurentNeg f) = laurentEval K t⁻¹ f := by
  have : (laurentEval K t).comp (laurentNeg (κ := κ)).toRingHom = laurentEval K t⁻¹ := by
    refine AddMonoidAlgebra.ringHom_ext (fun c => ?_) fun μ => ?_
    · simp only [RingHom.coe_comp, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        Function.comp_apply, laurentNeg_single, neg_zero]
      rw [laurentEval_single, laurentEval_single, weightCharHom_inv_apply, neg_zero]
    · simp only [RingHom.coe_comp, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        Function.comp_apply, laurentNeg_single, laurentEval_single, weightCharHom_inv_apply]
  exact RingHom.congr_fun this f

end Laurent

/-! ### Dualizing twists -/

section General

variable {K G : Type*} [Field K] [Group G] {W : Type*} [AddCommGroup W] [Module K W]

/-- The dual of a twist is the twist of the dual by the inverse character. -/
theorem dual_scaledRep (ρ : Representation K G W) (χ : G →* Kˣ) :
    (scaledRep ρ χ).dual = scaledRep ρ.dual χ⁻¹ := by
  refine MonoidHom.ext fun g => LinearMap.ext fun φ => LinearMap.ext fun w => ?_
  simp only [Representation.dual_apply, scaledRep_apply, Module.Dual.transpose_apply,
    LinearMap.comp_apply, LinearMap.smul_apply, map_smul, smul_eq_mul, map_inv,
    MonoidHom.inv_apply, Units.val_inv_eq_inv_val]

end General

variable {K : Type*} [Field K] {n : ℕ}

/-! ### The inverse-transpose automorphism -/

section InverseTranspose

variable (K n) in
/-- The automorphism `θ(g) = (g⁻¹)ᵀ` of `GL_n(K)`. -/
def inverseTranspose : GL (Fin n) K →* GL (Fin n) K where
  toFun g := ⟨((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ, (g : Matrix (Fin n) (Fin n) K)ᵀ,
    by rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.transpose_one]⟩
  map_one' := Units.ext (by simp)
  map_mul' g h := Units.ext (by simp [Matrix.transpose_mul, mul_inv_rev])

@[simp]
theorem coe_inverseTranspose (g : GL (Fin n) K) :
    (inverseTranspose K n g : Matrix (Fin n) (Fin n) K) =
      ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ :=
  rfl

@[simp]
theorem coe_inverseTranspose_inv (g : GL (Fin n) K) :
    (((inverseTranspose K n g)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (g : Matrix (Fin n) (Fin n) K)ᵀ :=
  rfl

theorem inverseTranspose_inverseTranspose (g : GL (Fin n) K) :
    inverseTranspose K n (inverseTranspose K n g) = g := by
  ext : 1
  rw [coe_inverseTranspose, coe_inverseTranspose_inv, Matrix.transpose_transpose]

theorem inverseTranspose_diagGL (t : Fin n → Kˣ) :
    inverseTranspose K n (diagGL t) = diagGL t⁻¹ := by
  ext : 1
  rw [coe_inverseTranspose, ← map_inv diagGL t, diagGL_coe, Matrix.diagonal_transpose]

variable {W : Type*} [AddCommGroup W] [Module K W] {ρ : Representation K (GL (Fin n) K) W}

/-- Twisting by `θ` negates the weights. -/
theorem weightSpace_comp_inverseTranspose (μ : Fin n → ℤ) :
    weightSpace (ρ.comp (inverseTranspose K n)) μ = weightSpace ρ (-μ) := by
  ext w
  simp only [mem_torusWeightSpace, MonoidHom.coe_comp, Function.comp_apply,
    inverseTranspose_diagGL]
  constructor
  · intro h t
    have := h t⁻¹
    rwa [inv_inv, weightCharHom_inv_apply] at this
  · intro h t
    rw [h t⁻¹, weightCharHom_inv_apply, neg_neg]

/-- **Twisting by `θ` negates the character.** -/
theorem ratCharacter_comp_inverseTranspose [Infinite K] [FiniteDimensional K W] :
    ratCharacter (ρ.comp (inverseTranspose K n)) = laurentNeg (ratCharacter ρ) := by
  refine TorusLaurent.ext fun μ => ?_
  rw [coeff_ratCharacter, coeff_laurentNeg, coeff_ratCharacter, weightSpace_comp_inverseTranspose]

/-- The subrepresentations of `ρ ∘ θ` are those of `ρ`. -/
def subrepInverseTransposeOrderIso :
    Subrepresentation ρ ≃o Subrepresentation (ρ.comp (inverseTranspose K n)) where
  toFun U := ⟨U.toSubmodule, fun g _ hw => U.apply_mem_toSubmodule (inverseTranspose K n g) hw⟩
  invFun U := ⟨U.toSubmodule, fun g w hw => by
    have := U.apply_mem_toSubmodule (inverseTranspose K n g) hw
    rwa [MonoidHom.coe_comp, Function.comp_apply, inverseTranspose_inverseTranspose] at this⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

theorem isIrreducible_comp_inverseTranspose_iff :
    Representation.IsIrreducible (ρ.comp (inverseTranspose K n)) ↔ ρ.IsIrreducible :=
  (OrderIso.isSimpleOrder_iff subrepInverseTransposeOrderIso).symm

/-- Twisting by `θ` keeps a representation rational. -/
theorem IsRationalRep.comp_inverseTranspose (h : IsRationalRep ρ) :
    IsRationalRep (ρ.comp (inverseTranspose K n)) := by
  refine HasCoeffsIn.isRationalRep_of_glRegularFunctions
    (h.hasCoeffsIn_glRegularFunctions.comp (B := glRegularFunctions K n) (inverseTranspose K n)
      fun F hF => ?_)
  refine comp_mem_of_forall_coord_mem _ (fun s => ?_) hF
  rcases s with p | u
  · exact inv_apply_mem_glRegularFunctions p.2 p.1
  · have : (fun g : GL (Fin n) K => glRationalCoord K n (inverseTranspose K n g) (Sum.inr u)) =
        fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K).det := by
      funext g
      change (((Matrix.GeneralLinearGroup.det (inverseTranspose K n g))⁻¹ : Kˣ) : K) = _
      rw [Units.val_inv_eq_inv_val, Matrix.GeneralLinearGroup.val_det_apply, coe_inverseTranspose,
        Matrix.det_transpose, ← Matrix.GeneralLinearGroup.val_det_apply, map_inv,
        Units.val_inv_eq_inv_val, inv_inv, Matrix.GeneralLinearGroup.val_det_apply]
    rw [this]
    exact det_mem_glRegularFunctions

end InverseTranspose

/-! ### Duals -/

section Dual

variable {W : Type*} [AddCommGroup W] [Module K W] {ρ : Representation K (GL (Fin n) K) W}

/-- The dual of a rational representation is rational. -/
theorem IsRationalRep.dual (h : IsRationalRep ρ) : IsRationalRep ρ.dual := by
  have := h.finiteDimensional
  refine HasCoeffsIn.isRationalRep_of_glRegularFunctions ⟨inferInstance, fun ψ φ => ?_⟩
  obtain ⟨w, rfl⟩ := (Module.evalEquiv K W).surjective ψ
  have : (fun g => (Module.evalEquiv K W w) (ρ.dual g φ)) = fun g => φ (ρ g⁻¹ w) := by
    funext g
    rfl
  rw [this]
  exact comp_inv_mem_glRegularFunctions (h.hasCoeffsIn_glRegularFunctions.coeff_mem φ w)

/-- The dual of an irreducible finite-dimensional representation is irreducible. -/
theorem isIrreducible_dual [FiniteDimensional K W] (hirr : ρ.IsIrreducible) :
    ρ.dual.IsIrreducible := by
  have := hirr
  -- the annihilator of a subrepresentation of the dual is a subrepresentation
  let coann : Subrepresentation ρ.dual → Subrepresentation ρ := fun U =>
    ⟨U.toSubmodule.dualCoannihilator, fun g w hw => by
      rw [Submodule.mem_dualCoannihilator] at hw ⊢
      intro φ hφ
      have := hw _ (U.apply_mem_toSubmodule g⁻¹ hφ)
      rw [Representation.dual_apply, inv_inv] at this
      exact this⟩
  have : Nontrivial (Subrepresentation ρ.dual) := by
    refine ⟨⟨⊥, ⊤, fun h => ?_⟩⟩
    have h1 : (⊥ : Submodule K (Module.Dual K W)) = ⊤ :=
      congrArg Subrepresentation.toSubmodule h
    apply (bot_ne_top : (⊥ : Subrepresentation ρ) ≠ ⊤)
    apply Subrepresentation.ext
    change (⊥ : Submodule K W) = ⊤
    rw [← Submodule.dualCoannihilator_top (R := K) (M := W), ← h1,
      Submodule.dualCoannihilator_bot]
  refine ⟨fun U => ?_⟩
  rcases IsSimpleOrder.eq_bot_or_eq_top (coann U) with h | h
  · right
    apply Subrepresentation.ext
    have hc : U.toSubmodule.dualCoannihilator = ⊥ := congrArg Subrepresentation.toSubmodule h
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := U.toSubmodule), hc,
      Submodule.dualAnnihilator_bot]
    rfl
  · left
    apply Subrepresentation.ext
    have hc : U.toSubmodule.dualCoannihilator = ⊤ := congrArg Subrepresentation.toSubmodule h
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := U.toSubmodule), hc,
      Submodule.dualAnnihilator_top]
    rfl

variable [Infinite K]

/-- **The character of the dual is the negated character.** -/
theorem IsRationalRep.ratCharacter_dual [CharZero K] (h : IsRationalRep ρ) :
    ratCharacter ρ.dual = laurentNeg (ratCharacter ρ) := by
  have := h.finiteDimensional
  refine (h.dual.eq_ratCharacter_of_forall _ fun t => ?_).symm
  rw [laurentEval_laurentNeg, ← h.trace_diagGL_eq, Representation.dual_apply,
    LinearMap.trace_transpose', ← map_inv diagGL t]

/-- **For an irreducible rational representation, `ρ ∘ θ ≅ ρ^∨`.** -/
theorem nonempty_equiv_comp_inverseTranspose_dual [CharZero K] (h : IsRationalRep ρ)
    (hirr : ρ.IsIrreducible) :
    Nonempty (Representation.Equiv (ρ.comp (inverseTranspose K n)) ρ.dual) := by
  have := h.finiteDimensional
  exact h.comp_inverseTranspose.nonempty_equiv_of_ratCharacter_eq h.dual
    (isIrreducible_comp_inverseTranspose_iff.mpr hirr) (isIrreducible_dual hirr)
    (by rw [ratCharacter_comp_inverseTranspose, h.ratCharacter_dual])

end Dual

end

end GLRep
