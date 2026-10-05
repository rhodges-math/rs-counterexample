import Schubert.GLRep.Borel.SpecialLinear

/-!
# Twisting sections by powers of the determinant

Multiplication by `det⁻ᶜ` sends `(B, η)`-semi-invariants of `𝒪(GL_n)/I` to
`(B, η + c·(1, …, 1))`-semi-invariants, and intertwines left translation twisted by the character
`det^c` of `B` (`GLRep.borelSemiInvariantDetTwist`). Geometrically: `𝓛(η + c·1) ≅ 𝓛(η)` with the
action of `B` twisted by `det^c`. Consequently the character of the sections of `𝓛(η + c·1)` is
`x^{−c·1}` times that of `𝓛(η)` (in the convention of `FlagVarieties.ch`).
-/

namespace GLRep

open MvPolynomial TauCeti

noncomputable section

variable {K : Type*} [Field K] {n : ℕ}

/-- Right translation sends `det` to `det(g) det`. -/
theorem rightTranslHom_genericDet (g : GL (Fin n) K) :
    rightTranslHom K n g
        (algebraMap (MvPolynomial (Fin n × Fin n) K) (GLCoord K n) (genericDet K n)) =
      (g : Matrix (Fin n) (Fin n) K).det •
        algebraMap (MvPolynomial (Fin n × Fin n) K) (GLCoord K n) (genericDet K n) := by
  rw [rightTranslHom_apply, rightSubstAway_algebraMap, rightSubst_det, map_mul,
    ← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply, mul_comm, Algebra.smul_def]

/-- Left translation sends `det` to `det(g)⁻¹ det`. -/
theorem leftTranslHom_genericDet (g : GL (Fin n) K) :
    leftTranslHom K n g
        (algebraMap (MvPolynomial (Fin n × Fin n) K) (GLCoord K n) (genericDet K n)) =
      ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det •
        algebraMap (MvPolynomial (Fin n × Fin n) K) (GLCoord K n) (genericDet K n) := by
  rw [leftTranslHom_apply, leftSubstAway_algebraMap, leftSubst_det, map_mul,
    ← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply, Algebra.smul_def]

/-- Right translation sends `det⁻¹` to `det(g)⁻¹ det⁻¹`. -/
theorem rightTranslHom_glDetInv (g : GL (Fin n) K) :
    rightTranslHom K n g (glDetInv K n) =
      (((Matrix.GeneralLinearGroup.det g)⁻¹ : Kˣ) : K) • glDetInv K n := by
  set u := rightTranslHom K n g (glDetInv K n)
  set e := glDetInv K n
  set D := algebraMap (MvPolynomial (Fin n × Fin n) K) (GLCoord K n) (genericDet K n)
  set A := algebraMap K (GLCoord K n) (((Matrix.GeneralLinearGroup.det g)⁻¹ : Kˣ) : K)
  set c := algebraMap K (GLCoord K n) (g : Matrix (Fin n) (Fin n) K).det
  have h2 : D * e = 1 := algebraMap_genericDet_mul_glDetInv
  have hRD : rightTranslHom K n g D = c * D := by
    rw [rightTranslHom_apply, rightSubstAway_algebraMap, rightSubst_det, map_mul,
      ← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply, mul_comm]
  have h1 : c * D * u = 1 := by
    rw [← hRD, ← map_mul, h2, map_one]
  have h3 : A * c = 1 := by
    rw [← map_mul, ← Matrix.GeneralLinearGroup.val_det_apply, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, map_one]
  rw [Algebra.smul_def]
  linear_combination (-u) * h2 + (A * e) * h1 - (u * D * e) * h3

variable (I : Ideal (GLCoord K n)) (hL : IsLeftBorelStable I) (hR : IsRightBorelStable I)

/-- The class of `det⁻¹` in `𝒪(GL_n)/I`. -/
abbrev quotDetInv : GLCoord K n ⧸ I := Ideal.Quotient.mk I (glDetInv K n)

/-- The class of `det` in `𝒪(GL_n)/I`. -/
abbrev quotDet : GLCoord K n ⧸ I :=
  Ideal.Quotient.mk I (algebraMap (MvPolynomial (Fin n × Fin n) K) (GLCoord K n)
    (genericDet K n))

theorem quotDet_mul_quotDetInv : quotDet I * quotDetInv I = 1 := by
  rw [quotDet, quotDetInv, ← map_mul, algebraMap_genericDet_mul_glDetInv, map_one]

theorem quotRightTranslHom_quotDetInv (b : borel K n) :
    quotRightTranslHom I hR b (quotDetInv I) =
      (((Matrix.GeneralLinearGroup.det (b : GL (Fin n) K))⁻¹ : Kˣ) : K) • quotDetInv I := by
  change Ideal.Quotient.mk I (rightTranslHom K n b (glDetInv K n)) = _
  rw [rightTranslHom_glDetInv, ← Ideal.Quotient.mkₐ_eq_mk K, map_smul]
  rfl

theorem quotLeftTranslHom_quotDetInv (b : borel K n) :
    quotLeftTranslHom I hL b (quotDetInv I) =
      ((Matrix.GeneralLinearGroup.det (b : GL (Fin n) K) : Kˣ) : K) • quotDetInv I := by
  change Ideal.Quotient.mk I (leftTranslHom K n b (glDetInv K n)) = _
  rw [leftTranslHom_glDetInv, ← Ideal.Quotient.mkₐ_eq_mk K, map_smul,
    Matrix.GeneralLinearGroup.val_det_apply]
  rfl

/-- `det(b)^c` is the value of the character `c·(1, …, 1)`. -/
theorem borelChar_natConst (c : ℕ) (b : borel K n) :
    borelChar K n (fun _ => (c : ℤ)) b = Matrix.GeneralLinearGroup.det (b : GL (Fin n) K) ^ c := by
  rw [← detZPow_borel, detZPow, MonoidHom.zpow_apply, zpow_natCast]

theorem det_pow_eq_borelChar (c : ℕ) (b : borel K n) :
    ((Matrix.GeneralLinearGroup.det (b : GL (Fin n) K) ^ c : Kˣ) : K) =
      (borelChar K n (fun _ => (c : ℤ)) b : K) := by
  rw [borelChar_natConst]

theorem mul_quotDetInv_pow_mem {η : Fin n → ℤ} {c : ℕ} {f : GLCoord K n ⧸ I}
    (hf : f ∈ borelSemiInvariants I hR η) :
    quotDetInv I ^ c * f ∈ borelSemiInvariants I hR (η + fun _ => (c : ℤ)) := by
  rw [mem_borelSemiInvariants] at hf ⊢
  intro b
  rw [map_mul, map_pow, quotRightTranslHom_quotDetInv, hf b, smul_pow, smul_mul_smul_comm]
  congr 1
  rw [borelChar_add, MonoidHom.mul_apply, borelChar_natConst, mul_inv, ← inv_pow,
    ← Units.val_pow_eq_pow_val, ← Units.val_mul, mul_comm]

theorem quotRightTranslHom_quotDet (b : borel K n) :
    quotRightTranslHom I hR b (quotDet I) =
      ((Matrix.GeneralLinearGroup.det (b : GL (Fin n) K) : Kˣ) : K) • quotDet I := by
  change Ideal.Quotient.mk I (rightTranslHom K n b _) = _
  rw [rightTranslHom_genericDet, ← Ideal.Quotient.mkₐ_eq_mk K, map_smul,
    Matrix.GeneralLinearGroup.val_det_apply]
  rfl

theorem mul_quotDet_pow_mem {η : Fin n → ℤ} {c : ℕ} {f : GLCoord K n ⧸ I}
    (hf : f ∈ borelSemiInvariants I hR (η + fun _ => (c : ℤ))) :
    quotDet I ^ c * f ∈ borelSemiInvariants I hR η := by
  rw [mem_borelSemiInvariants] at hf ⊢
  intro b
  rw [map_mul, map_pow, quotRightTranslHom_quotDet, hf b, smul_pow, smul_mul_smul_comm]
  congr 1
  rw [borelChar_add, MonoidHom.mul_apply, borelChar_natConst, ← Units.val_pow_eq_pow_val,
    ← Units.val_mul, mul_inv, mul_inv_cancel_comm_assoc]

variable (η : Fin n → ℤ) (c : ℕ)

/-- **Twisting sections by a power of the determinant**: multiplication by `det⁻ᶜ` is an
equivalence between the `(B, η)`-semi-invariants with the action twisted by the character
`det^c = c·(1, …, 1)` and the `(B, η + c·(1, …, 1))`-semi-invariants. -/
def borelSemiInvariantDetTwist :
    (scaledRep (borelSemiInvariantRep I hL hR η) (borelChar K n fun _ => (c : ℤ))).Equiv
      (borelSemiInvariantRep I hL hR (η + fun _ => (c : ℤ))) :=
  .mk
    { toFun := fun f => ⟨quotDetInv I ^ c * f, mul_quotDetInv_pow_mem I hR f.2⟩
      invFun := fun f => ⟨quotDet I ^ c * f, mul_quotDet_pow_mem I hR f.2⟩
      map_add' := fun f f' => Subtype.ext (mul_add _ _ _)
      map_smul' := fun a f => Subtype.ext (mul_smul_comm _ _ _)
      left_inv := fun f => Subtype.ext <| by
        change quotDet I ^ c * (quotDetInv I ^ c * f) = f
        rw [← mul_assoc, ← mul_pow, quotDet_mul_quotDetInv, one_pow, one_mul]
      right_inv := fun f => Subtype.ext <| by
        change quotDetInv I ^ c * (quotDet I ^ c * f) = f
        rw [← mul_assoc, ← mul_pow, mul_comm (quotDetInv I), quotDet_mul_quotDetInv, one_pow,
          one_mul] }
    fun b => LinearMap.ext fun f => Subtype.ext <| by
      change quotDetInv I ^ c * ((borelChar K n (fun _ => (c : ℤ)) b : K) •
          quotLeftTranslHom I hL b f) =
        quotLeftTranslHom I hL b (quotDetInv I ^ c * f)
      rw [map_mul, map_pow, quotLeftTranslHom_quotDetInv, smul_pow, smul_mul_assoc,
        mul_smul_comm, ← det_pow_eq_borelChar, Units.val_pow_eq_pow_val]

end

end GLRep
