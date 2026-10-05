import Schubert.GLRep.Borel.DetTwist
import Schubert.GLRep.Borel.GLRegular

/-!
# Twisting the induced representation by powers of the determinant

The determinant is a unit of `𝒪(GL_n)` (`GLRep.glDetUnit`). Multiplication by `det⁻ᶜ`, `c ∈ ℤ`,
sends `ind_B^G(η)` to `ind_B^G(η + c·(1, …, 1))` and intertwines the left regular action twisted
by `det^c` with the left regular action (`GLRep.indBorelDetTwist`):

  `ind_B^G(η) ⊗ det^c ≅ ind_B^G(η + c·1)`.
-/

namespace GLRep

open MvPolynomial TauCeti

noncomputable section

variable {K : Type*} [Field K] {n : ℕ}

variable (K n) in
/-- The determinant as a unit of `𝒪(GL_n)`. -/
def glDetUnit : (GLCoord K n)ˣ where
  val := algebraMap (MvPolynomial (Fin n × Fin n) K) (GLCoord K n) (genericDet K n)
  inv := glDetInv K n
  val_inv := algebraMap_genericDet_mul_glDetInv
  inv_val := by rw [mul_comm]; exact algebraMap_genericDet_mul_glDetInv

theorem units_map_leftTranslHom_glDetUnit (g : GL (Fin n) K) :
    Units.map ((leftTranslHom K n g : GLCoord K n →+* GLCoord K n) :
        GLCoord K n →* GLCoord K n) (glDetUnit K n) =
      Units.map ((algebraMap K (GLCoord K n) : K →+* GLCoord K n) : K →* GLCoord K n)
        (Matrix.GeneralLinearGroup.det g)⁻¹ * glDetUnit K n := by
  ext
  rw [Units.coe_map, Units.val_mul, Units.coe_map]
  change leftTranslHom K n g (algebraMap _ _ (genericDet K n)) = _
  rw [leftTranslHom_genericDet, Algebra.smul_def, ← Matrix.GeneralLinearGroup.val_det_apply,
    map_inv]
  rfl

theorem units_map_rightTranslHom_glDetUnit (g : GL (Fin n) K) :
    Units.map ((rightTranslHom K n g : GLCoord K n →+* GLCoord K n) :
        GLCoord K n →* GLCoord K n) (glDetUnit K n) =
      Units.map ((algebraMap K (GLCoord K n) : K →+* GLCoord K n) : K →* GLCoord K n)
        (Matrix.GeneralLinearGroup.det g) * glDetUnit K n := by
  ext
  rw [Units.coe_map, Units.val_mul, Units.coe_map]
  change rightTranslHom K n g (algebraMap _ _ (genericDet K n)) = _
  rw [rightTranslHom_genericDet, Algebra.smul_def, ← Matrix.GeneralLinearGroup.val_det_apply]
  rfl

/-- Left translation sends `det^k` to `det(g)^{−k} det^k`. -/
theorem leftTranslHom_glDetUnit_zpow (g : GL (Fin n) K) (k : ℤ) :
    leftTranslHom K n g ((glDetUnit K n ^ k : (GLCoord K n)ˣ) : GLCoord K n) =
      (((Matrix.GeneralLinearGroup.det g ^ (-k) : Kˣ)) : K) •
        ((glDetUnit K n ^ k : (GLCoord K n)ˣ) : GLCoord K n) := by
  have h := congrArg (fun u => ((u ^ k : (GLCoord K n)ˣ) : GLCoord K n))
    (units_map_leftTranslHom_glDetUnit (K := K) g)
  rw [mul_zpow, ← map_zpow, ← map_zpow, Units.val_mul, Units.coe_map, Units.coe_map] at h
  rw [Algebra.smul_def, ← inv_zpow']
  exact h

/-- Right translation sends `det^k` to `det(g)^k det^k`. -/
theorem rightTranslHom_glDetUnit_zpow (g : GL (Fin n) K) (k : ℤ) :
    rightTranslHom K n g ((glDetUnit K n ^ k : (GLCoord K n)ˣ) : GLCoord K n) =
      (((Matrix.GeneralLinearGroup.det g ^ k : Kˣ)) : K) •
        ((glDetUnit K n ^ k : (GLCoord K n)ˣ) : GLCoord K n) := by
  have h := congrArg (fun u => ((u ^ k : (GLCoord K n)ˣ) : GLCoord K n))
    (units_map_rightTranslHom_glDetUnit (K := K) g)
  rw [mul_zpow, ← map_zpow, ← map_zpow, Units.val_mul, Units.coe_map, Units.coe_map] at h
  rw [Algebra.smul_def]
  exact h

/-- Multiplication by `det⁻ᶜ` sends `ind_B^G(η)` to `ind_B^G(η')`, `η' = η + c·1`. -/
theorem mul_glDetUnit_zpow_mem {η η' : Fin n → ℤ} {c : ℤ} (hη : η' = η + fun _ => c)
    {f : GLCoord K n} (hf : f ∈ (indBorelSubrep K n η).toSubmodule) :
    ((glDetUnit K n ^ (-c) : (GLCoord K n)ˣ) : GLCoord K n) * f ∈
      (indBorelSubrep K n η').toSubmodule := by
  subst hη
  rw [mem_indBorelSubrep] at hf ⊢
  intro b
  rw [map_mul, rightTranslHom_glDetUnit_zpow, hf b, smul_mul_smul_comm]
  congr 1
  rw [borelChar_add, MonoidHom.mul_apply, ← detZPow_borel, detZPow, MonoidHom.zpow_apply,
    ← Units.val_mul, mul_inv, mul_comm, zpow_neg]

variable (K n) in
/-- **Twisting `ind_B^G(η)` by `det^c`**: multiplication by `det⁻ᶜ` is an equivalence
`ind_B^G(η) ⊗ det^c ≅ ind_B^G(η + c·1)`. -/
def indBorelDetTwist (η : Fin n → ℤ) (c : ℤ) :
    (scaledRep (indBorelRep K n η) (detZPow K n c)).Equiv
      (indBorelRep K n (η + fun _ => c)) :=
  .mk
    { toFun := fun f => ⟨_, mul_glDetUnit_zpow_mem rfl f.2⟩
      invFun := fun f => ⟨((glDetUnit K n ^ (-(-c)) : (GLCoord K n)ˣ) : GLCoord K n) * f,
        mul_glDetUnit_zpow_mem (by funext; simp) f.2⟩
      map_add' := fun f f' => Subtype.ext (mul_add _ _ _)
      map_smul' := fun a f => Subtype.ext (mul_smul_comm _ _ _)
      left_inv := fun f => Subtype.ext <| by
        change ((glDetUnit K n ^ (-(-c)) : (GLCoord K n)ˣ) : GLCoord K n) *
          (((glDetUnit K n ^ (-c) : (GLCoord K n)ˣ) : GLCoord K n) * f) = f
        rw [← mul_assoc, ← Units.val_mul, ← zpow_add, neg_add_cancel, zpow_zero, Units.val_one,
          one_mul]
      right_inv := fun f => Subtype.ext <| by
        change ((glDetUnit K n ^ (-c) : (GLCoord K n)ˣ) : GLCoord K n) *
          (((glDetUnit K n ^ (-(-c)) : (GLCoord K n)ˣ) : GLCoord K n) * f) = f
        rw [← mul_assoc, ← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero, Units.val_one,
          one_mul] }
    fun g => LinearMap.ext fun f => Subtype.ext <| by
      change ((glDetUnit K n ^ (-c) : (GLCoord K n)ˣ) : GLCoord K n) *
          ((detZPow K n c g : K) • leftTranslHom K n g f) =
        leftTranslHom K n g (((glDetUnit K n ^ (-c) : (GLCoord K n)ˣ) : GLCoord K n) * f)
      rw [map_mul, leftTranslHom_glDetUnit_zpow, neg_neg, smul_mul_assoc, mul_smul_comm, detZPow,
        MonoidHom.zpow_apply]

end

end GLRep
