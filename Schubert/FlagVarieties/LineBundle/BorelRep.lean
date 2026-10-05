import Schubert.FlagVarieties.LineBundle.SectionsAsSemiInvariants
import Schubert.GLRep.Borel.Regular

/-!
# The action of `B` on `H⁰(X, 𝓛(η))`

`B(R)` (`GLRep.borel R n`, invertible upper triangular matrices) acts on `𝒪(GLₙ)` by left
translation, `(b · f)(g) = f(b⁻¹ g)` (`GLRep.leftTranslHom`). Left translation commutes with the
right coaction, so for an ideal `J` stable under left translation by `B` it preserves the module
`(𝒪(GLₙ) ⧸ J)^{(B, η)}` of semi-invariants (`FlagVarieties.semiInvariantsRep`).

* **`FlagVarieties.sectionsRep`**: for a closed subscheme `X ⊆ Flₙ` whose preimage ideal `J` is
  stable under left translation by `B`, the representation of `B(R)` on `H⁰(X, 𝓛(η))`, transported
  from left translation on `(𝒪(GLₙ) ⧸ J)^{(B, η)}` through `sectionsEquivSemiInvariants`.
-/

noncomputable section

namespace FlagVarieties

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

universe u

variable (R : Type u) [CommRing R] (n : ℕ)

theorem genericMatrix_eq_glX (i j : Fin n) : genericMatrix R n i j = GLRep.glX i j :=
  (TauCeti.GeneralLinear.localizedGenericMatrix_apply R n i j).trans
    (TauCeti.GeneralLinear.coordinateRingMap_apply R n _)

theorem pointMatrix_leftTranslHom (g : GL (Fin n) R) :
    GLScheme.pointMatrix R n (GLRep.leftTranslHom R n g) =
      ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R).map (algebraMap R (GLCoord R n)) *
        genericMatrix R n := by
  ext i j
  change GLRep.leftTranslHom R n g (genericMatrix R n i j) = _
  rw [genericMatrix_eq_glX, GLRep.leftTranslHom_glX, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Algebra.smul_def, Matrix.map_apply, genericMatrix_eq_glX]

/-- Left translation on `𝒪(GLₙ) ⊗ 𝒪(B)`, acting on the first factor. -/
def leftTranslW (g : GL (Fin n) R) : GLBorelCoord R n →ₐ[R] GLBorelCoord R n :=
  Algebra.TensorProduct.map (GLRep.leftTranslHom R n g) (AlgHom.id R (BorelCoord R n))

theorem leftTranslW_inl (g : GL (Fin n) R) :
    (leftTranslW R n g).comp (GLBorelCoord.inl R n) = (GLBorelCoord.inl R n).comp
        (GLRep.leftTranslHom R n g) :=
  Algebra.TensorProduct.map_comp_includeLeft _ _

theorem leftTranslW_inr (g : GL (Fin n) R) :
    (leftTranslW R n g).comp (GLBorelCoord.inr R n) = GLBorelCoord.inr R n :=
  Algebra.TensorProduct.map_comp_includeRight _ _

/-- **Left and right translations commute**: `ρ ∘ L_g = (L_g ⊗ id) ∘ ρ`. -/
theorem rightCoactionW_comp_leftTransl (g : GL (Fin n) R) :
    (rightCoactionW R n).comp (GLRep.leftTranslHom R n g) =
      (leftTranslW R n g).comp (rightCoactionW R n) := by
  apply glCoord_algHom_ext R
  set G : Matrix (Fin n) (Fin n) R := ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)
  have hG : ∀ (φ : GLCoord R n →ₐ[R] GLBorelCoord R n),
      (G.map (algebraMap R (GLCoord R n))).map φ = G.map (algebraMap R (GLBorelCoord R n)) := by
    intro φ
    ext i j
    simp only [Matrix.map_apply, AlgHom.commutes]
  have hX : (genericMatrix R n).map (rightCoactionW R n) =
      GLScheme.pointMatrix R n (GLBorelCoord.inl R n) * (borelMatrix R n).map
          (GLBorelCoord.inr R n) :=
    pointMatrix_glPointOfMatrix R _ _
  have hL : GLScheme.pointMatrix R n ((leftTranslW R n g).comp (GLBorelCoord.inl R n)) =
      G.map (algebraMap R (GLBorelCoord R n)) * GLScheme.pointMatrix R n
          (GLBorelCoord.inl R n) := by
    rw [leftTranslW_inl, pointMatrix_comp, pointMatrix_leftTranslHom, map_mul_algHom, hG]
    rfl
  have hB : (borelMatrix R n).map ((leftTranslW R n g).comp (GLBorelCoord.inr R n)) =
      (borelMatrix R n).map (GLBorelCoord.inr R n) := by
    rw [leftTranslW_inr]
  rw [pointMatrix_comp, pointMatrix_comp, pointMatrix_leftTranslHom, map_mul_algHom, hG]
  change _ * (genericMatrix R n).map (rightCoactionW R n) =
    ((genericMatrix R n).map (rightCoactionW R n)).map (leftTranslW R n g)
  rw [hX, map_mul_algHom, map_map_algHom, hB, ← pointMatrix_comp, hL, Matrix.mul_assoc]

/-! ### Left translation on `𝒪(GLₙ) ⧸ J` -/

variable {R n}

/-- `J` is stable under left translation by `B(R)`. -/
def IsLeftTranslStable (J : Ideal (GLCoord R n)) : Prop :=
  ∀ b ∈ GLRep.borel R n, J ≤ J.comap (GLRep.leftTranslHom R n b)

variable (J : Ideal (GLCoord R n))

/-- Left translation by `B(R)` on `𝒪(GLₙ) ⧸ J`. -/
def leftTranslQuot (hJ : IsLeftTranslStable J) :
    GLRep.borel R n →* (GLCoord R n ⧸ J →ₐ[R] GLCoord R n ⧸ J) where
  toFun b := Ideal.quotientMapₐ J (GLRep.leftTranslHom R n b) (hJ b b.2)
  map_one' := Ideal.Quotient.algHom_ext _ (AlgHom.ext fun x => by simp)
  map_mul' b b' := Ideal.Quotient.algHom_ext _ (AlgHom.ext fun x => by simp)

theorem leftTranslQuot_mk (hJ : IsLeftTranslStable J) (b : GLRep.borel R n) (f : GLCoord R n) :
    leftTranslQuot J hJ b (Ideal.Quotient.mk J f) =
      Ideal.Quotient.mk J (GLRep.leftTranslHom R n b f) :=
  rfl

/-- Left translation is compatible with the defect `f ↦ ρ(f) - f ⊗ η⁻¹`. -/
theorem semiInvariantDefect_leftTransl (hJ : IsLeftTranslStable J) (η : Fin n → ℤ)
    (b : GLRep.borel R n) (f : GLCoord R n) :
    semiInvariantDefect R n J η (GLRep.leftTranslHom R n b f) =
      Algebra.TensorProduct.map (leftTranslQuot J hJ b) (AlgHom.id R (BorelCoord R n))
        (semiInvariantDefect R n J η f) := by
  have h1 := DFunLike.congr_fun (rightCoactionW_comp_leftTransl R n b) f
  rw [rightCoactionW_eq] at h1
  have h2 : (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R J) (AlgHom.id R (BorelCoord R n))).comp
      (Algebra.TensorProduct.map (GLRep.leftTranslHom R n b) (AlgHom.id R (BorelCoord R n))) =
      (Algebra.TensorProduct.map (leftTranslQuot J hJ b) (AlgHom.id R (BorelCoord R n))).comp
        (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R J) (AlgHom.id R (BorelCoord R n))) := by
    rw [← Algebra.TensorProduct.map_comp, ← Algebra.TensorProduct.map_comp]
    congr 1
  have e1 : rightCoactionMod R n J (GLRep.leftTranslHom R n b f) =
      Algebra.TensorProduct.map (leftTranslQuot J hJ b) (AlgHom.id R (BorelCoord R n))
        (rightCoactionMod R n J f) := by
    change Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R J) (AlgHom.id R (BorelCoord R n))
        (rightCoaction R n (GLRep.leftTranslHom R n b f)) =
      Algebra.TensorProduct.map (leftTranslQuot J hJ b) (AlgHom.id R (BorelCoord R n))
        (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R J) (AlgHom.id R (BorelCoord R n))
          (rightCoaction R n f))
    rw [show rightCoaction R n (GLRep.leftTranslHom R n b f) =
        Algebra.TensorProduct.map (GLRep.leftTranslHom R n b) (AlgHom.id R (BorelCoord R n))
          (rightCoaction R n f) from h1, ← AlgHom.comp_apply, h2, AlgHom.comp_apply]
  have e2 : Ideal.Quotient.mk J (GLRep.leftTranslHom R n b f) ⊗ₜ[R]
      (((borelCharacterUnit R n η)⁻¹ : (BorelCoord R n)ˣ) : BorelCoord R n) =
      Algebra.TensorProduct.map (leftTranslQuot J hJ b) (AlgHom.id R (BorelCoord R n))
        (Ideal.Quotient.mk J f ⊗ₜ[R]
          (((borelCharacterUnit R n η)⁻¹ : (BorelCoord R n)ˣ) : BorelCoord R n)) := by
    rw [Algebra.TensorProduct.map_tmul]
    rfl
  rw [semiInvariantDefect_apply, semiInvariantDefect_apply, map_sub, e1, e2]

theorem leftTranslQuot_mem_quotientSemiInvariants (hJ : IsLeftTranslStable J) (η : Fin n → ℤ)
    (b : GLRep.borel R n) {x : GLCoord R n ⧸ J} (hx : x ∈ quotientSemiInvariants R n J η) :
    leftTranslQuot J hJ b x ∈ quotientSemiInvariants R n J η := by
  obtain ⟨f, hf, rfl⟩ := hx
  refine ⟨GLRep.leftTranslHom R n b f, ?_, rfl⟩
  show semiInvariantDefect R n J η (GLRep.leftTranslHom R n b f) = 0
  rw [semiInvariantDefect_leftTransl J hJ η b f, LinearMap.mem_ker.mp hf, map_zero]

/-- **Left translation on the semi-invariants** `(𝒪(GLₙ) ⧸ J)^{(B, η)}`. -/
def semiInvariantsRep (hJ : IsLeftTranslStable J) (η : Fin n → ℤ) :
    Representation R (GLRep.borel R n) (quotientSemiInvariants R n J η) where
  toFun b := (leftTranslQuot J hJ b).toLinearMap.restrict
    (fun _ hx => leftTranslQuot_mem_quotientSemiInvariants J hJ η b hx)
  map_one' := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    change leftTranslQuot J hJ 1 x.1 = x.1
    rw [map_one]
    rfl
  map_mul' b b' := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    change leftTranslQuot J hJ (b * b') x.1 = leftTranslQuot J hJ b (leftTranslQuot J hJ b' x.1)
    rw [map_mul]
    rfl

variable (R n)

/-- **The action of `B` on `H⁰(X, 𝓛(η))`**.

For a closed subscheme `X ⊆ Flₙ` (ideal sheaf `I`) whose preimage ideal `J ⊆ 𝒪(GLₙ)` is stable
under left translation by `B(R)` (e.g. `X` a union of Schubert varieties), `b ∈ B(R)` acts on
`H⁰(X, 𝓛(η)) = Γ(X, i^* 𝓛(η))` by left translation of functions, `(b · f)(g) = f(b⁻¹ g)`, defined
on `(𝒪(GLₙ) ⧸ J)^{(B, η)}` and transported through `sectionsEquivSemiInvariants`. -/
def sectionsRep (I : (FlagScheme R n).IdealSheafData) (η : Fin n → ℤ)
    (hJ : IsLeftTranslStable (preimageIdeal R n I)) :
    Representation R (GLRep.borel R n) (sections R n I η) where
  toFun b := (sectionsEquivSemiInvariants R n I η).symm.toLinearMap ∘ₗ
    semiInvariantsRep (preimageIdeal R n I) hJ η b ∘ₗ
        (sectionsEquivSemiInvariants R n I η).toLinearMap
  map_one' := by
    refine LinearMap.ext fun x => ?_
    change (sectionsEquivSemiInvariants R n I η).symm
      (semiInvariantsRep (preimageIdeal R n I) hJ η 1 (sectionsEquivSemiInvariants R n I η x)) = x
    rw [map_one, Module.End.one_apply, LinearEquiv.symm_apply_apply]
  map_mul' b b' := by
    refine LinearMap.ext fun x => ?_
    change (sectionsEquivSemiInvariants R n I η).symm
      (semiInvariantsRep (preimageIdeal R n I) hJ η (b * b')
          (sectionsEquivSemiInvariants R n I η x)) =
      (sectionsEquivSemiInvariants R n I η).symm (semiInvariantsRep (preimageIdeal R n I) hJ η b
        ((sectionsEquivSemiInvariants R n I η) ((sectionsEquivSemiInvariants R n I η).symm
          (semiInvariantsRep (preimageIdeal R n I) hJ η b'
              (sectionsEquivSemiInvariants R n I η x)))))
    rw [map_mul, LinearEquiv.apply_symm_apply, Module.End.mul_apply]

theorem sectionsEquivSemiInvariants_sectionsRep (I : (FlagScheme R n).IdealSheafData)
    (η : Fin n → ℤ)
    (hJ : IsLeftTranslStable (preimageIdeal R n I)) (b : GLRep.borel R n)
    (s : sections R n I η) :
    sectionsEquivSemiInvariants R n I η (sectionsRep R n I η hJ b s) =
      semiInvariantsRep (preimageIdeal R n I) hJ η b (sectionsEquivSemiInvariants R n I η s) :=
  LinearEquiv.apply_symm_apply _ _

end FlagVarieties
