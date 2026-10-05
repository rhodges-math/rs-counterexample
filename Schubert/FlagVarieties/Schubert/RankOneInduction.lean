import Schubert.FlagVarieties.Schubert.SimpleSchubertGlobalSections
import Schubert.FlagVarieties.LineBundle.BorelRep

/-!
# Rank-one induction `H_{sᵢ}(M) = (𝒪(Pᵢ) ⊗ M)^B`

A `B`-module is modelled by a right `𝒪(B)`-coaction `ρ : M → M ⊗ 𝒪(B)`, `ρ(m) = Σ m₀ ⊗ m₁`
(so `b · m = Σ m₁(b) m₀`; the comodule axioms are not needed for the definitions below).

* `FlagVarieties.rankOneInduction R n i ρ`: the `R`-submodule `H_{sᵢ}(M) = (𝒪(Pᵢ) ⊗ M)^B` of
  `𝒪(Pᵢ) ⊗ M`, the invariants of the diagonal right coaction `f ⊗ m ↦ Σ (f₀ ⊗ m₀) ⊗ f₁ m₁`
  (`FlagVarieties.parabolicTensorCoaction`); as functions `x : Pᵢ → M`, the condition is
  `b · x(p b) = x(p)`, i.e. `x(p b) = b⁻¹ · x(p)`;
* `FlagVarieties.rankOneInductionMap`: functoriality in comodule maps;
* `FlagVarieties.rankOneInductionRep`: the action of `B(R)` by left translation,
  `(b · x)(p) = x(b⁻¹ p)`;
* for the character module `R_η` (`FlagVarieties.charCoaction`, `b · r = η(b) r`):
  `FlagVarieties.rankOneInductionSectionsEquiv : H_{sᵢ}(R_η) ≅ H⁰(X_{sᵢ}, 𝓛(η))`, compatible with
  the actions of `B(R)` (`FlagVarieties.rankOneInductionSectionsEquiv_rep`, against `sectionsRep`).
  Combined with `FlagVarieties.simpleSchubertSectionsEquiv`, `H_{sᵢ}(R_η)` is free of rank
  `max(0, η_{i+1} - ηᵢ + 1)`.
-/

noncomputable section

namespace FlagVarieties

open scoped TensorProduct

universe u v

variable (R : Type u) [CommRing R] (n : ℕ) (i : ℕ)

/-! ### `B(R)` acts on `Pᵢ` by left translation -/

/-- `Pᵢ` is stable under left translation by `B(R)`. -/
theorem isLeftTranslStable_parabolicIdeal : IsLeftTranslStable (parabolicIdeal R n i) := by
  intro b hb
  rw [parabolicIdeal, Ideal.span_le]
  rintro _ ⟨⟨⟨r, c⟩, hrc⟩, rfl⟩
  rw [SetLike.mem_coe, Ideal.mem_comap]
  have hinv : ((b⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R).BlockTriangular id :=
    (GLRep.borel R n).inv_mem hb
  have h := congrFun (congrFun (pointMatrix_leftTranslHom R n b) r) c
  simp only [Matrix.mul_apply, Matrix.map_apply] at h
  change GLRep.leftTranslHom R n b (genericMatrix R n r c) = _ at h
  rw [h]
  refine Ideal.sum_mem _ fun k _ => ?_
  by_cases hk : k < r
  · rw [hinv hk, map_zero, zero_mul]
    exact Ideal.zero_mem _
  · exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨⟨(k, c),
      lt_of_lt_of_le hrc (parabolicBlock_monotone i (not_lt.mp hk))⟩, rfl⟩)

/-- Left translation by `b ∈ B(R)` on `𝒪(Pᵢ)`, `(b · f)(p) = f(b⁻¹ p)`. -/
abbrev parabolicLeftTranslAlg (b : GLRep.borel R n) :
    ParabolicCoord R n i →ₐ[R] ParabolicCoord R n i :=
  leftTranslQuot (parabolicIdeal R n i) (isLeftTranslStable_parabolicIdeal R n i) b

/-- Left and right translations on `Pᵢ` commute. -/
theorem parabolicCoaction_leftTransl (b : GLRep.borel R n) (f : ParabolicCoord R n i) :
    parabolicCoaction R n i (parabolicLeftTranslAlg R n i b f) =
      Algebra.TensorProduct.map (parabolicLeftTranslAlg R n i b) (AlgHom.id R (BorelCoord R n))
        (parabolicCoaction R n i f) := by
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective f
  set J := parabolicIdeal R n i
  have hJ := isLeftTranslStable_parabolicIdeal R n i
  have h1 := DFunLike.congr_fun (rightCoactionW_comp_leftTransl R n b) g
  rw [rightCoactionW_eq] at h1
  have h2 : (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R J)
      (AlgHom.id R (BorelCoord R n))).comp
      (Algebra.TensorProduct.map (GLRep.leftTranslHom R n b) (AlgHom.id R (BorelCoord R n))) =
      (Algebra.TensorProduct.map (leftTranslQuot J hJ b) (AlgHom.id R (BorelCoord R n))).comp
        (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R J) (AlgHom.id R (BorelCoord R n))) := by
    rw [← Algebra.TensorProduct.map_comp, ← Algebra.TensorProduct.map_comp]
    congr 1
  rw [leftTranslQuot_mk, parabolicCoaction_mk, parabolicCoaction_mk]
  change Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R J) (AlgHom.id R (BorelCoord R n))
      (rightCoaction R n (GLRep.leftTranslHom R n b g)) =
    Algebra.TensorProduct.map (leftTranslQuot J hJ b) (AlgHom.id R (BorelCoord R n))
      (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R J) (AlgHom.id R (BorelCoord R n))
        (rightCoaction R n g))
  rw [show rightCoaction R n (GLRep.leftTranslHom R n b g) =
      Algebra.TensorProduct.map (GLRep.leftTranslHom R n b) (AlgHom.id R (BorelCoord R n))
        (rightCoaction R n g) from h1, ← AlgHom.comp_apply, h2, AlgHom.comp_apply]

/-! ### The induced module -/

section Induction

variable {M : Type v} [AddCommGroup M] [Module R M] {N : Type v} [AddCommGroup N] [Module R N]

/-- The diagonal right coaction of `B` on `𝒪(Pᵢ) ⊗ M`, `f ⊗ m ↦ Σ (f₀ ⊗ m₀) ⊗ f₁ m₁`, for a right
`𝒪(B)`-coaction `ρ` on `M`. -/
def parabolicTensorCoaction (ρ : M →ₗ[R] M ⊗[R] BorelCoord R n) :
    ParabolicCoord R n i ⊗[R] M →ₗ[R] (ParabolicCoord R n i ⊗[R] M) ⊗[R] BorelCoord R n :=
  (LinearMap.mul' R (BorelCoord R n)).lTensor _ ∘ₗ
    (TensorProduct.tensorTensorTensorComm R (ParabolicCoord R n i) (BorelCoord R n) M
      (BorelCoord R n)).toLinearMap ∘ₗ
    TensorProduct.map (parabolicCoaction R n i).toLinearMap ρ

theorem parabolicTensorCoaction_tmul (ρ : M →ₗ[R] M ⊗[R] BorelCoord R n)
    (f : ParabolicCoord R n i) (m : M) :
    parabolicTensorCoaction R n i ρ (f ⊗ₜ m) =
      (LinearMap.mul' R (BorelCoord R n)).lTensor _
        (TensorProduct.tensorTensorTensorComm R (ParabolicCoord R n i) (BorelCoord R n) M
          (BorelCoord R n) (parabolicCoaction R n i f ⊗ₜ ρ m)) :=
  rfl

/-- **Rank-one induction** `H_{sᵢ}(M) = (𝒪(Pᵢ) ⊗ M)^B`.

For a right `𝒪(B)`-coaction `ρ` on `M` (the `B`-module `M`), the invariants of the diagonal
coaction `FlagVarieties.parabolicTensorCoaction` on `𝒪(Pᵢ) ⊗ M`: as functions `x : Pᵢ → M`, those
with `x(p b) = b⁻¹ · x(p)`. This is the semi-invariant model of `H⁰(Pᵢ/B, Pᵢ ×^B M)`, as
`sectionsEquivSemiInvariants` is for line bundles (`FlagVarieties.rankOneInductionSectionsEquiv`).
-/
def rankOneInduction (ρ : M →ₗ[R] M ⊗[R] BorelCoord R n) :
    Submodule R (ParabolicCoord R n i ⊗[R] M) :=
  LinearMap.eqLocus (parabolicTensorCoaction R n i ρ)
    ((TensorProduct.mk R (ParabolicCoord R n i ⊗[R] M) (BorelCoord R n)).flip 1)

theorem mem_rankOneInduction (ρ : M →ₗ[R] M ⊗[R] BorelCoord R n)
    (x : ParabolicCoord R n i ⊗[R] M) :
    x ∈ rankOneInduction R n i ρ ↔ parabolicTensorCoaction R n i ρ x = x ⊗ₜ 1 := by
  rw [rankOneInduction, LinearMap.mem_eqLocus]
  rfl

variable {R n i}

variable (R n i) in
theorem tensorCoaction_rTensor (φ : M →ₗ[R] N) :
    (LinearMap.mul' R (BorelCoord R n)).lTensor (ParabolicCoord R n i ⊗[R] N) ∘ₗ
        (TensorProduct.tensorTensorTensorComm R (ParabolicCoord R n i) (BorelCoord R n) N
          (BorelCoord R n)).toLinearMap ∘ₗ
        TensorProduct.map LinearMap.id (φ.rTensor (BorelCoord R n)) =
      (φ.lTensor (ParabolicCoord R n i)).rTensor (BorelCoord R n) ∘ₗ
        (LinearMap.mul' R (BorelCoord R n)).lTensor (ParabolicCoord R n i ⊗[R] M) ∘ₗ
        (TensorProduct.tensorTensorTensorComm R (ParabolicCoord R n i) (BorelCoord R n) M
          (BorelCoord R n)).toLinearMap := by
  refine TensorProduct.ext_fourfold' fun p b m b' => ?_
  simp

/-- Naturality of the diagonal coaction in comodule maps. -/
theorem parabolicTensorCoaction_lTensor {ρ : M →ₗ[R] M ⊗[R] BorelCoord R n}
    {σ : N →ₗ[R] N ⊗[R] BorelCoord R n} (φ : M →ₗ[R] N) (hφ : φ.rTensor _ ∘ₗ ρ = σ ∘ₗ φ)
    (x : ParabolicCoord R n i ⊗[R] M) :
    parabolicTensorCoaction R n i σ (φ.lTensor _ x) =
      (φ.lTensor (ParabolicCoord R n i)).rTensor _ (parabolicTensorCoaction R n i ρ x) := by
  induction x with
  | tmul f m =>
    rw [LinearMap.lTensor_tmul, parabolicTensorCoaction_tmul, parabolicTensorCoaction_tmul,
      ← LinearMap.comp_apply σ φ, ← hφ, LinearMap.comp_apply]
    exact LinearMap.congr_fun (tensorCoaction_rTensor R n i φ) (parabolicCoaction R n i f ⊗ₜ ρ m)
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

/-- **Functoriality of `H_{sᵢ}`**: a map of comodules `φ : M → N` induces
`H_{sᵢ}(M) → H_{sᵢ}(N)`, `x ↦ (id ⊗ φ)(x)`. -/
def rankOneInductionMap {ρ : M →ₗ[R] M ⊗[R] BorelCoord R n} {σ : N →ₗ[R] N ⊗[R] BorelCoord R n}
    (φ : M →ₗ[R] N) (hφ : φ.rTensor _ ∘ₗ ρ = σ ∘ₗ φ) :
    rankOneInduction R n i ρ →ₗ[R] rankOneInduction R n i σ :=
  (φ.lTensor (ParabolicCoord R n i)).restrict fun x hx => by
    rw [mem_rankOneInduction] at hx ⊢
    rw [parabolicTensorCoaction_lTensor φ hφ, hx, LinearMap.rTensor_tmul]

theorem rankOneInductionMap_apply {ρ : M →ₗ[R] M ⊗[R] BorelCoord R n}
    {σ : N →ₗ[R] N ⊗[R] BorelCoord R n} (φ : M →ₗ[R] N) (hφ : φ.rTensor _ ∘ₗ ρ = σ ∘ₗ φ)
    (x : rankOneInduction R n i ρ) :
    (rankOneInductionMap φ hφ x : ParabolicCoord R n i ⊗[R] N) = φ.lTensor _ x :=
  rfl

theorem rankOneInductionMap_id (ρ : M →ₗ[R] M ⊗[R] BorelCoord R n) :
    rankOneInductionMap (i := i) (LinearMap.id : M →ₗ[R] M)
      (by rw [LinearMap.rTensor_id, LinearMap.id_comp, LinearMap.comp_id]) =
      LinearMap.id (M := rankOneInduction R n i ρ) := by
  refine LinearMap.ext fun x => Subtype.ext ?_
  change (LinearMap.id : M →ₗ[R] M).lTensor _ x.1 = x.1
  rw [LinearMap.lTensor_id, LinearMap.id_apply]

theorem rankOneInductionMap_comp {P : Type v} [AddCommGroup P] [Module R P]
    {ρ : M →ₗ[R] M ⊗[R] BorelCoord R n} {σ : N →ₗ[R] N ⊗[R] BorelCoord R n}
    {τ : P →ₗ[R] P ⊗[R] BorelCoord R n} (φ : M →ₗ[R] N) (hφ : φ.rTensor _ ∘ₗ ρ = σ ∘ₗ φ)
    (ψ : N →ₗ[R] P) (hψ : ψ.rTensor _ ∘ₗ σ = τ ∘ₗ ψ) :
    rankOneInductionMap (i := i) (ψ ∘ₗ φ) (by
      rw [LinearMap.rTensor_comp, LinearMap.comp_assoc, hφ, ← LinearMap.comp_assoc, hψ,
        LinearMap.comp_assoc]) =
      rankOneInductionMap ψ hψ ∘ₗ rankOneInductionMap φ hφ := by
  refine LinearMap.ext fun x => Subtype.ext ?_
  change (ψ ∘ₗ φ).lTensor _ x.1 = ψ.lTensor _ (φ.lTensor _ x.1)
  rw [LinearMap.lTensor_comp, LinearMap.comp_apply]

/-! ### The action of `B(R)` -/

variable (R n i) in
/-- Left translation by `b ∈ B(R)` on `𝒪(Pᵢ) ⊗ M`, acting on the first factor. -/
def parabolicLeftTransl (b : GLRep.borel R n) :
    ParabolicCoord R n i ⊗[R] M →ₗ[R] ParabolicCoord R n i ⊗[R] M :=
  (parabolicLeftTranslAlg R n i b).toLinearMap.rTensor M

theorem parabolicLeftTransl_tmul (b : GLRep.borel R n) (f : ParabolicCoord R n i) (m : M) :
    parabolicLeftTransl R n i b (f ⊗ₜ m) = parabolicLeftTranslAlg R n i b f ⊗ₜ m :=
  rfl

variable (R n i) in
theorem tensorCoaction_leftTransl (L : ParabolicCoord R n i →ₗ[R] ParabolicCoord R n i) :
    (LinearMap.mul' R (BorelCoord R n)).lTensor (ParabolicCoord R n i ⊗[R] M) ∘ₗ
        (TensorProduct.tensorTensorTensorComm R (ParabolicCoord R n i) (BorelCoord R n) M
          (BorelCoord R n)).toLinearMap ∘ₗ
        TensorProduct.map (L.rTensor (BorelCoord R n)) LinearMap.id =
      (L.rTensor M).rTensor (BorelCoord R n) ∘ₗ
        (LinearMap.mul' R (BorelCoord R n)).lTensor (ParabolicCoord R n i ⊗[R] M) ∘ₗ
        (TensorProduct.tensorTensorTensorComm R (ParabolicCoord R n i) (BorelCoord R n) M
          (BorelCoord R n)).toLinearMap := by
  refine TensorProduct.ext_fourfold' fun p b m b' => ?_
  simp

theorem parabolicTensorCoaction_leftTransl (ρ : M →ₗ[R] M ⊗[R] BorelCoord R n)
    (b : GLRep.borel R n) (x : ParabolicCoord R n i ⊗[R] M) :
    parabolicTensorCoaction R n i ρ (parabolicLeftTransl R n i b x) =
      (parabolicLeftTransl R n i b).rTensor _ (parabolicTensorCoaction R n i ρ x) := by
  induction x with
  | tmul f m =>
    have hmap' : (Algebra.TensorProduct.map (parabolicLeftTranslAlg R n i b)
        (AlgHom.id R (BorelCoord R n))).toLinearMap =
        (parabolicLeftTranslAlg R n i b).toLinearMap.rTensor (BorelCoord R n) :=
      TensorProduct.ext' fun p c => rfl
    have hmap : Algebra.TensorProduct.map (parabolicLeftTranslAlg R n i b)
        (AlgHom.id R (BorelCoord R n)) (parabolicCoaction R n i f) =
        (parabolicLeftTranslAlg R n i b).toLinearMap.rTensor (BorelCoord R n)
          (parabolicCoaction R n i f) :=
      LinearMap.congr_fun hmap' _
    rw [parabolicLeftTransl_tmul, parabolicTensorCoaction_tmul, parabolicTensorCoaction_tmul,
      parabolicCoaction_leftTransl, hmap]
    exact LinearMap.congr_fun (tensorCoaction_leftTransl R n i
      (parabolicLeftTranslAlg R n i b).toLinearMap) (parabolicCoaction R n i f ⊗ₜ ρ m)
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

theorem parabolicLeftTransl_one (x : ParabolicCoord R n i ⊗[R] M) :
    parabolicLeftTransl R n i 1 x = x := by
  induction x with
  | tmul f m =>
    rw [parabolicLeftTransl_tmul, parabolicLeftTranslAlg, map_one]
    rfl
  | add x y hx hy => rw [map_add, hx, hy]

theorem parabolicLeftTransl_mul (b b' : GLRep.borel R n) (x : ParabolicCoord R n i ⊗[R] M) :
    parabolicLeftTransl R n i (b * b') x =
      parabolicLeftTransl R n i b (parabolicLeftTransl R n i b' x) := by
  induction x with
  | tmul f m =>
    rw [parabolicLeftTransl_tmul, parabolicLeftTransl_tmul, parabolicLeftTransl_tmul,
      parabolicLeftTranslAlg, map_mul]
    rfl
  | add x y hx hy => rw [map_add, hx, hy, map_add, map_add]

theorem parabolicLeftTransl_mem (ρ : M →ₗ[R] M ⊗[R] BorelCoord R n) (b : GLRep.borel R n)
    {x : ParabolicCoord R n i ⊗[R] M} (hx : x ∈ rankOneInduction R n i ρ) :
    parabolicLeftTransl R n i b x ∈ rankOneInduction R n i ρ := by
  rw [mem_rankOneInduction] at hx ⊢
  rw [parabolicTensorCoaction_leftTransl, hx, LinearMap.rTensor_tmul]

variable (R n i) in
/-- **The action of `B(R)` on `H_{sᵢ}(M)`** by left translation, `(b · x)(p) = x(b⁻¹ p)`. -/
def rankOneInductionRep (ρ : M →ₗ[R] M ⊗[R] BorelCoord R n) :
    Representation R (GLRep.borel R n) (rankOneInduction R n i ρ) where
  toFun b := (parabolicLeftTransl R n i b).restrict fun _ hx => parabolicLeftTransl_mem ρ b hx
  map_one' := LinearMap.ext fun x => Subtype.ext (parabolicLeftTransl_one x.1)
  map_mul' b b' := LinearMap.ext fun x => Subtype.ext (parabolicLeftTransl_mul b b' x.1)

theorem rankOneInductionRep_apply (ρ : M →ₗ[R] M ⊗[R] BorelCoord R n) (b : GLRep.borel R n)
    (x : rankOneInduction R n i ρ) :
    (rankOneInductionRep R n i ρ b x : ParabolicCoord R n i ⊗[R] M) =
      parabolicLeftTransl R n i b x :=
  rfl

/-- The action of `B(R)` commutes with the maps `H_{sᵢ}(φ)`. -/
theorem rankOneInductionMap_rep {ρ : M →ₗ[R] M ⊗[R] BorelCoord R n}
    {σ : N →ₗ[R] N ⊗[R] BorelCoord R n} (φ : M →ₗ[R] N) (hφ : φ.rTensor _ ∘ₗ ρ = σ ∘ₗ φ)
    (b : GLRep.borel R n) (x : rankOneInduction R n i ρ) :
    rankOneInductionMap φ hφ (rankOneInductionRep R n i ρ b x) =
      rankOneInductionRep R n i σ b (rankOneInductionMap φ hφ x) := by
  refine Subtype.ext ?_
  change φ.lTensor _ (parabolicLeftTransl R n i b x.1) =
    parabolicLeftTransl R n i b (φ.lTensor _ x.1)
  rw [parabolicLeftTransl, parabolicLeftTransl, ← LinearMap.comp_apply, ← LinearMap.comp_apply,
    LinearMap.lTensor_comp_rTensor, LinearMap.rTensor_comp_lTensor]

end Induction

/-! ### The character modules `R_η` -/

variable {n} in
/-- **The character module `R_η`**: `b · r = η(b) r`, i.e. `ρ(r) = r ⊗ η`. -/
def charCoaction (η : Fin n → ℤ) : R →ₗ[R] R ⊗[R] BorelCoord R n :=
  (TensorProduct.mk R R (BorelCoord R n)).flip
    ((borelCharacterUnit R n η : (BorelCoord R n)ˣ) : BorelCoord R n)

variable {R n i}

/-- Multiplication by a unit of `𝒪(B)`, as a linear equivalence. -/
def borelUnitMul (u : (BorelCoord R n)ˣ) : BorelCoord R n ≃ₗ[R] BorelCoord R n :=
  LinearEquiv.ofLinearMap (LinearMap.mulRight R (u : BorelCoord R n))
    (LinearMap.mulRight R ((u⁻¹ : (BorelCoord R n)ˣ) : BorelCoord R n))
    (LinearMap.ext fun x => by simp [mul_assoc])
    (LinearMap.ext fun x => by simp [mul_assoc])

/-- `(p ⊗ b) ↦ (p ⊗ 1) ⊗ b η`. -/
def charTwist (η : Fin n → ℤ) :
    ParabolicCoord R n i ⊗[R] BorelCoord R n ≃ₗ[R]
      (ParabolicCoord R n i ⊗[R] R) ⊗[R] BorelCoord R n :=
  TensorProduct.congr (TensorProduct.rid R (ParabolicCoord R n i)).symm
    (borelUnitMul (borelCharacterUnit R n η))

theorem charTwist_tmul (η : Fin n → ℤ) (p : ParabolicCoord R n i) (b : BorelCoord R n) :
    charTwist η (p ⊗ₜ b) =
      (p ⊗ₜ (1 : R)) ⊗ₜ (b * ((borelCharacterUnit R n η : (BorelCoord R n)ˣ) : BorelCoord R n)) :=
  rfl

theorem parabolicTensorCoaction_charCoaction (η : Fin n → ℤ) (f : ParabolicCoord R n i) :
    parabolicTensorCoaction R n i (charCoaction R η) (f ⊗ₜ (1 : R)) =
      charTwist η (parabolicCoaction R n i f) := by
  have h : (LinearMap.mul' R (BorelCoord R n)).lTensor (ParabolicCoord R n i ⊗[R] R) ∘ₗ
      (TensorProduct.tensorTensorTensorComm R (ParabolicCoord R n i) (BorelCoord R n) R
        (BorelCoord R n)).toLinearMap ∘ₗ
      (TensorProduct.mk R (ParabolicCoord R n i ⊗[R] BorelCoord R n)
        (R ⊗[R] BorelCoord R n)).flip
        ((1 : R) ⊗ₜ ((borelCharacterUnit R n η : (BorelCoord R n)ˣ) : BorelCoord R n)) =
      (charTwist η).toLinearMap := by
    refine TensorProduct.ext' fun p b => ?_
    simp [charTwist_tmul]
  rw [parabolicTensorCoaction_tmul]
  exact LinearMap.congr_fun h (parabolicCoaction R n i f)

/-- For `M = R_η`, the invariants are the semi-invariants of weight `η`. -/
theorem tmul_one_mem_rankOneInduction_iff (η : Fin n → ℤ) (f : ParabolicCoord R n i) :
    f ⊗ₜ (1 : R) ∈ rankOneInduction R n i (charCoaction R η) ↔
      IsParabolicSemiInvariant η f := by
  have h : (f ⊗ₜ (1 : R)) ⊗ₜ (1 : BorelCoord R n) =
      charTwist η (f ⊗ₜ (((borelCharacterUnit R n η)⁻¹ : (BorelCoord R n)ˣ) : BorelCoord R n)) := by
    rw [charTwist_tmul, Units.inv_mul]
  rw [mem_rankOneInduction, parabolicTensorCoaction_charCoaction, h,
    (charTwist η).injective.eq_iff]
  rfl

theorem map_rid_rankOneInduction (η : Fin n → ℤ) :
    (rankOneInduction R n i (charCoaction R η)).map
        (TensorProduct.rid R (ParabolicCoord R n i) : ParabolicCoord R n i ⊗[R] R →ₗ[R] _) =
      quotientSemiInvariants R n (parabolicIdeal R n i) η := by
  ext f
  rw [Submodule.map_equiv_eq_comap_symm, Submodule.mem_comap, LinearEquiv.coe_coe,
    TensorProduct.rid_symm_apply, tmul_one_mem_rankOneInduction_iff,
    mem_quotientSemiInvariants_parabolicIdeal_iff]

variable (R n i) in
/-- `H_{sᵢ}(R_η) ≅ (𝒪(Pᵢ))^{(B, η)}`, `f ⊗ r ↦ r f`. -/
def rankOneInductionCharEquiv (η : Fin n → ℤ) :
    rankOneInduction R n i (charCoaction R η) ≃ₗ[R]
      quotientSemiInvariants R n (parabolicIdeal R n i) η :=
  (TensorProduct.rid R (ParabolicCoord R n i)).ofSubmodules _ _ (map_rid_rankOneInduction η)

theorem rankOneInductionCharEquiv_apply (η : Fin n → ℤ)
    (x : rankOneInduction R n i (charCoaction R η)) :
    (rankOneInductionCharEquiv R n i η x : ParabolicCoord R n i) =
      TensorProduct.rid R (ParabolicCoord R n i) x :=
  rfl

theorem rid_parabolicLeftTransl (b : GLRep.borel R n) (x : ParabolicCoord R n i ⊗[R] R) :
    TensorProduct.rid R (ParabolicCoord R n i) (parabolicLeftTransl R n i b x) =
      parabolicLeftTranslAlg R n i b (TensorProduct.rid R (ParabolicCoord R n i) x) := by
  have h : (TensorProduct.rid R (ParabolicCoord R n i)).toLinearMap ∘ₗ
      parabolicLeftTransl R n i b =
      (parabolicLeftTranslAlg R n i b).toLinearMap ∘ₗ
        (TensorProduct.rid R (ParabolicCoord R n i)).toLinearMap := by
    refine TensorProduct.ext' fun f r => ?_
    simp [parabolicLeftTransl_tmul]
  exact LinearMap.congr_fun h x

theorem rankOneInductionCharEquiv_rep (η : Fin n → ℤ) (b : GLRep.borel R n)
    (x : rankOneInduction R n i (charCoaction R η)) :
    rankOneInductionCharEquiv R n i η (rankOneInductionRep R n i (charCoaction R η) b x) =
      semiInvariantsRep (parabolicIdeal R n i) (isLeftTranslStable_parabolicIdeal R n i) η b
        (rankOneInductionCharEquiv R n i η x) :=
  Subtype.ext (rid_parabolicLeftTransl b x.1)

/-! ### `H_{sᵢ}(R_η) = H⁰(X_{sᵢ}, 𝓛(η))` -/

variable (hi : i + 1 < n)

theorem semiInvariantsEquivOfEq_semiInvariantsRep {J J' : Ideal (GLCoord R n)} (h : J = J')
    (hJ : IsLeftTranslStable J) (hJ' : IsLeftTranslStable J') (η : Fin n → ℤ)
    (b : GLRep.borel R n) (x : quotientSemiInvariants R n J η) :
    semiInvariantsEquivOfEq h η (semiInvariantsRep J hJ η b x) =
      semiInvariantsRep J' hJ' η b (semiInvariantsEquivOfEq h η x) := by
  subst h
  rfl

variable (R n i) in
/-- `X_{sᵢ}` is stable under `B`. -/
theorem isLeftTranslStable_preimageIdeal_simpleSchubert :
    IsLeftTranslStable (preimageIdeal R n (simpleSchubert R n i hi)) := by
  rw [preimageIdeal_simpleSchubert]
  exact isLeftTranslStable_parabolicIdeal R n i

variable (R n i) in
/-- **`H_{sᵢ}(R_η) ≅ H⁰(X_{sᵢ}, 𝓛(η))`**: rank-one induction of a character is the space of
sections of the line bundle over `X_{sᵢ} = Pᵢ/B` (`sectionsEquivSemiInvariants` and
`π⁻¹(X_{sᵢ}) = Pᵢ`). -/
def rankOneInductionSectionsEquiv (η : Fin n → ℤ) :
    rankOneInduction R n i (charCoaction R η) ≃ₗ[R] sections R n (simpleSchubert R n i hi) η :=
  (rankOneInductionCharEquiv R n i η).trans
    ((semiInvariantsEquivOfEq (preimageIdeal_simpleSchubert R n i hi).symm η).trans
      (sectionsEquivSemiInvariants R n _ η).symm)

/-- The isomorphism `H_{sᵢ}(R_η) ≅ H⁰(X_{sᵢ}, 𝓛(η))` is `B(R)`-equivariant. -/
theorem rankOneInductionSectionsEquiv_rep (η : Fin n → ℤ) (b : GLRep.borel R n)
    (x : rankOneInduction R n i (charCoaction R η)) :
    rankOneInductionSectionsEquiv R n i hi η (rankOneInductionRep R n i (charCoaction R η) b x) =
      sectionsRep R n (simpleSchubert R n i hi) η
        (isLeftTranslStable_preimageIdeal_simpleSchubert R n i hi) b
        (rankOneInductionSectionsEquiv R n i hi η x) := by
  apply (sectionsEquivSemiInvariants R n (simpleSchubert R n i hi) η).injective
  rw [sectionsEquivSemiInvariants_sectionsRep]
  simp only [rankOneInductionSectionsEquiv, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]
  rw [rankOneInductionCharEquiv_rep, semiInvariantsEquivOfEq_semiInvariantsRep]

/-- `H_{sᵢ}(R_η)` is free of rank `max(0, η_{i+1} - ηᵢ + 1)`. -/
theorem finrank_rankOneInduction_charCoaction [Nontrivial R] (η : Fin n → ℤ) :
    Module.finrank R (rankOneInduction R n i (charCoaction R η)) =
      (η (rowB n i hi) - η (rowA n i hi) + 1).toNat := by
  rw [(rankOneInductionSectionsEquiv R n i hi η).finrank_eq, finrank_sections_simpleSchubert]

end FlagVarieties
