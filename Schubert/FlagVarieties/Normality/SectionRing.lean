import Schubert.FlagVarieties.LineBundle.Minors
import Schubert.FlagVarieties.Modules.Geometric
import Schubert.FlagVarieties.Modules.SectionCharacter
import Schubert.FlagVarieties.Normality.Unconditional
import Schubert.FlagVarieties.Schubert.UnionPreimage

/-!
# The multigraded section ring of a Schubert union

A ring-level form of "`X_S` is the multi-Proj of its section ring", i.e. of the projective
normality of Schubert unions.

**Products of sections** (scheme-theoretic model, any commutative ring `R`). For an ideal
`J ⊆ 𝒪(GLₙ)`, the semi-invariants `quotientSemiInvariants R n J η ⊆ 𝒪(GLₙ)/J` (the scheme-theoretic
model of `H⁰(X, 𝓛(η))`) multiply: weight `η` times weight `η'` lands in weight `η + η'`, and `1` has
weight `0` (`FlagVarieties.mul_mem_quotientSemiInvariants`,
`FlagVarieties.one_mem_quotientSemiInvariants`). So they form a graded monoid, and `⨁_η` of them is
a commutative graded `R`-algebra. Transported through `sectionsEquivSemiInvariants`,
this gives

* `FlagVarieties.sectionsMul R n I η η' : H⁰(X, 𝓛(η)) →ₗ H⁰(X, 𝓛(η')) →ₗ H⁰(X, 𝓛(η + η'))`
  and its tensor form `sectionsMulTensor`, with unit `sectionsOne`;
* associativity, commutativity and the unit laws (`sectionsMul_assoc`, `sectionsMul_comm`,
  `sectionsMul_one_left`, `sectionsMul_one_right`), up to the identification
  `sectionsCongr : H⁰(X, 𝓛(η)) ≃ H⁰(X, 𝓛(η'))` for `η = η'`;
* `B`-equivariance: `sectionsRep_sectionsMul`, `sectionsRep_sectionsOne`.

The dominant part `dominantSectionRing J = ⨁_m H⁰(X, 𝓛(−λ_m))` (`λ_m = shapeWeight m`, `m` a
column shape) is a commutative graded `R`-algebra, and `sectionsDirectSumEquiv` identifies it with
`⨁_m H⁰(X, 𝓛(−λ_m))` built from the geometric sections, the product of homogeneous elements
being `sectionsMul` (`sectionsDirectSumEquiv_of_mul_of`).

**The isomorphism `S(X_S) ≅ A / I_S`** (over an algebraically closed field `K` of characteristic
`0`). Let `A = ⨁_m A_m` be the flag-minor (Plücker) algebra, graded by column shapes
(`PointModel.FlagMinorAlgebra K n`), and `S(X_S) = ⨁_m H⁰(X_S, 𝓛(−λ_m))` the section ring in the
ring model (`PointModel.SchubertSectionRing K S`, pieces
`sectionPiece K S m ≅ sectionSpace K S λ_m`). Restriction of functions is a surjective map of graded
`K`-algebras `A → S(X_S)` (projective normality), whose kernel is the ideal `I_S` of the elements
whose homogeneous components vanish on `X_S` (`ker_minorRestriction`). Hence
`PointModel.schubertSectionRingEquiv hS : A ⧸ I_S ≃ₐ[K] S(X_S)`, compatible with the gradings
(`schubertSectionRingEquiv_mk_of`; `I_S` is homogeneous, `mem_flagMinorIdeal_iff_of`).

With the geometric sections of the Schubert union subscheme `schubertUnion K n S`, the same
isomorphism is `geometricSectionRingEquiv` (`Normality/GeometricSections`).

Here `A` is the external direct sum of the spans `A_m ⊆ K[x_ij]`; that their internal sum is
direct is not used.
-/

noncomputable section

open Schubert Demazure.FlagModule Demazure.SchubertUnions FinPermutation
open scoped TensorProduct DirectSum

universe u

/-! ### Additivity of the shape weight -/

namespace FlagVarieties.PointModel

variable {n : ℕ}

theorem shapeWeightZ_add (m m' : ColumnShape n) :
    shapeWeightZ (m + m') = shapeWeightZ m + shapeWeightZ m' := by
  funext i
  simp only [shapeWeightZ, shapeWeight_add, Pi.add_apply, Nat.cast_add]

theorem shapeWeightZ_zero : shapeWeightZ (0 : ColumnShape n) = 0 := by
  funext i
  simp only [shapeWeightZ, shapeWeight_zero, Pi.zero_apply, Nat.cast_zero]

theorem neg_shapeWeightZ_add (m m' : ColumnShape n) :
    -shapeWeightZ m + -shapeWeightZ m' = -shapeWeightZ (m + m') := by
  rw [shapeWeightZ_add, neg_add]

/-! ### Graded maps between internally graded algebras -/

section Graded

variable {ι K P Q : Type*} [CommRing K] [CommRing P] [Algebra K P] [CommRing Q] [Algebra K Q]
  {M : ι → Submodule K P} {N : ι → Submodule K Q} (ψ : P →ₐ[K] Q)
  (hψ : ∀ i, ∀ x ∈ M i, ψ x ∈ N i)

/-- The degree-`i` component `M_i → N_i` of an algebra map respecting the gradings. -/
def gradedPiece (i : ι) : M i →ₗ[K] N i :=
  ψ.toLinearMap.restrict (hψ i)

theorem coe_gradedPiece (i : ι) (x : M i) : (gradedPiece ψ hψ i x : Q) = ψ x :=
  rfl

variable [AddCommMonoid ι] [DecidableEq ι] [SetLike.GradedMonoid M] [SetLike.GradedMonoid N]

/-- The map of graded algebras `⨁_i M_i → ⨁_i N_i` induced by an algebra map `ψ : P → Q` with
`ψ(M_i) ⊆ N_i`. -/
def gradedMap : (⨁ i, M i) →ₐ[K] ⨁ i, N i :=
  DirectSum.toAlgebra K _
    (fun i => (DirectSum.lof K ι (fun i => ↥(N i)) i).comp (gradedPiece ψ hψ i))
    (by
      rw [DirectSum.one_def]
      exact congrArg (DirectSum.of (fun i => ↥(N i)) 0) (Subtype.ext (map_one ψ)))
    (fun {i j} a b => by
      simp only [LinearMap.comp_apply, DirectSum.lof_eq_of, DirectSum.of_mul_of]
      exact congrArg (DirectSum.of (fun i => ↥(N i)) (i + j))
        (Subtype.ext (map_mul ψ (a : P) (b : P))))

theorem gradedMap_of (i : ι) (x : M i) :
    gradedMap ψ hψ (DirectSum.of (fun i => ↥(M i)) i x) =
      DirectSum.of (fun i => ↥(N i)) i (gradedPiece ψ hψ i x) := by
  show DirectSum.toAddMonoid (fun i => ((DirectSum.lof K ι (fun i => ↥(N i)) i).comp
    (gradedPiece ψ hψ i)).toAddMonoidHom) (DirectSum.of _ i x) = _
  exact DirectSum.toAddMonoid_of _ _ _

theorem gradedMap_apply (x : ⨁ i, M i) (i : ι) :
    gradedMap ψ hψ x i = gradedPiece ψ hψ i (x i) := by
  induction x using DirectSum.induction_on with
  | zero => rw [map_zero, DirectSum.zero_apply, DirectSum.zero_apply, map_zero]
  | of j y =>
    rw [gradedMap_of]
    by_cases h : j = i
    · subst h
      rw [DirectSum.of_eq_same, DirectSum.of_eq_same]
    · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm h), DirectSum.of_eq_of_ne _ _ _ (Ne.symm h),
        map_zero]
  | add x y hx hy => rw [map_add, DirectSum.add_apply, DirectSum.add_apply, hx, hy, map_add]

theorem gradedMap_eq_zero_iff (x : ⨁ i, M i) : gradedMap ψ hψ x = 0 ↔ ∀ i, ψ (x i) = 0 := by
  constructor
  · intro h i
    have := congrArg (fun y : ⨁ i, N i => ((y i : N i) : Q)) h
    simpa only [gradedMap_apply, DirectSum.zero_apply, ZeroMemClass.coe_zero,
      coe_gradedPiece] using this
  · intro h
    ext i
    rw [gradedMap_apply, DirectSum.zero_apply]
    exact h i

theorem gradedMap_surjective (h : ∀ i, Function.Surjective (gradedPiece ψ hψ i)) :
    Function.Surjective (gradedMap ψ hψ) := by
  intro y
  induction y using DirectSum.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | of i z =>
    obtain ⟨x, rfl⟩ := h i z
    exact ⟨DirectSum.of _ i x, gradedMap_of ψ hψ i x⟩
  | add y y' hy hy' =>
    obtain ⟨x, rfl⟩ := hy
    obtain ⟨x', rfl⟩ := hy'
    exact ⟨x + x', map_add _ _ _⟩

end Graded

end FlagVarieties.PointModel

/-! ### Products of sections (scheme-theoretic model, any commutative ring) -/

namespace FlagVarieties

open PointModel.Complex
open PointModel (shapeWeightZ_zero neg_shapeWeightZ_add)

section Products

variable {R : Type u} [CommRing R] {n : ℕ}

theorem semiInvariantDefect_mul {J : Ideal (GLCoord R n)} {η η' : Fin n → ℤ} {f g : GLCoord R n}
    (hf : semiInvariantDefect R n J η f = 0) (hg : semiInvariantDefect R n J η' g = 0) :
    semiInvariantDefect R n J (η + η') (f * g) = 0 := by
  rw [semiInvariantDefect_apply, sub_eq_zero] at hf hg ⊢
  rw [map_mul (rightCoactionMod R n J), hf, hg, Algebra.TensorProduct.tmul_mul_tmul,
    ← map_mul (Ideal.Quotient.mk J), borelCharacterUnit_add, mul_inv (borelCharacterUnit R n η),
    Units.val_mul]

/-- `1` is a section of `𝓛(0)`. -/
theorem one_mem_quotientSemiInvariants (J : Ideal (GLCoord R n)) :
    (1 : GLCoord R n ⧸ J) ∈ quotientSemiInvariants R n J 0 := by
  refine ⟨1, ?_, map_one (Ideal.Quotient.mkₐ R J)⟩
  have h1 : rightCoactionMod R n J 1 = 1 := (rightCoactionMod R n J).map_one
  rw [SetLike.mem_coe, LinearMap.mem_ker, semiInvariantDefect_apply, h1,
    map_one (Ideal.Quotient.mk J), borelCharacterUnit_zero, inv_one,
    Units.val_one, Algebra.TensorProduct.one_def, sub_self]

/-- **The product of sections**: `H⁰(X, 𝓛(η)) · H⁰(X, 𝓛(η')) ⊆ H⁰(X, 𝓛(η + η'))`. -/
theorem mul_mem_quotientSemiInvariants {J : Ideal (GLCoord R n)} {η η' : Fin n → ℤ}
    {x y : GLCoord R n ⧸ J} (hx : x ∈ quotientSemiInvariants R n J η)
        (hy : y ∈ quotientSemiInvariants R n J η') :
    x * y ∈ quotientSemiInvariants R n J (η + η') := by
  obtain ⟨f, hf, rfl⟩ := hx
  obtain ⟨g, hg, rfl⟩ := hy
  exact ⟨f * g, LinearMap.mem_ker.mpr
    (semiInvariantDefect_mul (LinearMap.mem_ker.mp hf) (LinearMap.mem_ker.mp hg)),
    map_mul (Ideal.Quotient.mkₐ R J) f g⟩

/-- The semi-invariants of all weights form a graded monoid; `⨁_η quotientSemiInvariants R n J η` is
a
commutative graded `R`-algebra. -/
instance gradedMonoid_quotientSemiInvariants (J : Ideal (GLCoord R n)) :
    SetLike.GradedMonoid (quotientSemiInvariants R n J) where
  one_mem := one_mem_quotientSemiInvariants J
  mul_mem := @fun _ _ _ _ hx hy => mul_mem_quotientSemiInvariants hx hy

/-- `H⁰(X, 𝓛(−λ))` for the dominant weight `λ = shapeWeight m` of a column shape `m`, in the
scheme-theoretic model. -/
abbrev dominantSemiInvariants (J : Ideal (GLCoord R n)) (m : ColumnShape n) :
    Submodule R (GLCoord R n ⧸ J) :=
  quotientSemiInvariants R n J (-shapeWeightZ m)

theorem mem_dominantSemiInvariants {J : Ideal (GLCoord R n)} {m : ColumnShape n}
    {x : GLCoord R n ⧸ J} :
    x ∈ dominantSemiInvariants J m ↔ x ∈ quotientSemiInvariants R n J (-shapeWeightZ m) :=
  Iff.rfl

instance gradedMonoid_dominantSemiInvariants (J : Ideal (GLCoord R n)) :
    SetLike.GradedMonoid (dominantSemiInvariants J) where
  one_mem := by
    rw [mem_dominantSemiInvariants, shapeWeightZ_zero, neg_zero]
    exact one_mem_quotientSemiInvariants J
  mul_mem := @fun m m' _ _ hx hy => by
    rw [mem_dominantSemiInvariants, ← neg_shapeWeightZ_add]
    exact mul_mem_quotientSemiInvariants hx hy

/-- **The dominant section ring** `⨁_m H⁰(X, 𝓛(−λ_m))` of `X`, in the scheme-theoretic model,
a commutative graded `R`-algebra. -/
abbrev dominantSectionRing (J : Ideal (GLCoord R n)) :=
  ⨁ m : ColumnShape n, dominantSemiInvariants J m

instance (J : Ideal (GLCoord R n)) (m : ColumnShape n) :
    AddCommGroup (dominantSemiInvariants J m) :=
  Submodule.addCommGroup _

instance (J : Ideal (GLCoord R n)) :
    DirectSum.GCommRing fun m : ColumnShape n => ↥(dominantSemiInvariants J m) :=
  SetLike.gcommRing _


end Products

/-! ### Multiplication of geometric sections -/

section Sections

variable (R : Type u) [CommRing R] (n : ℕ) (I : (FlagScheme R n).IdealSheafData)

/-- The multiplication `H⁰(X, 𝓛(η)) × H⁰(X, 𝓛(η')) → H⁰(X, 𝓛(η + η'))` on the semi-invariants. -/
def semiInvariantsMul (J : Ideal (GLCoord R n)) (η η' : Fin n → ℤ) :
    quotientSemiInvariants R n J η →ₗ[R] quotientSemiInvariants R n J η' →ₗ[R]
        quotientSemiInvariants R n J (η + η') :=
  LinearMap.mk₂ R (fun x y => ⟨x * y, mul_mem_quotientSemiInvariants x.2 y.2⟩)
    (fun _ _ _ => Subtype.ext (add_mul _ _ _)) (fun _ _ _ => Subtype.ext (smul_mul_assoc _ _ _))
    (fun _ _ _ => Subtype.ext (mul_add _ _ _)) (fun _ _ _ => Subtype.ext (mul_smul_comm _ _ _))

variable {R n} in
theorem coe_semiInvariantsMul {J : Ideal (GLCoord R n)} {η η' : Fin n → ℤ}
    (x : quotientSemiInvariants R n J η) (y : quotientSemiInvariants R n J η') :
    (semiInvariantsMul R n J η η' x y : GLCoord R n ⧸ J) = x * y :=
  rfl

/-- **The multiplication of sections** `H⁰(X, 𝓛(η)) × H⁰(X, 𝓛(η')) → H⁰(X, 𝓛(η + η'))`: the
product of the semi-invariant functions on `π⁻¹(X)`, transported through
`sectionsEquivSemiInvariants`. -/
def sectionsMul (η η' : Fin n → ℤ) :
    sections R n I η →ₗ[R] sections R n I η' →ₗ[R] sections R n I (η + η') :=
  ((semiInvariantsMul R n (preimageIdeal R n I) η η').compl₁₂
      (sectionsEquivSemiInvariants R n I η).toLinearMap
          (sectionsEquivSemiInvariants R n I η').toLinearMap).compr₂
    (sectionsEquivSemiInvariants R n I (η + η')).symm.toLinearMap

/-- The multiplication of sections on the tensor product,
`H⁰(X, 𝓛(η)) ⊗ H⁰(X, 𝓛(η')) → H⁰(X, 𝓛(η + η'))`. -/
def sectionsMulTensor (η η' : Fin n → ℤ) :
    sections R n I η ⊗[R] sections R n I η' →ₗ[R] sections R n I (η + η') :=
  TensorProduct.lift (sectionsMul R n I η η')

/-- The unit section `1 ∈ H⁰(X, 𝓛(0))`. -/
def sectionsOne : sections R n I 0 :=
  (sectionsEquivSemiInvariants R n I 0).symm ⟨1, one_mem_quotientSemiInvariants _⟩

/-- `H⁰(X, 𝓛(η)) ≃ H⁰(X, 𝓛(η'))` for equal weights `η = η'`. -/
def sectionsCongr {η η' : Fin n → ℤ} (h : η = η') : sections R n I η ≃ₗ[R] sections R n I η' := by
  subst h
  exact LinearEquiv.refl R _

variable {R n I}

theorem sectionsMulTensor_tmul {η η' : Fin n → ℤ} (s : sections R n I η)
    (t : sections R n I η') : sectionsMulTensor R n I η η' (s ⊗ₜ t) = sectionsMul R n I η η' s t :=
  TensorProduct.lift.tmul _ _

theorem sectionsEquivSemiInvariants_sectionsMul {η η' : Fin n → ℤ} (s : sections R n I η)
    (t : sections R n I η') :
    sectionsEquivSemiInvariants R n I (η + η') (sectionsMul R n I η η' s t) =
      semiInvariantsMul R n _ η η' (sectionsEquivSemiInvariants R n I η s)
          (sectionsEquivSemiInvariants R n I η' t) :=
  LinearEquiv.apply_symm_apply _ _

/-- On functions on `π⁻¹(X)`, the multiplication of sections is the product. -/
theorem coe_sectionsEquivSemiInvariants_sectionsMul {η η' : Fin n → ℤ} (s : sections R n I η)
    (t : sections R n I η') :
    (sectionsEquivSemiInvariants R n I (η + η') (sectionsMul R n I η η' s t) :
        GLCoord R n ⧸ preimageIdeal R n I) =
      sectionsEquivSemiInvariants R n I η s * sectionsEquivSemiInvariants R n I η' t := by
  rw [sectionsEquivSemiInvariants_sectionsMul, coe_semiInvariantsMul]

theorem coe_sectionsEquivSemiInvariants_sectionsOne :
    (sectionsEquivSemiInvariants R n I 0 (sectionsOne R n I) : GLCoord R n ⧸ preimageIdeal R n I) =
        1 := by
  rw [sectionsOne, LinearEquiv.apply_symm_apply]

theorem coe_sectionsEquivSemiInvariants_sectionsCongr {η η' : Fin n → ℤ} (h : η = η')
    (s : sections R n I η) :
    (sectionsEquivSemiInvariants R n I η' (sectionsCongr R n I h s) : GLCoord R n ⧸ preimageIdeal R
        n I) =
      sectionsEquivSemiInvariants R n I η s := by
  subst h
  rfl

/-- Sections are determined by their functions on `π⁻¹(X)`. -/
theorem sections_ext {η : Fin n → ℤ} {s t : sections R n I η}
    (h : (sectionsEquivSemiInvariants R n I η s : GLCoord R n ⧸ preimageIdeal R n I) =
      sectionsEquivSemiInvariants R n I η t) : s = t :=
  (sectionsEquivSemiInvariants R n I η).injective (Subtype.ext h)

/-- **Associativity** of the multiplication of sections. -/
theorem sectionsMul_assoc {η η' η'' : Fin n → ℤ} (s : sections R n I η)
    (t : sections R n I η') (u : sections R n I η'') :
    sectionsCongr R n I (add_assoc η η' η'')
        (sectionsMul R n I _ _ (sectionsMul R n I η η' s t) u) =
      sectionsMul R n I _ _ s (sectionsMul R n I η' η'' t u) := by
  apply sections_ext
  simp only [coe_sectionsEquivSemiInvariants_sectionsCongr,
      coe_sectionsEquivSemiInvariants_sectionsMul, mul_assoc]

/-- **Commutativity** of the multiplication of sections. -/
theorem sectionsMul_comm {η η' : Fin n → ℤ} (s : sections R n I η) (t : sections R n I η') :
    sectionsCongr R n I (add_comm η η') (sectionsMul R n I η η' s t) =
      sectionsMul R n I η' η t s := by
  apply sections_ext
  rw [coe_sectionsEquivSemiInvariants_sectionsCongr, coe_sectionsEquivSemiInvariants_sectionsMul,
    coe_sectionsEquivSemiInvariants_sectionsMul, mul_comm]

/-- `1 · s = s`. -/
theorem sectionsMul_one_left {η : Fin n → ℤ} (s : sections R n I η) :
    sectionsCongr R n I (zero_add η) (sectionsMul R n I 0 η (sectionsOne R n I) s) = s := by
  apply sections_ext
  rw [coe_sectionsEquivSemiInvariants_sectionsCongr, coe_sectionsEquivSemiInvariants_sectionsMul,
    coe_sectionsEquivSemiInvariants_sectionsOne, one_mul]

/-- `s · 1 = s`. -/
theorem sectionsMul_one_right {η : Fin n → ℤ} (s : sections R n I η) :
    sectionsCongr R n I (add_zero η) (sectionsMul R n I η 0 s (sectionsOne R n I)) = s := by
  apply sections_ext
  rw [coe_sectionsEquivSemiInvariants_sectionsCongr, coe_sectionsEquivSemiInvariants_sectionsMul,
    coe_sectionsEquivSemiInvariants_sectionsOne, mul_one]

theorem coe_semiInvariantsRep {J : Ideal (GLCoord R n)} (hJ : IsLeftTranslStable J)
    (η : Fin n → ℤ) (b : GLRep.borel R n) (x : quotientSemiInvariants R n J η) :
    (semiInvariantsRep J hJ η b x : GLCoord R n ⧸ J) = leftTranslQuot J hJ b x :=
  rfl

/-- **`B`-equivariance** of the multiplication of sections: `b · (s t) = (b · s)(b · t)`. -/
theorem sectionsRep_sectionsMul (hJ : IsLeftTranslStable (preimageIdeal R n I))
    {η η' : Fin n → ℤ} (b : GLRep.borel R n) (s : sections R n I η) (t : sections R n I η') :
    sectionsRep R n I (η + η') hJ b (sectionsMul R n I η η' s t) =
      sectionsMul R n I η η' (sectionsRep R n I η hJ b s) (sectionsRep R n I η' hJ b t) := by
  apply sections_ext
  rw [sectionsEquivSemiInvariants_sectionsRep, coe_sectionsEquivSemiInvariants_sectionsMul,
    sectionsEquivSemiInvariants_sectionsRep, sectionsEquivSemiInvariants_sectionsRep,
        coe_semiInvariantsRep,
    coe_semiInvariantsRep, coe_semiInvariantsRep, coe_sectionsEquivSemiInvariants_sectionsMul,
        map_mul]

/-- `B` fixes the unit section. -/
theorem sectionsRep_sectionsOne (hJ : IsLeftTranslStable (preimageIdeal R n I))
    (b : GLRep.borel R n) : sectionsRep R n I 0 hJ b (sectionsOne R n I) = sectionsOne R n I := by
  apply sections_ext
  rw [sectionsEquivSemiInvariants_sectionsRep, coe_semiInvariantsRep,
      coe_sectionsEquivSemiInvariants_sectionsOne,
    map_one]

variable (R n I) in
/-- `⨁_m H⁰(X, 𝓛(−λ_m))`, built from the geometric sections, is the dominant section ring of the
preimage ideal (`sectionsEquivSemiInvariants` in each degree). -/
def sectionsDirectSumEquiv :
    (⨁ m : ColumnShape n, sections R n I (-shapeWeightZ m)) ≃ₗ[R]
      dominantSectionRing (preimageIdeal R n I) :=
  DirectSum.congrLinearEquiv fun m => sectionsEquivSemiInvariants R n I (-shapeWeightZ m)

theorem sectionsDirectSumEquiv_of (m : ColumnShape n) (s : sections R n I (-shapeWeightZ m)) :
    sectionsDirectSumEquiv R n I (DirectSum.of _ m s) =
      DirectSum.of (fun m => ↥(dominantSemiInvariants (preimageIdeal R n I) m)) m
        (sectionsEquivSemiInvariants R n I _ s) := by
  rw [sectionsDirectSumEquiv, DirectSum.coe_congrLinearEquiv, DirectSum.lmap_of]
  rfl

/-- In the dominant section ring, the product of homogeneous sections is `sectionsMul`. -/
theorem sectionsDirectSumEquiv_of_mul_of {m m' : ColumnShape n}
    (s : sections R n I (-shapeWeightZ m)) (t : sections R n I (-shapeWeightZ m')) :
    sectionsDirectSumEquiv R n I (DirectSum.of _ m s) *
        sectionsDirectSumEquiv R n I (DirectSum.of _ m' t) =
      sectionsDirectSumEquiv R n I (DirectSum.of _ (m + m')
        (sectionsCongr R n I (neg_shapeWeightZ_add m m') (sectionsMul R n I _ _ s t))) := by
  rw [sectionsDirectSumEquiv_of, sectionsDirectSumEquiv_of, sectionsDirectSumEquiv_of,
    DirectSum.of_mul_of]
  refine congrArg (DirectSum.of _ (m + m')) (Subtype.ext ?_)
  rw [coe_sectionsEquivSemiInvariants_sectionsCongr, coe_sectionsEquivSemiInvariants_sectionsMul]
  rfl

end Sections

end FlagVarieties

/-! ### The section ring of a Schubert union and the flag-minor algebra -/

namespace FlagVarieties.PointModel

variable {K : Type*} [Field K] {n : ℕ}

theorem borelCharValue_zero (b : Matrix (Fin n) (Fin n) K) : borelCharValue 0 b = 1 := by
  simp [borelCharValue]

theorem borelCharValue_add_of_isBorel {b : GL (Fin n) K} (hb : IsBorel b) (η η' : Fin n → ℤ) :
    borelCharValue (η + η') (b : Matrix (Fin n) (Fin n) K) = borelCharValue η b *
        borelCharValue η' b := by
  rw [borelCharValue, borelCharValue, borelCharValue, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => zpow_add₀ (diag_ne_zero_of_isBorel hb i) _ _

theorem isSemiInvOn_one (Z : Set (GL (Fin n) K)) : IsSemiInvOn Z 0 (1 : GLCoord K n) :=
  fun g _ b _ => by rw [map_one, map_one, borelCharValue_zero, one_mul]

theorem IsSemiInvOn.mul {Z : Set (GL (Fin n) K)} {η η' : Fin n → ℤ} {t t' : GLCoord K n}
    (h : IsSemiInvOn Z η t) (h' : IsSemiInvOn Z η' t') : IsSemiInvOn Z (η + η') (t * t') :=
  fun g hg b hb => by
    rw [map_mul, map_mul, h g hg b hb, h' g hg b hb, borelCharValue_add_of_isBorel hb]
    ring

theorem isSemiInvOn_of_mem_orbitIdeal {S : Finset (Equiv.Perm (Fin n))} {t : GLCoord K n}
    (ht : t ∈ orbitIdeal K S) (η : Fin n → ℤ) : IsSemiInvOn (orbitSet K S) η t :=
  fun g hg b hb => by
    rw [mem_orbitIdeal.mp ht (g * b) (orbitSet_mul_borel hg hb), mem_orbitIdeal.mp ht g hg,
      mul_zero]

instance gradedMonoid_minorSpan : SetLike.GradedMonoid (minorSpan K (n := n)) where
  one_mem := one_mem_minorSpan
  mul_mem := @fun _ _ _ _ hp hq => mul_mem_minorSpan hp hq

instance (m : ColumnShape n) : AddCommGroup (minorSpan K m) :=
  Submodule.addCommGroup _

instance : DirectSum.GCommRing fun m : ColumnShape n => ↥(minorSpan K m) :=
  SetLike.gcommRing _

variable (K) in
/-- **The flag-minor (Plücker) algebra** `A = ⨁_m A_m`, `A_m = minorSpan K m` (the span of the
products of flag minors of column shape `m`), graded by column shapes. -/
abbrev FlagMinorAlgebra (n : ℕ) :=
  ⨁ m : ColumnShape n, minorSpan K m

section Pieces

variable (S : Finset (Equiv.Perm (Fin n)))

variable (K) in
/-- **`H⁰(X_S, 𝓛(−λ))`**, `λ = shapeWeight m`, as the classes in `𝒪(π⁻¹ X_S) = 𝒪(GLₙ)/I_S` of the
semi-invariants of weight `λ`. -/
def sectionPiece (m : ColumnShape n) : Submodule K (GLCoord K n ⧸ orbitIdeal K S) :=
  (semiInvSpace (orbitSet K S) (shapeWeightZ m)).map
    (Ideal.Quotient.mkₐ K (orbitIdeal K S)).toLinearMap

variable {S} in
theorem mk_mem_sectionPiece_iff {m : ColumnShape n} {t : GLCoord K n} :
    Ideal.Quotient.mk (orbitIdeal K S) t ∈ sectionPiece K S m ↔
      IsSemiInvOn (orbitSet K S) (shapeWeightZ m) t := by
  constructor
  · rintro ⟨u, hu, hut⟩
    have hut' : Ideal.Quotient.mk (orbitIdeal K S) u = Ideal.Quotient.mk (orbitIdeal K S) t := hut
    have hd : u - t ∈ orbitIdeal K S := Ideal.Quotient.eq.mp hut'
    have := (mem_semiInvSpace.mp hu).sub (isSemiInvOn_of_mem_orbitIdeal hd (shapeWeightZ m))
    rwa [sub_sub_cancel] at this
  · intro ht
    exact ⟨t, ht, rfl⟩

instance gradedMonoid_sectionPiece : SetLike.GradedMonoid (sectionPiece K S) where
  one_mem := ⟨1, by
      rw [SetLike.mem_coe, mem_semiInvSpace, shapeWeightZ_zero]
      exact isSemiInvOn_one _,
    map_one (Ideal.Quotient.mkₐ K (orbitIdeal K S))⟩
  mul_mem := @fun _ _ _ _ hx hy => by
    obtain ⟨t, ht, rfl⟩ := hx
    obtain ⟨t', ht', rfl⟩ := hy
    refine ⟨t * t', ?_, map_mul (Ideal.Quotient.mkₐ K (orbitIdeal K S)) t t'⟩
    rw [SetLike.mem_coe, mem_semiInvSpace, shapeWeightZ_add]
    exact (mem_semiInvSpace.mp ht).mul (mem_semiInvSpace.mp ht')

variable (K) in
/-- **The multigraded section ring** `S(X_S) = ⨁_m H⁰(X_S, 𝓛(−λ_m))` of a Schubert union, a
commutative graded `K`-algebra. -/
abbrev SchubertSectionRing :=
  ⨁ m : ColumnShape n, sectionPiece K S m

instance (m : ColumnShape n) : AddCommGroup (sectionPiece K S m) :=
  Submodule.addCommGroup _

instance : DirectSum.GCommRing fun m : ColumnShape n => ↥(sectionPiece K S m) :=
  SetLike.gcommRing _

variable (K)

/-- The map `semiInvSpace → H⁰(X_S, 𝓛(−λ))` taking a semi-invariant to its class. -/
def toSectionPiece (m : ColumnShape n) :
    semiInvSpace (orbitSet K S) (shapeWeightZ m) →ₗ[K] sectionPiece K S m :=
  (Ideal.Quotient.mkₐ K (orbitIdeal K S)).toLinearMap.restrict fun t ht => ⟨t, ht, rfl⟩

theorem toSectionPiece_surjective (m : ColumnShape n) :
    Function.Surjective (toSectionPiece K S m) := by
  rintro ⟨y, t, ht, rfl⟩
  exact ⟨⟨t, ht⟩, rfl⟩

theorem ker_toSectionPiece (m : ColumnShape n) :
    LinearMap.ker (toSectionPiece K S m) = semiInvVanishing K S (shapeWeightZ m) := by
  ext t
  rw [LinearMap.mem_ker, semiInvVanishing, Submodule.mem_comap, Submodule.restrictScalars_mem,
    Submodule.coe_subtype, ← Ideal.Quotient.eq_zero_iff_mem]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

/-- The degree-`m` piece of `S(X_S)` is the ring model `sectionSpace K S λ` of
`H⁰(X_S, 𝓛(−λ))`. -/
def sectionSpaceEquivPiece (m : ColumnShape n) :
    sectionSpace K S (shapeWeightZ m) ≃ₗ[K] sectionPiece K S m :=
  (Submodule.quotEquivOfEq _ _ (ker_toSectionPiece K S m).symm).trans
    ((toSectionPiece K S m).quotKerEquivOfSurjective (toSectionPiece_surjective K S m))

/-- Restriction of polynomials to `π⁻¹ X_S`: `K[x_ij] → 𝒪(GLₙ) → 𝒪(GLₙ)/I_S`. -/
def restrictHom : MatrixEntryPolynomial K n →ₐ[K] GLCoord K n ⧸ orbitIdeal K S :=
  (Ideal.Quotient.mkₐ K (orbitIdeal K S)).comp
    (IsScalarTower.toAlgHom K (MatrixEntryPolynomial K n) (GLCoord K n))

theorem restrictHom_mem_sectionPiece :
    ∀ m, ∀ p ∈ minorSpan K m, restrictHom K S p ∈ sectionPiece K S m :=
  fun _ p hp => ⟨algebraMap _ _ p, isSemiInvOn_of_mem_minorSpan hp _, rfl⟩

/-- In degree `m`, the restriction map is `minorRestriction` (under `sectionSpaceEquivPiece`). -/
theorem sectionSpaceEquivPiece_minorRestriction (m : ColumnShape n) (a : minorSpan K m) :
    sectionSpaceEquivPiece K S m (minorRestriction K S m a) =
      gradedPiece (restrictHom K S) (restrictHom_mem_sectionPiece K S) m a :=
  rfl

theorem restrictHom_eq_zero_iff {m : ColumnShape n} (a : minorSpan K m) :
    restrictHom K S a = 0 ↔ (a : MatrixEntryPolynomial K n) ∈ vanishSpan K m S := by
  rw [← minorRestriction_eq_zero_iff, minorRestriction, LinearMap.comp_apply, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero, restrictHom, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
    Ideal.Quotient.eq_zero_iff_mem]
  rfl

/-- **The restriction map** `A → S(X_S)`, a map of graded `K`-algebras. -/
def restrictMap : FlagMinorAlgebra K n →ₐ[K] SchubertSectionRing K S :=
  gradedMap (restrictHom K S) (restrictHom_mem_sectionPiece K S)

theorem restrictMap_of (m : ColumnShape n) (a : minorSpan K m) :
    restrictMap K S (DirectSum.of _ m a) =
      DirectSum.of (fun m => ↥(sectionPiece K S m)) m
        ⟨restrictHom K S a, restrictHom_mem_sectionPiece K S m a a.2⟩ :=
  gradedMap_of _ _ m a

theorem restrictMap_eq_zero_iff (x : FlagMinorAlgebra K n) :
    restrictMap K S x = 0 ↔ ∀ m, ((x m : minorSpan K m) : MatrixEntryPolynomial K n) ∈
        vanishSpan K m S := by
  rw [restrictMap, gradedMap_eq_zero_iff]
  exact forall_congr' fun m => restrictHom_eq_zero_iff K S (x m)

/-- **The ideal `I_S` of `X_S` in the flag-minor algebra**: the elements whose homogeneous
components `x_m ∈ A_m` all vanish on `π⁻¹ X_S`, i.e. lie in `vanishSpan K m S`. -/
def flagMinorIdeal : Ideal (FlagMinorAlgebra K n) where
  carrier := {x | ∀ m, ((x m : minorSpan K m) : MatrixEntryPolynomial K n) ∈ vanishSpan K m S}
  add_mem' := by
    intro x y hx hy m
    simpa only [DirectSum.add_apply, Submodule.coe_add] using add_mem (hx m) (hy m)
  zero_mem' := by
    intro m
    simpa only [DirectSum.zero_apply, ZeroMemClass.coe_zero] using zero_mem (vanishSpan K m S)
  smul_mem' c x hx := (restrictMap_eq_zero_iff K S (c • x)).mp (by
    rw [smul_eq_mul, map_mul, (restrictMap_eq_zero_iff K S x).mpr hx, mul_zero])

theorem mem_flagMinorIdeal {x : FlagMinorAlgebra K n} :
    x ∈ flagMinorIdeal K S ↔ ∀ m, ((x m : minorSpan K m) : MatrixEntryPolynomial K n) ∈
        vanishSpan K m S :=
  Iff.rfl

/-- `I_S` is a homogeneous ideal. -/
theorem mem_flagMinorIdeal_iff_of {x : FlagMinorAlgebra K n} :
    x ∈ flagMinorIdeal K S ↔ ∀ m, DirectSum.of _ m (x m) ∈ flagMinorIdeal K S := by
  constructor
  · intro hx m m'
    by_cases h : m = m'
    · subst h
      rw [DirectSum.of_eq_same]
      exact hx m
    · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm h), ZeroMemClass.coe_zero]
      exact zero_mem _
  · intro h m
    have := h m m
    rwa [DirectSum.of_eq_same] at this

/-- **The kernel of the restriction map is `I_S`** (`ker_minorRestriction` in each degree). -/
theorem ker_restrictMap : RingHom.ker (restrictMap K S) = flagMinorIdeal K S := by
  ext x
  exact RingHom.mem_ker.trans (restrictMap_eq_zero_iff K S x)

end Pieces

section Surjective

variable [IsAlgClosed K] [CharZero K] {S : Finset (Equiv.Perm (Fin n))}

theorem gradedPiece_restrictHom_surjective (hS : BruhatLower S) (m : ColumnShape n) :
    Function.Surjective (gradedPiece (restrictHom K S) (restrictHom_mem_sectionPiece K S) m) := by
  rintro ⟨y, t, ht, rfl⟩
  obtain ⟨a, ha, hat⟩ := PointModel.schubertUnion_normality m hS t ht
  refine ⟨⟨a, ha⟩, Subtype.ext ?_⟩
  exact (Ideal.Quotient.eq.mpr hat).symm

/-- **Projective normality for the section ring**: restriction `A → S(X_S)` is surjective. -/
theorem restrictMap_surjective (hS : BruhatLower S) :
    Function.Surjective (restrictMap K S) :=
  gradedMap_surjective _ _ (gradedPiece_restrictHom_surjective hS)

/-- **Projective normality of Schubert unions, algebraic form**: the multigraded section ring
`S(X_S) = ⨁_λ H⁰(X_S, 𝓛(−λ))` is the quotient `A ⧸ I_S` of the flag-minor algebra by the ideal of
`X_S`, as graded `K`-algebras (`schubertSectionRingEquiv_mk_of`), over an algebraically closed
field of characteristic `0`. -/
def schubertSectionRingEquiv (hS : BruhatLower S) :
    (FlagMinorAlgebra K n ⧸ flagMinorIdeal K S) ≃ₐ[K] SchubertSectionRing K S :=
  (Ideal.quotientEquivAlgOfEq K (ker_restrictMap K S).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (restrictMap_surjective hS))

theorem schubertSectionRingEquiv_mk (hS : BruhatLower S) (x : FlagMinorAlgebra K n) :
    schubertSectionRingEquiv hS (Ideal.Quotient.mk _ x) = restrictMap K S x :=
  rfl

/-- The isomorphism respects the gradings: the class of `a ∈ A_m` goes to its restriction in
degree `m`. -/
theorem schubertSectionRingEquiv_mk_of (hS : BruhatLower S) (m : ColumnShape n)
    (a : minorSpan K m) :
    schubertSectionRingEquiv hS (Ideal.Quotient.mk _ (DirectSum.of _ m a)) =
      DirectSum.of (fun m => ↥(sectionPiece K S m)) m
        ⟨restrictHom K S a, restrictHom_mem_sectionPiece K S m a a.2⟩ := by
  rw [schubertSectionRingEquiv_mk, restrictMap_of]

end Surjective

end FlagVarieties.PointModel
