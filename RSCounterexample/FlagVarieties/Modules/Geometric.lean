import RSCounterexample.FlagVarieties.Modules.BModuleModel
import RSCounterexample.FlagVarieties.LineBundle.BorelRep
import RSCounterexample.FlagVarieties.Normality.OrbitIdealComparison
import RSCounterexample.FlagVarieties.Schubert.Orbit
import RSCounterexample.GLRep.Borel.BorelComodule
import RSCounterexample.FlagVarieties.LineBundle.Density
import Mathlib.Algebra.CharZero.Infinite

/-!
# The geometric section modules

The sheaf-theoretic sections `H⁰(X, 𝓛(η)) = sections ℂ n I η` of a closed subscheme `X ⊆ Fl_n`
(ideal sheaf `I`), with the action of `B` by left translation (`FlagVarieties.sectionsRep`), are
identified (`FlagVarieties.sectionsEquivSemiInvariants`) with the scheme-theoretic
semi-invariants of `𝒪(π⁻¹X) = 𝒪(GL_n)/J`, `J = preimageIdeal ℂ n I`. This file compares them with
the ring model:

* over `ℂ`, the scheme-theoretic semi-invariants are the pointwise ones
  (`FlagVarieties.quotientSemiInvariants_eq_borelSemiInvariants`): `𝒪(π⁻¹X) ⊗ 𝒪(B)` is separated by
  the points of `B(ℂ)` (`FlagVarieties.tensor_ext_borelCoordPoint`, from the density of `B(ℂ)`);
* hence, when `J` is the orbit ideal of a set `S` of permutations,
  **`H⁰(X, 𝓛(η)) ≅ sectionRep S η` as representations of `B`**
  (`FlagVarieties.geometricSectionEquiv`). For a Schubert variety this holds by the description
  of the preimage ideal (`FlagVarieties.preimageIdeal_schubertVariety_eq_orbitIdeal`).

All ring-model results then hold for the geometric modules: characters, the dual Joseph modules
(`FlagVarieties.dualJoseph`, `FlagVarieties.ch_dualJoseph_negWeight`) and Demazure duality
(`FlagVarieties.sectionDemazureEquiv`). The preimage ideals and `Γ(X_w, 𝒪) = ℂ` are proved in the
library, so the results have no hypotheses.
-/

open Schubert GLRep TauCeti Module Demazure.FlagModule Demazure.HighestWeight
  Demazure.SchubertUnions FinPermutation

namespace FlagVarieties

open PointModel.Complex SectionRep
open scoped TensorProduct

noncomputable section

variable {n : ℕ}

/-! ### Points of `B` and separation, over an infinite field -/

section BorelPoints

variable {K : Type*} [Field K]

/-- The point `b ∈ B(K)` as an algebra map out of `𝒪(B) = BorelCoord K n`. -/
def borelCoordPoint (b : borel K n) : BorelCoord K n →ₐ[K] K :=
  borelPointOfMatrix K ((b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
    ((b : GL (Fin n) K).isUnit.map Matrix.detMonoidHom) b.2

theorem borelCoordPoint_ext [Infinite K] {x y : BorelCoord K n}
    (h : ∀ b : borel K n, borelCoordPoint b x = borelCoordPoint b y) : x = y := by
  rw [← sub_eq_zero]
  refine borelCoord_eq_zero_of_forall _ fun M hM hup => ?_
  let g : GL (Fin n) K := Matrix.GeneralLinearGroup.mkOfDetNeZero M hM.ne_zero
  have := h ⟨g, hup⟩
  rw [map_sub, sub_eq_zero]
  exact this

/-- **Point separation in `M ⊗ 𝒪(B)`**, for any `K`-vector space `M` (`K` infinite). -/
theorem tensor_ext_borelCoordPoint [Infinite K] {M : Type*} [AddCommGroup M] [Module K M]
    {t t' : M ⊗[K] BorelCoord K n}
    (h : ∀ b : borel K n, TensorProduct.rid K M ((borelCoordPoint b).toLinearMap.lTensor M t) =
      TensorProduct.rid K M ((borelCoordPoint b).toLinearMap.lTensor M t')) : t = t' := by
  classical
  let B := Module.Basis.ofVectorSpace K M
  apply (TensorProduct.equivFinsuppOfBasisLeft B).injective
  ext j
  refine borelCoordPoint_ext fun b => ?_
  have key : ∀ s : M ⊗[K] BorelCoord K n,
      borelCoordPoint b (TensorProduct.equivFinsuppOfBasisLeft B s j) =
        B.coord j (TensorProduct.rid K M ((borelCoordPoint b).toLinearMap.lTensor M s)) := by
    intro s
    rw [TensorProduct.equivFinsuppOfBasisLeft_apply]
    induction s with
    | tmul m c => simp [mul_comm]
    | add s s' hs hs' => simp only [map_add, hs, hs']
  rw [key, key, h b]

/-! ### The coaction at a point is right translation -/

theorem rid_lTensor_eq_algebra (x : BorelCoord K n →ₐ[K] K) (t : GLCoord K n ⊗[K] BorelCoord K n) :
    TensorProduct.rid K (GLCoord K n) (x.toLinearMap.lTensor (GLCoord K n) t) =
      Algebra.TensorProduct.rid K K (GLCoord K n)
        (Algebra.TensorProduct.map (AlgHom.id K (GLCoord K n)) x t) := by
  induction t with
  | tmul m c => simp
  | add s s' hs hs' => simp only [map_add, hs, hs']

/-- **At the point `b ∈ B(K)`, the right coaction is right translation by `b`.** -/
theorem rid_lTensor_rightCoaction (b : borel K n) (f : GLCoord K n) :
    TensorProduct.rid K (GLCoord K n)
        ((borelCoordPoint b).toLinearMap.lTensor (GLCoord K n) (rightCoaction K n f)) =
      rightTranslHom K n b f := by
  rw [rid_lTensor_eq_algebra]
  have key : ((Algebra.TensorProduct.rid K K (GLCoord K n)).toAlgHom.comp
      ((Algebra.TensorProduct.map (AlgHom.id K (GLCoord K n)) (borelCoordPoint b)).comp
        (rightCoaction K n))) = rightTranslHom K n (b : GL (Fin n) K) := by
    apply genericMatrix_algHom_ext
    ext i j
    have h1 := congrFun (congrFun (map_rightCoaction_genericMatrix K n) i) j
    simp only [Matrix.map_apply, Matrix.mul_apply] at h1
    have h2 : ∀ k, borelCoordPoint b (borelMatrix K n k j) =
        ((b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) k j :=
      fun k => congrFun (congrFun (borelMatrix_map_borelPointOfMatrix K _
        ((b : GL (Fin n) K).isUnit.map Matrix.detMonoidHom) b.2) k) j
    have hG : ∀ i j, genericMatrix K n i j = glX i j := fun i j => by
      rw [genericMatrix, TauCeti.GeneralLinear.localizedGenericMatrix_apply,
        TauCeti.GeneralLinear.coordinateRingMap_apply]
      rfl
    rw [Matrix.map_apply, Matrix.map_apply, AlgHom.comp_apply, AlgHom.comp_apply, h1, map_sum,
      map_sum, hG, rightTranslHom_glX]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, Algebra.TensorProduct.map_tmul,
      AlgHom.id_apply, h2, hG]
    rfl
  exact DFunLike.congr_fun key f

/-! ### Scheme-theoretic and pointwise semi-invariants -/

theorem rid_lTensor_rightCoactionMod (J : Ideal (GLCoord K n)) (b : borel K n) (f : GLCoord K n) :
    TensorProduct.rid K (GLCoord K n ⧸ J)
        ((borelCoordPoint b).toLinearMap.lTensor (GLCoord K n ⧸ J) (rightCoactionMod K n J f)) =
      Ideal.Quotient.mk J (rightTranslHom K n b f) := by
  change TensorProduct.rid K (GLCoord K n ⧸ J) ((borelCoordPoint b).toLinearMap.lTensor _
      ((Ideal.Quotient.mkₐ K J).toLinearMap.rTensor _ (rightCoaction K n f))) = _
  rw [GLRep.rid_lTensor_rTensor, rid_lTensor_rightCoaction]
  rfl

/-- Pointwise right stability implies scheme-theoretic right stability (`K` infinite). -/
theorem isBorelStable_of_isRightBorelStable [Infinite K] (J : Ideal (GLCoord K n))
    (hR : IsRightBorelStable J) : IsBorelStable K n J := fun f hf => by
  rw [RingHom.mem_ker]
  refine tensor_ext_borelCoordPoint fun b => ?_
  change TensorProduct.rid K _ ((borelCoordPoint b).toLinearMap.lTensor
      _ (rightCoactionMod K n J f)) = _
  rw [rid_lTensor_rightCoactionMod, LinearMap.map_zero, LinearEquiv.map_zero,
    Ideal.Quotient.eq_zero_iff_mem]
  exact hR b b.2 hf

theorem units_map_borelCoordPoint_borelDiag (b : borel K n) (i : Fin n) :
    Units.map (borelCoordPoint b : BorelCoord K n →* K) (FlagVarieties.borelDiag K n i) =
      GLRep.borelDiag K n b i := by
  ext
  rw [Units.coe_map, GLRep.borelDiag_apply_val]
  exact congrFun (congrFun (borelMatrix_map_borelPointOfMatrix K _
    ((b : GL (Fin n) K).isUnit.map Matrix.detMonoidHom) b.2) i) i

theorem borelCoordPoint_borelCharacterUnit_inv (b : borel K n) (η : Fin n → ℤ) :
    borelCoordPoint b (((borelCharacterUnit K n η)⁻¹ : (BorelCoord K n)ˣ) : BorelCoord K n) =
      (((GLRep.borelChar K n η b)⁻¹ : Kˣ) : K) := by
  have h : Units.map (borelCoordPoint b : BorelCoord K n →* K) (borelCharacterUnit K n η) =
      GLRep.borelChar K n η b := by
    rw [borelCharacterUnit, map_prod, GLRep.borelChar_apply]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_zpow, units_map_borelCoordPoint_borelDiag]
  rw [← h, ← map_inv, Units.coe_map]
  rfl

end BorelPoints

/-- **Over `ℂ`, the scheme-theoretic semi-invariants are the pointwise ones** (for a pointwise
right-stable
ideal). -/
theorem quotientSemiInvariants_eq_borelSemiInvariants (J : Ideal (GLCoord ℂ n))
    (hR : IsRightBorelStable J) (η : Fin n → ℤ) :
    quotientSemiInvariants ℂ n J η = borelSemiInvariants J hR η := by
  ext x
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [mem_quotientSemiInvariants_iff (isBorelStable_of_isRightBorelStable J hR),
      mem_borelSemiInvariants]
  constructor
  · intro h b
    have := congrArg (fun t => TensorProduct.rid ℂ (GLCoord ℂ n ⧸ J)
      ((borelCoordPoint b).toLinearMap.lTensor (GLCoord ℂ n ⧸ J) t)) h
    rw [rid_lTensor_rightCoactionMod, LinearMap.lTensor_tmul, TensorProduct.rid_tmul,
      AlgHom.toLinearMap_apply, borelCoordPoint_borelCharacterUnit_inv] at this
    exact this
  · intro h
    refine tensor_ext_borelCoordPoint fun b => ?_
    rw [rid_lTensor_rightCoactionMod, LinearMap.lTensor_tmul, TensorProduct.rid_tmul,
      AlgHom.toLinearMap_apply, borelCoordPoint_borelCharacterUnit_inv]
    exact h b

/-! ### The geometric sections are the ring-model sections -/

variable {S : Finset (Equiv.Perm (Fin n))}

/-- Left translation on the semi-invariants of `𝒪(GL_n)/I_S` is `sectionRep S η`. -/
def semiInvariantsRepEquiv (J : Ideal (GLCoord ℂ n)) (hJS : J = orbitIdeal S)
    (hJ : IsLeftTranslStable J) (η : Fin n → ℤ) :
    (semiInvariantsRep J hJ η).Equiv (sectionRep S η) := by
  subst hJS
  exact .mk (LinearEquiv.ofEq (quotientSemiInvariants ℂ n (orbitIdeal S) η)
      (sectionSubrep S η).toSubmodule
      (quotientSemiInvariants_eq_borelSemiInvariants _ (isRightBorelStable_orbitIdeal S) η))
    fun b => LinearMap.ext fun x => Subtype.ext rfl

/-- **`H⁰(X, 𝓛(η)) ≅ sectionRep S η` as representations of `B`**, when the ideal of `π⁻¹X` is the
orbit ideal of `S`. -/
def geometricSectionEquiv (I : (FlagScheme ℂ n).IdealSheafData)
    (hI : preimageIdeal ℂ n I = orbitIdeal S) (hJ : IsLeftTranslStable (preimageIdeal ℂ n I))
    (η : Fin n → ℤ) : (sectionsRep ℂ n I η hJ).Equiv (sectionRep S η) :=
  .mk ((sectionsEquivSemiInvariants ℂ n I η).trans (semiInvariantsRepEquiv _ hI hJ η).toLinearEquiv)
    fun b => LinearMap.ext fun s => by
      change (semiInvariantsRepEquiv _ hI hJ η).toLinearEquiv
          (sectionsEquivSemiInvariants ℂ n I η (sectionsRep ℂ n I η hJ b s)) =
        sectionRep S η b ((semiInvariantsRepEquiv _ hI hJ η).toLinearEquiv
          (sectionsEquivSemiInvariants ℂ n I η s))
      rw [sectionsEquivSemiInvariants_sectionsRep]
      exact (semiInvariantsRepEquiv _ hI hJ η).toIntertwiningMap.isIntertwining _ _ b _

theorem isLeftTranslStable_of_eq {I : (FlagScheme ℂ n).IdealSheafData}
    (hI : preimageIdeal ℂ n I = orbitIdeal S) : IsLeftTranslStable (preimageIdeal ℂ n I) := by
  rw [hI]
  exact isLeftBorelStable_orbitIdeal S

/-- The characters agree. -/
theorem ch_sectionsRep (I : (FlagScheme ℂ n).IdealSheafData)
    (hI : preimageIdeal ℂ n I = orbitIdeal S) (η : Fin n → ℤ) :
    ch (sectionsRep ℂ n I η (isLeftTranslStable_of_eq hI)) = ch (sectionRep S η) :=
  ch_eq_of_equiv (geometricSectionEquiv I hI _ η)

/-! ### Schubert varieties -/

/-- The ideal of `π⁻¹(X_w)` is the orbit ideal of `{v ≤ w}`
(`FlagVarieties.preimageIdeal_schubertVariety_eq_schubertOrbitIdeal` and
`FlagVarieties.PointModel.preimageIdeal_schubertVariety_eq_orbitIdeal`). -/
theorem preimageIdeal_schubertVariety_eq_orbitIdeal (w : Equiv.Perm (Fin n)) :
    preimageIdeal ℂ n (schubertVariety ℂ n w) = orbitIdeal (lowerSet w) :=
  PointModel.preimageIdeal_schubertVariety_eq_orbitIdeal w

/-- **The geometric dual Joseph module** `P(ν) = H⁰(X_σ, 𝓛(η))`, `σ = σ(ν)`, `η = η(ν)`, on the
sections. -/
abbrev dualJoseph (ν : Fin n → ℤ) :
    Representation ℂ (borel ℂ n)
      (sections ℂ n (schubertVariety ℂ n (schubertIndex ν)) (fibreWeight ν)) :=
  sectionsRep ℂ n _ (fibreWeight ν)
    (isLeftTranslStable_of_eq (preimageIdeal_schubertVariety_eq_orbitIdeal (schubertIndex ν)))

/-- The geometric `P(ν)` is the ring-model `P(ν)`. -/
def dualJosephEquiv (ν : Fin n → ℤ) :
    (dualJoseph ν).Equiv (SectionRep.dualJoseph ν) :=
  geometricSectionEquiv _ (preimageIdeal_schubertVariety_eq_orbitIdeal (schubertIndex ν)) _ _

/-- **`ch P(−u) = κ_u` for the geometric dual Joseph modules.** -/
theorem ch_dualJoseph_negWeight
    (u : Demazure.Composition n) :
    ch (dualJoseph (negWeight u)) = Demazure.toLaurent (Demazure.key u) := by
  rw [ch_eq_of_equiv (dualJosephEquiv _), SectionRep.ch_dualJoseph_negWeight]

end

end FlagVarieties
