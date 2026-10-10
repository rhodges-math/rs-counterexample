import RSCounterexample.Paper.Filtrations.DemazureUnions
import RSCounterexample.Paper.JosephPolo.GeneralTheorem
import RSCounterexample.TypeA.Permutations.BruhatCovers

/-!
# Section modules, dual Joseph modules and minimal relative Schubert modules

We model the section modules of Section 4.3.1 of the paper algebraically. For an antidominant
(weakly increasing) weight `η ∈ ℤⁿ`, write `η = k·(1,…,1) − λ` with `k = max(0, max η)` and
`λ ∈ ℕⁿ` weakly decreasing. For a finite set `S` of permutations, the module of sections of
`𝓛(η)` over the union of Schubert varieties `X_S = ⋃_{w ∈ S} X_w` is

  `H⁰(X_S, 𝓛(η)) = (Σ_{w ∈ S} D_w(λ))^∨ ⊗ det^k`,

the twisted dual of a sum of Demazure modules. Restriction of sections from `X_S` to a union
`X_{S'} ⊆ X_S` is the dual of the inclusion `D_{S'} ≤ D_S`.

Following van der Kallen [Definitions 2.3.2 and 2.3.4], for `ν ∈ ℤⁿ` let `η` be the weakly
increasing rearrangement of `ν` and `σ` the shortest permutation with `σ·η = ν`. Then

* the dual Joseph module is `P(ν) = H⁰(X_σ, 𝓛(η))`;
* the minimal relative Schubert module `Q(ν)` is the kernel of the restriction
  `H⁰(X_σ, 𝓛(η)) → H⁰(∂X_σ, 𝓛(η))`, where `∂X_σ = ⋃_{τ < σ} X_τ` is the Schubert boundary.

For a weak composition `u` we prove `ch P(−u) = κ_u`, the first identity of (1.7).
-/

namespace Schubert.RS

namespace BModules.BModule

open Representation

variable {n : ℕ}

theorem Hom.dualMap_dualNil {M N : BModule n} (f : M.Hom N) (X : upperNilpotent n)
    (φ : Module.Dual ℂ N) :
    f.toLinearMap.dualMap (N.dualNil X φ) = M.dualNil X (f.toLinearMap.dualMap φ) := by
  apply LinearMap.ext; intro v
  simp [f.map_nil]

theorem Hom.dualMap_dualTorus {M N : BModule n} (f : M.Hom N) (t : DiagonalTorus n)
    (φ : Module.Dual ℂ N) :
    f.toLinearMap.dualMap (N.dualTorus t φ) = M.dualTorus t (f.toLinearMap.dualMap φ) := by
  apply LinearMap.ext; intro v
  simp [f.map_torus]

/-- The dual of a homomorphism of `B`-modules. -/
def Hom.dual {M N : BModule n} (f : M.Hom N) : N.dual.Hom M.dual where
  toLinearMap := f.toLinearMap.dualMap
  map_nil X φ := f.dualMap_dualNil X φ
  map_torus t φ := f.dualMap_dualTorus t φ

theorem Hom.map_twistTorus {M N : BModule n} (f : M.Hom N) (k : ℤ) (t : DiagonalTorus n)
    (v : M) : f.toLinearMap (M.twistTorus k t v) = N.twistTorus k t (f.toLinearMap v) := by
  rw [twistTorus_apply, twistTorus_apply, map_smul, f.map_torus]

/-- The twist of a homomorphism of `B`-modules. -/
def Hom.twist {M N : BModule n} (f : M.Hom N) (k : ℤ) : (M.twist k).Hom (N.twist k) where
  toLinearMap := f.toLinearMap
  map_nil X v := f.map_nil X v
  map_torus t v := f.map_twistTorus k t v

/-- The kernel of a homomorphism of `B`-modules. -/
def Hom.ker {M N : BModule n} (f : M.Hom N) : BSubmodule M where
  toSubmodule := LinearMap.ker f.toLinearMap
  nil_mem X v hv := by
    rw [LinearMap.mem_ker] at hv ⊢
    rw [f.map_nil, hv, map_zero]
  torus_mem t v hv := by
    rw [LinearMap.mem_ker] at hv ⊢
    rw [f.map_torus, hv, map_zero]

end BModules.BModule

namespace Filtrations

open Representation BModules FinPermutation

noncomputable section

variable {n : ℕ}

/-! ### Sections over unions of Schubert varieties -/

/-- The shift `k = max(0, max η)`. -/
def weightShift (η : Weight n) : ℕ := Finset.univ.sup fun i => (η i).toNat

/-- The composition `k·(1,…,1) − η`, with `k = weightShift η`. -/
def weightComplement (η : Weight n) : Composition n :=
  fun i => ((weightShift η : ℤ) - η i).toNat

theorem le_weightShift (η : Weight n) (i : Fin n) : η i ≤ weightShift η := by
  have h : (η i).toNat ≤ weightShift η :=
    Finset.le_sup (f := fun i => (η i).toNat) (Finset.mem_univ i)
  have := Int.self_le_toNat (η i)
  omega

theorem weightComplement_cast (η : Weight n) (i : Fin n) :
    (weightComplement η i : ℤ) = weightShift η - η i := by
  have := le_weightShift η i
  simp only [weightComplement]
  omega

/-- Sections of `𝓛(k·1 − λ)` over `X_S`, for `λ = dom` weakly decreasing:
the dual of `Σ_{w ∈ S} D_w(λ)`, twisted by `det^k`. -/
def sectionModuleOf (k : ℕ) (dom : Composition n) (S : Finset (Equiv.Perm (Fin n))) :
    BModule n :=
  ((demazureUnionModule (columnsOfWeight dom) S).dual).twist k

/-- The section module `H⁰(X_S, 𝓛(η))` of an antidominant weight `η` over the union of
Schubert varieties `X_S = ⋃_{w ∈ S} X_w`. -/
def schubertSectionModule (η : Weight n) (S : Finset (Equiv.Perm (Fin n))) : BModule n :=
  sectionModuleOf (weightShift η) (weightComplement η) S

/-- Restriction of sections from `X_S` to `X_{S'}`, when `D_{S'} ≤ D_S` (i.e. `X_{S'} ⊆ X_S`). -/
def restrictSectionsOf (k : ℕ) (dom : Composition n) {S S' : Finset (Equiv.Perm (Fin n))}
    (h : demazureUnion (columnsOfWeight dom) S' ≤ demazureUnion (columnsOfWeight dom) S) :
    (sectionModuleOf k dom S).Hom (sectionModuleOf k dom S') :=
  ((demazureUnionInclusion _ h).dual).twist k

/-- The character of a section module, from the torus character of the Demazure sum. -/
theorem sectionModuleOf_hasCharacter (k : ℕ) (dom : Composition n)
    (S : Finset (Equiv.Perm (Fin n))) {p : Polynomial n}
    (hp : HasTorusCharacter (demazureUnionModule (columnsOfWeight dom) S).torus p) :
    (sectionModuleOf k dom S).HasCharacter
      (AddMonoidAlgebra.single (-BModule.constWeight (k : ℤ)) 1 * toLaurent p) :=
  (BModule.hasCharacter_dual_of_hasTorusCharacter _ hp).twist k

/-! ### Dual Joseph modules and minimal relative Schubert modules -/

/-- The Schubert boundary `{τ | τ < σ}`. -/
def schubertBoundary (σ : Equiv.Perm (Fin n)) : Finset (Equiv.Perm (Fin n)) := by
  classical exact Finset.univ.filter fun τ => τ <ᴮ σ

theorem mem_schubertBoundary {σ τ : Equiv.Perm (Fin n)} :
    τ ∈ schubertBoundary σ ↔ τ <ᴮ σ := by
  classical
  unfold schubertBoundary
  simp

theorem demazureUnion_boundary_le (m : ColumnShape n) (σ : Equiv.Perm (Fin n)) :
    demazureUnion m (schubertBoundary σ) ≤ demazureUnion m {σ} :=
  demazureUnion_mono m fun _ hτ =>
    ⟨σ, Finset.mem_singleton_self σ, (mem_schubertBoundary.mp hτ).1⟩

/-- The Schubert index `σ` of `ν`: the shortest permutation with `σ·η = ν`. -/
def schubertIndex (ν : Weight n) : Equiv.Perm (Fin n) :=
  compositionPermutation (weightComplement ν)

/-- The fibre weight `η` of `ν`: its weakly increasing rearrangement. -/
def fibreWeight (ν : Weight n) : Weight n :=
  fun i => (weightShift ν : ℤ) - dominantComposition (weightComplement ν) i

/-- The dual Joseph module `P(ν) = H⁰(X_σ, 𝓛(η))` [van der Kallen, Def. 2.3.2]. -/
def dualJoseph (ν : Weight n) : BModule n :=
  sectionModuleOf (weightShift ν) (dominantComposition (weightComplement ν)) {schubertIndex ν}

/-- The restriction `P(ν) = H⁰(X_σ, 𝓛(η)) → H⁰(∂X_σ, 𝓛(η))` to the Schubert boundary. -/
def restrictToBoundary (ν : Weight n) :
    (dualJoseph ν).Hom
      (sectionModuleOf (weightShift ν) (dominantComposition (weightComplement ν))
        (schubertBoundary (schubertIndex ν))) :=
  restrictSectionsOf _ _ (demazureUnion_boundary_le _ _)

/-- The minimal relative Schubert module `Q(ν) ⊆ P(ν)`: sections vanishing on the Schubert
boundary [van der Kallen, Def. 2.3.4]. -/
def minRelSchubertSubmodule (ν : Weight n) : BSubmodule (dualJoseph ν) :=
  (restrictToBoundary ν).ker

/-- The minimal relative Schubert module `Q(ν)` as a `B`-module. -/
def minRelSchubert (ν : Weight n) : BModule n := (minRelSchubertSubmodule ν).toBModule

/-- The weight `−u` of a weak composition `u`. -/
def negComposition (u : Composition n) : Weight n := fun i => -(u i : ℤ)

theorem weightShift_negComposition (u : Composition n) : weightShift (negComposition u) = 0 := by
  refine Nat.eq_zero_of_le_zero (Finset.sup_le fun i _ => ?_)
  simp [negComposition]

theorem weightComplement_negComposition (u : Composition n) :
    weightComplement (negComposition u) = u := by
  funext i
  simp [weightComplement, weightShift_negComposition, negComposition]

theorem schubertIndex_negComposition (u : Composition n) :
    schubertIndex (negComposition u) = compositionPermutation u := by
  rw [schubertIndex, weightComplement_negComposition]

theorem constWeight_zero : (BModule.constWeight 0 : Weight n) = 0 := rfl

/-- `P(−u)` is the dual of the Demazure module `D_u` (lines 1514–1517 of the paper). -/
theorem dualJoseph_negComposition (u : Composition n) :
    dualJoseph (negComposition u) =
      sectionModuleOf 0 (dominantComposition u) {compositionPermutation u} := by
  rw [dualJoseph, weightShift_negComposition, weightComplement_negComposition,
    schubertIndex_negComposition]

/-- The first identity of (1.7): `ch P(−u) = κ_u`. -/
theorem dualJoseph_hasCharacter (u : Composition n) :
    (dualJoseph (negComposition u)).HasCharacter (toLaurent (key u)) := by
  rw [dualJoseph_negComposition]
  have hp := demazureUnionModule_singleton_hasTorusCharacter (compositionShape u)
    (compositionPermutation u) (compositionFlagJP_and_character u).2
  have h := sectionModuleOf_hasCharacter 0 (dominantComposition u) {compositionPermutation u} hp
  rwa [Nat.cast_zero, constWeight_zero, neg_zero, ← AddMonoidAlgebra.one_def, one_mul] at h

/-! ### Agreement with the paper's description of `P(ν)` -/

theorem weightComplement_cast_schubertIndex (ν : Weight n) (i : Fin n) :
    (dominantComposition (weightComplement ν) i : ℤ) =
      weightShift ν - ν (schubertIndex ν i) := by
  rw [dominantComposition, weightComplement_cast]
  rfl

theorem fibreWeight_apply (ν : Weight n) (i : Fin n) :
    fibreWeight ν i = ν (schubertIndex ν i) := by
  rw [fibreWeight, weightComplement_cast_schubertIndex]
  ring

/-- `η` is weakly increasing (antidominant for the upper-triangular Borel subgroup). -/
theorem fibreWeight_monotone (ν : Weight n) : Monotone (fibreWeight ν) := by
  intro i j hij
  have h := dominantComposition_antitone (weightComplement ν) hij
  simp only [fibreWeight]
  omega

/-- `σ · η = ν`, where the symmetric group permutes coordinates. -/
theorem fibreWeight_schubertIndex_symm (ν : Weight n) (i : Fin n) :
    fibreWeight ν ((schubertIndex ν).symm i) = ν i := by
  rw [fibreWeight_apply, Equiv.apply_symm_apply]

/-- `σ` is the shortest such permutation: it is increasing on each block of equal entries
of `η`. -/
theorem schubertIndex_minimal (ν : Weight n) (i j : Fin n) (hij : i < j)
    (he : fibreWeight ν i = fibreWeight ν j) : schubertIndex ν i < schubertIndex ν j := by
  apply compositionPermutation_ties _ i j hij
  simp only [fibreWeight] at he
  omega

theorem weightShift_fibreWeight (ν : Weight n) : weightShift (fibreWeight ν) = weightShift ν := by
  apply le_antisymm
  · refine Finset.sup_le fun i _ => ?_
    rw [fibreWeight_apply]
    exact Finset.le_sup (f := fun i => (ν i).toNat) (Finset.mem_univ _)
  · refine Finset.sup_le fun i _ => ?_
    have : ν i = fibreWeight ν ((schubertIndex ν).symm i) := (fibreWeight_schubertIndex_symm ν i).symm
    rw [this]
    exact Finset.le_sup (f := fun i => (fibreWeight ν i).toNat) (Finset.mem_univ _)

theorem weightComplement_fibreWeight (ν : Weight n) :
    weightComplement (fibreWeight ν) = dominantComposition (weightComplement ν) := by
  funext i
  have h1 := weightComplement_cast (fibreWeight ν) i
  have h2 := weightComplement_cast_schubertIndex ν i
  rw [weightShift_fibreWeight, fibreWeight_apply] at h1
  omega

/-- `P(ν) = H⁰(X_σ, 𝓛(η))` with `η` and `σ` as in the paper. -/
theorem dualJoseph_eq_schubertSectionModule (ν : Weight n) :
    dualJoseph ν = schubertSectionModule (fibreWeight ν) {schubertIndex ν} := by
  rw [dualJoseph, schubertSectionModule, weightShift_fibreWeight, weightComplement_fibreWeight]

end

end Filtrations

end Schubert.RS
