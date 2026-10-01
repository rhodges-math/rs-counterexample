import Schubert.RS.HighestWeight.Irreducible
import Schubert.RS.Representation.FlagFinite
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Uniqueness of the irreducible module with a given highest weight (E7)

Let `ρ : gl_n → End M` and `σ : gl_n → End N` be irreducible, with nonzero highest-weight vectors
`v ∈ M` and `w ∈ N` of the same weight `μ`: vectors killed by `𝔫⁺` on which each `E_jj` acts by
`μ_j`. Then there is a unique-up-to-scalar isomorphism `M ≅ N` of `gl_n`-modules with
`v ↦ w` (`exists_equiv_of_isHighestWeightVector`). The proof is the classical one:
* `P = U(𝔫⁻)·(v, w) ⊆ M × N` is `gl_n`-stable (`rootSpan_lie_stable`);
* the projections of `P` onto `M` and `N` are onto (irreducibility);
* they are injective, because `(0, w)` and `(v, 0)` are not in `P`. On `P` the depth element
  `H = Σ_i i·E_ii` has `(v, w)` as its only eigenvector of eigenvalue `Σ_i i·μ_i`, up to scalars:
  lowering operators raise the `H`-eigenvalue, and eigenspaces are independent.
No finiteness and no torus action are needed.

`GLModule` is a finite-dimensional `gl_n`-module whose diagonal matrices act semisimply with
integral eigenvalues. This is the Lie-algebra form of a finite-dimensional rational
`GL_n(ℂ)`-module; the torus action is recovered from the integral weight decomposition. The
flag-minor span with its `gl_n`-action is the `GLModule` `flagOrbitModule m`. It is irreducible
(`flagOrbitModule_isIrreducible`, from E6), and every irreducible `GLModule` with a highest-weight
vector of weight `λ = shapeWeight m` is isomorphic to it (`nonempty_iso_flagOrbitModule`): the
uniqueness half of the theorem of the highest weight for this model.
-/

namespace Schubert.RS.HighestWeight

open Schubert.RS.Representation

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : ℕ}

/-! ### Highest-weight vectors of abstract `gl_n`-modules -/

section Abstract

variable {M : Type*} [AddCommGroup M] [Module ℂ M] (ρ : Square n →ₗ⁅ℂ⁆ Module.End ℂ M)

/-- `v` is a highest-weight vector of weight `μ`: it is killed by `𝔫⁺`, and `E_jj v = μ_j v`. -/
def IsHighestWeightVector (μ : Weight n) (v : M) : Prop :=
  (∀ a b : Fin n, a < b → ρ (Matrix.single a b 1) v = 0) ∧
    ∀ j : Fin n, ρ (Matrix.single j j 1) v = (μ j : ℂ) • v

/-- The joint eigenspace of the diagonal matrix units with eigenvalues `μ`. -/
def lieWeightSpace (μ : Weight n) : Submodule ℂ M where
  carrier := {x | ∀ j : Fin n, ρ (Matrix.single j j 1) x = (μ j : ℂ) • x}
  zero_mem' := by intro j; simp
  add_mem' := by intro x y hx hy j; rw [map_add, hx j, hy j, smul_add]
  smul_mem' := by intro c x hx j; rw [map_smul, hx j, smul_comm]

/-- The depth element `H = Σ_i i·E_ii`. -/
def depthElement (n : ℕ) : Square n := ∑ i : Fin n, ((i : ℕ) : ℂ) • Matrix.single i i 1

theorem depthElement_lie_single (a b : Fin n) :
    ⁅depthElement n, (Matrix.single a b 1 : Square n)⁆ =
      (((a : ℕ) : ℂ) - ((b : ℕ) : ℂ)) • Matrix.single a b 1 := by
  rw [depthElement, sum_lie]
  simp_rw [smul_lie, single_lie_single]
  simp only [smul_sub, Finset.sum_sub_distrib, sub_smul]
  congr 1
  · rw [Finset.sum_eq_single a]
    · rw [ite_eq_left rfl]
    · intro i _ hi
      rw [ite_eq_right hi, smul_zero]
    · simp
  · rw [Finset.sum_eq_single b]
    · rw [ite_eq_left rfl]
    · intro i _ hi
      rw [ite_eq_right (Ne.symm hi), smul_zero]
    · simp

variable {ρ}

theorem IsHighestWeightVector.depth {μ : Weight n} {v : M} (hv : IsHighestWeightVector ρ μ v) :
    ρ (depthElement n) v = (weightDepth μ : ℂ) • v := by
  rw [depthElement, map_sum, LinearMap.sum_apply, weightDepth, Int.cast_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, LinearMap.smul_apply, hv.2 i, smul_smul]
  push_cast
  rfl

/-- A matrix unit `E_ab` shifts the eigenvalue of the depth element by `a - b`. -/
theorem depth_single_mem_eigenspace {a b : Fin n} {c : ℂ} {y : M}
    (hy : y ∈ (ρ (depthElement n)).eigenspace c) :
    ρ (Matrix.single a b 1) y ∈
      (ρ (depthElement n)).eigenspace (c + (((a : ℕ) : ℂ) - ((b : ℕ) : ℂ))) := by
  rw [Module.End.mem_eigenspace_iff] at hy ⊢
  rw [apply_apply_eq, depthElement_lie_single, hy, map_smul, map_smul, LinearMap.smul_apply,
    add_smul]

/-- `U(𝔫⁻)·v` meets the depth-eigenspace of `v` only in `ℂ·v`. -/
theorem mem_span_of_mem_rootSpan_lower {μ : Weight n} {v : M}
    (hv : IsHighestWeightVector ρ μ v) {y : M}
    (hy : y ∈ rootSpan ρ (fun a b => b < a) v)
    (hH : ρ (depthElement n) y = (weightDepth μ : ℂ) • y) : y ∈ ℂ ∙ v := by
  set f := ρ (depthElement n)
  set h₀ : ℂ := (weightDepth μ : ℂ)
  let T : Submodule ℂ M := ⨆ k : {k : ℕ // 0 < k}, f.eigenspace (h₀ + (k : ℕ))
  have hT : ∀ a b : Fin n, b < a → ∀ x ∈ T, ρ (Matrix.single a b 1) x ∈ T := by
    intro a b hba x hx
    induction hx using Submodule.iSup_induction' with
    | mem k x hx =>
      have h := depth_single_mem_eigenspace (a := a) (b := b) hx
      have hk : h₀ + ((k : ℕ) : ℂ) + (((a : ℕ) : ℂ) - ((b : ℕ) : ℂ)) =
          h₀ + ((k.1 + ((a : ℕ) - (b : ℕ)) : ℕ) : ℂ) := by
        have : (b : ℕ) ≤ (a : ℕ) := hba.le
        push_cast [this]
        ring
      rw [hk] at h
      exact (le_iSup (fun k : {k : ℕ // 0 < k} => f.eigenspace (h₀ + (k : ℕ)))
        ⟨k.1 + ((a : ℕ) - (b : ℕ)), by have := k.2; omega⟩) h
    | zero => rw [map_zero]; exact T.zero_mem
    | add x y _ _ hx hy => rw [map_add]; exact T.add_mem hx hy
  let S : Submodule ℂ M :=
    { carrier := {y | ∃ c : ℂ, y - c • v ∈ T}
      add_mem' := by
        rintro x y ⟨c, hc⟩ ⟨d, hd⟩
        refine ⟨c + d, ?_⟩
        rw [show x + y - (c + d) • v = (x - c • v) + (y - d • v) by rw [add_smul]; abel]
        exact T.add_mem hc hd
      zero_mem' := ⟨0, by rw [zero_smul, sub_zero]; exact T.zero_mem⟩
      smul_mem' := by
        rintro c x ⟨d, hd⟩
        refine ⟨c * d, ?_⟩
        rw [show c • x - (c * d) • v = c • (x - d • v) by rw [smul_sub, smul_smul]]
        exact T.smul_mem c hd }
  have hvT : ∀ a b : Fin n, b < a → ρ (Matrix.single a b 1) v ∈ T := by
    intro a b hba
    have h := depth_single_mem_eigenspace (a := a) (b := b)
      ((Module.End.mem_eigenspace_iff).mpr hv.depth)
    have hk : h₀ + (((a : ℕ) : ℂ) - ((b : ℕ) : ℂ)) = h₀ + ((((a : ℕ) - (b : ℕ)) : ℕ) : ℂ) := by
      have : (b : ℕ) ≤ (a : ℕ) := hba.le
      push_cast [this]
      ring
    rw [hk] at h
    exact (le_iSup (fun k : {k : ℕ // 0 < k} => f.eigenspace (h₀ + (k : ℕ)))
      ⟨(a : ℕ) - (b : ℕ), by have : (b : ℕ) < (a : ℕ) := hba; omega⟩) h
  have hle : rootSpan ρ (fun a b => b < a) v ≤ S := by
    refine rootSpan_le ρ _ v ⟨1, by rw [one_smul, sub_self]; exact T.zero_mem⟩ ?_
    rintro a b hba x ⟨c, hc⟩
    refine ⟨0, ?_⟩
    rw [zero_smul, sub_zero, show x = (x - c • v) + c • v by abel, map_add, map_smul]
    exact T.add_mem (hT a b hba _ hc) (T.smul_mem c (hvT a b hba))
  obtain ⟨c, hc⟩ := hle hy
  have hTdisj : T ≤ ⨆ (j : ℂ) (_ : j ≠ h₀), f.eigenspace j := by
    refine iSup_le fun k => ?_
    refine le_iSup₂_of_le (h₀ + ((k : ℕ) : ℂ)) ?_ le_rfl
    intro h
    have hk := k.2
    have : ((k : ℕ) : ℂ) = 0 := by linear_combination h
    exact hk.ne' (by exact_mod_cast this)
  have heig : y - c • v ∈ f.eigenspace h₀ := by
    rw [Module.End.mem_eigenspace_iff, map_sub, map_smul, hH, hv.depth, smul_sub, smul_comm]
  have hzero : y - c • v = 0 := by
    have hd := (f.eigenspaces_iSupIndep h₀).mono_right hTdisj
    exact (Submodule.disjoint_def.mp hd) _ heig hc
  rw [sub_eq_zero] at hzero
  rw [hzero]
  exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self v)

variable (ρ) in
/-- The direct sum of two `gl_n`-modules. -/
def prodLie {N : Type*} [AddCommGroup N] [Module ℂ N] (σ : Square n →ₗ⁅ℂ⁆ Module.End ℂ N) :
    Square n →ₗ⁅ℂ⁆ Module.End ℂ (M × N) where
  toFun A := LinearMap.prodMap (ρ A) (σ A)
  map_add' A B := by
    apply LinearMap.ext
    rintro ⟨x, y⟩
    simp
  map_smul' c A := by
    apply LinearMap.ext
    rintro ⟨x, y⟩
    simp
  map_lie' {A B} := by
    apply LinearMap.ext
    rintro ⟨x, y⟩
    have h1 : ρ ⁅A, B⁆ x = ρ A (ρ B x) - ρ B (ρ A x) := by
      rw [LieHom.map_lie, LieRing.of_associative_ring_bracket]
      rfl
    have h2 : σ ⁅A, B⁆ y = σ A (σ B y) - σ B (σ A y) := by
      rw [LieHom.map_lie, LieRing.of_associative_ring_bracket]
      rfl
    show LinearMap.prodMap (ρ ⁅A, B⁆) (σ ⁅A, B⁆) (x, y) =
      ⁅LinearMap.prodMap (ρ A) (σ A), LinearMap.prodMap (ρ B) (σ B)⁆ (x, y)
    rw [LinearMap.prodMap_apply, h1, h2, LieRing.of_associative_ring_bracket]
    rfl

@[simp] theorem prodLie_apply {N : Type*} [AddCommGroup N] [Module ℂ N]
    (σ : Square n →ₗ⁅ℂ⁆ Module.End ℂ N) (A : Square n) (x : M) (y : N) :
    prodLie ρ σ A (x, y) = (ρ A x, σ A y) := rfl

/-- Uniqueness of irreducible `gl_n`-modules with a given highest weight: there is an
isomorphism of `gl_n`-modules sending one highest-weight vector to the other. -/
theorem exists_equiv_of_isHighestWeightVector {N : Type*} [AddCommGroup N] [Module ℂ N]
    {σ : Square n →ₗ⁅ℂ⁆ Module.End ℂ N}
    (hρ : ∀ W : Submodule ℂ M, (∀ A, ∀ x ∈ W, ρ A x ∈ W) → W = ⊥ ∨ W = ⊤)
    (hσ : ∀ W : Submodule ℂ N, (∀ A, ∀ x ∈ W, σ A x ∈ W) → W = ⊥ ∨ W = ⊤)
    {μ : Weight n} {v : M} {w : N} (hv0 : v ≠ 0) (hw0 : w ≠ 0)
    (hv : IsHighestWeightVector ρ μ v) (hw : IsHighestWeightVector σ μ w) :
    ∃ e : M ≃ₗ[ℂ] N, (∀ A x, e (ρ A x) = σ A (e x)) ∧ e v = w := by
  set τ := prodLie ρ σ
  have hx : IsHighestWeightVector τ μ (v, w) :=
    ⟨fun a b h => by rw [prodLie_apply, hv.1 a b h, hw.1 a b h]; rfl,
      fun j => by rw [prodLie_apply, hv.2 j, hw.2 j]; rfl⟩
  set P := rootSpan τ (fun a b => b < a) (v, w)
  have hP : ∀ A, ∀ y ∈ P, τ A y ∈ P := by
    refine fun A => rootSpan_lie_stable τ _ (v, w) (fun a b hab => ?_) A
    rcases lt_trichotomy a b with h | h | h
    · exact ⟨0, by rw [zero_smul]; exact hx.1 a b h⟩
    · subst h
      exact ⟨_, hx.2 a⟩
    · exact absurd h hab
  have hline : ∀ y ∈ P, τ (depthElement n) y = (weightDepth μ : ℂ) • y → y ∈ ℂ ∙ (v, w) :=
    fun y hy hH => mem_span_of_mem_rootSpan_lower hx hy hH
  have hsnd : ∀ z : N, ((0 : M), z) ∈ P → z = 0 := by
    let W : Submodule ℂ N := P.comap (LinearMap.inr ℂ M N)
    have hWs : ∀ A, ∀ z ∈ W, σ A z ∈ W := by
      intro A z hz
      have h := hP A _ hz
      rw [LinearMap.inr_apply, prodLie_apply, map_zero] at h
      exact h
    rcases hσ W hWs with h | h
    · intro z hz
      have : z ∈ W := hz
      rwa [h, Submodule.mem_bot] at this
    · exfalso
      have hw' : ((0 : M), w) ∈ P := by
        have : w ∈ W := by rw [h]; exact Submodule.mem_top
        exact this
      have hH : τ (depthElement n) ((0 : M), w) = (weightDepth μ : ℂ) • ((0 : M), w) := by
        rw [prodLie_apply, map_zero, hw.depth]
        simp
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hline _ hw' hH)
      have h1 : c • v = 0 := congrArg Prod.fst hc
      have h2 : c • w = w := congrArg Prod.snd hc
      rcases smul_eq_zero.mp h1 with hc0 | hv'
      · rw [hc0, zero_smul] at h2
        exact hw0 h2.symm
      · exact hv0 hv'
  have hfst : ∀ x : M, (x, (0 : N)) ∈ P → x = 0 := by
    let W : Submodule ℂ M := P.comap (LinearMap.inl ℂ M N)
    have hWs : ∀ A, ∀ x ∈ W, ρ A x ∈ W := by
      intro A x hx
      have h := hP A _ hx
      rw [LinearMap.inl_apply, prodLie_apply, map_zero] at h
      exact h
    rcases hρ W hWs with h | h
    · intro x hx
      have : x ∈ W := hx
      rwa [h, Submodule.mem_bot] at this
    · exfalso
      have hv' : (v, (0 : N)) ∈ P := by
        have : v ∈ W := by rw [h]; exact Submodule.mem_top
        exact this
      have hH : τ (depthElement n) (v, (0 : N)) = (weightDepth μ : ℂ) • (v, (0 : N)) := by
        rw [prodLie_apply, map_zero, hv.depth]
        simp
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hline _ hv' hH)
      have h1 : c • v = v := congrArg Prod.fst hc
      have h2 : c • w = 0 := congrArg Prod.snd hc
      rcases smul_eq_zero.mp h2 with hc0 | hw'
      · rw [hc0, zero_smul] at h1
        exact hv0 h1.symm
      · exact hw0 hw'
  let p₁ : P →ₗ[ℂ] M := (LinearMap.fst ℂ M N).comp P.subtype
  let p₂ : P →ₗ[ℂ] N := (LinearMap.snd ℂ M N).comp P.subtype
  have hxP : (v, w) ∈ P := mem_rootSpan_self τ _ (v, w)
  have hp₁ : Function.Bijective p₁ := by
    refine ⟨fun y y' hyy => ?_, ?_⟩
    · have hmem : y.val - y'.val ∈ P := P.sub_mem y.2 y'.2
      have hfst0 : (y.val - y'.val).1 = 0 := by
        simp only [Prod.fst_sub]
        exact sub_eq_zero.mpr hyy
      have hz := hsnd (y.val - y'.val).2 (by
        rw [show ((0 : M), (y.val - y'.val).2) = y.val - y'.val from
          Prod.ext hfst0.symm rfl]
        exact hmem)
      exact Subtype.ext (sub_eq_zero.mp (Prod.ext hfst0 hz))
    · rw [← LinearMap.range_eq_top]
      rcases hρ (LinearMap.range p₁) (by
        rintro A _ ⟨y, rfl⟩
        exact ⟨⟨τ A y.val, hP A _ y.2⟩, rfl⟩) with h | h
      · exfalso
        have : v ∈ LinearMap.range p₁ := ⟨⟨(v, w), hxP⟩, rfl⟩
        rw [h, Submodule.mem_bot] at this
        exact hv0 this
      · exact h
  have hp₂ : Function.Bijective p₂ := by
    refine ⟨fun y y' hyy => ?_, ?_⟩
    · have hmem : y.val - y'.val ∈ P := P.sub_mem y.2 y'.2
      have hsnd0 : (y.val - y'.val).2 = 0 := by
        simp only [Prod.snd_sub]
        exact sub_eq_zero.mpr hyy
      have hz := hfst (y.val - y'.val).1 (by
        rw [show ((y.val - y'.val).1, (0 : N)) = y.val - y'.val from
          Prod.ext rfl hsnd0.symm]
        exact hmem)
      exact Subtype.ext (sub_eq_zero.mp (Prod.ext hz hsnd0))
    · rw [← LinearMap.range_eq_top]
      rcases hσ (LinearMap.range p₂) (by
        rintro A _ ⟨y, rfl⟩
        exact ⟨⟨τ A y.val, hP A _ y.2⟩, rfl⟩) with h | h
      · exfalso
        have : w ∈ LinearMap.range p₂ := ⟨⟨(v, w), hxP⟩, rfl⟩
        rw [h, Submodule.mem_bot] at this
        exact hw0 this
      · exact h
  let e₁ := LinearEquiv.ofBijective p₁ hp₁
  let e₂ := LinearEquiv.ofBijective p₂ hp₂
  refine ⟨e₁.symm.trans e₂, fun A x => ?_, ?_⟩
  · set y := e₁.symm x
    have hy : e₁.symm (ρ A x) = ⟨τ A y.val, hP A _ y.2⟩ := by
      apply e₁.injective
      rw [LinearEquiv.apply_symm_apply]
      change ρ A x = (τ A y.val).1
      rw [show y.val = (y.val.1, y.val.2) from rfl, prodLie_apply]
      change ρ A x = ρ A (p₁ y)
      rw [show p₁ y = e₁ y from rfl, LinearEquiv.apply_symm_apply]
    rw [LinearEquiv.trans_apply, hy]
    change (τ A y.val).2 = σ A (p₂ y)
    rw [show y.val = (y.val.1, y.val.2) from rfl, prodLie_apply]
    rfl
  · have hy : e₁.symm v = ⟨(v, w), hxP⟩ := by
      apply e₁.injective
      rw [LinearEquiv.apply_symm_apply]
      rfl
    rw [LinearEquiv.trans_apply, hy]
    rfl

end Abstract

/-! ### `GLModule` and the flag-minor model -/

/-- A finite-dimensional `gl_n`-module whose diagonal matrices act semisimply with integral
eigenvalues, i.e. which is spanned by its integral weight spaces. This is the Lie-algebra form of a
finite-dimensional rational `GL_n(ℂ)`-module. -/
structure GLModule (n : ℕ) where
  /-- The underlying vector space. -/
  carrier : Type
  [instAddCommGroup : AddCommGroup carrier]
  [instModule : Module ℂ carrier]
  [instFiniteDimensional : FiniteDimensional ℂ carrier]
  /-- The action of `gl_n`. -/
  lie : Square n →ₗ⁅ℂ⁆ Module.End ℂ carrier
  /-- The integral weight spaces span. -/
  weight_span : ⨆ μ : Weight n, lieWeightSpace lie μ = ⊤

namespace GLModule

attribute [instance] instAddCommGroup instModule instFiniteDimensional

instance : CoeSort (GLModule n) Type := ⟨carrier⟩

/-- An isomorphism of `GLModule`s: a linear isomorphism intertwining the `gl_n`-actions. -/
structure Iso (M N : GLModule n) where
  /-- The underlying linear isomorphism. -/
  toLinearEquiv : M ≃ₗ[ℂ] N
  map_lie : ∀ (A : Square n) (x : M), toLinearEquiv (M.lie A x) = N.lie A (toLinearEquiv x)

/-- `M` is nonzero and has no `gl_n`-stable subspaces other than `0` and `M`. -/
def IsIrreducible (M : GLModule n) : Prop :=
  Nontrivial M ∧ ∀ W : Submodule ℂ M, (∀ A, ∀ x ∈ W, M.lie A x ∈ W) → W = ⊥ ∨ W = ⊤

end GLModule

@[inherit_doc] infixl:25 " ≃ᴳ " => GLModule.Iso

/-- A `gl_n`-stable polynomial subspace is stable under every `rowDerivation A`. -/
theorem IsLieStable.rowDerivation_mem {S : Submodule ℂ (MatrixPolynomial n)} (hS : IsLieStable S)
    (A : Square n) : ∀ p ∈ S, rowDerivation A p ∈ S := by
  intro p hp
  change polynomialLie n A p ∈ S
  rw [Matrix.matrix_eq_sum_single A, map_sum, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun a _ => ?_
  rw [map_sum, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun b _ => ?_
  rw [show (Matrix.single a b (A a b) : Square n) = A a b • Matrix.single a b 1 by
    rw [Matrix.smul_single, smul_eq_mul, mul_one], map_smul, LinearMap.smul_apply]
  exact S.smul_mem _ (hS a b p hp)

/-- The `gl_n`-action on the flag-minor span. -/
def flagOrbitLie (m : ColumnShape n) : Square n →ₗ⁅ℂ⁆ Module.End ℂ (flagOrbitSpan m) where
  toFun A := (polynomialLie n A).restrict
    (fun p hp => (flagOrbitSpan_isLieStable m).rowDerivation_mem A p hp)
  map_add' A B := by
    apply LinearMap.ext
    intro p
    apply Subtype.ext
    change polynomialLie n (A + B) p.val = polynomialLie n A p.val + polynomialLie n B p.val
    rw [map_add, LinearMap.add_apply]
  map_smul' c A := by
    apply LinearMap.ext
    intro p
    apply Subtype.ext
    change polynomialLie n (c • A) p.val = c • polynomialLie n A p.val
    rw [map_smul, LinearMap.smul_apply]
  map_lie' {A B} := by
    apply LinearMap.ext
    intro p
    apply Subtype.ext
    change polynomialLie n ⁅A, B⁆ p.val =
      polynomialLie n A (polynomialLie n B p.val) - polynomialLie n B (polynomialLie n A p.val)
    rw [LieHom.map_lie, LieRing.of_associative_ring_bracket]
    rfl

@[simp] theorem flagOrbitLie_val (m : ColumnShape n) (A : Square n) (p : flagOrbitSpan m) :
    (flagOrbitLie m A p).val = rowDerivation A p.val := rfl

/-- The flag-minor span as a `GLModule`. -/
abbrev flagOrbitModule (m : ColumnShape n) : GLModule n where
  carrier := flagOrbitSpan m
  lie := flagOrbitLie m
  weight_span := by
    rw [eq_top_iff]
    rintro ⟨p, hp⟩ -
    have hle : polynomialWeightSpan (flagOrbitSpan m) ≤ flagOrbitSpan m :=
      Submodule.span_le.mpr fun q hq => hq.1
    have hw : p ∈ polynomialWeightSpan (flagOrbitSpan m) := by
      rw [polynomialWeightSpan_eq _ (fun t q hq => flagOrbitSpan_torus_stable m t q hq)]
      exact hp
    suffices h : ∀ q (hq : q ∈ polynomialWeightSpan (flagOrbitSpan m)),
        (⟨q, hle hq⟩ : flagOrbitSpan m) ∈ ⨆ μ : Weight n, lieWeightSpace (flagOrbitLie m) μ from
      h p hw
    intro q hq
    induction hq using Submodule.span_induction with
    | mem q hq =>
      obtain ⟨_, μ, hμ⟩ := hq
      refine Submodule.mem_iSup_of_mem μ fun j => ?_
      apply Subtype.ext
      exact diagonalDerivation_of_weight j q μ hμ
    | zero => exact Submodule.zero_mem _
    | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
    | smul c x _ hx => exact Submodule.smul_mem _ c hx

/-- The highest flag polynomial as a vector of `flagOrbitModule m`. -/
def flagOrbitHighest (m : ColumnShape n) : flagOrbitModule m :=
  (⟨highestFlag m, highestFlag_mem_orbitSpan m⟩ : flagOrbitSpan m)

theorem flagOrbitHighest_ne_zero (m : ColumnShape n) : flagOrbitHighest m ≠ 0 := fun h =>
  highestFlag_ne_zero m (congrArg Subtype.val h)

theorem isHighestWeightVector_flagOrbitHighest (m : ColumnShape n) :
    IsHighestWeightVector (flagOrbitModule m).lie (dominantWeight m) (flagOrbitHighest m) := by
  refine ⟨fun a b hab => Subtype.ext (highestFlag_upper_invariant m a b hab), fun j => ?_⟩
  apply Subtype.ext
  change matrixUnitDerivation j j (highestFlag m) = ((dominantWeight m j : ℤ) : ℂ) • highestFlag m
  rw [matrixUnitDerivation_highestFlag_diag, dominantWeight, Int.cast_natCast]

/-- E7: the flag-minor model is an irreducible `GLModule`. -/
theorem flagOrbitModule_isIrreducible (m : ColumnShape n) : (flagOrbitModule m).IsIrreducible := by
  refine ⟨⟨⟨flagOrbitHighest m, 0, flagOrbitHighest_ne_zero m⟩⟩, fun W hW => ?_⟩
  let W' : Submodule ℂ (MatrixPolynomial n) := W.map (flagOrbitSpan m).subtype
  have hL : IsLieStable W' := by
    rintro a b _ ⟨x, hx, rfl⟩
    exact ⟨_, hW (Matrix.single a b 1) x hx, rfl⟩
  have hinj := Submodule.map_injective_of_injective (flagOrbitSpan m).injective_subtype
  rcases flagOrbitSpan_irreducible_lie m W' (by rintro _ ⟨x, _, rfl⟩; exact x.2) hL with h | h
  · left
    apply hinj
    exact h.trans (Submodule.map_bot _).symm
  · right
    apply hinj
    exact h.trans (Submodule.map_subtype_top _).symm

/-- E7, the theorem of the highest weight (uniqueness half) for this model: an irreducible
`GLModule` with a highest-weight vector `v` of weight `λ = shapeWeight m` is isomorphic to the
flag-minor span, by an isomorphism sending `v` to `v_λ`. -/
theorem exists_iso_flagOrbitModule (M : GLModule n) (hM : M.IsIrreducible) (m : ColumnShape n)
    (v : M) (hv : v ≠ 0) (hwt : v ∈ lieWeightSpace M.lie (dominantWeight m))
    (hinv : ∀ a b : Fin n, a < b → M.lie (Matrix.single a b 1) v = 0) :
    ∃ e : M ≃ᴳ flagOrbitModule m, e.toLinearEquiv v = flagOrbitHighest m := by
  obtain ⟨e, he, hev⟩ := exists_equiv_of_isHighestWeightVector hM.2
    (flagOrbitModule_isIrreducible m).2 hv (flagOrbitHighest_ne_zero m) ⟨hinv, hwt⟩
    (isHighestWeightVector_flagOrbitHighest m)
  exact ⟨⟨e, he⟩, hev⟩

/-- E7: an irreducible `GLModule` with a highest-weight vector of weight `λ = shapeWeight m` is
isomorphic to the flag-minor span. -/
theorem nonempty_iso_flagOrbitModule (M : GLModule n) (hM : M.IsIrreducible) (m : ColumnShape n)
    (v : M) (hv : v ≠ 0) (hwt : v ∈ lieWeightSpace M.lie (dominantWeight m))
    (hinv : ∀ a b : Fin n, a < b → M.lie (Matrix.single a b 1) v = 0) :
    Nonempty (M ≃ᴳ flagOrbitModule m) :=
  let ⟨e, _⟩ := exists_iso_flagOrbitModule M hM m v hv hwt hinv
  ⟨e⟩

end
end Schubert.RS.HighestWeight
