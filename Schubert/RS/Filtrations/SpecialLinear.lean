import Schubert.RS.Filtrations.Obstruction
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Filtrations over the Borel subgroup of `SL_n`

The Borel subgroup `B_SL = T_SL ⋉ U` of `SL_n(ℂ)` has the unipotent radical of the Borel
subgroup of `GL_n(ℂ)` and the torus `T_SL = {t | t₁ ⋯ tₙ = 1}`. Every `B`-module restricts to a
`B_SL`-module. A filtration of the restriction is a chain of subspaces stable under `𝔫⁺` and
`T_SL` (`SLFiltration`); its layers carry the induced actions (`SLLayerIso`). The `SL_n` forms
of the two filtration notions require the layers to be isomorphic, as `B_SL`-modules, to minimal
relative Schubert modules `Q(ν)`, respectively to section modules over unions of Schubert
varieties (`HasSLRelativeSchubertFiltration`, `HasSLSchubertFiltration`). Filtrations by
`B`-submodules are filtrations of the restriction (`HasFiltrationBy.hasSLFiltrationBy`), so the
`SL_n` notions are weaker.

The character obstruction carries over (`atomPositive_of_hasSLRelativeSchubertFiltration`,
`atomPositive_of_hasSLSchubertFiltration`), by the argument of the paper (lines 1579–1581):
characters of `T_SL` are integral weights modulo `ℤ·(1,…,1)`, and the total degree picks a
unique lift. Formally, all modules involved have a central character: scalar matrices `c·1` act
by `c^d` (`HasCentralCharacter`). Since `T = ℂˣ · T_SL` (`exists_scalarTorus_mul`),

* over a module with a central character, `T_SL`-stable subspaces are `T`-stable, so a
  `B_SL`-filtration is a `B`-filtration (`SLFiltration.toBFiltration`);
* a `B_SL`-isomorphism between modules with central characters shifts all weights by the same
  multiple of `(1,…,1)` (`SLIso.hasCharacter`), so `ch L = x^{j·1} ch Q`.
-/

namespace Schubert.RS

open Representation BModules FinPermutation SchubertUnions
open scoped TensorProduct

noncomputable section

variable {n : ℕ}

namespace BModules

/-! ### The torus of `SL_n` -/

/-- The determinant `t ↦ t₁ ⋯ tₙ` of a diagonal matrix. -/
def torusDet (n : ℕ) : DiagonalTorus n →* ℂˣ where
  toFun t := ∏ i, t i
  map_one' := by simp
  map_mul' s t := by simp [Finset.prod_mul_distrib]

theorem torusDet_apply (t : DiagonalTorus n) : torusDet n t = ∏ i, t i := rfl

/-- The diagonal torus `T_SL = {t | t₁ ⋯ tₙ = 1}` of `SL_n(ℂ)`. -/
def specialTorus (n : ℕ) : Subgroup (DiagonalTorus n) := (torusDet n).ker

theorem mem_specialTorus {t : DiagonalTorus n} : t ∈ specialTorus n ↔ ∏ i, t i = 1 :=
  MonoidHom.mem_ker

theorem torusDet_scalarTorus (c : ℂˣ) : torusDet n (scalarTorus n c) = c ^ n := by
  simp [torusDet, scalarTorus]

/-- The character `t ↦ (t₁ ⋯ tₙ)^j` of the weight `j·(1,…,1)`. -/
theorem integerWeightScalar_constWeight (j : ℤ) (t : DiagonalTorus n) :
    integerWeightScalar (BModule.constWeight j) t = ((torusDet n t : ℂˣ) : ℂ) ^ j := by
  simp only [integerWeightScalar, BModule.constWeight, torusDet_apply, Units.coe_prod,
    Finset.prod_zpow]

/-- Every determinant has an `n`-th root. -/
theorem exists_pow_eq_torusDet (t : DiagonalTorus n) : ∃ c : ℂˣ, c ^ n = torusDet n t := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨1, by simp [torusDet_apply]⟩
  · obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq ((torusDet n t : ℂˣ) : ℂ) hn
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow hn.ne'] at hz
      exact (torusDet n t).ne_zero hz.symm
    exact ⟨Units.mk0 z hz0, Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hz])⟩

/-- `T = ℂˣ · T_SL`: every diagonal matrix is a scalar matrix `c·1` times a diagonal matrix of
determinant one, with `cⁿ = det t`. -/
theorem exists_scalarTorus_mul (t : DiagonalTorus n) :
    ∃ c : ℂˣ, c ^ n = torusDet n t ∧ (scalarTorus n c)⁻¹ * t ∈ specialTorus n := by
  obtain ⟨c, hc⟩ := exists_pow_eq_torusDet t
  refine ⟨c, hc, ?_⟩
  rw [specialTorus, MonoidHom.mem_ker, map_mul, map_inv, torusDet_scalarTorus, hc,
    inv_mul_cancel]

/-- If every `n`-th root of unity `c` satisfies `c^m = 1`, then `c^m = (cⁿ)^j` for all `c`,
for some `j` (namely `m = n j`). -/
theorem exists_twist_exponent {m : ℤ} (h : ∀ c : ℂˣ, c ^ n = 1 → (c : ℂ) ^ m = 1) :
    ∃ j : ℤ, ∀ c : ℂˣ, (c : ℂ) ^ m = ((c : ℂ) ^ n) ^ j := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact ⟨0, fun c => by rw [zpow_zero]; exact h c (pow_zero c)⟩
  · have hζ := Complex.isPrimitiveRoot_exp n hn.ne'
    have hu : (Units.mk0 _ (hζ.ne_zero hn.ne')) ^ n = 1 :=
      Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]; exact hζ.pow_eq_one)
    obtain ⟨j, hj⟩ := (hζ.zpow_eq_one_iff_dvd m).mp (h _ hu)
    exact ⟨j, fun c => by rw [hj, zpow_mul, zpow_natCast]⟩

namespace BModule

/-! ### Central characters -/

/-- Scalar matrices `c·1` act on `M` by `c^d`; equivalently, all weights of `M` have total
degree `d`. -/
def HasCentralCharacter (M : BModule n) (d : ℤ) : Prop :=
  ∀ (c : ℂˣ) (v : M), M.torus (scalarTorus n c) v = ((c : ℂ) ^ d) • v

variable {M N : BModule n} {d e : ℤ}

theorem HasCentralCharacter.of_iso (hM : M.HasCentralCharacter d) (f : M ≃ᴮ N) :
    N.HasCentralCharacter d := by
  intro c v
  obtain ⟨w, rfl⟩ := f.toLinearEquiv.surjective v
  rw [← f.map_torus, hM, map_smul]

theorem HasCentralCharacter.dual (hM : M.HasCentralCharacter d) :
    M.dual.HasCentralCharacter (-d) := by
  intro c (φ : Module.Dual ℂ M)
  apply LinearMap.ext
  intro v
  change φ (M.torus (scalarTorus n c)⁻¹ v) = (c : ℂ) ^ (-d) * φ v
  have hinv : (scalarTorus n c)⁻¹ = scalarTorus n c⁻¹ := rfl
  rw [hinv, hM, map_smul, smul_eq_mul, Units.val_inv_eq_inv_val, inv_zpow']

theorem HasCentralCharacter.twist (hM : M.HasCentralCharacter d) (k : ℤ) :
    (M.twist k).HasCentralCharacter (n * k + d) := by
  intro c (v : M)
  change integerWeightScalar (constWeight k) (scalarTorus n c) • M.torus (scalarTorus n c) v = _
  rw [hM, smul_smul, integerWeightScalar_constWeight, torusDet_scalarTorus,
    Units.val_pow_eq_pow_val, ← zpow_natCast, ← zpow_mul, ← zpow_add₀ c.ne_zero]
  rfl

theorem HasCentralCharacter.tensor (hM : M.HasCentralCharacter d)
    (hN : N.HasCentralCharacter e) : (M.tensor N).HasCentralCharacter (d + e) := by
  intro c (v : M ⊗[ℂ] N)
  show M.tensorTorus N (scalarTorus n c) v = ((c : ℂ) ^ (d + e)) • v
  induction v using TensorProduct.inductionOn with
  | tmul x y =>
    rw [tensorTorus_tmul, hM, hN, TensorProduct.smul_tmul_smul, zpow_add₀ c.ne_zero]
  | add x y hx hy => rw [map_add, hx, hy, smul_add]

/-! ### Isomorphisms of `B_SL`-modules -/

/-- An isomorphism between the restrictions of two `B`-modules to `B_SL`: a linear isomorphism
commuting with `𝔫⁺` and with the torus `T_SL`. -/
structure SLIso (M N : BModule n) where
  /-- The underlying linear isomorphism. -/
  toLinearEquiv : M ≃ₗ[ℂ] N
  map_nil : ∀ X v, toLinearEquiv (M.nil X v) = N.nil X (toLinearEquiv v)
  map_torus : ∀ t ∈ specialTorus n, ∀ v,
    toLinearEquiv (M.torus t v) = N.torus t (toLinearEquiv v)

/-- A `B`-isomorphism restricts to a `B_SL`-isomorphism. -/
def Iso.toSLIso (f : M ≃ᴮ N) : SLIso M N :=
  ⟨f.toLinearEquiv, f.map_nil, fun t _ v => f.map_torus t v⟩

namespace SLIso

variable {L Q : BModule n} (f : SLIso L Q) {d' : ℤ}

include f in
/-- If some `c` with `cⁿ = 1` has `c^{d'-d} ≠ 1`, the scalar `c·1 ∈ T_SL` separates the central
characters, and a `B_SL`-isomorphism can only exist between zero modules. -/
theorem eq_zero_of_pow_ne_one (hL : L.HasCentralCharacter d) (hQ : Q.HasCentralCharacter d')
    {c : ℂˣ} (hc : c ^ n = 1) (hcd : (c : ℂ) ^ (d' - d) ≠ 1) (v : L) : v = 0 := by
  have hs : scalarTorus n c ∈ specialTorus n := by
    rw [specialTorus, MonoidHom.mem_ker, torusDet_scalarTorus, hc]
  have h := f.map_torus _ hs v
  rw [hL, hQ, map_smul] at h
  have hne : (c : ℂ) ^ d ≠ (c : ℂ) ^ d' := by
    intro h'
    apply hcd
    rw [zpow_sub₀ c.ne_zero, h', div_self (zpow_ne_zero _ c.ne_zero)]
  have h0 : ((c : ℂ) ^ d - (c : ℂ) ^ d') • f.toLinearEquiv v = 0 := by
    rw [sub_smul, h, sub_self]
  rcases smul_eq_zero.mp h0 with h1 | h1
  · exact absurd (sub_eq_zero.mp h1) hne
  · exact f.toLinearEquiv.map_eq_zero_iff.mp h1

/-- The twisting relation `t · f(v) = det(t)^j f(t · v)`, when `c^{d'-d} = (cⁿ)^j` for all `c`. -/
theorem torus_apply (hL : L.HasCentralCharacter d) (hQ : Q.HasCentralCharacter d') {j : ℤ}
    (hj : ∀ c : ℂˣ, (c : ℂ) ^ (d' - d) = ((c : ℂ) ^ n) ^ j) (t : DiagonalTorus n) (v : L) :
    Q.torus t (f.toLinearEquiv v) =
      (((torusDet n t : ℂˣ) : ℂ) ^ j) • f.toLinearEquiv (L.torus t v) := by
  obtain ⟨c, hc, hs₀⟩ := exists_scalarTorus_mul t
  obtain ⟨s, hs, rfl⟩ : ∃ s ∈ specialTorus n, t = scalarTorus n c * s :=
    ⟨_, hs₀, (mul_inv_cancel_left _ _).symm⟩
  rw [← hc, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, ← f.map_torus s hs, hQ,
    hL, map_smul, smul_smul, Units.val_pow_eq_pow_val, ← hj c, ← zpow_add₀ c.ne_zero,
    sub_add_cancel]

/-- Under the twisting relation, `f` maps the weight space of `μ` onto that of `μ + j·(1,…,1)`. -/
theorem map_weightSpace (hL : L.HasCentralCharacter d) (hQ : Q.HasCentralCharacter d') {j : ℤ}
    (hj : ∀ c : ℂˣ, (c : ℂ) ^ (d' - d) = ((c : ℂ) ^ n) ^ j) (μ : Weight n) :
    (L.weightSpace μ).map (f.toLinearEquiv : L →ₗ[ℂ] Q) =
      Q.weightSpace (μ + constWeight j) := by
  have hrel := f.torus_apply hL hQ hj
  have hsplit : ∀ t, integerWeightScalar (μ + constWeight j) t =
      ((torusDet n t : ℂˣ) : ℂ) ^ j * integerWeightScalar μ t := by
    intro t
    rw [integerWeightScalar_add, integerWeightScalar_constWeight, mul_comm]
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩ t
    change Q.torus t (f.toLinearEquiv v) = _
    rw [hrel, hv t, map_smul, smul_smul, hsplit]
    rfl
  · intro hw
    refine ⟨f.toLinearEquiv.symm w, ?_, f.toLinearEquiv.apply_symm_apply w⟩
    intro t
    apply f.toLinearEquiv.injective
    have h := hrel t (f.toLinearEquiv.symm w)
    rw [f.toLinearEquiv.apply_symm_apply, hw t, hsplit, mul_smul] at h
    rw [map_smul, f.toLinearEquiv.apply_symm_apply]
    exact (smul_right_injective Q (zpow_ne_zero _ (Units.ne_zero _))) h.symm

include f in
/-- A `B_SL`-isomorphism between modules with central characters matches the weight `μ` with
`μ + j·(1,…,1)`, for a fixed `j`. -/
theorem exists_finrank_weightSpace (hL : L.HasCentralCharacter d)
    (hQ : Q.HasCentralCharacter d') :
    ∃ j : ℤ, ∀ μ : Weight n, Module.finrank ℂ (L.weightSpace μ) =
      Module.finrank ℂ (Q.weightSpace (μ + constWeight j)) := by
  by_cases hdeg : ∀ c : ℂˣ, c ^ n = 1 → (c : ℂ) ^ (d' - d) = 1
  · obtain ⟨j, hj⟩ := exists_twist_exponent hdeg
    refine ⟨j, fun μ => ?_⟩
    rw [← f.map_weightSpace hL hQ hj μ, LinearEquiv.finrank_map_eq]
  · obtain ⟨c, hc⟩ := not_forall.mp hdeg
    obtain ⟨hc1, hc2⟩ := not_imp.mp hc
    have hL0 : ∀ v : L, v = 0 := f.eq_zero_of_pow_ne_one hL hQ hc1 hc2
    have hQ0 : ∀ w : Q, w = 0 := fun w => by
      obtain ⟨v, rfl⟩ := f.toLinearEquiv.surjective w
      rw [hL0 v, map_zero]
    refine ⟨0, fun μ => ?_⟩
    rw [Submodule.finrank_eq_zero.mpr (eq_bot_iff.mpr fun v _ => (Submodule.mem_bot ℂ).mpr (hL0 v)),
      Submodule.finrank_eq_zero.mpr (eq_bot_iff.mpr fun w _ => (Submodule.mem_bot ℂ).mpr (hQ0 w))]

include f in
/-- **Characters across `B_SL`-isomorphisms.** If `L ≅ Q` as `B_SL`-modules and both have
central characters, then `ch L = x^{j·1} ch Q` for some `j`. -/
theorem hasCharacter (hL : L.HasCentralCharacter d) (hQ : Q.HasCentralCharacter d')
    {g : Laurent n} (hg : Q.HasCharacter g) :
    ∃ j : ℤ, L.HasCharacter (AddMonoidAlgebra.single (constWeight j) 1 * g) := by
  obtain ⟨j, hj⟩ := f.exists_finrank_weightSpace hL hQ
  refine ⟨j, fun μ => ?_⟩
  rw [hj, hg]
  have h : -μ = constWeight j + -(μ + constWeight j) := by abel
  rw [h, laurent_coefficient_shift]

end SLIso

end BModule

namespace BSubmodule

variable {M : BModule n} {d : ℤ}

theorem hasCentralCharacter_toBModule (S : BSubmodule M) (hM : M.HasCentralCharacter d) :
    S.toBModule.HasCentralCharacter d :=
  fun c (v : S.toSubmodule) => Subtype.ext (hM c v)

theorem hasCentralCharacter_quotient (S : BSubmodule M) (hM : M.HasCentralCharacter d) :
    S.quotient.HasCentralCharacter d := by
  intro c v
  induction v using Submodule.Quotient.induction_on with
  | H v =>
    change Submodule.Quotient.mk (M.torus (scalarTorus n c) v) = _
    rw [hM]
    rfl

theorem hasCentralCharacter_subquotient (S S' : BSubmodule M) (hM : M.HasCentralCharacter d) :
    (S.subquotient S').HasCentralCharacter d :=
  hasCentralCharacter_quotient _ (hasCentralCharacter_toBModule S' hM)

end BSubmodule

end BModules

namespace Filtrations

open BModules.BModule

/-! ### Central characters of the modules of the paper -/

/-- `Σ_{w ∈ S} D_w(λ)` consists of polynomials of degree `|λ|`. -/
theorem demazureUnionModule_hasCentralCharacter (m : ColumnShape n)
    (S : Finset (Equiv.Perm (Fin n))) :
    (demazureUnionModule m S).HasCentralCharacter (flagDegree m) := by
  have key : ∀ (c : ℂˣ), ∀ p ∈ demazureUnion m S,
      polynomialTorus n (scalarTorus n c) p = (c : ℂ) ^ flagDegree m • p := by
    intro c p hp
    exact Submodule.iSup_induction (fun w : S => flagDemazure m w)
      (motive := fun q => polynomialTorus n (scalarTorus n c) q = (c : ℂ) ^ flagDegree m • q) hp
      (fun w q hq => flagDemazure_scalar m w c hq) (by simp)
      (fun x y hx hy => by rw [map_add, hx, hy, smul_add])
  intro c (v : demazureUnion m S)
  apply Subtype.ext
  change polynomialTorus n (scalarTorus n c) v.1 = (c : ℂ) ^ (flagDegree m : ℤ) • v.1
  rw [zpow_natCast]
  exact key c v v.2

theorem sectionModuleOf_hasCentralCharacter (k : ℕ) (dom : Composition n)
    (S : Finset (Equiv.Perm (Fin n))) :
    (sectionModuleOf k dom S).HasCentralCharacter
      (n * k - flagDegree (columnsOfWeight dom)) := by
  rw [sub_eq_add_neg]
  exact (demazureUnionModule_hasCentralCharacter _ S).dual.twist k

theorem schubertSectionModule_hasCentralCharacter (η : Weight n)
    (S : Finset (Equiv.Perm (Fin n))) :
    ∃ d, (schubertSectionModule η S).HasCentralCharacter d :=
  ⟨_, sectionModuleOf_hasCentralCharacter _ _ S⟩

theorem dualJoseph_hasCentralCharacter (ν : Weight n) :
    ∃ d, (dualJoseph ν).HasCentralCharacter d :=
  ⟨_, sectionModuleOf_hasCentralCharacter _ _ _⟩

theorem minRelSchubert_hasCentralCharacter (ν : Weight n) :
    ∃ d, (minRelSchubert ν).HasCentralCharacter d := by
  obtain ⟨d, hd⟩ := dualJoseph_hasCentralCharacter ν
  exact ⟨d, BSubmodule.hasCentralCharacter_toBModule _ hd⟩

/-! ### Filtrations of `B_SL`-modules -/

variable {M : BModule n}

/-- An identification of the layer `W'/W` of `M` (for subspaces `W ≤ W'`) with `L` as
`B_SL`-modules: the actions of `𝔫⁺` and `T_SL` induced from `M` correspond to those of `L`. -/
structure SLLayerIso (M : BModule n) (W W' : Submodule ℂ M) (L : BModule n) where
  /-- The underlying linear isomorphism `W'/W ≃ L`. -/
  toLinearEquiv : (↥W' ⧸ W.comap W'.subtype) ≃ₗ[ℂ] L
  map_nil : ∀ (X : upperNilpotent n) (v : W') (hv : M.nil X v ∈ W'),
    toLinearEquiv (Submodule.Quotient.mk ⟨M.nil X v, hv⟩) =
      L.nil X (toLinearEquiv (Submodule.Quotient.mk v))
  map_torus : ∀ t ∈ specialTorus n, ∀ (v : W') (hv : M.torus t v ∈ W'),
    toLinearEquiv (Submodule.Quotient.mk ⟨M.torus t v, hv⟩) =
      L.torus t (toLinearEquiv (Submodule.Quotient.mk v))

/-- A filtration of the restriction of `M` to `B_SL`: a chain `0 = W₀ ≤ W₁ ≤ ⋯ ≤ W_r = M` of
subspaces stable under `𝔫⁺` and `T_SL`. -/
structure SLFiltration (M : BModule n) where
  /-- The number `r` of layers. -/
  length : ℕ
  /-- The steps of the filtration. -/
  step : ℕ → Submodule ℂ M
  monotone : Monotone step
  step_zero : step 0 = ⊥
  step_length : step length = ⊤
  nil_mem : ∀ i X, ∀ v ∈ step i, M.nil X v ∈ step i
  torus_mem : ∀ i, ∀ t ∈ specialTorus n, ∀ v ∈ step i, M.torus t v ∈ step i

/-- The restriction of `M` to `B_SL` has a filtration whose layers are isomorphic, as
`B_SL`-modules, to members of `𝒞`. -/
def HasSLFiltrationBy (𝒞 : BModule n → Prop) (M : BModule n) : Prop :=
  ∃ F : SLFiltration M, ∀ i < F.length,
    ∃ L, 𝒞 L ∧ Nonempty (SLLayerIso M (F.step i) (F.step (i + 1)) L)

/-- `M` admits a relative Schubert filtration over `SL_n`: its restriction to `B_SL` has a
filtration whose layers are isomorphic, as `B_SL`-modules, to minimal relative Schubert modules
`Q(ν)`. -/
def HasSLRelativeSchubertFiltration (M : BModule n) : Prop :=
  HasSLFiltrationBy IsMinRelSchubertLayer M

/-- `M` admits a Schubert filtration in Polo's sense over `SL_n`: its restriction to `B_SL` has a
filtration whose layers are isomorphic, as `B_SL`-modules, to section modules over unions of
Schubert varieties. -/
def HasSLSchubertFiltration (M : BModule n) : Prop := HasSLFiltrationBy IsSchubertLayer M

/-- A filtration by `B`-submodules is a filtration of the restriction to `B_SL`. -/
theorem _root_.Schubert.RS.BModules.HasFiltrationBy.hasSLFiltrationBy {𝒞 : BModule n → Prop}
    (h : HasFiltrationBy 𝒞 M) :
    HasSLFiltrationBy 𝒞 M := by
  obtain ⟨F, hF⟩ := h
  refine ⟨⟨F.length, fun i => (F.step i).toSubmodule,
    fun i j hij => BSubmodule.le_def.mp (F.monotone hij), by rw [F.step_zero]; rfl,
    by rw [F.step_length]; rfl, fun i X v hv => (F.step i).nil_mem X v hv,
    fun i t _ v hv => (F.step i).torus_mem t v hv⟩, fun i hi => ⟨F.layer i, hF i hi, ⟨?_⟩⟩⟩
  exact
    { toLinearEquiv := LinearEquiv.refl ℂ _
      map_nil := fun _ _ _ => rfl
      map_torus := fun _ _ _ _ => rfl }

theorem HasRelativeSchubertFiltration.hasSL (h : HasRelativeSchubertFiltration M) :
    HasSLRelativeSchubertFiltration M :=
  BModules.HasFiltrationBy.hasSLFiltrationBy h

theorem HasSchubertFiltration.hasSL (h : HasSchubertFiltration M) : HasSLSchubertFiltration M :=
  BModules.HasFiltrationBy.hasSLFiltrationBy h

variable {d : ℤ}

/-- Over a module with a central character, `T_SL`-stable subspaces are `T`-stable. -/
theorem torus_mem_of_specialTorus (hM : M.HasCentralCharacter d) {W : Submodule ℂ M}
    (hW : ∀ t ∈ specialTorus n, ∀ v ∈ W, M.torus t v ∈ W) (t : DiagonalTorus n) :
    ∀ v ∈ W, M.torus t v ∈ W := by
  intro v hv
  obtain ⟨c, -, hs⟩ := exists_scalarTorus_mul t
  have ht : t = scalarTorus n c * ((scalarTorus n c)⁻¹ * t) := (mul_inv_cancel_left _ _).symm
  rw [ht, map_mul, Module.End.mul_apply, hM]
  exact W.smul_mem _ (hW _ hs v hv)

/-- Over a module with a central character, a filtration of the restriction to `B_SL` is a
filtration by `B`-submodules. -/
def SLFiltration.toBFiltration (F : SLFiltration M) (hM : M.HasCentralCharacter d) :
    BFiltration M where
  length := F.length
  step i := ⟨F.step i, F.nil_mem i, fun t => torus_mem_of_specialTorus hM (F.torus_mem i) t⟩
  monotone _ _ hij := BSubmodule.le_def.mpr (F.monotone hij)
  step_zero := BSubmodule.ext F.step_zero
  step_length := BSubmodule.ext F.step_length

/-- A `B_SL`-identification of a layer of `F` is a `B_SL`-isomorphism from the corresponding
layer of the `B`-filtration. -/
def SLLayerIso.toSLIso {F : SLFiltration M} (hM : M.HasCentralCharacter d) {i : ℕ}
    {L : BModule n} (e : SLLayerIso M (F.step i) (F.step (i + 1)) L) :
    SLIso ((F.toBFiltration hM).layer i) L where
  toLinearEquiv := e.toLinearEquiv
  map_nil X v := by
    induction v using Submodule.Quotient.induction_on with
    | H v => exact e.map_nil X v _
  map_torus t ht v := by
    induction v using Submodule.Quotient.induction_on with
    | H v => exact e.map_torus t ht v _

/-! ### The obstruction over `SL_n` -/

/-- If every member of `𝒞` has a central character and a shifted sum of atoms as character,
then a `B_SL`-filtration with layers in `𝒞` of a module with a central character and polynomial
character `f` forces `f` to be atom positive. -/
theorem atomPositive_of_hasSLFiltrationBy {𝒞 : BModule n → Prop}
    (h𝒞 : ∀ L, 𝒞 L → ∃ (g : Laurent n) (d' : ℤ),
      L.HasCharacter g ∧ IsShiftedAtomSum g ∧ L.HasCentralCharacter d')
    {f : Polynomial n} (hM : M.HasCharacter (toLaurent f)) (hc : M.HasCentralCharacter d)
    (hF : HasSLFiltrationBy 𝒞 M) : AtomPositive f := by
  obtain ⟨F, hF⟩ := hF
  refine atomPositive_of_filtration (F.toBFiltration hc) hM fun i hi => ?_
  obtain ⟨L, hL, ⟨e⟩⟩ := hF i hi
  obtain ⟨g, d', hg, hgs, hd'⟩ := h𝒞 L hL
  obtain ⟨j, hj⟩ := (e.toSLIso hc).hasCharacter
    (BSubmodule.hasCentralCharacter_subquotient _ _ hc) hd' hg
  exact ⟨_, hj, hgs.shift j⟩

/-- **Relative Schubert filtrations over `SL_n` force atom positivity.** -/
theorem atomPositive_of_hasSLRelativeSchubertFiltration {f : Polynomial n}
    (hM : M.HasCharacter (toLaurent f)) (hc : M.HasCentralCharacter d)
    (hF : HasSLRelativeSchubertFiltration M) : AtomPositive f := by
  refine atomPositive_of_hasSLFiltrationBy (fun L hL => ?_) hM hc hF
  obtain ⟨g, hg, hgs⟩ := exists_isShiftedAtomSum_of_minRelSchubertLayer hL
  obtain ⟨ν, ⟨e⟩⟩ := hL
  obtain ⟨d', hd'⟩ := minRelSchubert_hasCentralCharacter ν
  exact ⟨g, d', hg, hgs, hd'.of_iso e.symm⟩

/-- **Schubert filtrations in Polo's sense over `SL_n` force atom positivity.** -/
theorem atomPositive_of_hasSLSchubertFiltration {f : Polynomial n}
    (hM : M.HasCharacter (toLaurent f)) (hc : M.HasCentralCharacter d)
    (hF : HasSLSchubertFiltration M) : AtomPositive f := by
  refine atomPositive_of_hasSLFiltrationBy (fun L hL => ?_) hM hc hF
  obtain ⟨g, hg, hgs⟩ := exists_isShiftedAtomSum_of_schubertLayer hL
  obtain ⟨η, S, -, -, ⟨e⟩⟩ := hL
  obtain ⟨d', hd'⟩ := schubertSectionModule_hasCentralCharacter η S
  exact ⟨g, d', hg, hgs, hd'.of_iso e.symm⟩

end Filtrations

end

end Schubert.RS
