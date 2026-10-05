import Schubert.GLRep.Borel.Regular
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# The Borel subgroup of `SL_n` and central characters

The Borel subgroup of `SL_n(K)` is `B_SL = B ∩ SL_n` (`GLRep.borelSL`), the kernel of the
determinant on `B`. The scalar matrices `c·1` form a central subgroup of `B`
(`GLRep.borelScalar`). A representation of `B` has **central character** `d ∈ ℤ`
(`GLRep.HasCentralCharacter`) when `c·1` acts by `c^d`.

Over an algebraically closed field `B = K^× · B_SL` (`GLRep.exists_borelScalar_mul_mem_borelSL`).
Consequently, for a representation with a central character,

* a `B_SL`-stable subspace is `B`-stable, so a filtration of the restriction to `B_SL` is a
  filtration by subrepresentations of `B` with the same layers
  (`GLRep.HasCentralCharacter.toRepFiltration`);
* in characteristic zero, an equivalence of the restrictions to `B_SL` of two representations
  with central characters shifts all weights by the same multiple of `(1, …, 1)`
  (`GLRep.borelCharacter_eq_of_equiv_borelSL`).

This is the standard argument for the `SL_n` forms of the filtration
statements. The spaces of semi-invariants `(𝒪(GL_n)/I)^{(B, η)}` have central character
`η_1 + ⋯ + η_n` (`GLRep.hasCentralCharacter_borelSemiInvariantRep`).
-/

namespace GLRep

open Module TauCeti

noncomputable section

variable {K : Type*} [Field K] {n : ℕ}

/-! ### The Borel subgroup of `SL_n` and the scalar matrices -/

section Group

variable (K n) in
/-- The **Borel subgroup of `SL_n(K)`**: the elements of `B` of determinant one. -/
def borelSL : Subgroup (borel K n) :=
  (Matrix.GeneralLinearGroup.det.comp (borel K n).subtype).ker

theorem mem_borelSL {b : borel K n} :
    b ∈ borelSL K n ↔ Matrix.GeneralLinearGroup.det (b : GL (Fin n) K) = 1 :=
  MonoidHom.mem_ker

variable (K n) in
/-- The **scalar matrices** `c·1` in `B`. -/
def borelScalar : Kˣ →* borel K n :=
  (borelTorus K n).comp (MonoidHom.pi fun _ => MonoidHom.id Kˣ)

theorem borelScalar_apply (c : Kˣ) : borelScalar K n c = borelTorus K n fun _ => c :=
  rfl

theorem det_borelScalar (c : Kˣ) :
    Matrix.GeneralLinearGroup.det (borelScalar K n c : GL (Fin n) K) = c ^ n := by
  rw [det_borel, borelScalar_apply, borelDiag_borelTorus, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

theorem borelScalar_mem_borelSL {c : Kˣ} (hc : c ^ n = 1) : borelScalar K n c ∈ borelSL K n :=
  mem_borelSL.mpr (by rw [det_borelScalar, hc])

theorem borelChar_borelScalar (η : Fin n → ℤ) (c : Kˣ) :
    borelChar K n η (borelScalar K n c) = c ^ ∑ i, η i := by
  rw [borelScalar_apply, borelChar_borelTorus, weightChar_apply, torusCharacter_def,
    Finset.prod_zpow_eq_zpow_sum]

/-- **`B = K^× · B_SL`** over an algebraically closed field: every `b ∈ B` is a scalar matrix
`c·1`, with `cⁿ = det b`, times an element of `B_SL`. -/
theorem exists_borelScalar_mul_mem_borelSL [IsAlgClosed K] (b : borel K n) :
    ∃ c : Kˣ, c ^ n = Matrix.GeneralLinearGroup.det (b : GL (Fin n) K) ∧
      (borelScalar K n c)⁻¹ * b ∈ borelSL K n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨1, ?_, ?_⟩
    · ext
      simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_isEmpty]
    · rw [map_one, inv_one, one_mul, mem_borelSL]
      ext
      simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_isEmpty]
  · obtain ⟨z, hz⟩ :=
      IsAlgClosed.exists_pow_nat_eq ((Matrix.GeneralLinearGroup.det (b : GL (Fin n) K) : Kˣ) : K)
        hn
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow hn.ne'] at hz
      exact (Matrix.GeneralLinearGroup.det (b : GL (Fin n) K)).ne_zero hz.symm
    have hc : Units.mk0 z hz0 ^ n = Matrix.GeneralLinearGroup.det (b : GL (Fin n) K) :=
      Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hz])
    refine ⟨Units.mk0 z hz0, hc, mem_borelSL.mpr ?_⟩
    rw [Subgroup.coe_mul, map_mul, Subgroup.coe_inv, map_inv, det_borelScalar, hc,
      inv_mul_cancel]

/-- The torus version of `GLRep.exists_borelScalar_mul_mem_borelSL`. -/
theorem exists_borelTorus_eq_borelScalar_mul [IsAlgClosed K] (t : Fin n → Kˣ) :
    ∃ c : Kˣ, c ^ n = ∏ i, t i ∧
      (borelScalar K n c)⁻¹ * borelTorus K n t ∈ borelSL K n := by
  obtain ⟨c, hc, hmem⟩ := exists_borelScalar_mul_mem_borelSL (borelTorus K n t)
  refine ⟨c, ?_, hmem⟩
  rw [hc, det_borel, borelDiag_borelTorus]

end Group

/-! ### Central characters -/

section Central

variable {W : Type*} [AddCommGroup W] [Module K W] {ρ : Representation K (borel K n) W}
variable {V : Type*} [AddCommGroup V] [Module K V] {σ : Representation K (borel K n) V}

/-- A representation of `B` has **central character** `d` when every scalar matrix `c·1` acts by
`c^d`. -/
def HasCentralCharacter (ρ : Representation K (borel K n) W) (d : ℤ) : Prop :=
  ∀ (c : Kˣ) (w : W), ρ (borelScalar K n c) w = ((c ^ d : Kˣ) : K) • w

namespace HasCentralCharacter

variable {d d' : ℤ}

theorem of_injective (h : HasCentralCharacter ρ d) (φ : σ.IntertwiningMap ρ)
    (hφ : Function.Injective φ) : HasCentralCharacter σ d := fun c v =>
  hφ (by rw [φ.isIntertwining, map_smul, h])

theorem of_surjective (h : HasCentralCharacter ρ d) (φ : ρ.IntertwiningMap σ)
    (hφ : Function.Surjective φ) : HasCentralCharacter σ d := fun c v => by
  obtain ⟨w, rfl⟩ := hφ v
  rw [← φ.isIntertwining, h, map_smul]

theorem of_equiv (h : HasCentralCharacter ρ d) (e : ρ.Equiv σ) : HasCentralCharacter σ d :=
  h.of_surjective e.toIntertwiningMap e.toLinearEquiv.surjective

theorem subrepresentation (h : HasCentralCharacter ρ d) (U : Subrepresentation ρ) :
    HasCentralCharacter U.toRepresentation d :=
  h.of_injective ⟨U.toSubmodule.subtype, fun _ => rfl⟩ Subtype.val_injective

theorem quotient (h : HasCentralCharacter ρ d) (U : Subrepresentation ρ) :
    HasCentralCharacter U.quotient d :=
  h.of_surjective ⟨U.toSubmodule.mkQ, fun _ => rfl⟩ U.toSubmodule.mkQ_surjective

theorem subquotient (h : HasCentralCharacter ρ d) (U U' : Subrepresentation ρ) :
    HasCentralCharacter (GLRep.subquotient U U') d :=
  (h.subrepresentation U').quotient _

theorem tprod (h : HasCentralCharacter ρ d) (h' : HasCentralCharacter σ d') :
    HasCentralCharacter (ρ.tprod σ) (d + d') := fun c x => by
  induction x with
  | tmul v w =>
    rw [Representation.tprod_apply, TensorProduct.map_tmul, h, h', TensorProduct.smul_tmul_smul,
      ← Units.val_mul, ← zpow_add]
  | add x y hx hy => rw [map_add, hx, hy, smul_add]

theorem scaledRep (h : HasCentralCharacter ρ d) (η : Fin n → ℤ) :
    HasCentralCharacter (GLRep.scaledRep ρ (borelChar K n η)) (∑ i, η i + d) := fun c w => by
  rw [scaledRep_apply, h, borelChar_borelScalar, smul_smul, ← Units.val_mul, ← zpow_add]

end HasCentralCharacter

theorem hasCentralCharacter_borelCharRep (η : Fin n → ℤ) :
    HasCentralCharacter (borelCharRep K n η) (∑ i, η i) := fun c w => by
  rw [borelCharRep_apply, borelChar_borelScalar, smul_eq_mul]

/-! ### `B_SL`-stable subspaces and filtrations -/

section Filtration

variable [IsAlgClosed K] {d : ℤ}

/-- **Over a representation with a central character, a `B_SL`-stable subspace is
`B`-stable.** -/
theorem HasCentralCharacter.apply_mem (h : HasCentralCharacter ρ d)
    (U : Subrepresentation (ρ.comp (borelSL K n).subtype)) (b : borel K n) {w : W}
    (hw : w ∈ U.toSubmodule) : ρ b w ∈ U.toSubmodule := by
  obtain ⟨c, -, hc⟩ := exists_borelScalar_mul_mem_borelSL b
  have hb : b = borelScalar K n c * ((borelScalar K n c)⁻¹ * b) := by group
  rw [hb, map_mul, Module.End.mul_apply, h c]
  exact U.toSubmodule.smul_mem _ (U.apply_mem_toSubmodule ⟨_, hc⟩ hw)

/-- A `B_SL`-subrepresentation of a representation with a central character, as a
subrepresentation of `B`. -/
def HasCentralCharacter.toSubrep (h : HasCentralCharacter ρ d)
    (U : Subrepresentation (ρ.comp (borelSL K n).subtype)) : Subrepresentation ρ :=
  ⟨U.toSubmodule, fun b _ hw => h.apply_mem U b hw⟩

/-- **A filtration of the restriction to `B_SL`** of a representation with a central character
is a filtration by subrepresentations of `B`, with the same steps. -/
def HasCentralCharacter.toRepFiltration (h : HasCentralCharacter ρ d)
    (F : RepFiltration (ρ.comp (borelSL K n).subtype)) : RepFiltration ρ where
  length := F.length
  step i := h.toSubrep (F.step i)
  monotone _ _ hij := F.monotone hij
  step_zero := Subrepresentation.ext <| by
    have := congrArg Subrepresentation.toSubmodule F.step_zero
    exact this
  step_length := Subrepresentation.ext <| by
    have := congrArg Subrepresentation.toSubmodule F.step_length
    exact this

/-- The layers of a `B_SL`-filtration are the restrictions of the layers of the corresponding
filtration by subrepresentations of `B`. -/
def HasCentralCharacter.layerEquiv (h : HasCentralCharacter ρ d)
    (F : RepFiltration (ρ.comp (borelSL K n).subtype)) (i : ℕ) :
    (F.layer i).Equiv (((h.toRepFiltration F).layer i).comp (borelSL K n).subtype) :=
  .mk (LinearEquiv.refl K _) fun _ => rfl

end Filtration

/-! ### Equivalences over `B_SL` shift characters -/

section Shift

variable [IsAlgClosed K] [CharZero K] [NeZero n] {d d' : ℤ}

/-- If the restrictions to `B_SL` of two nonzero representations with central characters `d` and
`d'` are equivalent, then `n` divides `d − d'`. -/
theorem exists_sub_eq_mul_of_equiv_borelSL (hρ : HasCentralCharacter ρ d)
    (hσ : HasCentralCharacter σ d')
    (e : Representation.Equiv (ρ.comp (borelSL K n).subtype) (σ.comp (borelSL K n).subtype))
    {w : W} (hw : w ≠ 0) : ∃ j : ℤ, d - d' = n * j := by
  have : NeZero (n : K) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne n)⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K n
  set u := (hζ.isUnit (NeZero.ne n)).unit
  have hu : IsPrimitiveRoot u n :=
    IsPrimitiveRoot.coe_units_iff.mp ((hζ.isUnit (NeZero.ne n)).unit_spec ▸ hζ)
  have hmem : borelScalar K n u ∈ borelSL K n := borelScalar_mem_borelSL hu.pow_eq_one
  have hew : e w ≠ 0 := fun h0 => hw (e.toLinearEquiv.injective (by rw [map_zero]; exact h0))
  have key := e.toIntertwiningMap.isIntertwining _ _ ⟨_, hmem⟩ w
  change e (ρ (borelScalar K n u) w) = σ (borelScalar K n u) (e w) at key
  rw [hρ, hσ, map_smul] at key
  have hval : ((u ^ d : Kˣ) : K) = ((u ^ d' : Kˣ) : K) := smul_left_injective K hew key
  have h1 : u ^ (d - d') = 1 := by
    rw [zpow_sub, Units.ext hval, mul_inv_cancel]
  obtain ⟨j, hj⟩ := (hu.zpow_eq_one_iff_dvd (d - d')).mp h1
  exact ⟨j, hj⟩

omit [CharZero K] [NeZero n] in
/-- Under the hypotheses of `GLRep.borelCharacter_eq_of_equiv_borelSL`, the equivalence maps the
weight space of `μ` into the weight space of `μ − j·(1, …, 1)`. -/
theorem mem_borelWeightSpace_of_equiv_borelSL (hρ : HasCentralCharacter ρ d)
    (hσ : HasCentralCharacter σ d')
    (e : Representation.Equiv (ρ.comp (borelSL K n).subtype) (σ.comp (borelSL K n).subtype))
    {j : ℤ} (hj : d - d' = n * j) {μ : Fin n → ℤ} {w : W} (hw : w ∈ borelWeightSpace ρ μ) :
    e w ∈ borelWeightSpace σ (μ - fun _ => j) := by
  refine mem_borelWeightSpace.mpr fun t => ?_
  obtain ⟨c, hc, hmem⟩ := exists_borelTorus_eq_borelScalar_mul t
  have ht : borelTorus K n t = borelScalar K n c * ((borelScalar K n c)⁻¹ * borelTorus K n t) := by
    group
  have key := e.toIntertwiningMap.isIntertwining _ _ ⟨_, hmem⟩ w
  change e (ρ ((borelScalar K n c)⁻¹ * borelTorus K n t) w) =
    σ ((borelScalar K n c)⁻¹ * borelTorus K n t) (e w) at key
  have hσt : σ (borelTorus K n t) (e w) =
      ((c ^ d' : Kˣ) : K) • σ ((borelScalar K n c)⁻¹ * borelTorus K n t) (e w) := by
    conv_lhs => rw [ht]
    rw [map_mul, Module.End.mul_apply, hσ]
  rw [hσt, ← key, map_mul, Module.End.mul_apply, ← map_inv, hρ, mem_borelWeightSpace.mp hw t,
    smul_smul, map_smul, smul_smul]
  congr 1
  -- the scalar `c^{d'} c^{-d} t^μ` is `t^{μ - j·1}`
  have hcd : ((c ^ d' : Kˣ) : K) * ((c⁻¹ ^ d : Kˣ) : K) = ((((∏ i, t i) ^ j)⁻¹ : Kˣ) : K) := by
    rw [← Units.val_mul, ← hc, ← zpow_natCast, ← zpow_mul, inv_zpow', ← zpow_neg, ← zpow_add]
    congr 2
    linear_combination -hj
  rw [← mul_assoc, hcd, weightCharHom_apply, weightCharHom_apply, sub_eq_add_neg, weightChar_add,
    MonoidHom.mul_apply, Units.val_mul, mul_comm]
  congr 2
  rw [show (-fun _ : Fin n => j) = fun _ => -j from rfl, weightChar_const, zpow_neg]

/-- **An equivalence over `B_SL` shifts weights by a multiple of `(1, …, 1)`.** If the
restrictions to `B_SL` of two finite-dimensional representations of `B` with central characters
are equivalent, their characters differ by a monomial `x^{j·(1,…,1)}`. -/
theorem borelCharacter_eq_of_equiv_borelSL [FiniteDimensional K W] [FiniteDimensional K V]
    (hρ : HasCentralCharacter ρ d) (hσ : HasCentralCharacter σ d')
    (e : Representation.Equiv (ρ.comp (borelSL K n).subtype) (σ.comp (borelSL K n).subtype)) :
    ∃ j : ℤ, borelCharacter ρ = AddMonoidAlgebra.single (fun _ => j) 1 * borelCharacter σ := by
  by_cases hW : ∃ w : W, w ≠ 0
  · obtain ⟨w, hw⟩ := hW
    obtain ⟨j, hj⟩ := exists_sub_eq_mul_of_equiv_borelSL hρ hσ e hw
    have hj' : d' - d = n * (-j) := by linear_combination -hj
    refine ⟨j, TorusLaurent.ext fun μ => ?_⟩
    rw [AddMonoidAlgebra.coeff_single_mul_apply, one_mul, coeff_borelCharacter,
      coeff_borelCharacter]
    have hmap : (borelWeightSpace ρ μ).map e.toLinearEquiv.toLinearMap =
        borelWeightSpace σ (-(fun _ => j) + μ) := by
      ext v
      simp only [Submodule.mem_map]
      constructor
      · rintro ⟨w, hw, rfl⟩
        rw [neg_add_eq_sub]
        exact mem_borelWeightSpace_of_equiv_borelSL hρ hσ e hj hw
      · intro hv
        refine ⟨e.symm v, ?_, e.apply_symm_apply v⟩
        have := mem_borelWeightSpace_of_equiv_borelSL hσ hρ e.symm hj' hv
        convert this using 2
        funext i
        simp only [Pi.add_apply, Pi.neg_apply, Pi.sub_apply]
        ring
    exact_mod_cast (e.toLinearEquiv.ofSubmodules _ _ hmap).finrank_eq
  · simp only [ne_eq, not_exists, not_not] at hW
    have : Subsingleton W := ⟨fun a b => by rw [hW a, hW b]⟩
    have : Subsingleton V := e.toLinearEquiv.symm.toEquiv.subsingleton
    refine ⟨0, TorusLaurent.ext fun μ => ?_⟩
    rw [AddMonoidAlgebra.coeff_single_mul_apply, one_mul, coeff_borelCharacter,
      coeff_borelCharacter, finrank_zero_of_subsingleton, finrank_zero_of_subsingleton]

end Shift

/-! ### Central characters of semi-invariants -/

section SemiInvariants

/-- Left translation by a scalar matrix `c·1` is right translation by `c·1`. -/
theorem leftTranslHom_scalar (c : Kˣ) :
    leftTranslHom K n (borelScalar K n c : GL (Fin n) K) =
      rightTranslHom K n (borelScalar K n c⁻¹ : GL (Fin n) K) := by
  rw [leftTranslHom_apply, rightTranslHom_apply]
  refine GeneralLinear.algHom_ext_away _ _ ?_
  rw [leftSubstAway_comp, rightSubstAway_comp]
  congr 1
  apply MvPolynomial.algHom_ext
  rintro ⟨i, j⟩
  rw [leftSubst_X, rightSubst_X, ← Subgroup.coe_inv, ← map_inv, borelScalar_apply,
    coe_borelTorus,
    Finset.sum_eq_single i
      (fun k _ hk => by rw [diagGL_apply, ite_eq_right (Ne.symm hk), zero_smul]) (by simp),
    Finset.sum_eq_single j (fun k _ hk => by rw [diagGL_apply, ite_eq_right hk, zero_smul])
      (by simp),
    diagGL_apply, diagGL_apply, ite_eq_left rfl, ite_eq_left rfl]

variable (I : Ideal (GLCoord K n))

/-- **The semi-invariants `(𝒪(GL_n)/I)^{(B, η)}` have central character `η_1 + ⋯ + η_n`.** -/
theorem hasCentralCharacter_borelSemiInvariantRep (hL : IsLeftBorelStable I)
    (hR : IsRightBorelStable I) (η : Fin n → ℤ) :
    HasCentralCharacter (borelSemiInvariantRep I hL hR η) (∑ i, η i) := fun c f => by
  apply Subtype.ext
  obtain ⟨f, hf⟩ := f
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective f
  have hfc := (mem_borelSemiInvariants I).mp hf (borelScalar K n c⁻¹)
  change Ideal.Quotient.mk I (leftTranslHom K n (borelScalar K n c : GL (Fin n) K) x) =
    ((c ^ (∑ i, η i) : Kˣ) : K) • Ideal.Quotient.mk I x
  rw [leftTranslHom_scalar]
  change Ideal.Quotient.mk I (rightTranslHom K n (borelScalar K n c⁻¹ : GL (Fin n) K) x) = _ at hfc
  rw [hfc, borelChar_borelScalar, inv_zpow', zpow_neg, inv_inv]

end SemiInvariants

end Central

end

end GLRep
