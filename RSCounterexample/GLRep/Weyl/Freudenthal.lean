import RSCounterexample.GLRep.Weyl.LieWeights

/-!
# Freudenthal's formula for `gl_n`

Let `M` be an integral `gl_n(K)`-module, `K` a field of characteristic zero, on which the Casimir
element `Ω = ∑_{a,b} E_ab E_ba` acts by a scalar `c`. Write `m(μ) = dim M_μ` and, for `a < b`,
`t_{ab}(μ)` for the trace of `E_ba E_ab` on `M_μ` (`GLRep.stringTrace`). Taking traces on the
weight spaces gives:

* the **root-string recursion** `t_{ab}(μ − α) = t_{ab}(μ) + (μ_a − μ_b) m(μ)` for `α = ε_a − ε_b`
  (`GLRep.stringTrace_sub_root`). On `M_μ`, `E_ab E_ba = E_ba E_ab + (μ_a − μ_b)`, and
  `tr(E_ab E_ba | M_μ) = tr(E_ba E_ab | M_{μ−α})` because the trace of a composite does not depend
  on the order of the factors.
* **Freudenthal's formula** `c m(μ) = |μ|² m(μ) + ∑_{a<b} (μ_a − μ_b) m(μ) + 2 ∑_{a<b} t_{ab}(μ)`
  (`GLRep.freudenthal`).

Neither needs `sl₂` theory, only traces. As identities of Laurent polynomials they are exactly
the hypotheses of `GLRep.LaurentPoly.laplace_alternant_staircase_mul`
(`GLRep.freudenthal_laurent`, `GLRep.stringRecursion_laurent`).

## Main definitions

* `GLRep.weightShift`: `E_ab` as a linear map `M_μ → M_ν`, for `ν = μ + ε_a − ε_b`.
* `GLRep.stringTrace`: `t_{ab}(μ) = tr(E_ba E_ab | M_μ)`.

## Main results

* `GLRep.stringTrace_sub_root`, `GLRep.freudenthal`.
* `GLRep.freudenthal_laurent`, `GLRep.stringRecursion_laurent`.
-/

namespace GLRep

open Module LieModule Finset

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K : Type*} [Field K] {n : ℕ}
variable {M : Type*} [AddCommGroup M] [Module K M] [LieRingModule (Matrix (Fin n) (Fin n) K) M]
  [LieModule K (Matrix (Fin n) (Fin n) K) M]

/-! ### Shifting weight spaces -/

variable (K M) in
/-- `E_ab` as a linear map from the weight space of `μ` to that of `ν = μ + ε_a − ε_b`. -/
def weightShift (a b : Fin n) {μ ν : Fin n → ℤ} (h : ν = μ + root a b) :
    glWeightSpace K M μ →ₗ[K] glWeightSpace K M ν :=
  LinearMap.codRestrict _ ((toEnd K (Matrix (Fin n) (Fin n) K) M (matUnit a b)).comp
    (glWeightSpace K M μ).subtype) fun w => h ▸ lie_mem_glWeightSpace w.2 a b

@[simp] theorem weightShift_apply (a b : Fin n) {μ ν : Fin n → ℤ} (h : ν = μ + root a b)
    (w : glWeightSpace K M μ) :
    (weightShift K M a b h w : M) = ⁅(matUnit a b : Matrix (Fin n) (Fin n) K), (w : M)⁆ := rfl

theorem root_add_root (a b : Fin n) : root a b + root b a = 0 := by
  simp [root]

theorem add_root_add_root (μ : Fin n → ℤ) (a b : Fin n) : μ + root a b + root b a = μ := by
  rw [add_assoc, root_add_root, add_zero]

variable (K M) in
/-- `t_{ab}(μ)`: the trace of `E_ba E_ab` on the weight space of `μ`. -/
def stringTrace (a b : Fin n) (μ : Fin n → ℤ) : K :=
  LinearMap.trace K _ ((weightShift K M b a (add_root_add_root μ a b).symm).comp
    (weightShift K M a b (μ := μ) rfl))

/-- The definition of `t_{ab}(μ)` does not depend on how the intermediate weight is written. -/
theorem stringTrace_eq (a b : Fin n) {μ ν : Fin n → ℤ} (hν : ν = μ + root a b)
    (hμ : μ = ν + root b a) :
    stringTrace K M a b μ =
      LinearMap.trace K _ ((weightShift K M b a hμ).comp (weightShift K M a b hν)) := by
  subst hν
  rfl

/-- The bracket of opposite matrix units. -/
theorem matUnit_lie_matUnit (a b : Fin n) :
    ⁅(matUnit a b : Matrix (Fin n) (Fin n) K), (matUnit b a : Matrix (Fin n) (Fin n) K)⁆ =
      matUnit a a - matUnit b b := by
  rw [Ring.lie_def, Matrix.single_mul_single_same, Matrix.single_mul_single_same, one_mul]

variable (K M) in
/-- `tr(E_ab E_ba | M_μ)`. -/
def opTrace (a b : Fin n) (μ : Fin n → ℤ) : K :=
  LinearMap.trace K _ ((weightShift K M a b (add_root_add_root μ b a).symm).comp
    (weightShift K M b a (μ := μ) rfl))

/-- On `M_μ`, `E_ab E_ba = E_ba E_ab + (μ_a − μ_b)`. -/
theorem opTrace_eq_stringTrace_add [FiniteDimensional K M] (a b : Fin n) (μ : Fin n → ℤ) :
    opTrace K M a b μ =
      stringTrace K M a b μ + ((μ a : K) - μ b) * finrank K (glWeightSpace K M μ) := by
  have h2 : (weightShift K M a b (add_root_add_root μ b a).symm).comp
        (weightShift K M b a (μ := μ) rfl) =
      (weightShift K M b a (add_root_add_root μ a b).symm).comp
        (weightShift K M a b (μ := μ) rfl) + ((μ a : K) - μ b) • LinearMap.id := by
    ext ⟨w, hw⟩
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
      Submodule.coe_add, Submodule.coe_smul, weightShift_apply]
    have hc := lie_lie (L := Matrix (Fin n) (Fin n) K) (matUnit a b) (matUnit b a) w
    rw [matUnit_lie_matUnit a b, sub_lie, (mem_glWeightSpace.mp hw) a,
      (mem_glWeightSpace.mp hw) b, ← sub_smul] at hc
    rw [hc]
    abel
  rw [opTrace, h2, map_add, map_smul, LinearMap.trace_id, smul_eq_mul, mul_comm]
  rfl

/-- `tr(E_ab E_ba | M_μ) = tr(E_ba E_ab | M_{μ − α})`: the trace of a composite does not depend on
the order of the factors. -/
theorem opTrace_eq_stringTrace_add_root [FiniteDimensional K M] (a b : Fin n)
    (μ : Fin n → ℤ) :
    opTrace K M a b μ = stringTrace K M a b (μ + root b a) := by
  rw [stringTrace_eq a b (add_root_add_root μ b a).symm rfl, opTrace,
    LinearMap.trace_comp_comm']

/-- `tr(E_ba E_ab | M_μ) = t_{ab}(μ)`. -/
theorem opTrace_swap (a b : Fin n) (μ : Fin n → ℤ) :
    opTrace K M b a μ = stringTrace K M a b μ :=
  (stringTrace_eq a b rfl (add_root_add_root μ a b).symm).symm

/-- `tr(E_aa² | M_μ) = μ_a² dim M_μ`. -/
theorem opTrace_self [FiniteDimensional K M] (a : Fin n) (μ : Fin n → ℤ) :
    opTrace K M a a μ = ((μ a : K) * μ a) * finrank K (glWeightSpace K M μ) := by
  have h : (weightShift K M a a (add_root_add_root μ a a).symm).comp
      (weightShift K M a a (μ := μ) rfl) = ((μ a : K) * μ a) • LinearMap.id := by
    ext ⟨w, hw⟩
    have hw' := (mem_glWeightSpace.mp hw) a
    have hrw : ⁅(matUnit a a : Matrix (Fin n) (Fin n) K), w⁆ ∈ glWeightSpace K M μ := by
      rw [hw']
      exact Submodule.smul_mem _ _ hw
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply, Submodule.coe_smul,
      weightShift_apply]
    rw [(mem_glWeightSpace.mp hrw) a, hw', smul_smul]
  rw [opTrace, h, map_smul, LinearMap.trace_id, smul_eq_mul]

/-- **The root-string recursion**: `t_{ab}(μ − α) = t_{ab}(μ) + (μ_a − μ_b) m(μ)`, where
`α = ε_a − ε_b`. -/
theorem stringTrace_sub_root [FiniteDimensional K M] (a b : Fin n) (μ : Fin n → ℤ) :
    stringTrace K M a b (μ + root b a) =
      stringTrace K M a b μ + ((μ a : K) - μ b) * finrank K (glWeightSpace K M μ) := by
  rw [← opTrace_eq_stringTrace_add_root, opTrace_eq_stringTrace_add]

/-- Splitting a double sum over all pairs into the diagonal and the pairs `a < b`. -/
theorem sum_sum_eq_diag_add_posPairs {A : Type*} [AddCommMonoid A] (f : Fin n → Fin n → A) :
    ∑ a, ∑ b, f a b = ∑ a, f a a + ∑ p ∈ posPairs n, (f p.1 p.2 + f p.2 p.1) := by
  classical
  rw [sum_add_distrib]
  have h1 : ∑ a, ∑ b, f a b =
      ∑ p ∈ (univ : Finset (Fin n × Fin n)), f p.1 p.2 := by
    rw [← univ_product_univ, sum_product]
  have hsplit : (univ : Finset (Fin n × Fin n)) =
      (univ.image fun a => (a, a)) ∪ (posPairs n ∪ (posPairs n).image Prod.swap) := by
    ext ⟨a, b⟩
    simp only [mem_univ, mem_union, mem_image, mem_posPairs, Prod.mk.injEq, Prod.swap_prod_mk,
      true_iff, true_and, Prod.exists]
    rcases lt_trichotomy a b with h | rfl | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl ⟨a, rfl, rfl⟩
    · exact Or.inr (Or.inr ⟨b, a, h, rfl, rfl⟩)
  have hinj1 : Set.InjOn (fun a : Fin n => (a, a)) (univ : Finset (Fin n)) := by
    rintro a - b - h
    simpa using h
  have hinj2 : Set.InjOn Prod.swap (posPairs n : Set (Fin n × Fin n)) := by
    rintro p - q - h
    simpa using congrArg Prod.swap h
  have hd2 : Disjoint (posPairs n) ((posPairs n).image Prod.swap) := by
    rw [disjoint_left]
    rintro ⟨a, b⟩ h1 h2
    simp only [mem_posPairs] at h1
    simp only [mem_image, mem_posPairs, Prod.exists, Prod.swap_prod_mk, Prod.mk.injEq] at h2
    obtain ⟨c, d, hcd, rfl, rfl⟩ := h2
    exact lt_asymm h1 hcd
  have hd1 : Disjoint (univ.image fun a : Fin n => (a, a))
      (posPairs n ∪ (posPairs n).image Prod.swap) := by
    rw [disjoint_left]
    rintro ⟨a, b⟩ h1 h2
    simp only [mem_image, mem_univ, true_and, Prod.mk.injEq] at h1
    obtain ⟨c, rfl, rfl⟩ := h1
    simp only [mem_union, mem_posPairs, mem_image, Prod.exists, Prod.swap_prod_mk,
      Prod.mk.injEq] at h2
    rcases h2 with h | ⟨_, _, h, rfl, rfl⟩ <;> exact lt_irrefl _ h
  rw [h1, hsplit, sum_union hd1, sum_union hd2, sum_image hinj1, sum_image hinj2]
  rfl

/-- **Freudenthal's formula** for an integral `gl_n`-module on which the Casimir element acts by
`c`. -/
theorem freudenthal [FiniteDimensional K M] (c : K)
    (hΩ : ∀ m : M, ∑ i, ∑ j, ⁅(matUnit i j : Matrix (Fin n) (Fin n) K),
      ⁅(matUnit j i : Matrix (Fin n) (Fin n) K), m⁆⁆ = c • m)
    (μ : Fin n → ℤ) :
    c * finrank K (glWeightSpace K M μ) =
      (LaurentPoly.normSq μ : K) * finrank K (glWeightSpace K M μ) +
        ∑ p ∈ posPairs n, ((μ p.1 : K) - μ p.2) * finrank K (glWeightSpace K M μ) +
          2 * ∑ p ∈ posPairs n, stringTrace K M p.1 p.2 μ := by
  -- the Casimir element restricted to `M_μ`
  have hres : ∑ i, ∑ j, (weightShift K M i j (add_root_add_root μ j i).symm).comp
      (weightShift K M j i (μ := μ) rfl) = c • LinearMap.id := by
    ext ⟨w, hw⟩
    simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply, LinearMap.smul_apply,
      LinearMap.id_apply, Submodule.coe_sum, Submodule.coe_smul, weightShift_apply]
    exact hΩ w
  have htr := congrArg (LinearMap.trace K _) hres
  rw [map_sum, map_smul, LinearMap.trace_id, smul_eq_mul] at htr
  simp only [map_sum] at htr
  change ∑ i, ∑ j, opTrace K M i j μ = _ at htr
  rw [sum_sum_eq_diag_add_posPairs] at htr
  have hdiag : ∑ a, opTrace K M a a μ =
      (LaurentPoly.normSq μ : K) * finrank K (glWeightSpace K M μ) := by
    simp only [opTrace_self, LaurentPoly.normSq, Int.cast_sum, Int.cast_mul, sum_mul]
  have hpairs : ∀ p ∈ posPairs n, opTrace K M p.1 p.2 μ + opTrace K M p.2 p.1 μ =
      ((μ p.1 : K) - μ p.2) * finrank K (glWeightSpace K M μ) +
        2 * stringTrace K M p.1 p.2 μ := by
    intro p _
    rw [opTrace_eq_stringTrace_add, opTrace_swap]
    ring
  rw [hdiag, sum_congr rfl hpairs, sum_add_distrib, ← mul_sum] at htr
  rw [← htr]
  ring

end

end GLRep
