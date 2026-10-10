import RSCounterexample.GLRep.Borel.BorelLie

/-!
# Differentials of subrepresentations, equivalences and duals

Complements to `GLRep.IsRationalBorelRep.borelLie` (the differential `D_ab` of a rational
representation of `B` along `u_ab(t) = 1 + tE_ab`):

* the vector form of uniqueness (`GLRep.IsRationalBorelRep.borelLie_apply_eq_of_forall`): any
  polynomial expansion of `t ↦ ρ(u_ab(t)) w`, read through an injective linear map, has linear
  coefficient `D_ab w`;
* naturality: intertwining maps intertwine the `D_ab`
  (`GLRep.IsRationalBorelRep.borelLie_comp_of_intertwining`), in particular on subrepresentations
  (`GLRep.IsRationalBorelRep.subtype_borelLie`);
* duals: the dual of a rational representation of `B` is rational
  (`GLRep.IsRationalBorelRep.dual`), with `D_ab^∨ φ = −φ ∘ D_ab`
  (`GLRep.IsRationalBorelRep.borelLie_dual_apply`).
-/

namespace GLRep

open Module Polynomial TauCeti

noncomputable section

variable {K : Type*} [Field K] {n : ℕ} {a b : Fin n}

/-! ### Inversion on `B` -/

theorem upperTransvection_neg (hab : a < b) (t : K) :
    upperTransvection hab (-t) = (upperTransvection hab t)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← upperTransvection_add, neg_add_cancel, upperTransvection_zero]

/-- **Regular functions on `B` are stable under `b ↦ b⁻¹`.** -/
theorem comp_inv_mem_borelFunctions {f : borel K n → K} (hf : f ∈ borelFunctions K n) :
    (fun g => f g⁻¹) ∈ borelFunctions K n := by
  refine comp_mem_of_forall_coord_mem (fun g : borel K n => g⁻¹) (fun s => ?_) hf
  rcases s with ⟨i, j⟩ | i
  · exact inv_apply_mem_borelFunctions i j
  · have : (fun g : borel K n => borelCoord K n g⁻¹ (Sum.inr i)) =
        fun g : borel K n => ((borelDiag K n g i : Kˣ) : K) := by
      funext g
      rw [borelCoord_inr, map_inv, Pi.inv_apply, inv_inv]
    rw [this]
    exact diag_mem_borelFunctions i

namespace IsRationalBorelRep

variable {W : Type*} [AddCommGroup W] [Module K W] {ρ : Representation K (borel K n) W}
variable (hρ : IsRationalBorelRep ρ)

/-- **The dual of a rational representation of `B` is rational.** -/
theorem dual (hρ : IsRationalBorelRep ρ) : IsRationalBorelRep ρ.dual := by
  have := hρ.finiteDimensional
  refine ⟨inferInstance, fun ψ φ => ?_⟩
  obtain ⟨w, rfl⟩ := (Module.evalEquiv K W).surjective ψ
  have : (fun g => (Module.evalEquiv K W w) (ρ.dual g φ)) = fun g => φ (ρ g⁻¹ w) := by
    funext g
    rfl
  rw [this]
  exact comp_inv_mem_borelFunctions (hρ.coeff_mem φ w)

variable [Infinite K] [CharZero K]

/-- **Uniqueness, vector form**: if `j(ρ(u_ab(t)) w) = Σ_k t^k v_k` for all `t`, with `j` linear,
then `j(D_ab w) = v_1`. -/
theorem borelLie_apply_eq_of_forall (hab : a < b) {E : Type*} [AddCommGroup E] [Module K E]
    (j : W →ₗ[K] E) (w : W) {N : ℕ} (hN : 1 < N) (v : ℕ → E)
    (hv : ∀ t : K, j (ρ (upperTransvection hab t) w) = ∑ k ∈ Finset.range N, t ^ k • v k) :
    j (hρ.borelLie hab w) = v 1 := by
  obtain ⟨M, hM, hρM⟩ := hρ.exists_rho_upperTransvection_eq hab
  have key := coeff_eq_of_forall_sum_eq (K := K) (E := E)
    (fun k => j ((((k.factorial : ℕ) : K)⁻¹ • hρ.borelLie hab ^ k) w)) v
    (fun t => by
      rw [← hv t, hρM M le_rfl t, LinearMap.sum_apply, map_sum]
      exact Finset.sum_congr rfl fun k _ => by simp only [LinearMap.smul_apply, map_smul])
    hM hN
  simpa using key

variable {V : Type*} [AddCommGroup V] [Module K V] {σ : Representation K (borel K n) V}

/-- **Naturality**: intertwining maps intertwine the differentials. -/
theorem borelLie_comp_of_intertwining (hσ : IsRationalBorelRep σ) (hab : a < b)
    (f : W →ₗ[K] V) (hf : ∀ g w, f (ρ g w) = σ g (f w)) (w : W) :
    f (hρ.borelLie hab w) = hσ.borelLie hab (f w) :=
  ((hρ.forall_intertwining_iff hσ f).mp hf).2 a b hab w

/-- The differential of a subrepresentation is the restriction. -/
theorem subtype_borelLie (U : Subrepresentation ρ) (hab : a < b) (u : U.toSubmodule) :
    (IsRationalBorelRep.borelLie (HasCoeffsIn.subrepresentation hρ U) hab u : W) =
      hρ.borelLie hab u :=
  borelLie_comp_of_intertwining (HasCoeffsIn.subrepresentation hρ U) hρ hab
    U.toSubmodule.subtype (fun _ _ => rfl) u

/-- **The differential of the dual**: `D_ab^∨ φ = −φ ∘ D_ab`. -/
theorem borelLie_dual_apply (hab : a < b) (φ : Module.Dual K W) :
    IsRationalBorelRep.borelLie (dual hρ) hab φ = -(φ ∘ₗ hρ.borelLie hab) := by
  obtain ⟨M, hM, hρM⟩ := hρ.exists_rho_upperTransvection_eq hab
  have := (dual hρ).borelLie_apply_eq_of_forall hab LinearMap.id φ hM
    (fun k => ((-1 : K) ^ k * ((k.factorial : ℕ) : K)⁻¹) • (φ ∘ₗ hρ.borelLie hab ^ k))
    (fun t => by
      rw [LinearMap.id_apply, Representation.dual_apply, ← upperTransvection_neg,
        hρM M le_rfl (-t)]
      refine LinearMap.ext fun w => ?_
      rw [Module.Dual.transpose_apply, LinearMap.comp_apply, LinearMap.sum_apply, map_sum,
        LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [LinearMap.smul_apply, LinearMap.comp_apply, map_smul, smul_eq_mul]
      rw [neg_pow]
      ring)
  rw [LinearMap.id_apply] at this
  rw [this]
  ext w
  simp

end IsRationalBorelRep

end

end GLRep
