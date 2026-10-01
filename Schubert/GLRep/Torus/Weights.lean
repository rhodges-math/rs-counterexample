import Schubert.GLRep.Polynomial.Representation
import TauCeti.LinearAlgebra.Basis.DiagonalTorus.LaurentFunctions
import TauCeti.LinearAlgebra.Eigenspace.JointEigenvector.Basic
import Mathlib.Algebra.DirectSum.LinearMap
import Mathlib.LinearAlgebra.Trace

/-!
# Weights and characters of polynomial representations of a split torus

Let `T = (Kˣ)^κ` be a split torus over an infinite field `K`. The **weight space** of
`μ : κ → ℤ` in a representation `ρ` of `T` is the space of vectors `w` with
`ρ t w = t^μ w` for all `t`, where `t^μ = ∏ i, tᵢ^{μᵢ}` (`TauCeti.weightCharHom`).

A representation of `T` is *polynomial* when its matrix coefficients are polynomials in the
coordinates `tᵢ`. Such a representation is the direct sum of its weight spaces, and only weights
with nonnegative entries occur. The proof expands `ρ t` in monomials of `t`: by linear
independence of the characters of `T` the coefficients take their values in the weight spaces,
and at `t = 1` the expansion writes the identity as their sum.

The **character** of a polynomial representation is the polynomial
`∑_μ dim W_μ · x^μ ∈ ℤ[x_i : i ∈ κ]`. Its value at `t ∈ T` is the trace of `ρ t`, and it is the
only integer polynomial with this property in characteristic zero.

## Main definitions

* `GLRep.torusWeightSpace ρ μ`: the weight space of weight `μ`.
* `GLRep.torusCharacter ρ`: the character of a polynomial representation of the torus.

## Main results

* `GLRep.iSupIndep_torusWeightSpace`: weight spaces are independent.
* `GLRep.HasCoeffsIn.isInternal_torusWeightSpace`: a polynomial representation is the direct sum
  of its weight spaces.
* `GLRep.HasCoeffsIn.torusWeightSpace_eq_bot`: its weights have nonnegative entries.
* `GLRep.trace_eq_eval_torusCharacter`, `GLRep.eq_torusCharacter_of_forall_trace_eq`: the trace
  formula and the uniqueness of the character.
-/

namespace GLRep

open Module TauCeti

noncomputable section

variable {K : Type*} [Field K] {κ : Type*} [Fintype κ]
variable {W : Type*} [AddCommGroup W] [Module K W]

/-! ### Weight spaces -/

section WeightSpace

variable (ρ : Representation K (κ → Kˣ) W)

/-- The **weight space** of weight `μ`: the vectors that every point `t` of the torus scales by
the character value `t^μ = ∏ i, tᵢ^{μᵢ}`. -/
def torusWeightSpace (μ : κ → ℤ) : Submodule K W :=
  ⨅ t, Module.End.eigenspace (ρ t) (weightCharHom K μ t)

variable {ρ}

theorem mem_torusWeightSpace {μ : κ → ℤ} {w : W} :
    w ∈ torusWeightSpace ρ μ ↔ ∀ t, ρ t w = weightCharHom K μ t • w := by
  simp [torusWeightSpace]

theorem apply_of_mem_torusWeightSpace {μ : κ → ℤ} {w : W} (hw : w ∈ torusWeightSpace ρ μ)
    (t : κ → Kˣ) : ρ t w = weightCharHom K μ t • w :=
  mem_torusWeightSpace.mp hw t

variable (ρ) in
/-- **The weight spaces are independent**, over an infinite field. -/
theorem iSupIndep_torusWeightSpace [Infinite K] : iSupIndep (torusWeightSpace ρ) :=
  (iSupIndep_iInf_eigenspace (fun t => ρ t)).comp fun _ _ h =>
    weightCharHom_injective K (DFunLike.coe_injective h)

/-- Each operator `ρ t` preserves each weight space. -/
theorem mapsTo_torusWeightSpace (t : κ → Kˣ) (μ : κ → ℤ) :
    Set.MapsTo (ρ t) (torusWeightSpace ρ μ) (torusWeightSpace ρ μ) := fun w hw => by
  rw [SetLike.mem_coe, apply_of_mem_torusWeightSpace hw t]
  exact Submodule.smul_mem _ _ hw

/-- Intertwining maps send weight spaces to weight spaces. -/
theorem map_mem_torusWeightSpace {V : Type*} [AddCommGroup V] [Module K V]
    {σ : Representation K (κ → Kˣ) V} (φ : ρ.IntertwiningMap σ) {μ : κ → ℤ} {w : W}
    (hw : w ∈ torusWeightSpace ρ μ) : φ w ∈ torusWeightSpace σ μ :=
  mem_torusWeightSpace.mpr fun t => by
    rw [← φ.isIntertwining, apply_of_mem_torusWeightSpace hw t, map_smul]

end WeightSpace

/-! ### Polynomial representations of the torus -/

section Polynomial

variable {ρ : Representation K (κ → Kˣ) W}

/-- The monomial `t^α` as the character value of the nonnegative weight `α`. -/
theorem weightCharHom_natCast (α : κ →₀ ℕ) (t : κ → Kˣ) :
    weightCharHom K (fun i => (α i : ℤ)) t = ∏ i, (t i : K) ^ α i := by
  rw [weightCharHom_apply, weightChar_apply, torusCharacter_def, Units.coe_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [zpow_natCast, Units.val_pow_eq_pow_val]

/-- **The expansion of a polynomial representation of the torus into monomials.** -/
theorem HasCoeffsIn.exists_eq_sum_smul (h : HasCoeffsIn (coordFunctions K (torusCoord K κ)) ρ) :
    ∃ (S : Finset (κ →₀ ℕ)) (A : (κ →₀ ℕ) → Module.End K W),
      ∀ t, ρ t = ∑ α ∈ S, weightCharHom K (fun i => (α i : ℤ)) t • A α := by
  classical
  have := h.finiteDimensional
  let b := Module.finBasis K W
  choose P hP using fun i j => mem_coordFunctions.mp (h.toMatrix_mem b i j)
  refine ⟨Finset.univ.biUnion fun q : _ × _ => (P q.1 q.2).support,
    fun α => (LinearMap.toMatrix b b).symm (Matrix.of fun i j => (P i j).coeff α), fun t => ?_⟩
  refine (LinearMap.toMatrix b b).injective ?_
  rw [map_sum]
  ext i j
  have hsub : (P i j).support ⊆ Finset.univ.biUnion fun q : _ × _ => (P q.1 q.2).support :=
    fun α hα => Finset.mem_biUnion.mpr ⟨(i, j), Finset.mem_univ _, hα⟩
  have hterm : ∀ α : κ →₀ ℕ, LinearMap.toMatrix b b (weightCharHom K (fun i => (α i : ℤ)) t •
      (LinearMap.toMatrix b b).symm (Matrix.of fun i j => (P i j).coeff α)) i j =
      (P i j).coeff α * ∏ k, (t k : K) ^ α k := by
    intro α
    rw [map_smul, LinearEquiv.apply_symm_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul,
      weightCharHom_natCast, mul_comm]
  rw [hP i j t, MvPolynomial.eval_eq', Matrix.sum_apply]
  simp only [hterm]
  exact Finset.sum_subset hsub (f := fun α => (P i j).coeff α * ∏ k, (t k : K) ^ α k)
    fun α _ hα => by rw [MvPolynomial.notMem_support_iff.mp hα, zero_mul]

/-- In an expansion of the torus action into characters, the coefficient operators take their
values in the weight spaces of their exponents. -/
theorem apply_mem_torusWeightSpace_of_eq_sum_smul [Infinite K] {S : Finset (κ → ℤ)}
    {A : (κ → ℤ) → Module.End K W} (hA : ∀ t, ρ t = ∑ μ ∈ S, weightCharHom K μ t • A μ)
    {μ : κ → ℤ} (hμ : μ ∈ S) (w : W) : A μ w ∈ torusWeightSpace ρ μ := by
  refine mem_torusWeightSpace.mpr fun s => ?_
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff K]
  intro ψ
  rw [map_sub, map_smul, smul_eq_mul, sub_eq_zero]
  have hψ : ∀ (ψ : W →ₗ[K] K) (t : κ → Kˣ) (v : W),
      ψ (ρ t v) = ∑ ν ∈ S, weightCharHom K ν t * ψ (A ν v) := by
    intro ψ t v
    rw [hA t, LinearMap.sum_apply, map_sum]
    exact Finset.sum_congr rfl fun ν _ => by rw [LinearMap.smul_apply, map_smul, smul_eq_mul]
  have hli := linearIndependent_weightCharHom (K := K) (κ := κ)
  rw [linearIndependent_iff'] at hli
  have hsum : ∑ ν ∈ S, (ψ (ρ s (A ν w)) - weightCharHom K ν s * ψ (A ν w)) •
      ⇑(weightCharHom K ν) = 0 := by
    funext t
    have e1 := hψ (ψ ∘ₗ ρ s) t w
    have e2 := hψ ψ (s * t) w
    rw [map_mul, Module.End.mul_apply] at e2
    simp only [LinearMap.coe_comp, Function.comp_apply] at e1
    rw [Finset.sum_apply, Pi.zero_apply]
    simp only [Pi.smul_apply, smul_eq_mul, sub_mul, Finset.sum_sub_distrib]
    rw [sub_eq_zero]
    calc ∑ ν ∈ S, ψ (ρ s (A ν w)) * weightCharHom K ν t
        = ∑ ν ∈ S, weightCharHom K ν t * ψ (ρ s (A ν w)) :=
          Finset.sum_congr rfl fun ν _ => mul_comm _ _
      _ = ψ (ρ s (ρ t w)) := e1.symm
      _ = ∑ ν ∈ S, weightCharHom K ν (s * t) * ψ (A ν w) := e2
      _ = ∑ ν ∈ S, weightCharHom K ν s * ψ (A ν w) * weightCharHom K ν t :=
          Finset.sum_congr rfl fun ν _ => by rw [map_mul]; ring
  exact sub_eq_zero.mp (hli S _ hsum μ hμ)

variable [Infinite K]

/-- **The weight spaces of a polynomial representation of the torus span it.** -/
theorem HasCoeffsIn.iSup_torusWeightSpace_eq_top
    (h : HasCoeffsIn (coordFunctions K (torusCoord K κ)) ρ) :
    ⨆ μ, torusWeightSpace ρ μ = ⊤ := by
  classical
  obtain ⟨S, A, hA⟩ := h.exists_eq_sum_smul
  let e : (κ →₀ ℕ) → κ → ℤ := fun α i => (α i : ℤ)
  have he : Function.Injective e := fun α β hαβ => Finsupp.ext fun i => by
    simpa [e] using congrFun hαβ i
  let A' : (κ → ℤ) → Module.End K W := fun μ =>
    if hμ : ∃ α ∈ S, e α = μ then A hμ.choose else 0
  have hA'e : ∀ α ∈ S, A' (e α) = A α := by
    intro α hα
    have hex : ∃ β ∈ S, e β = e α := ⟨α, hα, rfl⟩
    simp only [A', hex, ↓reduceDIte]
    rw [he hex.choose_spec.2]
  have hA' : ∀ t, ρ t = ∑ μ ∈ S.image e, weightCharHom K μ t • A' μ := by
    intro t
    rw [hA t, Finset.sum_image fun α _ β _ h => he h]
    exact Finset.sum_congr rfl fun α hα => by rw [hA'e α hα]
  have hone : (1 : Module.End K W) = ∑ μ ∈ S.image e, A' μ := by
    rw [← map_one ρ, hA' 1]
    exact Finset.sum_congr rfl fun μ _ => by rw [map_one, one_smul]
  refine top_le_iff.mp fun w _ => ?_
  have hw : w = ∑ μ ∈ S.image e, A' μ w := by
    simpa only [Module.End.one_apply, LinearMap.sum_apply] using
      congrArg (fun f : Module.End K W => f w) hone
  rw [hw]
  exact Submodule.sum_mem _ fun μ hμ => Submodule.mem_iSup_of_mem μ
    (apply_mem_torusWeightSpace_of_eq_sum_smul hA' hμ w)

/-- **A polynomial representation of the torus is the direct sum of its weight spaces.** -/
theorem HasCoeffsIn.isInternal_torusWeightSpace
    (h : HasCoeffsIn (coordFunctions K (torusCoord K κ)) ρ) :
    DirectSum.IsInternal (torusWeightSpace ρ) :=
  (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr
    ⟨iSupIndep_torusWeightSpace ρ, h.iSup_torusWeightSpace_eq_top⟩

/-- **The weights of a polynomial representation of the torus are nonnegative.** -/
theorem HasCoeffsIn.torusWeightSpace_eq_bot
    (h : HasCoeffsIn (coordFunctions K (torusCoord K κ)) ρ) {μ : κ → ℤ} (hμ : ∃ i, μ i < 0) :
    torusWeightSpace ρ μ = ⊥ := by
  classical
  obtain ⟨S, A, hA⟩ := h.exists_eq_sum_smul
  let e : (κ →₀ ℕ) → κ → ℤ := fun α i => (α i : ℤ)
  have he : Function.Injective e := fun α β hαβ => Finsupp.ext fun i => by
    simpa [e] using congrFun hαβ i
  -- the nonnegative weight spaces already span
  have htop : ⨆ ν ∈ S.image e, torusWeightSpace ρ ν = ⊤ := by
    let A' : (κ → ℤ) → Module.End K W := fun ν =>
      if hν : ∃ α ∈ S, e α = ν then A hν.choose else 0
    have hA'e : ∀ α ∈ S, A' (e α) = A α := by
      intro α hα
      have hex : ∃ β ∈ S, e β = e α := ⟨α, hα, rfl⟩
      simp only [A', hex, ↓reduceDIte]
      rw [he hex.choose_spec.2]
    have hA' : ∀ t, ρ t = ∑ ν ∈ S.image e, weightCharHom K ν t • A' ν := by
      intro t
      rw [hA t, Finset.sum_image fun α _ β _ h => he h]
      exact Finset.sum_congr rfl fun α hα => by rw [hA'e α hα]
    refine top_le_iff.mp fun w _ => ?_
    have hw : w = ∑ ν ∈ S.image e, A' ν w := by
      have hone : (1 : Module.End K W) = ∑ ν ∈ S.image e, A' ν := by
        rw [← map_one ρ, hA' 1]
        exact Finset.sum_congr rfl fun ν _ => by rw [map_one, one_smul]
      simpa only [Module.End.one_apply, LinearMap.sum_apply] using
        congrArg (fun f : Module.End K W => f w) hone
    rw [hw]
    exact Submodule.sum_mem _ fun ν hν =>
      (Submodule.mem_iSup_of_mem ν (Submodule.mem_iSup_of_mem hν
        (apply_mem_torusWeightSpace_of_eq_sum_smul hA' hν w)))
  have hnot : μ ∉ S.image e := by
    rintro hm
    obtain ⟨α, -, rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨i, hi⟩ := hμ
    exact absurd hi (not_lt.mpr (Int.natCast_nonneg _))
  have hdisj : Disjoint (torusWeightSpace ρ μ) (⨆ ν ∈ S.image e, torusWeightSpace ρ ν) :=
    (iSupIndep_torusWeightSpace ρ).disjoint_biSup hnot
  rw [htop, disjoint_top] at hdisj
  exact hdisj

/-- A finite-dimensional representation has finitely many nonzero weight spaces. -/
theorem finite_torusWeightSpace_ne_bot [FiniteDimensional K W] (ρ : Representation K (κ → Kˣ) W) :
    {μ | torusWeightSpace ρ μ ≠ ⊥}.Finite :=
  WellFoundedGT.finite_ne_bot_of_iSupIndep (iSupIndep_torusWeightSpace ρ)

end Polynomial

/-! ### The character -/

section Character

variable [Infinite K]

/-- The multiplicity function `α ↦ dim W_α` on nonnegative weights. -/
def weightMultiplicity (ρ : Representation K (κ → Kˣ) W) (α : κ →₀ ℕ) : ℤ :=
  finrank K (torusWeightSpace ρ fun i => (α i : ℤ))

theorem finite_support_weightMultiplicity [FiniteDimensional K W]
    (ρ : Representation K (κ → Kˣ) W) :
    (Function.support (weightMultiplicity ρ)).Finite := by
  refine ((finite_torusWeightSpace_ne_bot ρ).preimage
    (f := fun α : κ →₀ ℕ => fun i => (α i : ℤ)) fun α _ β _ h => Finsupp.ext fun i => by
      simpa using congrFun h i).subset fun α hα => ?_
  intro hbot
  apply hα
  rw [weightMultiplicity, hbot, finrank_bot, Nat.cast_zero]

open Classical in
/-- The **character** `∑_α dim W_α · x^α` of a finite-dimensional representation of the torus,
recording the nonnegative weights (it is `0` for an infinite-dimensional representation). For a
polynomial representation every weight is nonnegative, and the character is the polynomial whose
value at `t` is the trace of `ρ t` (`GLRep.trace_eq_eval_torusCharacter`). -/
def torusCharacter (ρ : Representation K (κ → Kˣ) W) : MvPolynomial κ ℤ :=
  if h : (Function.support (weightMultiplicity ρ)).Finite then
    AddMonoidAlgebra.ofCoeff (Finsupp.ofSupportFinite (weightMultiplicity ρ) h)
  else 0

theorem torusCharacter_eq [FiniteDimensional K W] (ρ : Representation K (κ → Kˣ) W) :
    torusCharacter ρ = AddMonoidAlgebra.ofCoeff
      (Finsupp.ofSupportFinite (weightMultiplicity ρ) (finite_support_weightMultiplicity ρ)) := by
  simp only [torusCharacter, finite_support_weightMultiplicity ρ, ↓reduceDIte]

theorem coeff_torusCharacter [FiniteDimensional K W] (ρ : Representation K (κ → Kˣ) W)
    (α : κ →₀ ℕ) :
    (torusCharacter ρ).coeff α = finrank K (torusWeightSpace ρ fun i => (α i : ℤ)) := by
  rw [torusCharacter_eq]
  rfl

variable {ρ : Representation K (κ → Kˣ) W}

/-- **The trace formula.** For a polynomial representation of the torus, the trace of `ρ t` is
the value of the character at `t`. -/
theorem trace_eq_eval_torusCharacter (h : HasCoeffsIn (coordFunctions K (torusCoord K κ)) ρ)
    (t : κ → Kˣ) :
    LinearMap.trace K W (ρ t) =
      MvPolynomial.eval₂ (Int.castRingHom K) (fun i => (t i : K)) (torusCharacter ρ) := by
  have := h.finiteDimensional
  classical
  have hint := h.isInternal_torusWeightSpace
  have hfin := finite_torusWeightSpace_ne_bot ρ
  rw [LinearMap.trace_eq_sum_trace_restrict' hint hfin (mapsTo_torusWeightSpace t)]
  have hres : ∀ μ, LinearMap.trace K _ ((ρ t).restrict (mapsTo_torusWeightSpace t μ)) =
      finrank K (torusWeightSpace ρ μ) * weightCharHom K μ t := by
    intro μ
    have : (ρ t).restrict (mapsTo_torusWeightSpace t μ) =
        weightCharHom K μ t • LinearMap.id := by
      ext ⟨w, hw⟩
      exact apply_of_mem_torusWeightSpace hw t
    rw [this, map_smul, LinearMap.trace_id, smul_eq_mul, mul_comm]
  simp only [hres]
  -- every nonzero weight space has a nonnegative weight, so the sum runs over the support of
  -- the multiplicity function
  let e : (κ →₀ ℕ) → κ → ℤ := fun α i => (α i : ℤ)
  have he : Function.Injective e := fun α β hαβ => Finsupp.ext fun i => by
    simpa [e] using congrFun hαβ i
  have hset : hfin.toFinset = (finite_support_weightMultiplicity ρ).toFinset.image e := by
    ext μ
    rw [Set.Finite.mem_toFinset, Finset.mem_image]
    constructor
    · intro hμ
      by_cases hneg : ∃ i, μ i < 0
      · exact absurd (h.torusWeightSpace_eq_bot hneg) hμ
      · push Not at hneg
        have hα : e (Finsupp.equivFunOnFinite.symm fun i => (μ i).toNat) = μ := funext fun i => by
          simp [e, Int.toNat_of_nonneg (hneg i)]
        refine ⟨_, ?_, hα⟩
        rw [Set.Finite.mem_toFinset, Function.mem_support, weightMultiplicity, ne_eq,
          Nat.cast_eq_zero, Submodule.finrank_eq_zero]
        exact fun hbot => hμ (by rw [← hα]; exact hbot)
    · rintro ⟨α, hα, rfl⟩
      rw [Set.Finite.mem_toFinset, Function.mem_support, weightMultiplicity, ne_eq,
        Nat.cast_eq_zero, Submodule.finrank_eq_zero] at hα
      exact hα
  rw [hset, Finset.sum_image fun α _ β _ hαβ => he hαβ, MvPolynomial.eval₂_eq', torusCharacter_eq,
    MvPolynomial.support, AddMonoidAlgebra.coeff_ofCoeff, Finsupp.ofSupportFinite_support]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [weightCharHom_natCast, Finsupp.ofSupportFinite_coe]
  simp [weightMultiplicity, e]

end Character

end

end GLRep
