import RSCounterexample.GLRep.Levi.Multiplicity
import RSCounterexample.GLRep.Rational.Twist

/-!
# Laurent characters of representations of a split torus

A representation `π` of the split torus `T = (Kˣ)^κ` is **rational** when some twist of it by a
character `t ↦ t^ν` is polynomial (`GLRep.IsRationalTorusRep`). Its weights may then be negative,
and its character is the Laurent polynomial `∑_μ dim W_μ · x^μ` (`GLRep.laurentCharacter`), an
element of `GLRep.TorusLaurent κ = ℤ[x_i^{±1} : i ∈ κ]`.

* Twisting by `t^ν` shifts the weights by `ν` and multiplies the character by `x^ν`
  (`GLRep.laurentCharacter_scaledRep`).
* The value of the character at `t ∈ T` is the trace of `π(t)`
  (`GLRep.IsRationalTorusRep.trace_eq_laurentEval`), and the character is the only Laurent
  polynomial with this property (`GLRep.IsRationalTorusRep.eq_laurentCharacter_of_forall`).
* For a polynomial representation the Laurent character is the character
  (`GLRep.laurentCharacter_eq_polyToLaurent`).

## Main definitions

* `GLRep.TorusLaurent κ`, `GLRep.laurentEval K t`, `GLRep.polyToLaurent κ`.
* `GLRep.laurentCharacter π`, `GLRep.IsRationalTorusRep π`.
-/

namespace GLRep

open Module TauCeti

noncomputable section

/-- Laurent polynomials with integer coefficients in the variables `κ`. -/
abbrev TorusLaurent (κ : Type*) := AddMonoidAlgebra ℤ (κ → ℤ)

variable {K : Type*} [Field K] {κ : Type*} [Fintype κ]
variable {W : Type*} [AddCommGroup W] [Module K W]

/-! ### Evaluation and polynomials -/

variable (K) in
/-- Evaluation of a Laurent polynomial at a point `t` of the torus: `x^μ ↦ t^μ`. -/
def laurentEval (t : κ → Kˣ) : TorusLaurent κ →+* K :=
  (AddMonoidAlgebra.lift ℤ K (κ → ℤ)
    { toFun := fun μ => weightCharHom K (Multiplicative.toAdd μ) t
      map_one' := by simp
      map_mul' := fun μ ν => by
        simp only [toAdd_mul, weightCharHom_apply, weightChar_add, MonoidHom.mul_apply,
          Units.val_mul] }).toRingHom

theorem laurentEval_single (t : κ → Kˣ) (μ : κ → ℤ) (c : ℤ) :
    laurentEval K t (AddMonoidAlgebra.single μ c) = c * weightCharHom K μ t := by
  simp [laurentEval, zsmul_eq_mul]

theorem laurentEval_eq_sum (t : κ → Kˣ) (f : TorusLaurent κ) :
    laurentEval K t f = f.coeff.sum fun μ c => (c : K) * weightCharHom K μ t := by
  simp [laurentEval, AddMonoidAlgebra.lift_apply, zsmul_eq_mul]

/-- The exponents of monomials as integer weights. -/
def expWeight (κ : Type*) : (κ →₀ ℕ) →+ (κ → ℤ) where
  toFun a i := a i
  map_zero' := by
    funext i
    simp
  map_add' a b := by
    funext i
    simp

omit [Fintype κ] in
theorem expWeight_injective : Function.Injective (expWeight κ) := fun a b h =>
  Finsupp.ext fun i => by simpa [expWeight] using congrFun h i

variable (κ) in
/-- Polynomials as Laurent polynomials. -/
def polyToLaurent : MvPolynomial κ ℤ →+* TorusLaurent κ :=
  AddMonoidAlgebra.mapDomainRingHom ℤ (expWeight κ)

omit [Fintype κ] in
theorem polyToLaurent_injective : Function.Injective (polyToLaurent κ) :=
  AddMonoidAlgebra.mapDomain_injective expWeight_injective

theorem laurentEval_polyToLaurent (t : κ → Kˣ) (P : MvPolynomial κ ℤ) :
    laurentEval K t (polyToLaurent κ P) =
      MvPolynomial.eval₂ (Int.castRingHom K) (fun i => (t i : K)) P := by
  classical
  have h : (laurentEval K t).comp (polyToLaurent κ) =
      MvPolynomial.eval₂Hom (Int.castRingHom K) fun i => (t i : K) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) fun i => ?_
    · simp only [RingHom.coe_comp, Function.comp_apply, MvPolynomial.coe_eval₂Hom,
        MvPolynomial.eval₂_C]
      have hC : (MvPolynomial.C a : MvPolynomial κ ℤ) = (a : MvPolynomial κ ℤ) := by simp
      rw [hC, map_intCast, map_intCast, eq_intCast]
    · have hX : polyToLaurent κ (MvPolynomial.X i) =
          AddMonoidAlgebra.single (expWeight κ (Finsupp.single i 1)) 1 :=
        AddMonoidAlgebra.mapDomain_single
      have hw : expWeight κ (Finsupp.single i 1) = Pi.single i 1 := by
        funext j
        simp [expWeight, Finsupp.single_apply, Pi.single_apply, eq_comm]
      simp only [RingHom.coe_comp, Function.comp_apply, MvPolynomial.coe_eval₂Hom,
        MvPolynomial.eval₂_X, hX, laurentEval_single, hw, weightCharHom_apply, weightChar_single,
        Int.cast_one, one_mul]
  exact congrArg (fun f : MvPolynomial κ ℤ →+* K => f P) h

/-! ### The Laurent character -/

variable (K) in
/-- The function `μ ↦ dim W_μ`. -/
def weightDim (π : Representation K (κ → Kˣ) W) (μ : κ → ℤ) : ℤ :=
  finrank K (torusWeightSpace π μ)

theorem finite_support_weightDim [Infinite K] [FiniteDimensional K W]
    (π : Representation K (κ → Kˣ) W) : (Function.support (weightDim K π)).Finite := by
  refine (finite_torusWeightSpace_ne_bot π).subset fun μ hμ hbot => hμ ?_
  rw [weightDim, hbot, finrank_bot, Nat.cast_zero]

open Classical in
/-- The **Laurent character** `∑_μ dim W_μ · x^μ` of a finite-dimensional representation of the
torus (`0` for an infinite-dimensional one). -/
def laurentCharacter (π : Representation K (κ → Kˣ) W) : TorusLaurent κ :=
  if h : (Function.support (weightDim K π)).Finite then
    AddMonoidAlgebra.ofCoeff (Finsupp.ofSupportFinite (weightDim K π) h)
  else 0

theorem coeff_laurentCharacter [Infinite K] [FiniteDimensional K W]
    (π : Representation K (κ → Kˣ) W) (μ : κ → ℤ) :
    (laurentCharacter π).coeff μ = finrank K (torusWeightSpace π μ) := by
  simp only [laurentCharacter, finite_support_weightDim π, ↓reduceDIte]
  rfl

omit [Fintype κ] in
/-- Two Laurent polynomials with the same coefficients agree. -/
theorem TorusLaurent.ext {f g : TorusLaurent κ} (h : ∀ μ, f.coeff μ = g.coeff μ) : f = g :=
  AddMonoidAlgebra.coeff_injective (Finsupp.ext h)

/-! ### Twisting by a character -/

/-- **Twisting by `t^ν` shifts the weights by `ν`.** -/
theorem torusWeightSpace_scaledRep (π : Representation K (κ → Kˣ) W) (ν μ : κ → ℤ) :
    torusWeightSpace (scaledRep π (weightChar K ν)) (μ + ν) = torusWeightSpace π μ := by
  ext w
  simp only [mem_torusWeightSpace, scaledRep_apply]
  refine forall_congr' fun t => ?_
  rw [weightCharHom_apply, weightChar_add, MonoidHom.mul_apply, Units.val_mul, mul_comm,
    mul_smul, ← weightCharHom_apply, ← weightCharHom_apply]
  constructor
  · intro h
    have := congrArg (fun x => ((weightChar K ν t : Kˣ) : K)⁻¹ • x) h
    simpa [smul_smul, inv_mul_cancel₀ (Units.ne_zero (weightChar K ν t))] using this
  · intro h
    rw [h, weightCharHom_apply]

/-- **Twisting by `t^ν` multiplies the Laurent character by `x^ν`.** -/
theorem laurentCharacter_scaledRep [Infinite K] [FiniteDimensional K W]
    (π : Representation K (κ → Kˣ) W) (ν : κ → ℤ) :
    laurentCharacter (scaledRep π (weightChar K ν)) =
      AddMonoidAlgebra.single ν 1 * laurentCharacter π := by
  refine TorusLaurent.ext fun μ => ?_
  rw [coeff_laurentCharacter, AddMonoidAlgebra.coeff_single_mul_apply, one_mul,
    coeff_laurentCharacter, ← torusWeightSpace_scaledRep π ν (-ν + μ), neg_add_cancel_comm]

/-! ### Rational representations of the torus -/

/-- A representation of the torus is **rational** when some twist of it by a character is
polynomial. -/
def IsRationalTorusRep (π : Representation K (κ → Kˣ) W) : Prop :=
  ∃ ν : κ → ℤ, HasCoeffsIn (coordFunctions K (torusCoord K κ)) (scaledRep π (weightChar K ν))

theorem HasCoeffsIn.isRationalTorusRep {π : Representation K (κ → Kˣ) W}
    (h : HasCoeffsIn (coordFunctions K (torusCoord K κ)) π) : IsRationalTorusRep π := by
  refine ⟨0, ?_⟩
  have : GLRep.scaledRep π (weightChar K (0 : κ → ℤ)) = π := by
    ext t w
    simp
  rwa [this]

namespace IsRationalTorusRep

variable {π : Representation K (κ → Kˣ) W}

theorem finiteDimensional (h : IsRationalTorusRep π) : FiniteDimensional K W :=
  h.choose_spec.finiteDimensional

variable [Infinite K]

/-- A rational representation of the torus is the direct sum of its weight spaces. -/
theorem iSup_torusWeightSpace_eq_top (h : IsRationalTorusRep π) :
    ⨆ μ, torusWeightSpace π μ = ⊤ := by
  obtain ⟨ν, hν⟩ := h
  rw [← hν.iSup_torusWeightSpace_eq_top]
  refine le_antisymm (iSup_le fun μ => ?_) (iSup_le fun μ => ?_)
  · rw [← torusWeightSpace_scaledRep π ν μ]
    exact le_iSup (torusWeightSpace (scaledRep π (weightChar K ν))) (μ + ν)
  · rw [show μ = (μ - ν) + ν by abel, torusWeightSpace_scaledRep]
    exact le_iSup (torusWeightSpace π) (μ - ν)

theorem isInternal (h : IsRationalTorusRep π) : DirectSum.IsInternal (torusWeightSpace π) :=
  (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr
    ⟨iSupIndep_torusWeightSpace π, h.iSup_torusWeightSpace_eq_top⟩

/-- **The trace formula** for a rational representation of the torus. -/
theorem trace_eq_laurentEval (h : IsRationalTorusRep π) (t : κ → Kˣ) :
    LinearMap.trace K W (π t) = laurentEval K t (laurentCharacter π) := by
  have := h.finiteDimensional
  have hfin := finite_torusWeightSpace_ne_bot π
  have hmaps : ∀ μ, Set.MapsTo (π t) (torusWeightSpace π μ) (torusWeightSpace π μ) :=
    fun μ => mapsTo_torusWeightSpace t μ
  rw [LinearMap.trace_eq_sum_trace_restrict' h.isInternal hfin hmaps, laurentEval_eq_sum]
  have hres : ∀ μ, (π t).restrict (hmaps μ) = weightCharHom K μ t • LinearMap.id := fun μ =>
    LinearMap.ext fun w => Subtype.ext (apply_of_mem_torusWeightSpace w.2 t)
  simp only [hres, map_smul, LinearMap.trace_id, smul_eq_mul]
  rw [Finsupp.sum]
  simp only [laurentCharacter, finite_support_weightDim π, ↓reduceDIte]
  refine Finset.sum_congr ?_ fun μ _ => ?_
  · ext μ
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq,
      Finsupp.mem_support_iff, Finsupp.ofSupportFinite_coe, weightDim, ne_eq, Nat.cast_eq_zero,
      Submodule.finrank_eq_zero]
  · simp only [Finsupp.ofSupportFinite_coe, weightDim, Int.cast_natCast]
    ring

variable [CharZero K]

/-- **The Laurent character is determined by the traces.** -/
theorem eq_laurentCharacter_of_forall (h : IsRationalTorusRep π) (f : TorusLaurent κ)
    (hf : ∀ t, laurentEval K t f = LinearMap.trace K W (π t)) : f = laurentCharacter π := by
  classical
  set g := laurentCharacter π
  have hzero : ∀ t, laurentEval K t (f - g) = 0 := fun t => by
    rw [map_sub, hf t, h.trace_eq_laurentEval t, sub_self]
  refine sub_eq_zero.mp (TorusLaurent.ext fun μ => ?_)
  rw [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  set F := f - g
  have hlin := linearIndependent_iff'.mp (linearIndependent_weightCharHom K (κ := κ))
    F.coeff.support (fun ν => (F.coeff ν : K)) (by
      funext t
      have := hzero t
      rw [laurentEval_eq_sum, Finsupp.sum] at this
      simpa [Finset.sum_apply, mul_comm] using this)
  by_cases hμ : μ ∈ F.coeff.support
  · exact_mod_cast hlin μ hμ
  · exact Finsupp.notMem_support_iff.mp hμ

end IsRationalTorusRep

/-- For a polynomial representation of the torus, the Laurent character is the character. -/
theorem laurentCharacter_eq_polyToLaurent [Infinite K] [CharZero K]
    {π : Representation K (κ → Kˣ) W} (h : HasCoeffsIn (coordFunctions K (torusCoord K κ)) π) :
    laurentCharacter π = polyToLaurent κ (torusCharacter π) := by
  refine (h.isRationalTorusRep.eq_laurentCharacter_of_forall _ fun t => ?_).symm
  rw [laurentEval_polyToLaurent, trace_eq_eval_torusCharacter h t]

end

end GLRep
