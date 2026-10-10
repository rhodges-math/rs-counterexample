import RSCounterexample.GLRep.Levi.Split
import RSCounterexample.GLRep.Multiplicity.GL
import Mathlib.Algebra.DirectSum.LinearMap

/-!
# Multiplicity spaces for the first block of a Levi group

Let `ρ` be a representation of the Levi group `L = GL_{d_0}(K) × L'` on `W`, and `σ` a
representation of the first block `GL_{d_0}(K)`. The **multiplicity space** `Hom_{GL_{d_0}}(σ, ρ)`
is a representation of `L'`, acting by composition (`GLRep.multRep`), polynomial when `ρ` is
(`GLRep.IsPolynomialLeviRep.multRep`).

Its weights are read off the weight spaces `W_η` of the torus of `L'` in `W`, which are
subrepresentations of the first block (`GLRep.tailWeightSubrep`): the weight space of `η` in the
multiplicity space is `Hom_{GL_{d_0}}(σ, W_η)` (`GLRep.finrank_tailWeightSubrep`).

## Main definitions

* `GLRep.piConst`: the representation on `ι → W` acting in every coordinate.
* `GLRep.headRep`, `GLRep.tailRep`: the restrictions of `ρ` to `GL_{d_0}(K)` and to `L'`.
* `GLRep.multRep`: the multiplicity space as a representation of `L'`.
* `GLRep.tailWeightSubrep`: the weight spaces of the torus of `L'`.

## Main results

* `GLRep.HasCoeffsIn.piConst`, `GLRep.IsPolynomialLeviRep.multRep`.
* `GLRep.finrank_tailWeightSubrep`.
* `GLRep.trace_mul_eq_sum_weight`: traces on a weight decomposition.
-/

namespace GLRep

open Module Representation TauCeti

noncomputable section

variable {K : Type*} [Field K]
variable {W : Type*} [AddCommGroup W] [Module K W]

/-! ### Products of copies of a representation -/

section PiConst

variable {G : Type*} [Monoid G]

variable (ι : Type*) in
/-- The representation on `ι → W` acting in every coordinate. -/
def piConst (ρ : Representation K G W) : Representation K G (ι → W) where
  toFun g := LinearMap.pi fun i => ρ g ∘ₗ LinearMap.proj i
  map_one' := by
    ext x i
    simp
  map_mul' g h := by
    ext x i
    simp

@[simp] theorem piConst_apply {ι : Type*} (ρ : Representation K G W) (g : G) (x : ι → W)
    (i : ι) : piConst ι ρ g x i = ρ g (x i) := rfl

/-- A finite product of copies of a representation with coefficients in `A` has coefficients in
`A`. -/
theorem HasCoeffsIn.piConst {ι : Type*} [Fintype ι] {A : Subalgebra K (G → K)}
    {ρ : Representation K G W} (h : HasCoeffsIn A ρ) : HasCoeffsIn A (GLRep.piConst ι ρ) := by
  classical
  have := h.finiteDimensional
  refine ⟨inferInstance, fun F x => ?_⟩
  have hx : (fun g => F (GLRep.piConst ι ρ g x)) =
      ∑ i, fun g => (F ∘ₗ LinearMap.single K (fun _ => W) i) (ρ g (x i)) := by
    funext g
    simp only [Finset.sum_apply, LinearMap.comp_apply, LinearMap.coe_single]
    rw [← map_sum]
    congr 1
    conv_lhs => rw [← Finset.univ_sum_single (GLRep.piConst ι ρ g x)]
    rfl
  rw [hx]
  exact Subalgebra.sum_mem _ fun i _ => h.coeff_mem _ _

end PiConst

/-! ### The multiplicity space -/

variable {s : ℕ} {d : Fin (s + 1) → ℕ} {ρ : Representation K (LeviGroup K d) W}
variable {V : Type*} [AddCommGroup V] [Module K V]

variable (ρ) in
/-- The restriction of a representation of the Levi group to its first block. -/
abbrev headRep : Representation K (GL (Fin (d 0)) K) W := ρ.comp (leviBlock K d 0)

variable (ρ) in
/-- The restriction of a representation of the Levi group to the other blocks. -/
abbrev tailRep : Representation K (LeviGroup K (Fin.tail d)) W := ρ.comp (leviTail K d)

theorem headRep_mul_tailRep (g : GL (Fin (d 0)) K) (h : LeviGroup K (Fin.tail d)) :
    headRep ρ g * tailRep ρ h = tailRep ρ h * headRep ρ g := by
  simp only [MonoidHom.comp_apply, ← map_mul, (leviBlock_commute_leviTail g h).eq]

theorem headRep_tailRep_apply (g : GL (Fin (d 0)) K) (h : LeviGroup K (Fin.tail d)) (w : W) :
    headRep ρ g (tailRep ρ h w) = tailRep ρ h (headRep ρ g w) :=
  LinearMap.congr_fun (headRep_mul_tailRep g h) w

variable (ρ) in
/-- The **multiplicity space** `Hom_{GL_{d_0}}(σ, ρ)`, on which the other blocks act by
composition. -/
def multRep (σ : Representation K (GL (Fin (d 0)) K) V) :
    Representation K (LeviGroup K (Fin.tail d)) (IntertwiningMap σ (headRep ρ)) where
  toFun h :=
    { toFun := fun φ => ⟨tailRep ρ h ∘ₗ φ.toLinearMap, fun g => LinearMap.ext fun v => by
          change tailRep ρ h (φ (σ g v)) = headRep ρ g (tailRep ρ h (φ v))
          rw [φ.isIntertwining, headRep_tailRep_apply]⟩
      map_add' := fun φ ψ => IntertwiningMap.ext (LinearMap.ext fun v => by
        change tailRep ρ h (φ v + ψ v) = tailRep ρ h (φ v) + tailRep ρ h (ψ v)
        exact map_add _ _ _)
      map_smul' := fun c φ => IntertwiningMap.ext (LinearMap.ext fun v => by
        change tailRep ρ h (c • φ v) = c • tailRep ρ h (φ v)
        exact map_smul _ _ _) }
  map_one' := LinearMap.ext fun φ => IntertwiningMap.ext (LinearMap.ext fun v => by
    change tailRep ρ 1 (φ v) = φ v
    rw [map_one, Module.End.one_apply])
  map_mul' h h' := LinearMap.ext fun φ => IntertwiningMap.ext (LinearMap.ext fun v => by
    change tailRep ρ (h * h') (φ v) = tailRep ρ h (tailRep ρ h' (φ v))
    rw [map_mul, Module.End.mul_apply])

@[simp] theorem multRep_apply_apply (σ : Representation K (GL (Fin (d 0)) K) V)
    (h : LeviGroup K (Fin.tail d)) (φ : IntertwiningMap σ (headRep ρ)) (v : V) :
    multRep ρ σ h φ v = tailRep ρ h (φ v) := rfl

/-- **The multiplicity space is polynomial.** -/
theorem IsPolynomialLeviRep.multRep (hρ : IsPolynomialLeviRep ρ)
    (σ : Representation K (GL (Fin (d 0)) K) V) [FiniteDimensional K V] :
    IsPolynomialLeviRep (GLRep.multRep ρ σ) := by
  let b := Module.finBasis K V
  let T : IntertwiningMap (GLRep.multRep ρ σ) (piConst (Fin (finrank K V)) (tailRep ρ)) :=
    { toLinearMap :=
        { toFun := fun φ j => φ (b j)
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      isIntertwining' := fun _ => LinearMap.ext fun _ => rfl }
  refine (HasCoeffsIn.piConst hρ.comp_leviTail).of_injective T fun φ ψ hφψ => ?_
  refine IntertwiningMap.ext (b.ext fun j => ?_)
  exact congrFun hφψ j

/-! ### Weight spaces of the other blocks -/

variable (ρ) in
/-- The weight space of `η` for the torus of the other blocks, a subrepresentation of the first
block. -/
def tailWeightSubrep (η : (Σ q : Fin s, Fin (Fin.tail d q)) → ℤ) :
    Subrepresentation (headRep ρ) where
  toSubmodule := torusWeightSpace ((tailRep ρ).comp (leviTorus K (Fin.tail d))) η
  apply_mem_toSubmodule g w hw := by
    rw [mem_torusWeightSpace] at hw ⊢
    intro t
    rw [MonoidHom.comp_apply, ← headRep_tailRep_apply, ← MonoidHom.comp_apply (tailRep ρ), hw t,
      map_smul]

/-- **The weight spaces of the multiplicity space**: the weight space of `η` in
`Hom_{GL_{d_0}}(σ, ρ)` has the dimension of `Hom_{GL_{d_0}}(σ, W_η)`. -/
theorem finrank_tailWeightSubrep (σ : Representation K (GL (Fin (d 0)) K) V)
    (η : (Σ q : Fin s, Fin (Fin.tail d q)) → ℤ) :
    finrank K (IntertwiningMap σ (tailWeightSubrep ρ η).toRepresentation) =
      finrank K (torusWeightSpace ((multRep ρ σ).comp (leviTorus K (Fin.tail d))) η) := by
  set N := tailWeightSubrep ρ η
  let incl : IntertwiningMap N.toRepresentation (headRep ρ) :=
    ⟨N.toSubmodule.subtype, fun _ => rfl⟩
  have hmem : ∀ ψ : IntertwiningMap σ N.toRepresentation, incl.comp ψ ∈
      torusWeightSpace ((multRep ρ σ).comp (leviTorus K (Fin.tail d))) η := by
    intro ψ
    rw [mem_torusWeightSpace]
    intro t
    refine IntertwiningMap.ext (LinearMap.ext fun v => ?_)
    have := (mem_torusWeightSpace.mp (ψ v).2) t
    exact this
  have hval : ∀ φ ∈ torusWeightSpace ((multRep ρ σ).comp (leviTorus K (Fin.tail d))) η, ∀ v,
      φ v ∈ N.toSubmodule := by
    intro φ hφ v
    change φ v ∈ torusWeightSpace _ η
    rw [mem_torusWeightSpace]
    intro t
    have := congrArg (fun ψ : IntertwiningMap σ (headRep ρ) => ψ v)
      ((mem_torusWeightSpace.mp hφ) t)
    exact this
  let e : IntertwiningMap σ N.toRepresentation ≃ₗ[K]
      torusWeightSpace ((multRep ρ σ).comp (leviTorus K (Fin.tail d))) η :=
    { toFun := fun ψ => ⟨incl.comp ψ, hmem ψ⟩
      invFun := fun φ =>
        ⟨LinearMap.codRestrict N.toSubmodule (φ : IntertwiningMap σ (headRep ρ)).toLinearMap
            (hval φ φ.2), fun g => LinearMap.ext fun v => Subtype.ext
          (by exact LinearMap.congr_fun (φ.1.isIntertwining' g) v)⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact e.finrank_eq

/-! ### Traces on weight decompositions -/

/-- An endomorphism commuting with a representation of the torus preserves its weight spaces. -/
theorem mapsTo_torusWeightSpace_of_commute {κ : Type*} [Fintype κ]
    {π : Representation K (κ → Kˣ) W} {f : Module.End K W} (hf : ∀ t, f * π t = π t * f)
    (η : κ → ℤ) : ∀ w ∈ torusWeightSpace π η, f w ∈ torusWeightSpace π η := fun w hw => by
  rw [mem_torusWeightSpace] at hw ⊢
  intro t
  rw [← Module.End.mul_apply, ← hf t, Module.End.mul_apply, hw t, map_smul]

/-- **Traces on a weight decomposition.** If `f` commutes with a polynomial representation `π`
of a split torus, the trace of `f π(t)` is the sum over the weights `η` of `t^η` times the trace
of `f` on the weight space of `η`. -/
theorem trace_mul_eq_sum_weight [Infinite K] {κ : Type*} [Fintype κ]
    {π : Representation K (κ → Kˣ) W} (hπ : HasCoeffsIn (coordFunctions K (torusCoord K κ)) π)
    (f : Module.End K W) (hf : ∀ t, f * π t = π t * f) (F : Finset (κ → ℤ))
    (hF : ∀ η, torusWeightSpace π η ≠ ⊥ → η ∈ F) (t : κ → Kˣ) :
    LinearMap.trace K W (f * π t) = ∑ η ∈ F, weightCharHom K η t *
      LinearMap.trace K (torusWeightSpace π η)
        (f.restrict (mapsTo_torusWeightSpace_of_commute hf η)) := by
  have := hπ.finiteDimensional
  have hmaps : ∀ η, Set.MapsTo (f * π t) (torusWeightSpace π η) (torusWeightSpace π η) :=
    fun η w hw => mapsTo_torusWeightSpace_of_commute hf η _ (mapsTo_torusWeightSpace t η hw)
  have hfin := finite_torusWeightSpace_ne_bot π
  rw [LinearMap.trace_eq_sum_trace_restrict' hπ.isInternal_torusWeightSpace hfin hmaps]
  have hres : ∀ η, (f * π t).restrict (hmaps η) =
      weightCharHom K η t • f.restrict (mapsTo_torusWeightSpace_of_commute hf η) := by
    intro η
    refine LinearMap.ext fun w => Subtype.ext ?_
    change f (π t w) = weightCharHom K η t • f w
    rw [apply_of_mem_torusWeightSpace w.2 t, map_smul]
  simp_rw [hres, map_smul, smul_eq_mul]
  refine Finset.sum_subset (fun η hη => hF η ((Set.Finite.mem_toFinset _).mp hη))
    fun η _ hη => ?_
  have hbot : torusWeightSpace π η = ⊥ := by
    by_contra h
    exact hη ((Set.Finite.mem_toFinset _).mpr h)
  have : Subsingleton (torusWeightSpace π η) := Submodule.subsingleton_iff_eq_bot.mpr hbot
  rw [show f.restrict (mapsTo_torusWeightSpace_of_commute hf η) = 0 from
    LinearMap.ext fun _ => Subsingleton.elim _ _, map_zero, mul_zero]

end

end GLRep
