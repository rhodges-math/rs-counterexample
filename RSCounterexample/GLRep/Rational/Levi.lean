import RSCounterexample.GLRep.Rational.GL

/-!
# Rational representations of Levi groups

Let `L = ∏_p GL_{d_p}(K)` be a Levi group, `K` a field of characteristic zero. A representation of
`L` is **rational** when some twist of it by a power `∏_p det(g_p)^k` of the determinants is
polynomial (`GLRep.IsRationalLeviRep`). Its character is a Laurent polynomial in the variables
`x_{p,i}` (`GLRep.ratLeviCharacter`).

For a family `λ = (λ_p)` of dominant weights `λ_p ∈ ℤ^{d_p}`, `GLRep.ratLeviIrrep K d λ` is the
external tensor product `⊠_p V(λ_p)` of the irreducible rational representations, with character
the rational Schur polynomial `GLRep.ratLeviSchur d λ` (`GLRep.ratLeviCharacter_ratLeviIrrep`).
The character of a rational representation `ρ` of `L` is the sum of these weighted by the
multiplicities (`GLRep.IsRationalLeviRep.exists_ratLeviCharacter_eq_sum`):

`ch ρ = ∑_λ dim Hom_L(⊠_p V(λ_p), ρ) · s_λ`.

The proof twists `ρ` to a polynomial representation and uses the polynomial expansion
`GLRep.IsPolynomialLeviRep.exists_leviCharacter_eq_sum`; the families `λ` that do not become
polynomial under the twist do not occur (`GLRep.IsPolynomialLeviRep.ratLeviMultiplicity_eq_zero`).

## Main definitions

* `GLRep.leviDetZPow K d c`: the character `g ↦ ∏_p det(g_p)^{c_p}`.
* `GLRep.IsRationalLeviRep`, `GLRep.ratLeviCharacter`.
* `GLRep.ratLeviIrrep K d λ`, `GLRep.ratLeviSchur d λ`, `GLRep.ratLeviMultiplicity ρ λ`.

## Main results

* `GLRep.extTensor_scaledRep`, `GLRep.extTensorEquiv`.
* `GLRep.IsRationalLeviRep.trace_leviTorus_eq`,
  `GLRep.IsRationalLeviRep.ratLeviCharacter_scaledRep`.
* `GLRep.ratLeviCharacter_ratLeviIrrep`, `GLRep.nonempty_equiv_ratLeviIrrep_leviIrrep`,
  `GLRep.nonempty_equiv_scaledRep_ratLeviIrrep`.
* `GLRep.IsRationalLeviRep.exists_ratLeviCharacter_eq_sum`.
-/

namespace GLRep

open Module Representation TauCeti

noncomputable section

variable {K : Type*} [Field K] {s : ℕ} {d : Fin s → ℕ}
variable {W : Type*} [AddCommGroup W] [Module K W] {ρ : Representation K (LeviGroup K d) W}
variable {V : Type*} [AddCommGroup V] [Module K V] {σ : Representation K (LeviGroup K d) V}

/-! ### Powers of the determinants -/

variable (K d) in
/-- The character `g ↦ ∏_p det(g_p)^{c_p}` of the Levi group, `c ∈ ℤ^s`. -/
def leviDetZPow (c : Fin s → ℤ) : LeviGroup K d →* Kˣ :=
  ∏ p, (detZPow K (d p) (c p)).comp (leviEval K d p)

theorem leviDetZPow_apply (c : Fin s → ℤ) (g : LeviGroup K d) :
    leviDetZPow K d c g = ∏ p, detZPow K (d p) (c p) (g p) := by
  simp [leviDetZPow]

theorem leviDetZPow_zero : leviDetZPow K d 0 = 1 :=
  MonoidHom.ext fun g => by simp [leviDetZPow_apply, detZPow_zero]

theorem leviDetZPow_leviTorus (c : Fin s → ℤ) (t : (Σ p : Fin s, Fin (d p)) → Kˣ) :
    leviDetZPow K d c (leviTorus K d t) = weightChar K (fun x => c x.1) t := by
  rw [leviDetZPow_apply, weightChar_apply, torusCharacter_def, Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [leviTorus_apply, detZPow_diagGL, weightChar_apply, torusCharacter_def]

/-! ### External tensor products -/

section ExtTensor

variable {V' : Fin s → Type*} [∀ p, AddCommGroup (V' p)] [∀ p, Module K (V' p)]
variable {V'' : Fin s → Type*} [∀ p, AddCommGroup (V'' p)] [∀ p, Module K (V'' p)]

/-- **Twisting the factors of an external tensor product** is twisting it by the product of the
characters. -/
theorem extTensor_scaledRep (ρ' : (p : Fin s) → Representation K (GL (Fin (d p)) K) (V' p))
    (χ : (p : Fin s) → GL (Fin (d p)) K →* Kˣ) :
    extTensor (fun p => scaledRep (ρ' p) (χ p)) =
      scaledRep (extTensor ρ') (∏ p, (χ p).comp (leviEval K d p)) := by
  refine MonoidHom.ext fun g => PiTensorProduct.ext (MultilinearMap.ext fun v => ?_)
  simp only [LinearMap.compMultilinearMap_apply, extTensor_tprod, scaledRep_apply,
    MonoidHom.finsetProd_apply, MonoidHom.comp_apply, leviEval_apply, Units.coe_prod]
  rw [MultilinearMap.map_smul_univ]

theorem scaledRep_extTensor_leviDetZPow
    (ρ' : (p : Fin s) → Representation K (GL (Fin (d p)) K) (V' p)) (c : Fin s → ℤ) :
    scaledRep (extTensor ρ') (leviDetZPow K d c) =
      extTensor fun p => scaledRep (ρ' p) (detZPow K (d p) (c p)) :=
  (extTensor_scaledRep _ _).symm

/-- Equivalences of the factors give an equivalence of the external tensor products. -/
def extTensorEquiv {ρ' : (p : Fin s) → Representation K (GL (Fin (d p)) K) (V' p)}
    {σ' : (p : Fin s) → Representation K (GL (Fin (d p)) K) (V'' p)}
    (e : (p : Fin s) → (ρ' p).Equiv (σ' p)) : (extTensor ρ').Equiv (extTensor σ') :=
  .mk (PiTensorProduct.congr fun p => (e p).toLinearEquiv) fun g => by
    refine PiTensorProduct.ext (MultilinearMap.ext fun v => ?_)
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearEquiv.coe_coe, extTensor_tprod, PiTensorProduct.congr_tprod]
    congr 1
    funext p
    exact IntertwiningMap.isIntertwining _ _ (e p).toIntertwiningMap (g p) (v p)

end ExtTensor

/-! ### Rational representations -/

/-- A representation of the Levi group `∏_p GL_{d_p}(K)` is **rational** when some twist of it by
a power `g ↦ ∏_p det(g_p)^k`, `k ≥ 0`, of the determinants is polynomial. -/
def IsRationalLeviRep (ρ : Representation K (LeviGroup K d) W) : Prop :=
  ∃ k : ℕ, IsPolynomialLeviRep (scaledRep ρ (leviDetZPow K d fun _ => k))

theorem IsPolynomialLeviRep.isRationalLeviRep (h : IsPolynomialLeviRep ρ) :
    IsRationalLeviRep ρ := by
  refine ⟨0, ?_⟩
  have : (leviDetZPow K d fun _ => ((0 : ℕ) : ℤ)) = 1 := by
    rw [← leviDetZPow_zero]
    rfl
  rwa [this, scaledRep_one]

namespace IsRationalLeviRep

theorem finiteDimensional (h : IsRationalLeviRep ρ) : FiniteDimensional K W :=
  h.choose_spec.finiteDimensional

theorem of_equiv (h : IsRationalLeviRep ρ) (e : ρ.Equiv σ) : IsRationalLeviRep σ :=
  ⟨h.choose, HasCoeffsIn.of_equiv h.choose_spec (scaledRepEquiv e _)⟩

theorem comp_leviTorus_scaledRep (c : Fin s → ℤ) :
    (scaledRep ρ (leviDetZPow K d c)).comp (leviTorus K d) =
      scaledRep (ρ.comp (leviTorus K d)) (weightChar K fun x => c x.1) := by
  ext t w
  simp only [MonoidHom.comp_apply, scaledRep_apply, leviDetZPow_leviTorus]

/-- The restriction to the torus of a rational representation of the Levi group is rational. -/
theorem isRationalTorusRep (h : IsRationalLeviRep ρ) :
    IsRationalTorusRep (ρ.comp (leviTorus K d)) := by
  obtain ⟨k, hk⟩ := h
  refine ⟨fun _ => (k : ℤ), ?_⟩
  have := comp_leviTorus_scaledRep (ρ := ρ) fun _ => (k : ℤ)
  rw [← this]
  exact hk.comp_leviTorus

end IsRationalLeviRep

/-! ### Characters -/

variable (ρ) in
/-- The **character** `∑_μ dim W_μ · x^μ` of a rational representation of the Levi group, a
Laurent polynomial in the variables `x_{p,i}`. -/
def ratLeviCharacter : TorusLaurent (Σ p : Fin s, Fin (d p)) :=
  laurentCharacter (ρ.comp (leviTorus K d))

section Infinite

variable [Infinite K]

/-- **The trace formula** for a rational representation of the Levi group. -/
theorem IsRationalLeviRep.trace_leviTorus_eq (h : IsRationalLeviRep ρ)
    (t : (Σ p : Fin s, Fin (d p)) → Kˣ) :
    LinearMap.trace K W (ρ (leviTorus K d t)) = laurentEval K t (ratLeviCharacter ρ) :=
  h.isRationalTorusRep.trace_eq_laurentEval t

/-- **Twisting by `∏_p det(g_p)^{c_p}` multiplies the character by `∏_{p,i} x_{p,i}^{c_p}`.** -/
theorem IsRationalLeviRep.ratLeviCharacter_scaledRep (h : IsRationalLeviRep ρ) (c : Fin s → ℤ) :
    ratLeviCharacter (scaledRep ρ (leviDetZPow K d c)) =
      AddMonoidAlgebra.single (fun x => c x.1) 1 * ratLeviCharacter ρ := by
  have := h.finiteDimensional
  rw [ratLeviCharacter, IsRationalLeviRep.comp_leviTorus_scaledRep, laurentCharacter_scaledRep]
  rfl

end Infinite

variable [CharZero K]

/-- The character of a rational representation of the Levi group is the only Laurent polynomial
whose values on the diagonal torus are the traces. -/
theorem IsRationalLeviRep.eq_ratLeviCharacter_of_forall (h : IsRationalLeviRep ρ)
    (f : TorusLaurent (Σ p : Fin s, Fin (d p)))
    (hf : ∀ t, laurentEval K t f = LinearMap.trace K W (ρ (leviTorus K d t))) :
    f = ratLeviCharacter ρ :=
  h.isRationalTorusRep.eq_laurentCharacter_of_forall f hf

theorem ratLeviCharacter_eq_of_equiv (hρ : IsRationalLeviRep ρ) (hσ : IsRationalLeviRep σ)
    (e : ρ.Equiv σ) : ratLeviCharacter ρ = ratLeviCharacter σ := by
  refine hσ.eq_ratLeviCharacter_of_forall _ fun t => ?_
  rw [← hρ.trace_leviTorus_eq]
  have : σ (leviTorus K d t) = e.toLinearEquiv.conj (ρ (leviTorus K d t)) := by
    ext v
    obtain ⟨w, rfl⟩ := e.toLinearEquiv.surjective v
    simp only [LinearEquiv.conj_apply, LinearMap.coe_comp, LinearEquiv.coe_coe,
      Function.comp_apply, LinearEquiv.symm_apply_apply]
    exact (IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap _ w).symm
  rw [this, LinearMap.trace_conj']

/-- For a polynomial representation the rational character is the character. -/
theorem IsPolynomialLeviRep.ratLeviCharacter_eq (h : IsPolynomialLeviRep ρ) :
    ratLeviCharacter ρ = polyToLaurent _ (leviCharacter ρ) :=
  laurentCharacter_eq_polyToLaurent h.comp_leviTorus

/-- The character of `ρ` in terms of that of a polynomial twist. -/
theorem ratLeviCharacter_eq_of_isPolynomialLeviRep_scaledRep {k : ℕ}
    (hk : IsPolynomialLeviRep (scaledRep ρ (leviDetZPow K d fun _ => k))) :
    ratLeviCharacter ρ = AddMonoidAlgebra.single (fun _ => -(k : ℤ)) 1 *
      polyToLaurent _ (leviCharacter (scaledRep ρ (leviDetZPow K d fun _ => k))) := by
  have h : IsRationalLeviRep ρ := ⟨k, hk⟩
  rw [← IsPolynomialLeviRep.ratLeviCharacter_eq hk, h.ratLeviCharacter_scaledRep, ← mul_assoc,
    single_const_mul_single_const, neg_add_cancel, single_const_zero, one_mul]

/-! ### The irreducible rational representations -/

variable (K d) in
/-- The external tensor product `⊠_p V(λ_p)` of the irreducible rational representations
`V(λ_p) = GLRep.ratIrrep K (d p) λ_p`, for a family of dominant weights `λ_p ∈ ℤ^{d_p}`. -/
abbrev ratLeviIrrep (l : (p : Fin s) → DominantWeight (d p)) :
    Representation K (LeviGroup K d)
      (PiTensorProduct K fun p => IrrepSpace K (d p) (l p).detShiftShape) :=
  extTensor fun p => ratIrrep K (d p) (l p)

/-- `⊠_p V(λ_p)` is the twist of `⊠_p V(λ_p − λ_{p,d_p})` by `∏_p det(g_p)^{λ_{p,d_p}}`. -/
theorem ratLeviIrrep_eq (l : (p : Fin s) → DominantWeight (d p)) :
    ratLeviIrrep K d l = scaledRep (leviIrrep K d fun p => (l p).detShiftShape)
      (leviDetZPow K d fun p => (l p).detShift) :=
  extTensor_scaledRep _ _

/-- For polynomial dominant weights, `⊠_p V(λ_p)` is `GLRep.leviIrrep K d λ`. -/
theorem nonempty_equiv_ratLeviIrrep_leviIrrep {l : (p : Fin s) → DominantWeight (d p)}
    (hl : ∀ p, (l p).IsPolynomial) :
    Nonempty ((ratLeviIrrep K d l).Equiv (leviIrrep K d fun p => (l p).shape)) :=
  ⟨extTensorEquiv fun p => (nonempty_equiv_ratIrrep_irrep (hl p)).some⟩

/-- **The twist of `⊠_p V(λ_p)` by `∏_p det(g_p)^{c_p}` is `⊠_p V(λ_p + c_p)`.** -/
theorem nonempty_equiv_scaledRep_ratLeviIrrep (l : (p : Fin s) → DominantWeight (d p))
    (c : Fin s → ℤ) :
    Nonempty ((scaledRep (ratLeviIrrep K d l) (leviDetZPow K d c)).Equiv
      (ratLeviIrrep K d fun p => (l p).shift (c p))) := by
  rw [scaledRep_extTensor_leviDetZPow]
  exact ⟨extTensorEquiv fun p => (nonempty_equiv_scaledRep_ratIrrep (l p) (c p)).some⟩

theorem isRationalLeviRep_ratLeviIrrep (l : (p : Fin s) → DominantWeight (d p)) :
    IsRationalLeviRep (ratLeviIrrep K d l) := by
  obtain ⟨k, hk⟩ := exists_forall_isPolynomial_shift l
  refine ⟨k, ?_⟩
  obtain ⟨e⟩ := nonempty_equiv_scaledRep_ratLeviIrrep (K := K) l fun _ => (k : ℤ)
  obtain ⟨e'⟩ := nonempty_equiv_ratLeviIrrep_leviIrrep (K := K) hk
  exact HasCoeffsIn.of_equiv (isPolynomialLeviRep_leviIrrep _) (e.trans e').symm

/-! ### Rational Schur polynomials -/

variable (d) in
/-- The **rational Schur polynomial** `∏_p s_{λ_p}(x_{p,·})` of a family of dominant weights
`λ_p ∈ ℤ^{d_p}`: the product of the monomial `∏_{p,i} x_{p,i}^{λ_{p,d_p}}` and the Schur polynomials
`s_{λ_p − λ_{p,d_p}}(x_{p,·})`. -/
def ratLeviSchur (l : (p : Fin s) → DominantWeight (d p)) :
    TorusLaurent (Σ p : Fin s, Fin (d p)) :=
  AddMonoidAlgebra.single (fun x => (l x.1).detShift) 1 *
    polyToLaurent _ (leviSchur d fun p => (l p).detShiftShape)

theorem detShift_shift_of_fin {n : ℕ} (l : DominantWeight n) (c : ℤ) (i : Fin n) :
    (l.shift c).detShift = l.detShift + c := by
  cases n with
  | zero => exact i.elim0
  | succ n => exact DominantWeight.detShift_shift l c

/-- **`s_{λ + c} = (∏_{p,i} x_{p,i}^{c_p}) s_λ`.** -/
theorem ratLeviSchur_shift (l : (p : Fin s) → DominantWeight (d p)) (c : Fin s → ℤ) :
    ratLeviSchur d (fun p => (l p).shift (c p)) =
      AddMonoidAlgebra.single (fun x => c x.1) 1 * ratLeviSchur d l := by
  have hc : (fun x : Σ p : Fin s, Fin (d p) => ((l x.1).shift (c x.1)).detShift) =
      (fun x => c x.1) + fun x => (l x.1).detShift := by
    funext x
    rw [detShift_shift_of_fin _ _ x.2, Pi.add_apply, add_comm]
  simp only [ratLeviSchur, detShiftShape_shift]
  rw [hc, ← mul_assoc, AddMonoidAlgebra.single_mul_single, one_mul]

/-- **The character of `⊠_p V(λ_p)` is the rational Schur polynomial `s_λ`.** -/
theorem ratLeviCharacter_ratLeviIrrep (l : (p : Fin s) → DominantWeight (d p)) :
    ratLeviCharacter (ratLeviIrrep K d l) = ratLeviSchur d l := by
  have h := isPolynomialLeviRep_leviIrrep (K := K) (d := d) fun p => (l p).detShiftShape
  rw [ratLeviIrrep_eq, (IsPolynomialLeviRep.isRationalLeviRep h).ratLeviCharacter_scaledRep,
    IsPolynomialLeviRep.ratLeviCharacter_eq h,
    leviCharacter_leviIrrep fun p => DominantWeight.colLen_zero_detShiftShape_le (l p),
    ratLeviSchur]

/-- For polynomial dominant weights the rational Schur polynomial is the product of the Schur
polynomials of the blocks. -/
theorem ratLeviSchur_of_isPolynomial {l : (p : Fin s) → DominantWeight (d p)}
    (hl : ∀ p, (l p).IsPolynomial) :
    ratLeviSchur d l = polyToLaurent _ (leviSchur d fun p => (l p).shape) := by
  obtain ⟨e⟩ := nonempty_equiv_ratLeviIrrep_leviIrrep (K := ℚ) hl
  have h := isPolynomialLeviRep_leviIrrep (K := ℚ) (d := d) fun p => (l p).shape
  rw [← ratLeviCharacter_ratLeviIrrep (K := ℚ), ratLeviCharacter_eq_of_equiv
    (isRationalLeviRep_ratLeviIrrep l) (IsPolynomialLeviRep.isRationalLeviRep h) e,
    IsPolynomialLeviRep.ratLeviCharacter_eq h,
    leviCharacter_leviIrrep fun p => DominantWeight.colLen_zero_shape_le (l p)]

/-! ### Multiplicities -/

variable (ρ) in
/-- The **multiplicity** `dim Hom_L(⊠_p V(λ_p), ρ)`. -/
def ratLeviMultiplicity (l : (p : Fin s) → DominantWeight (d p)) : ℕ :=
  finrank K ((ratLeviIrrep K d l).IntertwiningMap ρ)

theorem ratLeviMultiplicity_eq_of_equiv (e : ρ.Equiv σ) (l : (p : Fin s) → DominantWeight (d p)) :
    ratLeviMultiplicity ρ l = ratLeviMultiplicity σ l :=
  (intertwiningMapCongrRight e).finrank_eq

/-- For polynomial dominant weights the multiplicity is the polynomial one. -/
theorem ratLeviMultiplicity_eq_leviMultiplicity {l : (p : Fin s) → DominantWeight (d p)}
    (hl : ∀ p, (l p).IsPolynomial) :
    ratLeviMultiplicity ρ l = leviMultiplicity ρ fun p => (l p).shape :=
  (intertwiningMapCongrLeft (nonempty_equiv_ratLeviIrrep_leviIrrep hl).some).finrank_eq

/-- A polynomial representation of the Levi group admits no nonzero intertwining map from
`⊠_p V(λ_p)` when some `λ_p` has a negative entry: restricted to the factor `GL_{d_p}(K)`, such a
map would be an intertwining map from `V(λ_p)` to a polynomial representation. -/
theorem IsPolynomialLeviRep.intertwiningMap_ratLeviIrrep_eq_zero (h : IsPolynomialLeviRep ρ)
    {l : (p : Fin s) → DominantWeight (d p)} (hl : ¬ ∀ p, (l p).IsPolynomial)
    (f : (ratLeviIrrep K d l).IntertwiningMap ρ) : f = 0 := by
  obtain ⟨p, hp⟩ := not_forall.mp hl
  have key : ∀ w : (q : Fin s) → IrrepSpace K (d q) (l q).detShiftShape,
      f (PiTensorProduct.tprod K w) = 0 := by
    intro w
    let F : (ratIrrep K (d p) (l p)).IntertwiningMap (ρ.comp (leviBlock K d p)) :=
      ⟨f.toLinearMap ∘ₗ (PiTensorProduct.tprod K).toLinearMap w p,
        fun g => LinearMap.ext fun v => by
          change f (PiTensorProduct.tprod K (Function.update w p (ratIrrep K (d p) (l p) g v))) =
            ρ (leviBlock K d p g) (f (PiTensorProduct.tprod K (Function.update w p v)))
          have hupd : (fun q => ratIrrep K (d q) (l q) (leviBlock K d p g q)
              (Function.update w p v q)) = Function.update w p (ratIrrep K (d p) (l p) g v) := by
            funext q
            rcases eq_or_ne q p with rfl | hq
            · simp [leviBlock]
            · simp [leviBlock, hq]
          rw [← IntertwiningMap.isIntertwining _ _ f (leviBlock K d p g), extTensor_tprod, hupd]⟩
    have hF : F = 0 := IsPolynomialRep.intertwiningMap_ratIrrep_eq_zero
      (IsPolynomialLeviRep.comp_leviBlock h p) hp F
    have h0 : F (w p) = 0 := by
      rw [hF]
      rfl
    change f (PiTensorProduct.tprod K (Function.update w p (w p))) = 0 at h0
    rwa [Function.update_eq_self] at h0
  refine IntertwiningMap.ext (PiTensorProduct.ext (MultilinearMap.ext fun w => ?_))
  exact key w

/-- A polynomial representation of the Levi group does not contain `⊠_p V(λ_p)` when some `λ_p`
has a negative entry. -/
theorem IsPolynomialLeviRep.ratLeviMultiplicity_eq_zero (h : IsPolynomialLeviRep ρ)
    {l : (p : Fin s) → DominantWeight (d p)} (hl : ¬ ∀ p, (l p).IsPolynomial) :
    ratLeviMultiplicity ρ l = 0 := by
  have : Subsingleton ((ratLeviIrrep K d l).IntertwiningMap ρ) :=
    subsingleton_of_forall_eq 0 (IsPolynomialLeviRep.intertwiningMap_ratLeviIrrep_eq_zero h hl)
  exact Module.finrank_zero_of_subsingleton

/-- Twisting by `∏_p det(g_p)^{c_p}` shifts the multiplicities by `c`. -/
theorem ratLeviMultiplicity_scaledRep (l : (p : Fin s) → DominantWeight (d p)) (c : Fin s → ℤ) :
    ratLeviMultiplicity (scaledRep ρ (leviDetZPow K d c)) (fun p => (l p).shift (c p)) =
      ratLeviMultiplicity ρ l := by
  obtain ⟨e⟩ := nonempty_equiv_scaledRep_ratLeviIrrep (K := K) l c
  rw [ratLeviMultiplicity, ratLeviMultiplicity, ← (intertwiningMapCongrLeft e).finrank_eq]
  exact (intertwiningMapScaledEquiv _ _ _).finrank_eq.symm

/-- **The character of a rational representation of a Levi group** is the sum of the rational
Schur polynomials `s_λ` weighted by the multiplicities `dim Hom_L(⊠_p V(λ_p), ρ)`, over a finite
set of families of dominant weights outside which the multiplicities vanish. -/
theorem IsRationalLeviRep.exists_ratLeviCharacter_eq_sum (h : IsRationalLeviRep ρ) :
    ∃ S : Finset ((p : Fin s) → DominantWeight (d p)),
      (∀ l ∉ S, ratLeviMultiplicity ρ l = 0) ∧
      ratLeviCharacter ρ = ∑ l ∈ S, (ratLeviMultiplicity ρ l : ℤ) • ratLeviSchur d l := by
  classical
  obtain ⟨k, hk⟩ := h
  obtain ⟨S', hS'n, hS'z, hS'χ⟩ := IsPolynomialLeviRep.exists_leviCharacter_eq_sum hk
  set φ : (Fin s → YoungDiagram) → (p : Fin s) → DominantWeight (d p) :=
    fun μ p => (weightOfShape (d p) (μ p)).shift (-(k : ℤ)) with hφ
  have hmult : ∀ l : (p : Fin s) → DominantWeight (d p), ratLeviMultiplicity ρ l =
      ratLeviMultiplicity (scaledRep ρ (leviDetZPow K d fun _ => k))
        (fun p => (l p).shift k) :=
    fun l => (ratLeviMultiplicity_scaledRep l _).symm
  have hφμ : ∀ μ ∈ S', ratLeviMultiplicity ρ (φ μ) =
      leviMultiplicity (scaledRep ρ (leviDetZPow K d fun _ => k)) μ := by
    intro μ hμ
    have hshift : (fun p => (φ μ p).shift (k : ℤ)) = fun p => weightOfShape (d p) (μ p) := by
      funext p
      simp only [hφ, DominantWeight.shift_shift, neg_add_cancel, DominantWeight.shift_zero]
    have hshape : (fun p => (weightOfShape (d p) (μ p)).shape) = μ :=
      funext fun p => shape_weightOfShape (hS'n μ hμ p)
    rw [hmult, hshift, ratLeviMultiplicity_eq_leviMultiplicity
      fun p => isPolynomial_weightOfShape _ _, hshape]
  have hinj : Set.InjOn φ S' := by
    intro μ hμ ν hν hμν
    funext p
    have := congrArg (fun l : (p : Fin s) → DominantWeight (d p) => (l p).shift (k : ℤ)) hμν
    simp only [hφ, DominantWeight.shift_shift, neg_add_cancel, DominantWeight.shift_zero] at this
    rw [← shape_weightOfShape (hS'n μ hμ p), this, shape_weightOfShape (hS'n ν hν p)]
  refine ⟨S'.image φ, fun l hl => ?_, ?_⟩
  · rw [hmult]
    by_cases hp : ∀ p, ((l p).shift k).IsPolynomial
    · rw [ratLeviMultiplicity_eq_leviMultiplicity hp]
      refine hS'z _ (fun p => DominantWeight.colLen_zero_shape_le _) fun hm => hl ?_
      refine Finset.mem_image.mpr ⟨_, hm, ?_⟩
      funext p
      simp only [hφ, weightOfShape_shape (hp p), DominantWeight.shift_shift, add_neg_cancel,
        DominantWeight.shift_zero]
    · exact IsPolynomialLeviRep.ratLeviMultiplicity_eq_zero hk hp
  · rw [ratLeviCharacter_eq_of_isPolynomialLeviRep_scaledRep hk, hS'χ, map_sum, Finset.mul_sum,
      Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun μ hμ => ?_
    have hshape : (fun p => (weightOfShape (d p) (μ p)).shape) = μ :=
      funext fun p => shape_weightOfShape (hS'n μ hμ p)
    rw [hφμ μ hμ, map_zsmul, mul_smul_comm, hφ,
      ratLeviSchur_shift (fun p => weightOfShape (d p) (μ p)) fun _ => -(k : ℤ),
      ratLeviSchur_of_isPolynomial fun p => isPolynomial_weightOfShape _ _, hshape]

end

end GLRep
