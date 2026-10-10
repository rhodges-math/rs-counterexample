import RSCounterexample.GLRep.Torus.Character

/-!
# Levi groups: blocks, external tensor products and characters

The Levi group `L = ∏_{p < s} GL_{d_p}(K)` contains each factor `GL_{d_p}(K)` (`GLRep.leviBlock`)
and maps onto it (`Pi.evalMonoidHom`). Its diagonal torus `GLRep.leviTorus` is indexed by the
pairs `(p, i)` with `i < d_p`.

* Restricting a polynomial representation of `L` to a factor gives a polynomial representation of
  that factor, and pulling a polynomial representation of a factor back to `L` gives a polynomial
  representation of `L`.
* The **external tensor product** `⊠_p ρ_p` of representations `ρ_p` of the factors
  (`GLRep.extTensor`) is a polynomial representation of `L` when every `ρ_p` is polynomial.
* The **character** of a polynomial representation of `L` (`GLRep.leviCharacter`) is a polynomial
  in the variables `x_{p,i}`. The character of `⊠_p ρ_p` is the product over `p` of the characters
  of the `ρ_p`, each in its own block of variables (`GLRep.leviCharacter_extTensor`).

## Main definitions

* `GLRep.leviTorus`, `GLRep.leviBlock`, `GLRep.extTensor`, `GLRep.leviCharacter`.

## Main results

* `GLRep.IsPolynomialLeviRep.comp_leviBlock`, `GLRep.IsPolynomialRep.comp_leviEval`,
  `GLRep.isPolynomialLeviRep_extTensor`.
* `GLRep.trace_leviTorus_eq_eval_leviCharacter`, `GLRep.eq_leviCharacter_of_forall_trace_eq`.
* `GLRep.trace_piTensorProduct_map`: the trace of a tensor product of a finite family of
  endomorphisms.
* `GLRep.leviCharacter_extTensor`.
-/

namespace GLRep

open Module TauCeti

noncomputable section

variable {K : Type*} [Field K]
variable {W : Type*} [AddCommGroup W] [Module K W]
variable {V : Type*} [AddCommGroup V] [Module K V]
variable {s : ℕ} {d : Fin s → ℕ}

/-! ### The torus and the blocks -/

section Blocks

variable (K d)

/-- The **diagonal torus** of the Levi group: `t` goes to the block-diagonal element whose block
`p` is `diag(t_{p,0}, …, t_{p,d_p - 1})`. -/
def leviTorus : ((Σ p : Fin s, Fin (d p)) → Kˣ) →* LeviGroup K d where
  toFun t p := diagGL fun i => t ⟨p, i⟩
  map_one' := by
    funext p
    exact map_one (diagGL (k := K) (ι := Fin (d p)))
  map_mul' t t' := by
    funext p
    exact map_mul (diagGL (k := K) (ι := Fin (d p))) (fun i => t ⟨p, i⟩) (fun i => t' ⟨p, i⟩)

/-- The inclusion of the factor `GL_{d_p}(K)` into the Levi group. -/
def leviBlock (p : Fin s) : GL (Fin (d p)) K →* LeviGroup K d :=
  MonoidHom.mulSingle (fun q => GL (Fin (d q)) K) p

/-- The projection of the Levi group onto its factor `GL_{d_p}(K)`. -/
def leviEval (p : Fin s) : LeviGroup K d →* GL (Fin (d p)) K :=
  Pi.evalMonoidHom (fun q => GL (Fin (d q)) K) p

variable {K d}

@[simp] theorem leviTorus_apply (t : (Σ p : Fin s, Fin (d p)) → Kˣ) (p : Fin s) :
    leviTorus K d t p = diagGL fun i => t ⟨p, i⟩ := rfl

@[simp] theorem leviEval_apply (g : LeviGroup K d) (p : Fin s) : leviEval K d p g = g p := rfl

theorem leviEval_leviBlock (p : Fin s) (g : GL (Fin (d p)) K) :
    leviEval K d p (leviBlock K d p g) = g := by
  simp [leviBlock, leviEval]

theorem leviCoord_leviTorus_mem (x : LeviIndex d) :
    (fun t => leviCoord K d (leviTorus K d t) x) ∈
      coordFunctions K (torusCoord K (Σ p : Fin s, Fin (d p))) := by
  obtain ⟨p, i, j⟩ := x
  by_cases hij : i = j
  · subst hij
    have : (fun t => leviCoord K d (leviTorus K d t) ⟨p, i, i⟩) =
        fun t => torusCoord K _ t ⟨p, i⟩ := by
      funext t
      simp [leviCoord, diagGL_apply]
    rw [this]
    exact coord_mem_coordFunctions _ _
  · have : (fun t => leviCoord K d (leviTorus K d t) ⟨p, i, j⟩) = 0 := by
      funext t
      simp [leviCoord, diagGL_apply, hij]
    rw [this]
    exact zero_mem _

theorem leviCoord_leviBlock_mem (p : Fin s) (x : LeviIndex d) :
    (fun g => leviCoord K d (leviBlock K d p g) x) ∈ glPolynomialFunctions K (d p) := by
  obtain ⟨q, i, j⟩ := x
  by_cases hq : q = p
  · subst hq
    have : (fun g => leviCoord K d (leviBlock K d q g) ⟨q, i, j⟩) =
        fun g => glCoord K (d q) g (i, j) := by
      funext g
      simp [leviCoord, leviBlock]
    rw [this]
    exact coord_mem_coordFunctions _ _
  · have : (fun g => leviCoord K d (leviBlock K d p g) ⟨q, i, j⟩) =
        fun _ => (1 : Matrix (Fin (d q)) (Fin (d q)) K) i j := by
      funext g
      simp [leviCoord, leviBlock, Pi.mulSingle_eq_of_ne hq]
    rw [this]
    exact Subalgebra.algebraMap_mem _ _

theorem glCoord_leviEval_mem (p : Fin s) (x : Fin (d p) × Fin (d p)) :
    (fun g => glCoord K (d p) (leviEval K d p g) x) ∈ leviPolynomialFunctions K d :=
  coord_mem_coordFunctions (leviCoord K d) ⟨p, x⟩

end Blocks

/-! ### Polynomial representations of Levi groups -/

section Polynomial

/-- The restriction of a polynomial representation of the Levi group to the diagonal torus is a
polynomial representation of the torus. -/
theorem IsPolynomialLeviRep.comp_leviTorus {ρ : Representation K (LeviGroup K d) W}
    (h : IsPolynomialLeviRep ρ) :
    HasCoeffsIn (coordFunctions K (torusCoord K (Σ p : Fin s, Fin (d p))))
      (ρ.comp (leviTorus K d)) :=
  h.comp _ fun _ hf => comp_mem_coordFunctions _ leviCoord_leviTorus_mem hf

/-- **Restricting to a factor.** The restriction of a polynomial representation of the Levi group
to the factor `GL_{d_p}(K)` is polynomial. -/
theorem IsPolynomialLeviRep.comp_leviBlock {ρ : Representation K (LeviGroup K d) W}
    (h : IsPolynomialLeviRep ρ) (p : Fin s) : IsPolynomialRep (ρ.comp (leviBlock K d p)) :=
  h.comp _ fun _ hf => comp_mem_coordFunctions _ (leviCoord_leviBlock_mem p) hf

/-- **Pulling back from a factor.** A polynomial representation of the factor `GL_{d_p}(K)`,
pulled back along the projection, is a polynomial representation of the Levi group. -/
theorem IsPolynomialRep.comp_leviEval {ρ : Representation K (GL (Fin (d p)) K) W}
    (h : IsPolynomialRep ρ) : IsPolynomialLeviRep (ρ.comp (leviEval K d p)) :=
  h.comp _ fun _ hf => comp_mem_coordFunctions _ (glCoord_leviEval_mem p) hf

variable {V' : Fin s → Type*} [∀ p, AddCommGroup (V' p)] [∀ p, Module K (V' p)]

/-- The **external tensor product** `⊠_p ρ_p` of representations `ρ_p` of the factors
`GL_{d_p}(K)`: an element `g` of the Levi group acts by `⊗_p ρ_p(g_p)`. -/
def extTensor (ρ' : (p : Fin s) → Representation K (GL (Fin (d p)) K) (V' p)) :
    Representation K (LeviGroup K d) (PiTensorProduct K V') :=
  piTensor fun p => (ρ' p).comp (leviEval K d p)

theorem extTensor_tprod (ρ' : (p : Fin s) → Representation K (GL (Fin (d p)) K) (V' p))
    (g : LeviGroup K d) (v : (p : Fin s) → V' p) :
    extTensor ρ' g (PiTensorProduct.tprod K v) =
      PiTensorProduct.tprod K fun p => ρ' p (g p) (v p) :=
  piTensor_tprod _ g v

/-- The external tensor product of polynomial representations is polynomial. -/
theorem isPolynomialLeviRep_extTensor
    {ρ' : (p : Fin s) → Representation K (GL (Fin (d p)) K) (V' p)}
    (h : ∀ p, IsPolynomialRep (ρ' p)) : IsPolynomialLeviRep (extTensor ρ') :=
  HasCoeffsIn.piTensor fun p => (h p).comp_leviEval

end Polynomial

/-! ### Traces of tensor products of families -/

section Trace

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {V' : ι → Type*} [∀ i, AddCommGroup (V' i)]
  [∀ i, Module K (V' i)] [∀ i, FiniteDimensional K (V' i)]

/-- **The trace of a tensor product of a finite family of endomorphisms** is the product of their
traces. -/
theorem trace_piTensorProduct_map (f : (i : ι) → Module.End K (V' i)) :
    LinearMap.trace K (PiTensorProduct K V') (PiTensorProduct.map f) =
      ∏ i, LinearMap.trace K (V' i) (f i) := by
  classical
  let b := fun i => Module.finBasis K (V' i)
  rw [LinearMap.trace_eq_matrix_trace K (Basis.piTensorProduct b)]
  simp_rw [LinearMap.trace_eq_matrix_trace K (b _), Matrix.trace, Matrix.diag]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [LinearMap.toMatrix_apply, Basis.piTensorProduct_apply, PiTensorProduct.map_tprod,
    Basis.piTensorProduct_repr_tprod_apply]
  simp [LinearMap.toMatrix_apply]

end Trace

/-! ### Characters -/

section Character

variable [Infinite K] {ρ : Representation K (LeviGroup K d) W}
  {σ : Representation K (LeviGroup K d) V}

variable (ρ) in
/-- The **character** of a representation of the Levi group: the character of its restriction to
the diagonal torus, a polynomial in the variables `x_{p,i}`. -/
def leviCharacter : MvPolynomial (Σ p : Fin s, Fin (d p)) ℤ :=
  torusCharacter (ρ.comp (leviTorus K d))

/-- **The trace formula** for a polynomial representation of the Levi group. -/
theorem trace_leviTorus_eq_eval_leviCharacter (h : IsPolynomialLeviRep ρ)
    (t : (Σ p : Fin s, Fin (d p)) → Kˣ) :
    LinearMap.trace K W (ρ (leviTorus K d t)) =
      MvPolynomial.eval₂ (Int.castRingHom K) (fun i => (t i : K)) (leviCharacter ρ) :=
  trace_eq_eval_torusCharacter h.comp_leviTorus t

/-- The character of a polynomial representation of the Levi group is the only integer
polynomial whose values on the diagonal torus are the traces. -/
theorem eq_leviCharacter_of_forall_trace_eq [CharZero K] (h : IsPolynomialLeviRep ρ)
    (χ : MvPolynomial (Σ p : Fin s, Fin (d p)) ℤ)
    (hχ : ∀ t, MvPolynomial.eval₂ (Int.castRingHom K) (fun i => (t i : K)) χ =
      LinearMap.trace K W (ρ (leviTorus K d t))) :
    χ = leviCharacter ρ :=
  eq_torusCharacter_of_forall_trace_eq h.comp_leviTorus χ hχ

theorem leviCharacter_eq_of_equiv [CharZero K] (hρ : IsPolynomialLeviRep ρ)
    (hσ : IsPolynomialLeviRep σ) (e : ρ.Equiv σ) : leviCharacter ρ = leviCharacter σ :=
  torusCharacter_eq_of_equiv hρ.comp_leviTorus hσ.comp_leviTorus (equivComp e _)

theorem leviCharacter_prod [CharZero K] (hρ : IsPolynomialLeviRep ρ)
    (hσ : IsPolynomialLeviRep σ) :
    leviCharacter (ρ.prod σ) = leviCharacter ρ + leviCharacter σ := by
  rw [leviCharacter, prod_comp]
  exact torusCharacter_prod hρ.comp_leviTorus hσ.comp_leviTorus

theorem leviCharacter_tprod [CharZero K] (hρ : IsPolynomialLeviRep ρ)
    (hσ : IsPolynomialLeviRep σ) :
    leviCharacter (ρ.tprod σ) = leviCharacter ρ * leviCharacter σ := by
  rw [leviCharacter, tprod_comp]
  exact torusCharacter_tprod hρ.comp_leviTorus hσ.comp_leviTorus

/-- The variables of block `p` inside the variables of the Levi torus. -/
def blockVar (p : Fin s) (i : Fin (d p)) : Σ q : Fin s, Fin (d q) := ⟨p, i⟩

/-- **The character of an external tensor product** is the product over the blocks of the
characters of the factors, each written in the variables of its block. -/
theorem leviCharacter_extTensor [CharZero K] {V' : Fin s → Type*} [∀ p, AddCommGroup (V' p)]
    [∀ p, Module K (V' p)] {ρ' : (p : Fin s) → Representation K (GL (Fin (d p)) K) (V' p)}
    (h : ∀ p, IsPolynomialRep (ρ' p)) :
    leviCharacter (extTensor ρ') = ∏ p, MvPolynomial.rename (blockVar p) (character (ρ' p)) := by
  have := fun p => (h p).finiteDimensional
  refine (eq_leviCharacter_of_forall_trace_eq (isPolynomialLeviRep_extTensor h) _
    fun t => ?_).symm
  rw [MvPolynomial.eval₂_prod]
  simp_rw [MvPolynomial.eval₂_rename]
  change _ = LinearMap.trace K _ (PiTensorProduct.map fun p => ρ' p (leviTorus K d t p))
  rw [trace_piTensorProduct_map]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [leviTorus_apply, trace_diagGL_eq_eval_character (h p)]
  rfl

end Character

end

end GLRep
