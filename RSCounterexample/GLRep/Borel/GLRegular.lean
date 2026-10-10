import RSCounterexample.GLRep.Borel.Evaluation

/-!
# Regular functions on `GL_n` and the induced representations `ind_B^G(η)`

The **regular functions** on `GL_n(K)` are the polynomials in the matrix entries `g_ij` and in
`det(g)⁻¹` (`GLRep.glRegularFunctions K n`). A finite-dimensional representation of `GL_n(K)` has
regular matrix coefficients exactly when it is rational in the sense of `GLRep.IsRationalRep`
(some twist by a power of the determinant is polynomial):
`GLRep.isRationalRep_iff_hasCoeffsIn_glRegularFunctions`.

The left regular representation of `GL_n(K)` on `𝒪(GL_n)` has regular matrix coefficients
(`GLRep.hasLocalCoeffsIn_leftRegularRep`). Its subrepresentation of `(B, η)`-semi-invariants
under right translation is the induced representation `ind_B^G(η) = 𝒪(GL_n)^{(B, η)}`
(`GLRep.indBorelRep`), the space of global sections of the line bundle `𝓛(η)` on `G/B`; its
finite-dimensional subrepresentations are rational
(`GLRep.isRationalRep_of_injective_indBorelRep`).
-/

namespace GLRep

open MvPolynomial TauCeti

noncomputable section

/-! ### Regular functions -/

section Functions

variable (K : Type*) [CommRing K] (n : ℕ)

/-- The coordinates of `g ∈ GL_n(K)`: the matrix entries `g_ij` (index `Sum.inl (i, j)`) and
`det(g)⁻¹` (index `Sum.inr ()`). -/
def glRationalCoord (g : GL (Fin n) K) : (Fin n × Fin n) ⊕ Unit → K :=
  Sum.elim (fun p => (g : Matrix (Fin n) (Fin n) K) p.1 p.2)
    fun _ => ((Matrix.GeneralLinearGroup.det g)⁻¹ : Kˣ)

/-- The **regular functions** on `GL_n(K)`: polynomials in the entries and in `det⁻¹`. -/
abbrev glRegularFunctions : Subalgebra K (GL (Fin n) K → K) :=
    coordFunctions K (glRationalCoord K n)

variable {K n}

theorem entry_mem_glRegularFunctions (i j : Fin n) :
    (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K) i j) ∈ glRegularFunctions K n :=
  coord_mem_coordFunctions (glRationalCoord K n) (Sum.inl (i, j))

theorem detInv_mem_glRegularFunctions :
    (fun g : GL (Fin n) K => (((Matrix.GeneralLinearGroup.det g)⁻¹ : Kˣ) : K)) ∈
      glRegularFunctions K n :=
  coord_mem_coordFunctions (glRationalCoord K n) (Sum.inr ())

theorem det_mem_glRegularFunctions :
    (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K).det) ∈ glRegularFunctions K n :=
  mem_coordFunctions.mpr ⟨rename Sum.inl (genericDet K n), fun g => by
    rw [eval_rename]
    exact ((glEval_algebraMap g _).symm.trans (glEval_genericDet g)).symm⟩

theorem adjugate_mem_glRegularFunctions (i k : Fin n) :
    (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K).adjugate i k) ∈
      glRegularFunctions K n := by
  refine mem_coordFunctions.mpr
    ⟨rename Sum.inl ((Matrix.mvPolynomialX (Fin n) (Fin n) K).adjugate i k), fun g => ?_⟩
  rw [eval_rename]
  have h1 : (glRationalCoord K n g ∘ Sum.inl) =
      fun p : Fin n × Fin n => (g : Matrix (Fin n) (Fin n) K) p.1 p.2 := rfl
  rw [h1]
  conv_lhs => rw [← Matrix.mvPolynomialX_mapMatrix_eval (g : Matrix (Fin n) (Fin n) K)]
  rw [← RingHom.map_adjugate]
  rfl

/-- The entries of `g⁻¹` are regular functions on `GL_n(K)`. -/
theorem inv_apply_mem_glRegularFunctions (i k : Fin n) :
    (fun g : GL (Fin n) K => ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i k) ∈
      glRegularFunctions K n := by
  have : (fun g : GL (Fin n) K => ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i k) =
      (fun g : GL (Fin n) K => (((Matrix.GeneralLinearGroup.det g)⁻¹ : Kˣ) : K)) *
        fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K).adjugate i k := by
    funext g
    rw [Matrix.coe_units_inv, Matrix.inv_def, Pi.mul_apply, Matrix.smul_apply, smul_eq_mul,
      ← Matrix.GeneralLinearGroup.val_det_apply, Ring.inverse_unit]
  rw [this]
  exact mul_mem detInv_mem_glRegularFunctions (adjugate_mem_glRegularFunctions i k)

/-- Regular functions on `GL_n(K)` restrict to regular functions on `B`. -/
theorem comp_borel_subtype_mem_of_glRegular {f : GL (Fin n) K → K}
    (hf : f ∈ glRegularFunctions K n) : f ∘ (borel K n).subtype ∈ borelFunctions K n := by
  refine comp_mem_of_forall_coord_mem _ (fun s => ?_) hf
  rcases s with p | u
  · exact coord_mem_coordFunctions (borelCoord K n) (Sum.inl p)
  · have : (fun b : borel K n => glRationalCoord K n ((borel K n).subtype b) (Sum.inr u)) =
        ∏ l, fun b : borel K n => (((borelDiag K n b l)⁻¹ : Kˣ) : K) := by
      funext b
      change (((Matrix.GeneralLinearGroup.det (b : GL (Fin n) K))⁻¹ : Kˣ) : K) = _
      rw [det_borel, Finset.prod_apply, ← Finset.prod_inv_distrib, Units.coe_prod]
    rw [this]
    exact prod_mem fun l _ => diag_inv_mem_borelFunctions l

end Functions

/-! ### Regular coefficients and rationality -/

section Rational

variable {K : Type*} [Field K] {n : ℕ}
variable {W : Type*} [AddCommGroup W] [Module K W] {ρ : Representation K (GL (Fin n) K) W}

/-- The polynomial functions are regular. -/
theorem glPolynomialFunctions_le_glRegularFunctions :
    glPolynomialFunctions K n ≤ glRegularFunctions K n :=
  coordFunctions_le fun p => entry_mem_glRegularFunctions p.1 p.2

theorem detPow_mul_mem_of_le {f : GL (Fin n) K → K} {M N : ℕ} (hMN : M ≤ N)
    (hf : (fun g => (detPow K n M g : K)) * f ∈ glPolynomialFunctions K n) :
    (fun g => (detPow K n N g : K)) * f ∈ glPolynomialFunctions K n := by
  have : (fun g => (detPow K n N g : K)) * f =
      (fun g => (detPow K n (N - M) g : K)) * ((fun g => (detPow K n M g : K)) * f) := by
    funext g
    simp only [Pi.mul_apply, detPow_apply, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hMN]
  rw [this]
  exact mul_mem (detPow_mem _) hf

/-- **Every regular function on `GL_n(K)` becomes polynomial after multiplication by a power of
the determinant.** -/
theorem exists_detPow_mul_mem {f : GL (Fin n) K → K} (hf : f ∈ glRegularFunctions K n) :
    ∃ N : ℕ, (fun g => (detPow K n N g : K)) * f ∈ glPolynomialFunctions K n := by
  rw [glRegularFunctions, coordFunctions_eq_adjoin] at hf
  induction hf using Algebra.adjoin_induction with
  | mem f hf =>
    obtain ⟨s, rfl⟩ := hf
    rcases s with p | u
    · exact ⟨0, by
        rw [show (fun g => (detPow K n 0 g : K)) = 1 by funext g; simp [detPow_apply], one_mul]
        exact coord_mem_coordFunctions (glCoord K n) p⟩
    · refine ⟨1, ?_⟩
      have : (fun g => (detPow K n 1 g : K)) *
          (fun g : GL (Fin n) K => glRationalCoord K n g (Sum.inr u)) = 1 := by
        funext g
        change (detPow K n 1 g : K) * (((Matrix.GeneralLinearGroup.det g)⁻¹ : Kˣ) : K) = 1
        rw [detPow_apply, pow_one, ← Matrix.GeneralLinearGroup.val_det_apply, ← Units.val_mul,
          mul_inv_cancel, Units.val_one]
      rw [this]
      exact one_mem _
  | algebraMap c =>
    exact ⟨0, by
      rw [show (fun g => (detPow K n 0 g : K)) = 1 by funext g; simp [detPow_apply], one_mul]
      exact Subalgebra.algebraMap_mem _ c⟩
  | add f f' _ _ hf hf' =>
    obtain ⟨M, hM⟩ := hf
    obtain ⟨N, hN⟩ := hf'
    refine ⟨M + N, ?_⟩
    rw [mul_add]
    exact add_mem (detPow_mul_mem_of_le (by omega) hM) (detPow_mul_mem_of_le (by omega) hN)
  | mul f f' _ _ hf hf' =>
    obtain ⟨M, hM⟩ := hf
    obtain ⟨N, hN⟩ := hf'
    refine ⟨M + N, ?_⟩
    have : (fun g => (detPow K n (M + N) g : K)) * (f * f') =
        ((fun g => (detPow K n M g : K)) * f) * ((fun g => (detPow K n N g : K)) * f') := by
      funext g
      simp only [Pi.mul_apply, detPow_apply, pow_add]
      ring
    rw [this]
    exact mul_mem hM hN

/-- A representation of `GL_n(K)` with regular matrix coefficients is rational. -/
theorem HasCoeffsIn.isRationalRep_of_glRegularFunctions
    (h : HasCoeffsIn (glRegularFunctions K n) ρ) : IsRationalRep ρ := by
  classical
  have := h.finiteDimensional
  let b := Module.finBasis K W
  choose N hN using fun i j => exists_detPow_mul_mem (h.toMatrix_mem b i j)
  let M : ℕ := Finset.univ.sup fun ij : _ × _ => N ij.1 ij.2
  refine ⟨M, (hasCoeffsIn_iff_toMatrix b).mpr fun i j => ?_⟩
  have hle : N i j ≤ M :=
    Finset.le_sup (f := fun ij : _ × _ => N ij.1 ij.2) (Finset.mem_univ (i, j))
  have : (fun g => LinearMap.toMatrix b b (GLRep.scaledRep ρ (detPow K n M) g) i j) =
      (fun g => (detPow K n M g : K)) * fun g => LinearMap.toMatrix b b (ρ g) i j := by
    funext g
    simp only [LinearMap.toMatrix_apply, scaledRep_apply, map_smul, Finsupp.smul_apply,
      smul_eq_mul, Pi.mul_apply]
  rw [this]
  exact detPow_mul_mem_of_le hle (hN i j)

/-- A rational representation of `GL_n(K)` has regular matrix coefficients. -/
theorem IsRationalRep.hasCoeffsIn_glRegularFunctions (h : IsRationalRep ρ) :
    HasCoeffsIn (glRegularFunctions K n) ρ := by
  obtain ⟨k, hk⟩ := h
  refine ⟨hk.finiteDimensional, fun f w => ?_⟩
  have : (fun g => f (ρ g w)) =
      (fun g : GL (Fin n) K => (((Matrix.GeneralLinearGroup.det g)⁻¹ : Kˣ) : K) ^ k) *
        fun g => f (scaledRep ρ (detPow K n k) g w) := by
    funext g
    rw [Pi.mul_apply, scaledRep_apply, map_smul, smul_eq_mul, ← mul_assoc, detPow_apply,
      ← Matrix.GeneralLinearGroup.val_det_apply, ← Units.val_pow_eq_pow_val,
      ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← mul_pow, inv_mul_cancel, one_pow,
      Units.val_one, one_mul]
  rw [this]
  exact mul_mem (pow_mem detInv_mem_glRegularFunctions k)
    (glPolynomialFunctions_le_glRegularFunctions (hk.coeff_mem f w))

/-- **Rational representations of `GL_n(K)` are those with regular matrix coefficients.** -/
theorem isRationalRep_iff_hasCoeffsIn_glRegularFunctions :
    IsRationalRep ρ ↔ HasCoeffsIn (glRegularFunctions K n) ρ :=
  ⟨IsRationalRep.hasCoeffsIn_glRegularFunctions,
    HasCoeffsIn.isRationalRep_of_glRegularFunctions⟩

end Rational

/-! ### The left regular representation and `ind_B^G(η)` -/

section Induced

variable {K : Type*} [Field K] {n : ℕ}

/-- **The matrix coefficients of the left regular representation of `GL_n(K)` on `𝒪(GL_n)` are
regular functions.** -/
theorem hasLocalCoeffsIn_leftRegularRep :
    HasLocalCoeffsIn (glRegularFunctions K n) (leftRegularRep K n) := by
  refine hasLocalCoeffsIn_algebraRep (leftTranslHom K n) adjoin_glX_glDetInv ?_
  rintro r (⟨p, rfl⟩ | hr)
  · have : orbitAlgHom (leftTranslHom K n) (glX p.1 p.2) =
        fun g : GL (Fin n) K => ∑ k, (fun g : GL (Fin n) K =>
          ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) p.1 k) g • glX k p.2 := by
      funext g
      exact leftTranslHom_glX _ _ _
    rw [this]
    exact sum_smul_mem_range_coeffTensorHom _ _ (fun k _ => inv_apply_mem_glRegularFunctions _ k) _
  · rw [Set.mem_singleton_iff] at hr
    subst hr
    have : orbitAlgHom (leftTranslHom K n) (glDetInv K n) =
        fun g : GL (Fin n) K => (fun g : GL (Fin n) K =>
          (g : Matrix (Fin n) (Fin n) K).det) g • glDetInv K n := by
      funext g
      exact leftTranslHom_glDetInv _
    rw [this]
    exact smul_mem_range_coeffTensorHom det_mem_glRegularFunctions _

variable (K n) in
/-- The `(B, η)`-semi-invariants `𝒪(GL_n)^{(B, η)}`, as a subrepresentation of the left regular
representation of `GL_n(K)`. -/
def indBorelSubrep (η : Fin n → ℤ) : Subrepresentation (leftRegularRep K n) :=
  semiInvariantSubrep (leftRegularRep K n) ((rightRegularRep K n).comp (borel K n).subtype)
    (fun g b => leftRegularRep_comp_rightRegularRep g b) (borelChar K n η)

theorem mem_indBorelSubrep {η : Fin n → ℤ} {f : GLCoord K n} :
    f ∈ (indBorelSubrep K n η).toSubmodule ↔
      ∀ b : borel K n, rightTranslHom K n b f = (((borelChar K n η b)⁻¹ : Kˣ) : K) • f :=
  Iff.rfl

variable (K n) in
/-- The **induced representation** `ind_B^G(η) = 𝒪(GL_n)^{(B, η)}`: the regular functions with
`f(g b) = η(b)⁻¹ f(g)`, on which `GL_n(K)` acts by left translation. These are the global sections
of the line bundle `𝓛(η)` on `G/B`. -/
abbrev indBorelRep (η : Fin n → ℤ) :
    Representation K (GL (Fin n) K) (indBorelSubrep K n η).toSubmodule :=
  (indBorelSubrep K n η).toRepresentation

theorem hasLocalCoeffsIn_indBorelRep (η : Fin n → ℤ) :
    HasLocalCoeffsIn (glRegularFunctions K n) (indBorelRep K n η) :=
  hasLocalCoeffsIn_leftRegularRep.subrepresentation _

/-- **The finite-dimensional subrepresentations of `ind_B^G(η)` are rational**: a
finite-dimensional representation with an injective intertwining map into `ind_B^G(η)` is
rational. -/
theorem isRationalRep_of_injective_indBorelRep (η : Fin n → ℤ) {V : Type*} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {σ : Representation K (GL (Fin n) K) V}
    (φ : σ.IntertwiningMap (indBorelRep K n η)) (hφ : Function.Injective φ) :
    IsRationalRep σ :=
  ((hasLocalCoeffsIn_indBorelRep η).of_injective φ
    hφ).hasCoeffsIn.isRationalRep_of_glRegularFunctions

end Induced

end

end GLRep
