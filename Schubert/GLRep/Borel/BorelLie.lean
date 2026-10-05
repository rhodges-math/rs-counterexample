import Schubert.GLRep.Borel.BorelStabilityDifferential

/-!
# Rational representations of `B` and their differentials

Let `ρ` be a rational representation of the Borel subgroup `B ⊆ GL_n(K)`, `K` infinite of
characteristic zero. Along the upper transvections `u_ab(t) = 1 + tE_ab` (`a < b`,
`GLRep.upperTransvection`), `t ↦ ρ(u_ab(t))` is a polynomial with values in `End W` and a
one-parameter group, hence an exponential:

  `ρ(u_ab(t)) = Σ_k t^k/k! · D_ab^k` (`GLRep.IsRationalBorelRep.exists_rho_upperTransvection_eq`),

with `D_ab = dρ(E_ab)` (`GLRep.IsRationalBorelRep.borelLie`) the unique linear coefficient
(`GLRep.IsRationalBorelRep.borelLie_eq_of_forall`). This gives the dictionary between `B` and
`𝔟 = 𝔱 ⊕ 𝔫⁺`, for every rational representation of `B`:

* a subspace is `B`-stable iff it is stable under the torus and under the `D_ab`, `a < b`
  (`GLRep.IsRationalBorelRep.forall_mem_iff`);
* a linear map between rational representations commutes with `B` iff it commutes with the torus
  and with the `D_ab` (`GLRep.IsRationalBorelRep.forall_intertwining_iff`);
* the torus normalizes the `D_ab`: `ρ(t) D_ab ρ(t)⁻¹ = (t_a/t_b) D_ab`
  (`GLRep.IsRationalBorelRep.conj_borelLie`);
* for the restriction of a polynomial representation of `GL_n`, `D_ab` is the differential
  `dρ(E_ab)` of GLRep (`GLRep.IsRationalBorelRep.borelLie_restrictBorel`).
-/

namespace GLRep

open Module Polynomial TauCeti

noncomputable section

variable {K : Type*} [Field K] {n : ℕ}

/-! ### Coefficients of polynomial expansions -/

section Coefficients

variable {E : Type*} [AddCommGroup E] [Module K E]

theorem sum_range_ite_lt (f : ℕ → E) {N M : ℕ} (hNM : N ≤ M) :
    ∑ k ∈ Finset.range M, (if k < N then f k else 0) = ∑ k ∈ Finset.range N, f k := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  refine Finset.sum_congr (Finset.ext fun k => ?_) fun _ _ => rfl
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

/-- **Uniqueness of polynomial expansions** over an infinite field. -/
theorem coeff_eq_of_forall_sum_eq [Infinite K] {N₁ N₂ : ℕ} (A B : ℕ → E)
    (h : ∀ t : K, ∑ k ∈ Finset.range N₁, t ^ k • A k = ∑ k ∈ Finset.range N₂, t ^ k • B k)
    {k : ℕ} (h₁ : k < N₁) (h₂ : k < N₂) : A k = B k := by
  let C : ℕ → E := fun k => (if k < N₁ then A k else 0) - (if k < N₂ then B k else 0)
  have hC : ∀ t : K, ∑ k ∈ Finset.range (max N₁ N₂), t ^ k • C k ∈ (⊥ : Submodule K E) := by
    intro t
    rw [Submodule.mem_bot]
    simp only [C, smul_sub, smul_ite, smul_zero, Finset.sum_sub_distrib]
    rw [sum_range_ite_lt _ (le_max_left _ _), sum_range_ite_lt _ (le_max_right _ _), h t,
      sub_self]
  have := mem_of_forall_sum_pow_smul_mem ⊥ C hC (k := k) (lt_max_of_lt_left h₁)
  rw [Submodule.mem_bot] at this
  simpa only [C, h₁, h₂, ite_true, sub_eq_zero] using this

end Coefficients

/-! ### Upper transvections in `B` -/

/-- The upper transvection `u_ab(t) = 1 + tE_ab` (`a < b`) as an element of `B`. -/
def upperTransvection {a b : Fin n} (hab : a < b) (t : K) : borel K n :=
  ⟨transvectionGL hab.ne t, transvectionGL_mem_borel hab t⟩

variable {a b : Fin n}

theorem coe_upperTransvection (hab : a < b) (t : K) :
    ((upperTransvection hab t : borel K n) : GL (Fin n) K) = transvectionGL hab.ne t :=
  rfl

theorem upperTransvection_add (hab : a < b) (s t : K) :
    upperTransvection hab (s + t) = upperTransvection hab s * upperTransvection hab t := by
  refine Subtype.ext (Units.ext ?_)
  rw [Subgroup.coe_mul, Units.val_mul, coe_upperTransvection, coe_upperTransvection,
    coe_upperTransvection, coe_transvectionGL, coe_transvectionGL, coe_transvectionGL,
    Matrix.transvection_mul_transvection_same (h := hab.ne)]

theorem upperTransvection_zero (hab : a < b) : upperTransvection hab (0 : K) = 1 :=
  Subtype.ext (transvectionGL_zero hab.ne)

theorem borelDiag_upperTransvection (hab : a < b) (t : K) :
    borelDiag K n (upperTransvection hab t) = 1 := by
  funext k
  refine Units.ext ?_
  rw [borelDiag_apply_val, Pi.one_apply, Units.val_one, coe_upperTransvection,
    coe_transvectionGL, Matrix.transvection, Matrix.add_apply, Matrix.one_apply_eq,
    Matrix.single_apply, ite_eq_right_iff.mpr fun h => absurd (h.1.trans h.2.symm) hab.ne,
    add_zero]

/-- A function polynomial in coordinates is a polynomial along a curve whose coordinates are
polynomials. -/
theorem exists_polynomial_of_mem_coordFunctions {G σ : Type*} {c : G → σ → K} (γ : K → G)
    (hγ : ∀ s, ∃ q : K[X], ∀ t, c (γ t) s = q.eval t) {f : G → K}
    (hf : f ∈ coordFunctions K c) : ∃ q : K[X], ∀ t, f (γ t) = q.eval t := by
  choose qs hqs using hγ
  obtain ⟨P, hP⟩ := mem_coordFunctions.mp hf
  refine ⟨MvPolynomial.aeval qs P, fun t => ?_⟩
  rw [hP]
  clear hP hf
  induction P using MvPolynomial.induction_on with
  | C x => simp
  | add p q hp hq => rw [map_add, map_add, eval_add, hp, hq]
  | mul_X p s hp => rw [map_mul, map_mul, eval_mul, hp, MvPolynomial.eval_X,
      MvPolynomial.aeval_X, hqs]

/-- **Regular functions on `B` are polynomials along the upper transvections.** -/
theorem exists_polynomial_borelFunctions (hab : a < b) {f : borel K n → K}
    (hf : f ∈ borelFunctions K n) : ∃ q : K[X], ∀ t, f (upperTransvection hab t) = q.eval t := by
  classical
  refine exists_polynomial_of_mem_coordFunctions _ (fun s => ?_) hf
  rcases s with ⟨i, j⟩ | i
  · refine ⟨C (if i = j then 1 else 0) + (if a = i ∧ b = j then X else 0), fun t => ?_⟩
    rw [borelCoord_inl, coe_upperTransvection, coe_transvectionGL, Matrix.transvection,
      Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, eval_add, eval_C]
    split_ifs <;> simp
  · refine ⟨C 1, fun t => ?_⟩
    rw [borelCoord_inr, borelDiag_upperTransvection, Pi.one_apply, inv_one, Units.val_one,
      eval_C]

/-! ### The differential along `u_ab` -/

namespace IsRationalBorelRep

variable {W : Type*} [AddCommGroup W] [Module K W] {ρ : Representation K (borel K n) W}
variable (hρ : IsRationalBorelRep ρ)

/-- The index type of the basis `Module.finBasis K W`. -/
abbrev BorelLieIndex (W : Type*) [AddCommGroup W] [Module K W] := Fin (finrank K W)

/-- The basis `Module.finBasis K W`. -/
def basis : Basis (BorelLieIndex (K := K) W) K W :=
  have := hρ.finiteDimensional
  Module.finBasis K W

theorem exists_lineMatrix (hab : a < b) :
    ∃ Q : Matrix (BorelLieIndex (K := K) W) (BorelLieIndex (K := K) W) K[X], ∀ t,
      Q.map (eval t) = LinearMap.toMatrix hρ.basis hρ.basis (ρ (upperTransvection hab t)) := by
  choose Q hQ using fun i j : BorelLieIndex (K := K) W =>
    exists_polynomial_borelFunctions hab (hρ.coeff_mem (hρ.basis.coord i) (hρ.basis j))
  refine ⟨Matrix.of Q, fun t => Matrix.ext fun i j => ?_⟩
  rw [Matrix.map_apply, Matrix.of_apply, ← hQ, LinearMap.toMatrix_apply, Basis.coord_apply]

/-- The matrix of `t ↦ ρ(u_ab(t))`, a matrix of polynomials. -/
def lineMatrix (hab : a < b) : Matrix (BorelLieIndex (K := K) W) (BorelLieIndex (K := K) W) K[X] :=
  (hρ.exists_lineMatrix hab).choose

theorem lineMatrix_eval (hab : a < b) (t : K) :
    (hρ.lineMatrix hab).map (eval t) =
      LinearMap.toMatrix hρ.basis hρ.basis (ρ (upperTransvection hab t)) :=
  (hρ.exists_lineMatrix hab).choose_spec t

/-- The matrix of the differential `D_ab`: the derivative at `0`. -/
def lieMatrix (hab : a < b) : Matrix (BorelLieIndex (K := K) W) (BorelLieIndex (K := K) W) K :=
  (hρ.lineMatrix hab).map fun q => (derivative q).eval 0

variable [Infinite K]

/-- `Q'(t) = D · Q(t)`, from the one-parameter group law. -/
theorem derivative_lineMatrix_eval (hab : a < b) (t : K) :
    (hρ.lineMatrix hab).map (fun q => (derivative q).eval t) =
      hρ.lieMatrix hab * (hρ.lineMatrix hab).map (eval t) := by
  have hM : ∀ s, (hρ.lineMatrix hab).map (eval (s + t)) =
      (hρ.lineMatrix hab).map (eval s) * (hρ.lineMatrix hab).map (eval t) := by
    intro s
    rw [lineMatrix_eval, lineMatrix_eval, lineMatrix_eval, upperTransvection_add, map_mul,
      LinearMap.toMatrix_mul]
  set Q := hρ.lineMatrix hab
  set M := fun s : K => Q.map (eval s)
  ext i j
  -- the polynomial identity `Q(X + t) = Q(X) M(t)` in the entry `(i, j)`
  have hpoly : (Q i j).comp (X + C t) = ∑ k, Q i k * C (M t k j) := by
    refine Polynomial.funext fun s => ?_
    rw [eval_comp, eval_add, eval_X, eval_C, eval_finsetSum]
    have := congrFun (congrFun (hM s) i) j
    simp only [Matrix.map_apply, Matrix.mul_apply] at this
    rw [this]
    exact Finset.sum_congr rfl fun k _ => by rw [eval_mul, eval_C]; rfl
  have hd := congrArg (fun p => (derivative p).eval 0) hpoly
  simp only [derivative_comp, derivative_add, derivative_X, derivative_C, add_zero, one_mul,
    eval_comp, eval_add, eval_X, eval_C, zero_add, derivative_sum, derivative_mul, mul_zero,
    eval_finsetSum, eval_mul] at hd
  rw [Matrix.map_apply, hd, Matrix.mul_apply]
  rfl

theorem derivative_lineMatrix (hab : a < b) :
    (hρ.lineMatrix hab).map derivative = (hρ.lieMatrix hab).map C * hρ.lineMatrix hab := by
  refine Matrix.ext fun i j => ?_
  refine Polynomial.funext fun t => ?_
  have := congrFun (congrFun (hρ.derivative_lineMatrix_eval hab t) i) j
  rw [Matrix.map_apply, Matrix.mul_apply] at this
  rw [Matrix.map_apply, this, Matrix.mul_apply, eval_finsetSum]
  exact Finset.sum_congr rfl fun k _ => by simp only [eval_mul, Matrix.map_apply, eval_C]

/-- The coefficient matrices `A_k` of `t ↦ ρ(u_ab(t))`. -/
def coeffMatrix (hab : a < b) (k : ℕ) : Matrix (BorelLieIndex (K := K) W) (BorelLieIndex (K := K) W)
    K :=
  (hρ.lineMatrix hab).map fun q => q.coeff k

omit [Infinite K] in
theorem coeffMatrix_zero (hab : a < b) : hρ.coeffMatrix hab 0 = 1 := by
  have h := hρ.lineMatrix_eval hab 0
  rw [upperTransvection_zero, map_one, LinearMap.toMatrix_one] at h
  rw [← h]
  ext i j
  rw [coeffMatrix, Matrix.map_apply, Matrix.map_apply, coeff_zero_eq_eval_zero]

theorem coeffMatrix_succ [CharZero K] (hab : a < b) (k : ℕ) :
    hρ.coeffMatrix hab (k + 1) =
      ((k + 1 : ℕ) : K)⁻¹ • (hρ.lieMatrix hab * hρ.coeffMatrix hab k) := by
  have hk : (k : K) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  refine Matrix.ext fun i j => ?_
  have h := congrArg (fun q => q.coeff k)
    (congrFun (congrFun (hρ.derivative_lineMatrix hab) i) j)
  simp only [Matrix.map_apply, coeff_derivative, Matrix.mul_apply, finsetSum_coeff, coeff_C_mul]
    at h
  simp only [coeffMatrix, Matrix.smul_apply, Matrix.mul_apply, Matrix.map_apply, smul_eq_mul]
  rw [← h]
  push_cast
  field_simp

/-- **`A_k = D^k / k!`.** -/
theorem coeffMatrix_eq_pow (hab : a < b) [CharZero K] (k : ℕ) :
    hρ.coeffMatrix hab k = ((k.factorial : ℕ) : K)⁻¹ • hρ.lieMatrix hab ^ k := by
  induction k with
  | zero => rw [hρ.coeffMatrix_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul, pow_zero]
  | succ k ih =>
    rw [hρ.coeffMatrix_succ, ih, Matrix.mul_smul, smul_smul, pow_succ', Nat.factorial_succ,
      Nat.cast_mul, mul_inv]

/-- **The differential `D_ab = dρ(E_ab)`** of a rational representation of `B`. -/
def borelLie (hab : a < b) : Module.End K W :=
  Matrix.toLin hρ.basis hρ.basis (hρ.lieMatrix hab)

/-- **The exponential formula** `ρ(u_ab(t)) = Σ_k t^k/k! · D_ab^k`, a finite sum: it holds for
every bound `M ≥ N`. -/
theorem exists_rho_upperTransvection_eq [CharZero K] (hab : a < b) :
    ∃ N : ℕ, 1 < N ∧ ∀ M, N ≤ M → ∀ t : K, ρ (upperTransvection hab t) =
      ∑ k ∈ Finset.range M, t ^ k • (((k.factorial : ℕ) : K)⁻¹ • hρ.borelLie hab ^ k) := by
  classical
  let N := (Finset.univ.sup fun ij : BorelLieIndex (K := K) W × BorelLieIndex (K := K) W =>
    (hρ.lineMatrix hab ij.1 ij.2).natDegree) + 2
  refine ⟨N, by omega, fun M hM t => ?_⟩
  apply (LinearMap.toMatrix hρ.basis hρ.basis).injective
  rw [← hρ.lineMatrix_eval hab t, map_sum]
  refine Matrix.ext fun i j => ?_
  have hdeg : (hρ.lineMatrix hab i j).natDegree < M := by
    have := Finset.le_sup (f := fun ij : BorelLieIndex (K := K) W × BorelLieIndex (K := K) W =>
      (hρ.lineMatrix hab ij.1 ij.2).natDegree) (Finset.mem_univ (i, j))
    simp only at this
    omega
  rw [Matrix.map_apply, eval_eq_sum_range' hdeg, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, map_smul, borelLie, ← Matrix.toLin_pow, LinearMap.toMatrix_toLin,
    ← hρ.coeffMatrix_eq_pow, Matrix.smul_apply, coeffMatrix, Matrix.map_apply,
    smul_eq_mul, mul_comm]

/-- **Uniqueness**: any polynomial expansion of `t ↦ ρ(u_ab(t))` has linear coefficient
`D_ab`. -/
theorem borelLie_eq_of_forall [CharZero K] (hab : a < b) {N : ℕ} (hN : 1 < N)
    (A : ℕ → Module.End K W) (hA : ∀ t : K, ρ (upperTransvection hab t) =
      ∑ k ∈ Finset.range N, t ^ k • A k) : hρ.borelLie hab = A 1 := by
  obtain ⟨M, hM, hρM⟩ := hρ.exists_rho_upperTransvection_eq hab
  have := coeff_eq_of_forall_sum_eq (K := K)
    (fun k => ((k.factorial : ℕ) : K)⁻¹ • hρ.borelLie hab ^ k) A
    (fun t => (hρM M le_rfl t).symm.trans (hA t)) hM hN
  simpa using this

/-! ### Stability and intertwiners -/

theorem borelLie_mem_of_forall [CharZero K] (hab : a < b) (U : Submodule K W)
    (hU : ∀ t, ∀ u ∈ U, ρ (upperTransvection hab t) u ∈ U) :
    ∀ u ∈ U, hρ.borelLie hab u ∈ U := by
  intro u hu
  obtain ⟨N, hN, hρN⟩ := hρ.exists_rho_upperTransvection_eq hab
  have key := mem_of_forall_sum_pow_smul_mem U
    (fun k => (((k.factorial : ℕ) : K)⁻¹ • hρ.borelLie hab ^ k) u)
    (fun t => by
      have := hU t u hu
      rw [hρN N le_rfl t, LinearMap.sum_apply] at this
      simpa only [LinearMap.smul_apply] using this) (k := 1) hN
  simpa using key

theorem mem_of_borelLie_mem [CharZero K] (hab : a < b) (U : Submodule K W)
    (hU : ∀ u ∈ U, hρ.borelLie hab u ∈ U) (t : K) :
    ∀ u ∈ U, ρ (upperTransvection hab t) u ∈ U := by
  intro u hu
  have hpow : ∀ k, ∀ u ∈ U, (hρ.borelLie hab ^ k) u ∈ U := by
    intro k
    induction k with
    | zero => intro u hu; simpa using hu
    | succ k ih =>
      intro u hu
      rw [pow_succ, Module.End.mul_apply]
      exact ih _ (hU u hu)
  obtain ⟨N, -, hρN⟩ := hρ.exists_rho_upperTransvection_eq hab
  rw [hρN N le_rfl t, LinearMap.sum_apply]
  exact Submodule.sum_mem _ fun k _ => by
    rw [LinearMap.smul_apply, LinearMap.smul_apply]
    exact U.smul_mem _ (U.smul_mem _ (hpow k u hu))

omit [Infinite K] in
/-- **Induction over `B`** for properties of elements of the subgroup: generators are the torus and
the upper transvections. -/
theorem _root_.GLRep.borel_induction' {P : borel K n → Prop}
    (hmul : ∀ g h, P g → P h → P (g * h))
    (htv : ∀ {a b : Fin n} (hab : a < b) (t : K), P (upperTransvection hab t))
    (hdiag : ∀ t, P (borelTorus K n t)) (g : borel K n) : P g := by
  obtain ⟨g, hg⟩ := g
  have key := borel_induction (K := K)
    (P := fun g => g ∈ borel K n ∧ ∀ hg : g ∈ borel K n, P ⟨g, hg⟩)
    (fun g h hPg hPh => ⟨mul_mem hPg.1 hPh.1, fun _ => hmul _ _ (hPg.2 hPg.1) (hPh.2 hPh.1)⟩)
    (fun hab t => ⟨transvectionGL_mem_borel hab t, fun _ => htv hab t⟩)
    (fun t => ⟨(borelTorus K n t).2, fun _ => hdiag t⟩) hg
  exact key.2 hg

/-- **The differential criterion for subspaces**: a subspace is `B`-stable iff it is stable under
the torus and under the differentials `D_ab`, `a < b`. -/
theorem forall_mem_iff [CharZero K] (U : Submodule K W) :
    (∀ g, ∀ u ∈ U, ρ g u ∈ U) ↔ (∀ t, ∀ u ∈ U, ρ (borelTorus K n t) u ∈ U) ∧
      ∀ (a b : Fin n) (hab : a < b), ∀ u ∈ U, hρ.borelLie hab u ∈ U := by
  constructor
  · intro h
    exact ⟨fun t => h _, fun a b hab => hρ.borelLie_mem_of_forall hab U fun t => h _⟩
  · rintro ⟨hT, hL⟩ g
    refine borel_induction' (P := fun g => ∀ u ∈ U, ρ g u ∈ U) ?_ ?_ hT g
    · intro g g₁ hg hg₁ u hu
      rw [map_mul, Module.End.mul_apply]
      exact hg _ (hg₁ u hu)
    · intro a b hab t
      exact hρ.mem_of_borelLie_mem hab U (hL a b hab) t

variable {V : Type*} [AddCommGroup V] [Module K V] {σ : Representation K (borel K n) V}

/-- **The differential criterion for maps**: a linear map between rational representations of `B`
commutes with `B` iff it commutes with the torus and with the differentials `D_ab`, `a < b`. -/
theorem forall_intertwining_iff [CharZero K] (hσ : IsRationalBorelRep σ) (f : W →ₗ[K] V) :
    (∀ g w, f (ρ g w) = σ g (f w)) ↔
      (∀ t w, f (ρ (borelTorus K n t) w) = σ (borelTorus K n t) (f w)) ∧
        ∀ (a b : Fin n) (hab : a < b) (w : W),
          f (hρ.borelLie hab w) = hσ.borelLie hab (f w) := by
  constructor
  · intro h
    refine ⟨fun t => h _, fun a b hab => ?_⟩
    obtain ⟨N₁, hN₁, h₁⟩ := hρ.exists_rho_upperTransvection_eq hab
    obtain ⟨N₂, hN₂, h₂⟩ := hσ.exists_rho_upperTransvection_eq hab
    have key := coeff_eq_of_forall_sum_eq (K := K) (E := W →ₗ[K] V)
      (fun k => f ∘ₗ (((k.factorial : ℕ) : K)⁻¹ • hρ.borelLie hab ^ k))
      (fun k => (((k.factorial : ℕ) : K)⁻¹ • hσ.borelLie hab ^ k) ∘ₗ f)
      (fun t => by
        refine LinearMap.ext fun w => ?_
        have hw := h (upperTransvection hab t) w
        rw [h₁ N₁ le_rfl t, h₂ N₂ le_rfl t] at hw
        simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul] at hw
        simpa only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
          map_smul] using hw)
      hN₁ hN₂
    intro w
    simpa using LinearMap.congr_fun key w
  · rintro ⟨hT, hL⟩ g
    refine borel_induction' (P := fun g => ∀ w, f (ρ g w) = σ g (f w)) ?_ ?_ hT g
    · intro g g₁ hg hg₁ w
      rw [map_mul, Module.End.mul_apply, hg, hg₁, map_mul, Module.End.mul_apply]
    · intro a b hab t w
      have hpow : ∀ k w, f ((hρ.borelLie hab ^ k) w) = (hσ.borelLie hab ^ k) (f w) := by
        intro k
        induction k with
        | zero => intro w; rfl
        | succ k ih =>
          intro w
          rw [pow_succ, Module.End.mul_apply, ih, hL a b hab, pow_succ, Module.End.mul_apply]
      obtain ⟨N₁, -, h₁⟩ := hρ.exists_rho_upperTransvection_eq hab
      obtain ⟨N₂, -, h₂⟩ := hσ.exists_rho_upperTransvection_eq hab
      rw [h₁ (max N₁ N₂) (le_max_left _ _) t, h₂ (max N₁ N₂) (le_max_right _ _) t,
        LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [LinearMap.smul_apply, map_smul, hpow]

omit [Infinite K] in
/-- The torus normalizes the upper transvections: `t u_ab(s) t⁻¹ = u_ab((t_a/t_b) s)`. -/
theorem borelTorus_mul_upperTransvection (hab : a < b) (t : Fin n → Kˣ) (s : K) :
    borelTorus K n t * upperTransvection hab s * (borelTorus K n t)⁻¹ =
      upperTransvection hab (((t a / t b : Kˣ) : K) * s) := by
  refine Subtype.ext (Units.ext ?_)
  simp only [Subgroup.coe_mul, Units.val_mul, coe_borelTorus,
    coe_upperTransvection, coe_transvectionGL, ← map_inv, diagGL_coe]
  ext i j
  simp only [Matrix.transvection, Matrix.mul_add, Matrix.mul_one, Matrix.add_apply,
    Matrix.diagonal_apply, Matrix.one_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.single_apply, Pi.inv_apply,
    Units.val_div_eq_div_val]
  by_cases hij : i = j
  · subst hij
    have hai : ¬(a = i ∧ b = i) := fun h => hab.ne (h.1.trans h.2.symm)
    simp [hai]
  · by_cases h : a = i ∧ b = j
    · obtain ⟨rfl, rfl⟩ := h
      simp [hij]
      field_simp
    · simp [hij, h]

/-- **The torus normalizes the differentials**: `ρ(t) D_ab ρ(t)⁻¹ = (t_a/t_b) D_ab`. -/
theorem conj_borelLie [CharZero K] (hab : a < b) (t : Fin n → Kˣ) :
    ρ (borelTorus K n t) * hρ.borelLie hab * ρ (borelTorus K n t)⁻¹ =
      ((t a / t b : Kˣ) : K) • hρ.borelLie hab := by
  obtain ⟨N, hN, hρN⟩ := hρ.exists_rho_upperTransvection_eq hab
  set c : K := ((t a / t b : Kˣ) : K)
  have key := coeff_eq_of_forall_sum_eq (K := K) (E := Module.End K W)
    (fun k => ρ (borelTorus K n t) * (((k.factorial : ℕ) : K)⁻¹ • hρ.borelLie hab ^ k) *
      ρ (borelTorus K n t)⁻¹)
    (fun k => c ^ k • (((k.factorial : ℕ) : K)⁻¹ • hρ.borelLie hab ^ k))
    (fun s => by
      have h := congrArg ρ (borelTorus_mul_upperTransvection hab t s)
      rw [map_mul, map_mul, hρN N le_rfl s, hρN N le_rfl (c * s)] at h
      rw [Finset.mul_sum, Finset.sum_mul] at h
      simp only [mul_smul_comm, smul_mul_assoc, mul_pow, smul_smul] at h ⊢
      refine h.trans (Finset.sum_congr rfl fun k _ => ?_)
      congr 1
      ring)
    hN hN
  simpa using key

/-- **For the restriction of a polynomial representation of `GL_n`, `D_ab` is GLRep's
differential `dρ(E_ab)`.** -/
theorem borelLie_restrictBorel [CharZero K] {ρ : Representation K (GL (Fin n) K) W}
    (h : IsPolynomialRep ρ) (hab : a < b) :
    h.restrictBorel.borelLie hab = h.lie (Matrix.single a b 1) := by
  rw [h.restrictBorel.borelLie_eq_of_forall hab (N := h.curveDegree (Matrix.single a b 1) + 2)
    (by omega) (fun k => ((k.factorial : ℕ) : K)⁻¹ • h.lie (Matrix.single a b 1) ^ k)
    (fun t => by
      rw [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
        coe_upperTransvection, h.rho_transvectionGL_eq hab.ne t]
      exact Finset.sum_congr rfl fun k _ => by rw [smul_smul])]
  simp

end IsRationalBorelRep

end

end GLRep
