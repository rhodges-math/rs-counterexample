import RSCounterexample.GLRep.Borel.Frobenius
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Roots

/-!
# Vanishing of `ind_B^G(η)` for non-antidominant `η`

Over an infinite field, `ind_B^G(η) = 0` unless `η` is weakly increasing
(`GLRep.indBorelSubrep_eq_bot`). In geometric terms: `H⁰(G/B, 𝓛(−λ)) = 0` unless `λ` is dominant.

The proof is the rank-one computation. Let `η_i > η_j` with `i < j`, let `f ∈ ind_B^G(η)` and
`g ∈ GL_n(K)`. Along the lower transvection `v(z) = 1 + z E_ji` the function `z ↦ f(g v(z))` is
a polynomial `P` (`GLRep.exists_polynomial_glEval`). For `z ≠ 0`,
`v(z) = u(z⁻¹) w₀ t(z) u(z⁻¹)` with `u(c) = 1 + c E_ij`, a fixed `w₀`, and
`t(z) = diag(…, z, …, z⁻¹, …)` (`GLRep.transvectionGL_lower_eq`), so that
`z^{η_i − η_j} P(z) = R(z⁻¹)` for the polynomial `R(w) = f(g u(w) w₀)`. Comparing degrees forces
`P = 0` (`GLRep.eq_zero_of_forall_pow_mul_eval`), and `f(g) = P(0) = 0`.
-/

namespace GLRep

open Matrix Polynomial TauCeti

noncomputable section

variable {K : Type*} [Field K] {n : ℕ}

/-! ### Membership in `ind_B^G(η)` pointwise -/

theorem mem_indBorelSubrep_iff_glEval [Infinite K] {η : Fin n → ℤ} {f : GLCoord K n} :
    f ∈ (indBorelSubrep K n η).toSubmodule ↔ ∀ (g : GL (Fin n) K) (b : borel K n),
      glEval (g * (b : GL (Fin n) K)) f = (((borelChar K n η b)⁻¹ : Kˣ) : K) * glEval g f := by
  rw [mem_indBorelSubrep]
  constructor
  · intro h g b
    have := congrArg (glEval g) (h b)
    rwa [glEval_rightTranslHom, map_smul, smul_eq_mul] at this
  · intro h b
    refine glCoord_ext fun g => ?_
    rw [glEval_rightTranslHom, map_smul, smul_eq_mul]
    exact h g b

/-! ### Regular functions along polynomial families -/

/-- Along a family of invertible matrices with polynomial entries and constant determinant, a
regular function on `GL_n` is a polynomial. -/
theorem exists_polynomial_glEval (f : GLCoord K n) (A : Matrix (Fin n) (Fin n) K[X]) (c : Kˣ)
    (h : K → GL (Fin n) K)
    (hA : ∀ z, ((h z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = A.map (evalRingHom z))
    (hdet : ∀ z, Matrix.GeneralLinearGroup.det (h z) = c) :
    ∃ P : K[X], ∀ z, glEval (h z) f = P.eval z := by
  obtain ⟨⟨p, ⟨_, k, rfl⟩⟩, hpk⟩ := IsLocalization.surj (Submonoid.powers (genericDet K n)) f
  refine ⟨MvPolynomial.aeval (fun q : Fin n × Fin n => A q.1 q.2) p *
    Polynomial.C (((c ^ k)⁻¹ : Kˣ) : K), fun z => ?_⟩
  have h1 := congrArg (glEval (h z)) hpk
  simp only at h1
  rw [map_mul, map_pow, map_pow, glEval_genericDet, glEval_algebraMap] at h1
  have h2 : Polynomial.eval z (MvPolynomial.aeval (fun q : Fin n × Fin n => A q.1 q.2) p) =
      MvPolynomial.aeval (fun q : Fin n × Fin n =>
        ((h z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) q.1 q.2) p := by
    have hF : (fun q : Fin n × Fin n => Polynomial.aeval z (A q.1 q.2)) =
        fun q => ((h z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) q.1 q.2 :=
      funext fun q => by rw [hA, Matrix.map_apply, coe_aeval_eq_eval, coe_evalRingHom]
    rw [← coe_aeval_eq_eval, ← AlgHom.comp_apply, MvPolynomial.comp_aeval, hF]
  have hc : ((h z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = c := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, hdet]
  rw [eval_mul, eval_C, h2, ← h1, hc, mul_assoc, ← Units.val_pow_eq_pow_val, ← Units.val_mul,
    mul_inv_cancel, Units.val_one, mul_one]

/-- A polynomial `P` with `z^d P(z) = R(z⁻¹)` for all `z ≠ 0`, `d > 0`, is zero. -/
theorem eq_zero_of_forall_pow_mul_eval [Infinite K] {P R : K[X]} {d : ℕ} (hd : 0 < d)
    (h : ∀ z : Kˣ, (z : K) ^ d * P.eval (z : K) = R.eval ((z⁻¹ : Kˣ) : K)) : P = 0 := by
  set e := R.natDegree
  have hT : ∀ z : Kˣ, (R.reflect e).eval (z : K) = (X ^ (d + e) * P).eval (z : K) := by
    intro z
    have := eval₂_reflect_mul_pow (RingHom.id K) ((z⁻¹ : Kˣ) : K) e R le_rfl
    rw [invOf_units, inv_inv] at this
    change (R.reflect e).eval (z : K) * ((z⁻¹ : Kˣ) : K) ^ e = R.eval ((z⁻¹ : Kˣ) : K) at this
    rw [← h z] at this
    rw [eval_mul, eval_pow, eval_X, pow_add]
    calc (R.reflect e).eval (z : K)
        = (R.reflect e).eval (z : K) * ((z⁻¹ : Kˣ) : K) ^ e * (z : K) ^ e := by
          rw [mul_assoc, ← mul_pow, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_pow,
            mul_one]
      _ = _ := by rw [this]; ring
  have hEq : R.reflect e = X ^ (d + e) * P := by
    refine Polynomial.eq_of_infinite_eval_eq _ _ ?_
    refine Set.Infinite.mono (fun x (hx : x ∈ ({0}ᶜ : Set K)) => ?_)
      (Set.finite_singleton (0 : K)).infinite_compl
    exact hT (Units.mk0 x hx)
  have hT0 : R.reflect e = 0 := by
    ext k
    rw [coeff_zero]
    by_cases hk : e < k
    · rw [coeff_reflect, revAt_eq_self_of_lt hk]
      exact coeff_eq_zero_of_natDegree_lt hk
    · rw [hEq, coeff_X_pow_mul', ite_eq_right_iff]
      intro hle
      omega
  rw [hT0, eq_comm, mul_eq_zero] at hEq
  exact hEq.resolve_left (pow_ne_zero _ X_ne_zero)

/-! ### Transvections -/

variable {i j : Fin n}

/-- GLRep's `transvectionGL` (`GLRep.Lie.Integration`) is Mathlib's `Matrix.transvection`. -/
@[simp]
theorem coe_transvectionGL (hij : i ≠ j) (c : K) :
    ((transvectionGL hij c : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = transvection i j c := by
  rw [transvectionGL, coe_lineGL, transvection, Matrix.smul_single, smul_eq_mul, mul_one]

theorem transvectionGL_zero (hij : i ≠ j) : transvectionGL hij (0 : K) = 1 :=
  Units.ext (by rw [coe_transvectionGL, transvection_zero, Units.val_one])

theorem det_transvectionGL (hij : i ≠ j) (c : K) :
    Matrix.GeneralLinearGroup.det (transvectionGL hij c) = 1 := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, coe_transvectionGL, Units.val_one]
  exact Matrix.det_transvection_of_ne i j hij c

/-- An upper transvection lies in `B`. -/
theorem transvectionGL_mem_borel (hij : i < j) (c : K) : transvectionGL hij.ne c ∈ borel K n := by
  rw [mem_borel_iff_forall]
  intro a b hba
  rw [coe_transvectionGL, transvection, Matrix.add_apply, Matrix.one_apply_ne hba.ne', zero_add,
    Matrix.single_apply, ite_eq_right_iff]
  rintro ⟨rfl, rfl⟩
  exact absurd hij (not_lt.mpr hba.le)

/-- An upper transvection has trivial weight. -/
theorem borelChar_transvectionGL (hij : i < j) (c : K) (η : Fin n → ℤ) :
    borelChar K n η ⟨transvectionGL hij.ne c, transvectionGL_mem_borel hij c⟩ = 1 := by
  rw [borelChar_apply]
  refine Finset.prod_eq_one fun k _ => ?_
  have : borelDiag K n ⟨transvectionGL hij.ne c, transvectionGL_mem_borel hij c⟩ k = 1 := by
    refine Units.ext ?_
    rw [borelDiag_apply_val, Units.val_one]
    have hk : (transvection i j c : Matrix (Fin n) (Fin n) K) k k = 1 := by
      rw [transvection, Matrix.add_apply, Matrix.one_apply_eq, Matrix.single_apply,
        ite_eq_right_iff.mpr fun h => absurd (h.1.trans h.2.symm) hij.ne, add_zero]
    rw [← coe_transvectionGL hij.ne] at hk
    exact hk
  rw [this, one_zpow]

/-- The torus element with `z` in position `i` and `z⁻¹` in position `j`. -/
def torusPair (i j : Fin n) (z : Kˣ) : Fin n → Kˣ := Pi.mulSingle i z * Pi.mulSingle j z⁻¹

theorem weightChar_torusPair (η : Fin n → ℤ) (z : Kˣ) :
    weightChar K η (torusPair i j z) = z ^ η i * z⁻¹ ^ η j := by
  rw [weightChar_apply, torusPair, torusCharacter_mul, torusCharacter_mulSingle,
    torusCharacter_mulSingle]

theorem coe_diagGL_torusPair (hij : i ≠ j) (z : Kˣ) :
    ((diagGL (torusPair i j z) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      1 + single i i ((z : K) - 1) + single j j ((z : K)⁻¹ - 1) := by
  ext a b
  rw [diagGL_coe, Matrix.diagonal_apply, Matrix.add_apply, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply, Matrix.single_apply]
  by_cases hab : a = b
  · subst hab
    by_cases hai : a = i
    · subst hai
      simp [torusPair, hij, hij.symm]
    · by_cases haj : a = j
      · subst haj
        simp [torusPair, hai, Ne.symm hai]
      · simp [torusPair, hai, haj, Ne.symm hai, Ne.symm haj]
  · have h1 : ¬(i = a ∧ i = b) := fun h => hab (h.1.symm.trans h.2)
    have h2 : ¬(j = a ∧ j = b) := fun h => hab (h.1.symm.trans h.2)
    simp [hab, h1, h2]

theorem transvection_lower_eq (hij : i ≠ j) {z : K} (hz : z ≠ 0) :
    transvection i j z⁻¹ * (transvection i j (-1) * transvection j i 1 * transvection i j (-1)) *
      (1 + single i i (z - 1) + single j j (z⁻¹ - 1)) * transvection i j z⁻¹ =
      transvection j i z := by
  simp only [transvection, add_mul, mul_add, one_mul, mul_one, Matrix.single_mul_single_same,
    Matrix.single_mul_single_of_ne, hij, hij.symm, ne_eq, not_false_eq_true, add_zero]
  have hji : j ≠ i := hij.symm
  ext a b
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  by_cases hia : i = a <;> by_cases hja : j = a <;> by_cases hib : i = b <;>
    by_cases hjb : j = b <;> simp_all <;> field_simp <;> ring

/-- The fixed element `w₀ = u(−1) v(1) u(−1)` of the rank-one computation. -/
def rankOneWeyl (hij : i ≠ j) : GL (Fin n) K :=
  transvectionGL hij (-1) * transvectionGL hij.symm 1 * transvectionGL hij (-1)

/-- **The rank-one factorization** `v(z) = u(z⁻¹) w₀ t(z) u(z⁻¹)`. -/
theorem transvectionGL_lower_eq (hij : i ≠ j) (z : Kˣ) :
    transvectionGL hij.symm (z : K) = transvectionGL hij ((z⁻¹ : Kˣ) : K) * rankOneWeyl hij *
      diagGL (torusPair i j z) * transvectionGL hij ((z⁻¹ : Kˣ) : K) := by
  refine Units.ext ?_
  simp only [Units.val_mul, rankOneWeyl, coe_transvectionGL, coe_diagGL_torusPair hij,
    Units.val_inv_eq_inv_val]
  exact (transvection_lower_eq hij z.ne_zero).symm

theorem map_evalRingHom_C (M : Matrix (Fin n) (Fin n) K) (z : K) :
    (M.map C).map (evalRingHom z) = M := by
  ext a b
  simp

theorem map_evalRingHom_transvection (a b : Fin n) (z : K) :
    (transvection a b (X : K[X])).map (evalRingHom z) = transvection a b z := by
  ext c d
  simp only [Matrix.map_apply, transvection, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply, coe_evalRingHom]
  split_ifs <;> simp

/-! ### Vanishing -/

/-- **`ind_B^G(η) = 0` unless `η` is weakly increasing.** -/
theorem eq_zero_of_mem_indBorelSubrep [Infinite K] {η : Fin n → ℤ} (hη : ¬ Monotone η)
    {f : GLCoord K n} (hf : f ∈ (indBorelSubrep K n η).toSubmodule) : f = 0 := by
  obtain ⟨i, j, hij, hηij⟩ : ∃ i j : Fin n, i < j ∧ η j < η i := by
    simp only [Monotone, not_forall, not_le] at hη
    obtain ⟨a, b, hab, h⟩ := hη
    exact ⟨a, b, lt_of_le_of_ne hab (by rintro rfl; exact lt_irrefl _ h), h⟩
  rw [mem_indBorelSubrep_iff_glEval] at hf
  refine glCoord_ext fun g => ?_
  rw [map_zero]
  set W := rankOneWeyl (K := K) hij.ne
  set gm : Matrix (Fin n) (Fin n) K := (g : Matrix (Fin n) (Fin n) K)
  obtain ⟨P, hP⟩ := exists_polynomial_glEval f (gm.map C * transvection j i X)
    (Matrix.GeneralLinearGroup.det g) (fun z => g * transvectionGL hij.ne.symm z)
    (fun z => by
      rw [Units.val_mul, coe_transvectionGL, Matrix.map_mul, map_evalRingHom_C,
        map_evalRingHom_transvection])
    (fun z => by rw [map_mul, det_transvectionGL, mul_one])
  obtain ⟨R, hR⟩ := exists_polynomial_glEval f
    (gm.map C * transvection i j X * (W : Matrix (Fin n) (Fin n) K).map C)
    (Matrix.GeneralLinearGroup.det g * Matrix.GeneralLinearGroup.det W)
    (fun w => g * transvectionGL hij.ne w * W)
    (fun w => by
      rw [Units.val_mul, Units.val_mul, coe_transvectionGL, Matrix.map_mul, Matrix.map_mul,
        map_evalRingHom_C, map_evalRingHom_C, map_evalRingHom_transvection])
    (fun w => by rw [map_mul, map_mul, det_transvectionGL, mul_one])
  obtain ⟨d, hd⟩ : ∃ d : ℕ, (d : ℤ) = η i - η j := ⟨(η i - η j).toNat, by omega⟩
  have hd0 : 0 < d := by omega
  have hrel : ∀ z : Kˣ, (z : K) ^ d * P.eval (z : K) = R.eval ((z⁻¹ : Kˣ) : K) := by
    intro z
    let b : borel K n := borelTorus K n (torusPair i j z) *
      ⟨transvectionGL hij.ne ((z⁻¹ : Kˣ) : K), transvectionGL_mem_borel hij _⟩
    have hb : borelChar K n η b = z ^ η i * z⁻¹ ^ η j := by
      rw [map_mul, borelChar_borelTorus, borelChar_transvectionGL hij, mul_one,
        weightChar_torusPair]
    have hfb := hf (g * transvectionGL hij.ne ((z⁻¹ : Kˣ) : K) * W) b
    have hgb : g * transvectionGL hij.ne ((z⁻¹ : Kˣ) : K) * W * (b : GL (Fin n) K) =
        g * transvectionGL hij.ne.symm (z : K) := by
      rw [transvectionGL_lower_eq hij.ne z]
      simp only [b, Subgroup.coe_mul, coe_borelTorus, mul_assoc]
      rfl
    rw [hgb, hP, hR, hb] at hfb
    rw [hfb, ← mul_assoc, ← Units.val_pow_eq_pow_val, ← Units.val_mul]
    have hunit : z ^ d * (z ^ η i * z⁻¹ ^ η j)⁻¹ = 1 := by
      rw [← zpow_natCast, hd]
      group
    rw [hunit, Units.val_one, one_mul]
  have hP0 := eq_zero_of_forall_pow_mul_eval hd0 hrel
  have := hP 0
  rw [hP0, eval_zero, transvectionGL_zero, mul_one] at this
  exact this

/-- **Vanishing**: `ind_B^G(η) = 0` unless `η` is weakly increasing (over an infinite field). -/
theorem indBorelSubrep_eq_bot [Infinite K] {η : Fin n → ℤ} (hη : ¬ Monotone η) :
    indBorelSubrep K n η = ⊥ :=
  Subrepresentation.ext ((Submodule.eq_bot_iff _).mpr fun _ hf =>
    eq_zero_of_mem_indBorelSubrep hη hf)

end

end GLRep
