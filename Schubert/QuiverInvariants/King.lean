import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Projection
import Mathlib.Tactic.Module
import Schubert.QuiverInvariants.Basic

/-!
# King's inequalities

Let `f ≠ 0` be a semi-invariant of weight `σ` on the representations of a forward quiver on the
vertex family `ι`, of dimension vector `n = dim ι`, over an infinite field. This file proves the
easy half of King's criterion, in the form of Baldoni–Vergne–Walter, Lemma 3.2:
* `∑_p σ_p n_p = 0`;
* `∑_p σ_p β_p ≥ 0` whenever a general representation of dimension `n` has a quotient of
  dimension `β`.

The proof uses one-parameter subgroups. If `V` has a subrepresentation `S`, choose complements
`T_p` of the `S_p` and let `g(c)` act by `c` on `S_p` and as the identity on `T_p`. Then
`g(c) · V = V + (c - 1) • W` for a fixed `W`, so `c ↦ f(g(c) · V)` is a polynomial; it equals
`c ^ (-∑_p σ_p dim S_p) · f(V)`, which forces `∑_p σ_p dim S_p ≤ 0` when `f(V) ≠ 0`. No block
decomposition of the vertex spaces is needed.

## Main definitions

* `QuiverInvariants.scaleOn h c`: for complementary subspaces `U ⊕ W = V`, the linear map acting
  by `c` on `U` and as the identity on `W`.
* `QuiverInvariants.FQuiver.oneParam h c`: the corresponding element of `GLFamily K ι`, for
  complements `h p : IsCompl (S p) (T p)` at every vertex.

## Main results

* `QuiverInvariants.nonneg_of_eval_eq_zpow_mul`: a polynomial `P` with `P(c) = c ^ k · a` for all
  `c ≠ 0`, where `a ≠ 0`, over an infinite field, forces `k ≥ 0`.
* `QuiverInvariants.det_scaleOn`: `det (scaleOn h c) = c ^ dim U`.
* `QuiverInvariants.FQuiver.act_oneParam`: `g(c) · V = V + (c - 1) • W` when `S` is a
  subrepresentation of `V`.
* `QuiverInvariants.FQuiver.IsSemiInvariant.sum_mul_finrank_nonpos`: King's inequality at a point
  where `f` does not vanish: `∑_p σ_p dim S_p ≤ 0` for every subrepresentation `S`.
* `QuiverInvariants.FQuiver.IsSemiInvariant.sum_mul_card_eq_zero`: `∑_p σ_p n_p = 0`.
* `QuiverInvariants.FQuiver.IsSemiInvariant.sum_mul_nonneg_of_generalQuot`: King's inequalities
  `∑_p σ_p β_p ≥ 0` for general quotients `β`.
-/

open Polynomial

namespace QuiverInvariants

noncomputable section

/-! ### One-variable lemmas -/

section OneVariable

variable {K : Type*} [Field K] [Infinite K]

theorem infinite_setOf_ne_zero : {c : K | c ≠ 0}.Infinite :=
  (Set.finite_singleton (0 : K)).infinite_compl

/-- **The one-parameter-subgroup argument.** If a polynomial satisfies `P(c) = c ^ k · a` for
every nonzero `c`, with `a ≠ 0`, then `k ≥ 0`. -/
theorem nonneg_of_eval_eq_zpow_mul {P : K[X]} {k : ℤ} {a : K} (ha : a ≠ 0)
    (h : ∀ c : K, c ≠ 0 → P.eval c = c ^ k * a) : 0 ≤ k := by
  by_contra hk
  push Not at hk
  obtain ⟨j, hj⟩ : ∃ j : ℕ, k = -(j : ℤ) := ⟨(-k).toNat, by omega⟩
  have hj0 : j ≠ 0 := by rintro rfl; simp at hj; omega
  have hQ : X ^ j * P - C a = 0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot _ (infinite_setOf_ne_zero.mono fun c hc => ?_)
    have hc' : (c : K) ≠ 0 := hc
    simp only [Set.mem_ofPred_eq, IsRoot, eval_sub, eval_mul, eval_pow, eval_X, eval_C,
      h c hc', hj, zpow_neg, zpow_natCast]
    field_simp
    ring
  have := congrArg (eval 0) hQ
  simp [zero_pow hj0, ha] at this

/-- If `c ^ k = 1` for every nonzero `c` in an infinite field, then `k = 0`. -/
theorem eq_zero_of_zpow_eq_one {k : ℤ} (h : ∀ c : K, c ≠ 0 → c ^ k = 1) : k = 0 := by
  have h₁ : 0 ≤ k := nonneg_of_eval_eq_zpow_mul (K := K) (P := 1) one_ne_zero fun c hc => by
    rw [h c hc, eval_one, one_mul]
  have h₂ : 0 ≤ -k := nonneg_of_eval_eq_zpow_mul (K := K) (P := 1) one_ne_zero fun c hc => by
    rw [zpow_neg, h c hc, eval_one, inv_one, one_mul]
  omega

end OneVariable

/-! ### One-parameter subgroups adapted to a subspace -/

section Scale

variable {K : Type*} [Field K] {V V' : Type*} [AddCommGroup V] [Module K V] [AddCommGroup V']
  [Module K V']

/-- For complementary subspaces `U ⊕ W = V`, the linear map acting by `c` on `U` and as the
identity on `W`. -/
def scaleOn {U W : Submodule K V} (h : IsCompl U W) (c : K) : V →ₗ[K] V :=
  (Submodule.prodEquivOfIsCompl U W h : U × W →ₗ[K] V) ∘ₗ
    LinearMap.prodMap (c • LinearMap.id) LinearMap.id ∘ₗ
    ((Submodule.prodEquivOfIsCompl U W h).symm : V →ₗ[K] U × W)

variable {U W : Submodule K V} (h : IsCompl U W)

theorem scaleOn_apply (c : K) (x : V) :
    scaleOn h c x = c • U.projection W h x + W.projection U h.symm x := by
  simp [scaleOn]

theorem scaleOn_one : scaleOn h 1 = LinearMap.id := by
  ext x
  simp [scaleOn_apply, Submodule.projection_add_projection_eq_self]

theorem scaleOn_mul (c d : K) : scaleOn h (c * d) = scaleOn h c ∘ₗ scaleOn h d := by
  ext x
  have hPQ : U.projection W h (W.projection U h.symm x) = 0 :=
    Submodule.projection_apply_of_mem_right h (Submodule.projection_apply_mem h.symm x)
  have hQP : W.projection U h.symm (U.projection W h x) = 0 :=
    Submodule.projection_apply_of_mem_right h.symm (Submodule.projection_apply_mem h x)
  have hPP : U.projection W h (U.projection W h x) = U.projection W h x :=
    Submodule.projection_apply_of_mem_left h (Submodule.projection_apply_mem h x)
  have hQQ : W.projection U h.symm (W.projection U h.symm x) = W.projection U h.symm x :=
    Submodule.projection_apply_of_mem_left h.symm (Submodule.projection_apply_mem h.symm x)
  simp only [scaleOn_apply, LinearMap.comp_apply, map_add, map_smul, hPQ, hQP, hPP, hQQ,
    smul_zero, add_zero, zero_add]
  module

/-- **The determinant of the one-parameter subgroup**: `det (scaleOn h c) = c ^ dim U`. -/
theorem det_scaleOn [FiniteDimensional K V] (c : K) :
    LinearMap.det (scaleOn h c) = c ^ Module.finrank K U := by
  rw [scaleOn, LinearMap.det_conj, LinearMap.det_prodMap, LinearMap.det_smul, LinearMap.det_id,
    LinearMap.det_id, mul_one, mul_one]

/-- **Conjugation by the one-parameter subgroups.** If `f` maps `U` into `U'`, then
`scaleOn h' c ∘ f ∘ scaleOn h c⁻¹ = f + (c - 1) • (P' ∘ f ∘ R)`, where `P'` is the projection
onto `U'` along `W'` and `R` the projection onto `W` along `U`. -/
theorem scaleOn_comp_comp_scaleOn_inv {U' W' : Submodule K V'} (h' : IsCompl U' W')
    {f : V →ₗ[K] V'} (hf : ∀ x ∈ U, f x ∈ U') {c : K} (hc : c ≠ 0) :
    scaleOn h' c ∘ₗ f ∘ₗ scaleOn h c⁻¹ =
      f + (c - 1) • (U'.projection W' h' ∘ₗ f ∘ₗ W.projection U h.symm) := by
  ext x
  have hfx : f x = f (U.projection W h x) + f (W.projection U h.symm x) := by
    rw [← map_add, Submodule.projection_add_projection_eq_self]
  have hy₁ : f (U.projection W h x) ∈ U' := hf _ (Submodule.projection_apply_mem h x)
  have h₁ : U'.projection W' h' (f (U.projection W h x)) = f (U.projection W h x) :=
    Submodule.projection_apply_of_mem_left h' hy₁
  have h₂ : W'.projection U' h'.symm (f (U.projection W h x)) = 0 :=
    Submodule.projection_apply_of_mem_right h'.symm hy₁
  have hy₂ := (Submodule.projection_add_projection_eq_self h' (f (W.projection U h.symm x))).symm
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply, scaleOn_apply,
    map_add, map_smul, h₁, h₂]
  rw [hfx]
  generalize f (U.projection W h x) = y₁ at *
  generalize f (W.projection U h.symm x) = y₂ at *
  generalize U'.projection W' h' y₂ = a at *
  generalize W'.projection U' h'.symm y₂ = b at *
  subst hy₂
  simp only [smul_add, smul_smul, inv_mul_cancel₀ hc, one_smul, smul_zero]
  module

end Scale

/-! ### One-parameter subgroups of `GL` -/

section OneParam

variable {K : Type*} [Field K]

/-- A product of integer powers of one element of a commutative group. -/
theorem prod_zpow_eq_zpow_sum {α G : Type*} [CommGroup G] (s : Finset α) (f : α → ℤ) (a : G) :
    ∏ i ∈ s, a ^ f i = a ^ ∑ i ∈ s, f i := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s hi ih => rw [Finset.prod_cons, Finset.sum_cons, ih, zpow_add]

variable {κ : Type*} [Fintype κ] [DecidableEq κ] {U W : Submodule K (κ → K)}

/-- The element of `GL(K^κ)` acting by `c` on `U` and as the identity on a complement `W`. -/
def scaleGL (h : IsCompl U W) (c : Kˣ) : GL κ K where
  val := LinearMap.toMatrix' (scaleOn h c)
  inv := LinearMap.toMatrix' (scaleOn h ↑c⁻¹)
  val_inv := by
    rw [← LinearMap.toMatrix'_comp, ← scaleOn_mul, Units.mul_inv, scaleOn_one,
      LinearMap.toMatrix'_id]
  inv_val := by
    rw [← LinearMap.toMatrix'_comp, ← scaleOn_mul, Units.inv_mul, scaleOn_one,
      LinearMap.toMatrix'_id]

theorem val_scaleGL (h : IsCompl U W) (c : Kˣ) :
    (scaleGL h c : Matrix κ κ K) = LinearMap.toMatrix' (scaleOn h c) :=
  rfl

theorem val_scaleGL_inv (h : IsCompl U W) (c : Kˣ) :
    (((scaleGL h c)⁻¹ : GL κ K) : Matrix κ κ K) = LinearMap.toMatrix' (scaleOn h (c : K)⁻¹) := by
  rw [← Units.val_inv_eq_inv_val]
  rfl

theorem det_scaleGL (h : IsCompl U W) (c : Kˣ) :
    Matrix.GeneralLinearGroup.det (scaleGL h c) = c ^ Module.finrank K U := by
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, val_scaleGL, LinearMap.det_toMatrix',
    det_scaleOn, Units.val_pow_eq_pow_val]

end OneParam

/-! ### King's inequalities -/

namespace FQuiver

variable (Q : FQuiver) {K : Type*} [Field K] {ι : Fin Q.s → Type} [∀ p, Fintype (ι p)]
  [∀ p, DecidableEq (ι p)] {S T : (p : Fin Q.s) → Submodule K (ι p → K)}

/-- The **one-parameter subgroup adapted to a family of subspaces** `S p` with complements `T p`:
at every vertex it acts by `c` on `S p` and as the identity on `T p`. -/
def oneParam (h : ∀ p, IsCompl (S p) (T p)) (c : Kˣ) : GLFamily K ι :=
  fun p => scaleGL (h p) c

/-- The character `χ_σ` on the one-parameter subgroup: `χ_σ(g(c)) = c ^ (∑_p σ_p dim S_p)`. -/
theorem chi_oneParam (h : ∀ p, IsCompl (S p) (T p)) (σ : Fin Q.s → ℤ) (c : Kˣ) :
    chi σ (Q.oneParam h c) = c ^ ∑ p, σ p * (Module.finrank K (S p) : ℤ) := by
  simp only [chi, oneParam, det_scaleGL, ← zpow_natCast, ← zpow_mul]
  rw [prod_zpow_eq_zpow_sum]
  simp only [mul_comm]

/-- The arrow data `W` with `g(c) · V = V + (c - 1) • W`: on `e : p → q` it is
`P_q ∘ V_e ∘ R_p`, where `P_q` projects onto `S q` along `T q` and `R_p` onto `T p` along
`S p`. -/
def oneParamDelta (h : ∀ p, IsCompl (S p) (T p)) (V : Q.Rep K ι) : Q.Rep K ι :=
  fun e => LinearMap.toMatrix' ((S (Q.tgt e)).projection (T (Q.tgt e)) (h _) ∘ₗ
    Matrix.toLin' (V e) ∘ₗ (T (Q.src e)).projection (S (Q.src e)) (h _).symm)

/-- **The one-parameter subgroup acts affinely**: if `S` is a subrepresentation of `V`, then
`g(c) · V = V + (c - 1) • W`. -/
theorem act_oneParam (h : ∀ p, IsCompl (S p) (T p)) {V : Q.Rep K ι} (hS : Q.IsSubrep V S)
    (c : Kˣ) : Q.act (Q.oneParam h c) V = V + ((c : K) - 1) • Q.oneParamDelta h V := by
  funext e
  have key := scaleOn_comp_comp_scaleOn_inv (h (Q.src e)) (h (Q.tgt e))
    (f := Matrix.toLin' (V e)) (fun x hx => hS e x hx) c.ne_zero
  rw [act_apply, oneParam, oneParam, val_scaleGL, val_scaleGL_inv,
    ← LinearMap.toMatrix'_toLin' (V e), ← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_comp,
    LinearMap.comp_assoc, key, map_add, map_smul, LinearMap.toMatrix'_toLin']
  rfl

/-- The coordinates of `g(c) · V` lie on a line. -/
theorem coord_act_oneParam (h : ∀ p, IsCompl (S p) (T p)) {V : Q.Rep K ι}
    (hS : Q.IsSubrep V S) (c : Kˣ) :
    Q.coord (Q.act (Q.oneParam h c) V) =
      (Q.coord V - Q.coord (Q.oneParamDelta h V)) + (c : K) • Q.coord (Q.oneParamDelta h V) := by
  rw [Q.act_oneParam h hS, coord_add, coord_smul, sub_smul, one_smul]
  abel

/-- **King's inequality at a point.** Let `f` be a semi-invariant of weight `σ` over an infinite
field, and `V` a representation with `f(V) ≠ 0`. Then `∑_p σ_p dim S_p ≤ 0` for every
subrepresentation `S` of `V`. -/
theorem IsSemiInvariant.sum_mul_finrank_nonpos [Infinite K] {σ : Fin Q.s → ℤ}
    {f : MvPolynomial (Q.Entry ι) K} (hf : Q.IsSemiInvariant σ f) {V : Q.Rep K ι}
    (hV : MvPolynomial.eval (Q.coord V) f ≠ 0) {S : (p : Fin Q.s) → Submodule K (ι p → K)}
    (hS : Q.IsSubrep V S) : ∑ p, σ p * (Module.finrank K (S p) : ℤ) ≤ 0 := by
  choose T h using fun p => (S p).exists_isCompl
  obtain ⟨P, hP⟩ := exists_polynomial_eval_add_smul f
    (Q.coord V - Q.coord (Q.oneParamDelta h V)) (Q.coord (Q.oneParamDelta h V))
  have key := nonneg_of_eval_eq_zpow_mul (P := P)
    (k := -∑ p, σ p * (Module.finrank K (S p) : ℤ)) hV fun c hc => by
      have := hf (Q.oneParam h (Units.mk0 c hc)) V
      rw [Q.coord_act_oneParam h hS, Q.chi_oneParam h σ, Units.val_mk0] at this
      rw [hP, this, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, Units.val_mk0,
        zpow_neg]
  linarith

/-- **Scalars act trivially**: a nonzero semi-invariant of weight `σ` on representations of
dimension `n` satisfies `∑_p σ_p n_p = 0`. -/
theorem IsSemiInvariant.sum_mul_card_eq_zero [Infinite K] {σ : Fin Q.s → ℤ}
    {f : MvPolynomial (Q.Entry ι) K} (hf : Q.IsSemiInvariant σ f) (hf0 : f ≠ 0) :
    ∑ p, σ p * (Fintype.card (ι p) : ℤ) = 0 := by
  obtain ⟨x, -, hx⟩ := (zariskiDense_univ (K := K) (σ := Q.Entry ι)).exists_eval_ne_zero hf0
  have hV : MvPolynomial.eval (Q.coord (Q.ofCoord x)) f ≠ 0 := hx
  have h : ∀ p, IsCompl (⊤ : Submodule K (ι p → K)) ⊥ := fun _ => isCompl_top_bot
  have hdelta : Q.oneParamDelta h (Q.ofCoord x) = 0 := by
    funext e
    have : (⊥ : Submodule K (ι (Q.src e) → K)).projection ⊤ (h _).symm = 0 :=
      LinearMap.ext fun y => (Submodule.mem_bot K).mp (Submodule.projection_apply_mem _ y)
    simp [oneParamDelta, this]
  refine neg_eq_zero.mp (eq_zero_of_zpow_eq_one (K := K) fun c hc => ?_)
  have := hf (Q.oneParam h (Units.mk0 c hc)) (Q.ofCoord x)
  rw [Q.act_oneParam h (Q.isSubrep_top _), hdelta, smul_zero, add_zero, Q.chi_oneParam h σ,
    Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, Units.val_mk0] at this
  have h1 := mul_right_cancel₀ hV (this.symm.trans (one_mul _).symm)
  simpa [zpow_neg, finrank_top, Module.finrank_fintype_fun_eq_card] using h1

/-- **King's inequalities** (Baldoni–Vergne–Walter, Lemma 3.2, density form). If `f ≠ 0` is a
semi-invariant of weight `σ` and a general representation on `ι` has a quotient of dimension
`β`, then `∑_p σ_p β_p ≥ 0`. -/
theorem IsSemiInvariant.sum_mul_nonneg_of_generalQuot [Infinite K] {σ : Fin Q.s → ℤ}
    {f : MvPolynomial (Q.Entry ι) K} (hf : Q.IsSemiInvariant σ f) (hf0 : f ≠ 0)
    {β : Fin Q.s → ℕ} (hβ : Q.GeneralQuot K ι β) : 0 ≤ ∑ p, σ p * (β p : ℤ) := by
  obtain ⟨_, ⟨V, ⟨S, hS, hdim⟩, rfl⟩, hV⟩ := hβ.exists_eval_ne_zero hf0
  have h₁ := hf.sum_mul_finrank_nonpos Q hV hS
  have h₂ := hf.sum_mul_card_eq_zero Q hf0
  have hβS : ∀ p, (β p : ℤ) = Fintype.card (ι p) - Module.finrank K (S p) := fun p => by
    have := hdim p
    omega
  simp only [hβS, mul_sub, Finset.sum_sub_distrib]
  linarith

end FQuiver

end

end QuiverInvariants
