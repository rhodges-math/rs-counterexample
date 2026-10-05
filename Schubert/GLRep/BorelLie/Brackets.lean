import Schubert.GLRep.Borel.BorelLieDual

/-!
# The bracket relations of the differentials of a rational `B`-representation

Let `ρ` be a rational representation of the Borel subgroup `B ⊆ GL_n(K)`, `K` infinite of
characteristic zero, with differentials `D_ab = dρ(E_ab)`, `a < b`
(`GLRep.IsRationalBorelRep.borelLie`). The `D_ab` satisfy the commutation relations of the
matrix units `E_ab` in `𝔫⁺`:

* `borelLie_comm`: `D_ab D_cd = D_cd D_ab` if `b ≠ c` and `a ≠ d`;
* `borelLie_bracket`: `D_ab D_bc - D_bc D_ab = D_ac` for `a < b < c`.

They follow from the group relations `u_ab(s) u_cd(t) = u_cd(t) u_ab(s)` and
`u_ab(s) u_bc(t) = u_ac(st) u_bc(t) u_ab(s)` by extracting coefficients of the exponential
expansions `ρ(u_ab(t)) = Σ_k t^k/k! D_ab^k`, with a product rule (`sum_mul_sum_eq_sum`).

Consequence (**generation by the simple roots**): a subspace is `B`-stable iff it is stable under
the torus and under the simple-root differentials `D_{a,a+1}`
(`IsRationalBorelRep.forall_mem_iff_simple`), and a linear map between rational representations
commutes with `B` iff it commutes with the torus and with the `D_{a,a+1}`
(`IsRationalBorelRep.forall_intertwining_iff_simple`).
-/

namespace GLRep

open Module

noncomputable section

variable {K : Type*} [Field K] {n : ℕ}

/-! ### Group relations among upper transvections -/

section Group

variable {a b c d : Fin n}

theorem upperTransvection_mul_comm (hab : a < b) (hcd : c < d) (hbc : b ≠ c) (had : a ≠ d)
    (s t : K) :
    upperTransvection hab s * upperTransvection hcd t =
      upperTransvection hcd t * upperTransvection hab s := by
  refine Subtype.ext (Units.ext ?_)
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_upperTransvection,
    coe_upperTransvection, coe_transvectionGL, coe_transvectionGL, Matrix.transvection,
    Matrix.transvection]
  have h1 : Matrix.single a b s * Matrix.single c d t = 0 :=
    Matrix.single_mul_single_of_ne s a b c hbc t
  have h2 : Matrix.single c d t * Matrix.single a b s = 0 :=
    Matrix.single_mul_single_of_ne t c d a (Ne.symm had) s
  simp only [add_mul, mul_add, one_mul, mul_one, h1, h2, add_zero]
  abel

theorem upperTransvection_mul_upperTransvection (hab : a < b) (hbc : b < c) (s t : K) :
    upperTransvection hab s * upperTransvection hbc t =
      upperTransvection (hab.trans hbc) (s * t) * upperTransvection hbc t *
        upperTransvection hab s := by
  refine Subtype.ext (Units.ext ?_)
  simp only [Subgroup.coe_mul, Units.val_mul, coe_upperTransvection, coe_transvectionGL,
    Matrix.transvection]
  have hca : c ≠ a := (hab.trans hbc).ne'
  have hcb : c ≠ b := hbc.ne'
  have h1 : Matrix.single a b s * Matrix.single b c t = Matrix.single a c (s * t) :=
    Matrix.single_mul_single_same s a b c t
  have h2 : Matrix.single a c (s * t) * Matrix.single b c t = 0 :=
    Matrix.single_mul_single_of_ne (s * t) a c b hcb t
  have h3 : Matrix.single b c t * Matrix.single a b s = 0 :=
    Matrix.single_mul_single_of_ne t b c a hca s
  have h4 : Matrix.single a c (s * t) * Matrix.single a b s = 0 :=
    Matrix.single_mul_single_of_ne (s * t) a c a hca s
  simp only [add_mul, mul_add, one_mul, mul_one, h1, h2, h3, h4, add_zero]
  abel

end Group

/-! ### A product rule for polynomial expansions -/

section Product

variable {A : Type*} [Ring A] [Algebra K A]

/-- The product of two polynomial expansions, regrouped by degree. -/
theorem sum_mul_sum_eq_sum (F G : ℕ → A) (N : ℕ) (t : K) :
    (∑ i ∈ Finset.range N, t ^ i • F i) * (∑ j ∈ Finset.range N, t ^ j • G j) =
      ∑ k ∈ Finset.range (2 * N), t ^ k •
        ∑ p ∈ (Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 = k),
          F p.1 * G p.2 := by
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  have hmaps : ∀ p ∈ Finset.range N ×ˢ Finset.range N, p.1 + p.2 ∈ Finset.range (2 * N) := by
    intro p hp
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
    rw [Finset.mem_range]
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.mem_filter] at hp
  rw [smul_mul_smul_comm, ← pow_add, hp.2]

theorem filter_add_eq_one {N : ℕ} (hN : 1 < N) :
    (Finset.range N ×ˢ Finset.range N).filter (fun p : ℕ × ℕ => p.1 + p.2 = 1) =
      {(0, 1), (1, 0)} := by
  ext ⟨i, j⟩
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_insert,
    Finset.mem_singleton, Prod.mk.injEq]
  omega

/-- **Product rule**: the linear coefficient of a product of expansions. -/
theorem sum_filter_add_eq_one (F G : ℕ → A) {N : ℕ} (hN : 1 < N) :
    ∑ p ∈ (Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 = 1),
      F p.1 * G p.2 = F 0 * G 1 + F 1 * G 0 := by
  rw [filter_add_eq_one hN, Finset.sum_pair (by simp)]

end Product

/-! ### The bracket relations -/

namespace IsRationalBorelRep

variable {W : Type*} [AddCommGroup W] [Module K W] {ρ : Representation K (borel K n) W}
variable (hρ : IsRationalBorelRep ρ) [Infinite K] [CharZero K]
variable {a b c d : Fin n}

include hρ in
/-- The expansion `ρ(u_ab(t)) = Σ_k t^k (D_ab^k / k!)` with any large enough bound. -/
theorem exists_expansion (hab : a < b) :
    ∃ N : ℕ, 1 < N ∧ ∀ M, N ≤ M → ∀ t : K, ρ (upperTransvection hab t) =
      ∑ k ∈ Finset.range M, t ^ k • (((k.factorial : ℕ) : K)⁻¹ • hρ.borelLie hab ^ k) :=
  hρ.exists_rho_upperTransvection_eq hab

/-- A transvection commuting with `u_ab` commutes with `D_ab`. -/
theorem rho_upperTransvection_borelLie_apply (hab : a < b) (hcd : c < d) (hbc : b ≠ c)
    (had : a ≠ d) (s : K) (w : W) :
    ρ (upperTransvection hcd s) (hρ.borelLie hab w) =
      hρ.borelLie hab (ρ (upperTransvection hcd s) w) := by
  obtain ⟨N, hN, hρN⟩ := hρ.exists_expansion hab
  have key := hρ.borelLie_apply_eq_of_forall hab (ρ (upperTransvection hcd s)) w hN
    (fun k => (((k.factorial : ℕ) : K)⁻¹ • hρ.borelLie hab ^ k) (ρ (upperTransvection hcd s) w))
    (fun t => by
      rw [← Module.End.mul_apply, ← map_mul,
        ← upperTransvection_mul_comm hab hcd hbc had t s, map_mul, Module.End.mul_apply,
        hρN N le_rfl t, LinearMap.sum_apply]
      simp only [LinearMap.smul_apply])
  simpa using key

/-- **Commuting roots**: `D_ab D_cd = D_cd D_ab` if `b ≠ c` and `a ≠ d`. -/
theorem borelLie_comm (hab : a < b) (hcd : c < d) (hbc : b ≠ c) (had : a ≠ d) :
    hρ.borelLie hab * hρ.borelLie hcd = hρ.borelLie hcd * hρ.borelLie hab := by
  obtain ⟨N, hN, hρN⟩ := hρ.exists_expansion hcd
  refine LinearMap.ext fun w => ?_
  have key := hρ.borelLie_apply_eq_of_forall hcd (hρ.borelLie hab) w hN
    (fun k => (((k.factorial : ℕ) : K)⁻¹ • hρ.borelLie hcd ^ k) (hρ.borelLie hab w))
    (fun t => by
      rw [← hρ.rho_upperTransvection_borelLie_apply hab hcd hbc had t w, hρN N le_rfl t,
        LinearMap.sum_apply]
      simp only [LinearMap.smul_apply])
  simpa [Module.End.mul_apply] using key

/-- `D_ab ρ(u_bc(t)) = ρ(u_bc(t)) D_ab + t D_ac ρ(u_bc(t))`. -/
theorem borelLie_rho_upperTransvection_apply (hab : a < b) (hbc : b < c) (t : K) (w : W) :
    hρ.borelLie hab (ρ (upperTransvection hbc t) w) =
      ρ (upperTransvection hbc t) (hρ.borelLie hab w) +
        t • hρ.borelLie (hab.trans hbc) (ρ (upperTransvection hbc t) w) := by
  obtain ⟨N₁, hN₁, h₁⟩ := hρ.exists_expansion hab
  obtain ⟨N₂, hN₂, h₂⟩ := hρ.exists_expansion (hab.trans hbc)
  set M := max N₁ N₂
  set Y := ρ (upperTransvection hbc t)
  let F : ℕ → Module.End K W := fun i =>
    (t ^ i * ((i.factorial : ℕ) : K)⁻¹) • hρ.borelLie (hab.trans hbc) ^ i * Y
  let G : ℕ → Module.End K W := fun j => ((j.factorial : ℕ) : K)⁻¹ • hρ.borelLie hab ^ j
  have hexp : ∀ s : K, ρ (upperTransvection hab s) * Y =
      ∑ k ∈ Finset.range (2 * M), s ^ k •
        ∑ p ∈ (Finset.range M ×ˢ Finset.range M).filter (fun p => p.1 + p.2 = k),
          F p.1 * G p.2 := by
    intro s
    rw [← sum_mul_sum_eq_sum, ← map_mul, upperTransvection_mul_upperTransvection hab hbc s t,
      map_mul, map_mul, h₂ M (le_max_right _ _) (s * t), h₁ M (le_max_left _ _) s,
      Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [F]
    rw [smul_mul_assoc, smul_mul_assoc, smul_mul_assoc, smul_smul, smul_smul, mul_pow, mul_assoc]
  have hM : 1 < M := lt_max_of_lt_left hN₁
  have key := hρ.borelLie_apply_eq_of_forall hab LinearMap.id (Y w) (by omega : 1 < 2 * M)
    (fun k => (∑ p ∈ (Finset.range M ×ˢ Finset.range M).filter (fun p => p.1 + p.2 = k),
      F p.1 * G p.2) w)
    (fun s => by
      rw [LinearMap.id_apply, ← Module.End.mul_apply, hexp s, LinearMap.sum_apply]
      simp only [LinearMap.smul_apply])
  rw [LinearMap.id_apply, sum_filter_add_eq_one F G hM] at key
  rw [key]
  simp only [F, G, LinearMap.add_apply, Module.End.mul_apply, pow_zero, pow_one,
    Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, inv_one, mul_one, one_smul,
    Module.End.one_apply, LinearMap.smul_apply]

/-- **The bracket relation** `D_ab D_bc - D_bc D_ab = D_ac` for `a < b < c`. -/
theorem borelLie_bracket (hab : a < b) (hbc : b < c) :
    hρ.borelLie hab * hρ.borelLie hbc - hρ.borelLie hbc * hρ.borelLie hab =
      hρ.borelLie (hab.trans hbc) := by
  obtain ⟨N, hN, hρN⟩ := hρ.exists_expansion hbc
  refine LinearMap.ext fun w => ?_
  let X : ℕ → Module.End K W := fun k => ((k.factorial : ℕ) : K)⁻¹ • hρ.borelLie hbc ^ k
  let v : ℕ → W := fun k => X k (hρ.borelLie hab w) +
    if k = 0 then 0 else hρ.borelLie (hab.trans hbc) (X (k - 1) w)
  have key := hρ.borelLie_apply_eq_of_forall hbc (hρ.borelLie hab) w (by omega : 1 < N + 1) v
    (fun t => by
      rw [hρ.borelLie_rho_upperTransvection_apply hab hbc t w]
      nth_rewrite 1 [hρN (N + 1) (by omega) t]
      rw [hρN N le_rfl t, LinearMap.sum_apply, LinearMap.sum_apply, map_sum, Finset.smul_sum]
      simp only [v, smul_add, Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_range_succ']
      simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false, Nat.add_sub_cancel,
        ite_true, smul_zero, add_zero]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [LinearMap.smul_apply, map_smul, smul_smul, pow_succ, mul_comm])
  simp only [v, X, Nat.factorial_one, Nat.cast_one, inv_one, one_smul, pow_one, one_ne_zero,
    ite_false, Nat.sub_self, Nat.factorial_zero, pow_zero, Module.End.one_apply] at key
  rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, key, add_sub_cancel_left]

/-! ### Generation by the simple roots -/

omit [Infinite K] [CharZero K] in
/-- An induction principle over the positive roots: a property of the roots that holds for the
simple roots and is closed under `(a, c), (c, b) ↦ (a, b)` holds for every root. -/
theorem root_induction {P : ∀ a b : Fin n, a < b → Prop}
    (hsimple : ∀ (a b : Fin n) (hab : a < b), b.val = a.val + 1 → P a b hab)
    (htrans : ∀ (a c b : Fin n) (hac : a < c) (hcb : c < b), P a c hac → P c b hcb →
      P a b (hac.trans hcb)) :
    ∀ (a b : Fin n) (hab : a < b), P a b hab := by
  intro a b hab
  obtain ⟨d, hd⟩ : ∃ d, b.val - a.val = d + 1 := ⟨b.val - a.val - 1, by omega⟩
  induction d generalizing b with
  | zero => exact hsimple a b hab (by omega)
  | succ d ih =>
    let c : Fin n := ⟨b.val - 1, by omega⟩
    have hac : a < c := by
      change a.val < b.val - 1
      omega
    have hcb : c < b := by
      change b.val - 1 < b.val
      omega
    exact htrans a c b hac hcb (ih c hac (by change b.val - 1 - a.val = d + 1; omega))
      (hsimple c b hcb (by change b.val = b.val - 1 + 1; omega))

/-- **Simple-root generation for subspaces**: a subspace is `B`-stable iff it is stable under the
torus and under the simple-root differentials `D_{a,a+1}`. -/
theorem forall_mem_iff_simple (U : Submodule K W) :
    (∀ g, ∀ u ∈ U, ρ g u ∈ U) ↔ (∀ t, ∀ u ∈ U, ρ (borelTorus K n t) u ∈ U) ∧
      ∀ (a b : Fin n) (hab : a < b), b.val = a.val + 1 → ∀ u ∈ U, hρ.borelLie hab u ∈ U := by
  rw [hρ.forall_mem_iff]
  refine and_congr_right fun _ => ⟨fun h a b hab _ => h a b hab, fun h => ?_⟩
  refine root_induction h fun a c b hac hcb h₁ h₂ u hu => ?_
  rw [← hρ.borelLie_bracket hac hcb, LinearMap.sub_apply, Module.End.mul_apply,
    Module.End.mul_apply]
  exact U.sub_mem (h₁ _ (h₂ u hu)) (h₂ _ (h₁ u hu))

variable {V : Type*} [AddCommGroup V] [Module K V] {σ : Representation K (borel K n) V}

/-- **Simple-root generation for maps**: a linear map between rational representations of `B`
commutes with `B` iff it commutes with the torus and with the `D_{a,a+1}`. -/
theorem forall_intertwining_iff_simple (hσ : IsRationalBorelRep σ) (f : W →ₗ[K] V) :
    (∀ g w, f (ρ g w) = σ g (f w)) ↔
      (∀ t w, f (ρ (borelTorus K n t) w) = σ (borelTorus K n t) (f w)) ∧
        ∀ (a b : Fin n) (hab : a < b), b.val = a.val + 1 → ∀ w : W,
          f (hρ.borelLie hab w) = hσ.borelLie hab (f w) := by
  rw [hρ.forall_intertwining_iff hσ]
  refine and_congr_right fun _ => ⟨fun h a b hab _ => h a b hab, fun h => ?_⟩
  refine root_induction h fun a c b hac hcb h₁ h₂ w => ?_
  rw [← hρ.borelLie_bracket hac hcb, ← hσ.borelLie_bracket hac hcb, LinearMap.sub_apply,
    LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, Module.End.mul_apply,
    Module.End.mul_apply, map_sub, h₁, h₂, h₂, h₁]

end IsRationalBorelRep

end

end GLRep
