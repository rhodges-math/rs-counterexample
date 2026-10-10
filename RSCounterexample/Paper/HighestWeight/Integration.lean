import RSCounterexample.Paper.HighestWeight.Uniqueness
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.LinearAlgebra.DFinsupp

/-!
# `GLModule`s and representations of `GL_n(ℂ)`

This file connects `GLModule` with Mathlib's `Representation ℂ (GL (Fin n) ℂ)`.

* `GLModule.Integrates M π`: a representation `π` of `GL_n(ℂ)` on the carrier of `M` integrates
  the `gl_n`-action. The matrix units `E_ab` (`a ≠ b`) act nilpotently, the transvection
  `1 + tE_ab` acts by `exp(t·E_ab)`, and the diagonal torus acts on the weight space of `μ` by
  the character `μ`. The differential of a rational representation of `GL_n(ℂ)` has these
  properties.
* For such `π`, a `gl_n`-stable subspace is `π`-stable (`GLModule.Integrates.stable`), and every
  isomorphism of `GLModule`s intertwines the group actions (`GLModule.Integrates.intertwining`).
  The proof uses `units_induction`: every invertible matrix is a product of transvections and a
  diagonal matrix.
* The flag-minor span carries the representation `flagOrbitRepresentation m`. It integrates
  `flagOrbitModule m` and is irreducible (`flagOrbitRepresentation_isIrreducible`).
* `nonempty_equiv_flagOrbitRepresentation`: an irreducible representation that integrates a
  `GLModule` with a highest-weight vector of weight `λ = shapeWeight m` is equivalent to
  `flagOrbitRepresentation m` as a Mathlib representation.
-/

namespace Schubert.RS.HighestWeight

open Schubert.RS.Representation

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : ℕ}

/-! ### Splitting invariant subspaces into weight spaces -/

section Splitting

variable {M : Type*} [AddCommGroup M] [Module ℂ M] (ρ : Square n →ₗ⁅ℂ⁆ Module.End ℂ M)

/-- A subspace stable under the diagonal matrix units, inside a finite sum of weight spaces, is
spanned by the weight vectors it contains. -/
theorem mem_iSup_inf_lieWeightSpace_of_finset (W : Submodule ℂ M)
    (hW : ∀ j : Fin n, ∀ x ∈ W, ρ (Matrix.single j j 1) x ∈ W) (s : Finset (Weight n)) :
    ∀ x ∈ W, x ∈ (⨆ μ ∈ s, lieWeightSpace ρ μ) → x ∈ ⨆ μ, W ⊓ lieWeightSpace ρ μ := by
  classical
  induction s using Finset.strongInduction with
  | H s ih =>
  intro x hxW hxs
  by_cases hcard : s.card ≤ 1
  · obtain ⟨μ, hμ⟩ := Finset.card_le_one_iff_subset_singleton.mp hcard
    have hle : (⨆ ν ∈ s, lieWeightSpace ρ ν) ≤ lieWeightSpace ρ μ := by
      refine iSup₂_le fun ν hν => ?_
      rw [Finset.mem_singleton.mp (hμ hν)]
    exact Submodule.mem_iSup_of_mem μ ⟨hxW, hle hxs⟩
  · obtain ⟨μ, hμ, ν, hν, hne⟩ := (Finset.one_lt_card (s := s)).mp (by omega)
    obtain ⟨j, hj⟩ : ∃ j, μ j ≠ ν j := Function.ne_iff.mp hne
    obtain ⟨f, hf⟩ := (Submodule.mem_iSup_finset_iff_exists_sum _ x).mp hxs
    have hdiff : ((μ j : ℂ) - (ν j : ℂ)) ≠ 0 := by
      rw [sub_ne_zero]
      exact fun h => hj (Int.cast_injective h)
    set c : ℂ := ((μ j : ℂ) - (ν j : ℂ))⁻¹
    set y := c • (ρ (Matrix.single j j 1) x - (ν j : ℂ) • x) with hy_def
    have hyW : y ∈ W := W.smul_mem _ (W.sub_mem (hW j x hxW) (W.smul_mem _ hxW))
    have hfκ : ∀ κ, ρ (Matrix.single j j 1) (f κ : M) = (κ j : ℂ) • (f κ : M) :=
      fun κ => (f κ).2 j
    have hy : y = ∑ κ ∈ s, (c * ((κ j : ℂ) - (ν j : ℂ))) • (f κ : M) := by
      rw [hy_def, ← hf, map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib, Finset.smul_sum]
      refine Finset.sum_congr rfl fun κ _ => ?_
      rw [hfκ κ, ← sub_smul, smul_smul]
    have hmem : ∀ (t : Finset (Weight n)) (g : Weight n → ℂ), ∀ κ ∈ t,
        g κ • (f κ : M) ∈ ⨆ ν ∈ t, lieWeightSpace ρ ν := fun t g κ hκ =>
      (le_iSup₂ (f := fun ν (_ : ν ∈ t) => lieWeightSpace ρ ν) κ hκ)
        (Submodule.smul_mem _ _ (f κ).2)
    have hys : y ∈ ⨆ κ ∈ s.erase ν, lieWeightSpace ρ κ := by
      rw [hy, ← Finset.add_sum_erase s _ hν, sub_self, mul_zero, zero_smul, zero_add]
      exact Submodule.sum_mem _ fun κ hκ => hmem _ (fun κ => c * ((κ j : ℂ) - (ν j : ℂ))) κ hκ
    have hr : x - y ∈ ⨆ κ ∈ s.erase μ, lieWeightSpace ρ κ := by
      have hx' : x - y = ∑ κ ∈ s, (1 - c * ((κ j : ℂ) - (ν j : ℂ))) • (f κ : M) := by
        rw [hy, ← hf, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun κ _ => ?_
        rw [sub_smul, one_smul]
      rw [hx', ← Finset.add_sum_erase s _ hμ, inv_mul_cancel₀ hdiff, sub_self, zero_smul,
        zero_add]
      exact Submodule.sum_mem _ fun κ hκ =>
        hmem _ (fun κ => 1 - c * ((κ j : ℂ) - (ν j : ℂ))) κ hκ
    have h1 := ih (s.erase ν) (Finset.erase_ssubset hν) y hyW hys
    have h2 := ih (s.erase μ) (Finset.erase_ssubset hμ) (x - y) (W.sub_mem hxW hyW) hr
    rw [show x = y + (x - y) by abel]
    exact Submodule.add_mem _ h1 h2

/-- If the weight spaces span, a subspace stable under the diagonal matrix units is spanned by
the weight vectors it contains. -/
theorem mem_iSup_inf_lieWeightSpace (hspan : ⨆ μ : Weight n, lieWeightSpace ρ μ = ⊤)
    (W : Submodule ℂ M) (hW : ∀ j : Fin n, ∀ x ∈ W, ρ (Matrix.single j j 1) x ∈ W) :
    ∀ x ∈ W, x ∈ ⨆ μ, W ⊓ lieWeightSpace ρ μ := by
  intro x hx
  have hxt : x ∈ ⨆ μ : Weight n, lieWeightSpace ρ μ := by rw [hspan]; exact Submodule.mem_top
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.mp hxt
  exact mem_iSup_inf_lieWeightSpace_of_finset ρ W hW s x hx hs

end Splitting

/-! ### Generating `GL_n` -/

/-- A property of invertible matrices that holds for `1`, transvections and invertible diagonal
matrices and is closed under products holds for every invertible matrix. -/
theorem units_induction {P : (Square n)ˣ → Prop} (hone : P 1)
    (hmul : ∀ g h, P g → P h → P (g * h))
    (htv : ∀ {a b : Fin n} (hab : a ≠ b) (t : ℂ), P (transvectionUnit hab t))
    (hdiag : ∀ t, P (diagonalUnit t)) (g : (Square n)ˣ) : P g := by
  classical
  obtain ⟨L, L', D, hg⟩ := Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec g.val
  have hdet : ∀ L : List (Matrix.TransvectionStruct (Fin n) ℂ),
      (L.map Matrix.TransvectionStruct.toMatrix).prod.det = 1 := by
    intro L
    induction L with
    | nil => simp
    | cons x L ih =>
      rw [List.map_cons, List.prod_cons, Matrix.det_mul, ih, mul_one,
        Matrix.TransvectionStruct.toMatrix, Matrix.det_transvection_of_ne _ _ x.hij]
  have hD : ∀ i, D i ≠ 0 := by
    intro i hi
    have h : IsUnit g.val.det := (Matrix.isUnit_iff_isUnit_det _).mp g.isUnit
    rw [hg, Matrix.det_mul, Matrix.det_mul, hdet, hdet, one_mul, mul_one,
      Matrix.det_diagonal] at h
    exact h.ne_zero (Finset.prod_eq_zero (Finset.mem_univ i) hi)
  let tv : Matrix.TransvectionStruct (Fin n) ℂ → (Square n)ˣ := fun s => transvectionUnit s.hij s.c
  have htv_val : ∀ s, (tv s).val = s.toMatrix := by
    intro s
    change 1 + s.c • Matrix.single s.i s.j 1 = Matrix.transvection s.i s.j s.c
    rw [Matrix.transvection, Matrix.smul_single, smul_eq_mul, mul_one]
  have hprod : ∀ L : List (Matrix.TransvectionStruct (Fin n) ℂ),
      ((L.map tv).prod).val = (L.map Matrix.TransvectionStruct.toMatrix).prod := by
    intro L
    induction L with
    | nil => simp
    | cons s L ih => rw [List.map_cons, List.prod_cons, Units.val_mul, ih, htv_val, List.map_cons,
        List.prod_cons]
  have hPL : ∀ L : List (Matrix.TransvectionStruct (Fin n) ℂ), P (L.map tv).prod := by
    intro L
    induction L with
    | nil => simpa using hone
    | cons s L ih =>
      rw [List.map_cons, List.prod_cons]
      exact hmul _ _ (htv s.hij s.c) ih
  let t : DiagonalTorus n := fun i => Units.mk0 (D i) (hD i)
  have hg' : g = (L.map tv).prod * diagonalUnit t * (L'.map tv).prod := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hprod, hprod, hg]
    rfl
  rw [hg']
  exact hmul _ _ (hmul _ _ (hPL L) (hdiag t)) (hPL L')

/-! ### Representations integrating a `GLModule` -/

/-- The representation `π` of `GL_n(ℂ)` on the carrier of `M` integrates the `gl_n`-action:
each `E_ab` (`a ≠ b`) acts nilpotently and the transvection `1 + tE_ab` acts by
`exp(t·E_ab) = Σ_k t^k E_ab^k / k!`; an invertible diagonal matrix `t` acts on the weight
space of `μ` by `Π_i t_i^{μ_i}`. -/
structure GLModule.Integrates (M : GLModule n) (π : _root_.Representation ℂ (GL (Fin n) ℂ) M) :
    Prop where
  nilpotent : ∀ {a b : Fin n}, a ≠ b → ∀ x : M, ∃ N : ℕ, (M.lie (Matrix.single a b 1) ^ N) x = 0
  transvection : ∀ {a b : Fin n} (hab : a ≠ b) (t : ℂ) (x : M) (N : ℕ),
    (M.lie (Matrix.single a b 1) ^ N) x = 0 →
      π (transvectionUnit hab t) x =
        ∑ k ∈ Finset.range N, (t ^ k / (k.factorial : ℂ)) • (M.lie (Matrix.single a b 1) ^ k) x
  diagonal : ∀ (μ : Weight n) (t : DiagonalTorus n), ∀ x ∈ lieWeightSpace M.lie μ,
    π (diagonalUnit t) x = integerWeightScalar μ t • x

namespace GLModule.Integrates

variable {M N : GLModule n} {π : _root_.Representation ℂ (GL (Fin n) ℂ) M}
  {σ : _root_.Representation ℂ (GL (Fin n) ℂ) N}

/-- A `gl_n`-stable subspace is stable under an integrating representation. -/
theorem stable (h : M.Integrates π) (W : Submodule ℂ M) (hW : ∀ A, ∀ x ∈ W, M.lie A x ∈ W)
    (g : GL (Fin n) ℂ) : ∀ x ∈ W, π g x ∈ W := by
  have hpow : ∀ (A : Square n) (k : ℕ), ∀ x ∈ W, (M.lie A ^ k) x ∈ W := by
    intro A k
    induction k with
    | zero => intro x hx; simpa using hx
    | succ k ih => intro x hx; rw [pow_succ', Module.End.mul_apply]; exact hW A _ (ih x hx)
  refine units_induction (P := fun g => ∀ x ∈ W, π g x ∈ W) ?_ ?_ ?_ ?_ g
  · intro x hx
    rw [map_one, Module.End.one_apply]
    exact hx
  · intro g g' hg hg' x hx
    rw [map_mul, Module.End.mul_apply]
    exact hg _ (hg' x hx)
  · intro a b hab t x hx
    obtain ⟨N, hN⟩ := h.nilpotent hab x
    rw [h.transvection hab t x N hN]
    exact Submodule.sum_mem _ fun k _ => W.smul_mem _ (hpow _ k x hx)
  · intro t x hx
    have hx' := mem_iSup_inf_lieWeightSpace M.lie M.weight_span W (fun j => hW _) x hx
    clear hx
    induction hx' using Submodule.iSup_induction' with
    | mem μ y hy =>
      rw [h.diagonal μ t y hy.2]
      exact W.smul_mem _ hy.1
    | zero => rw [map_zero]; exact W.zero_mem
    | add y z _ _ hy hz => rw [map_add]; exact W.add_mem hy hz

/-- An isomorphism of `GLModule`s intertwines integrating representations. -/
theorem intertwining (hM : M.Integrates π) (hN : N.Integrates σ) (e : M ≃ᴳ N)
    (g : GL (Fin n) ℂ) (x : M) : e.toLinearEquiv (π g x) = σ g (e.toLinearEquiv x) := by
  have hpow : ∀ (A : Square n) (k : ℕ) (x : M),
      e.toLinearEquiv ((M.lie A ^ k) x) = (N.lie A ^ k) (e.toLinearEquiv x) := by
    intro A k
    induction k with
    | zero => intro x; rfl
    | succ k ih =>
      intro x
      rw [pow_succ', Module.End.mul_apply, e.map_lie, ih, pow_succ', Module.End.mul_apply]
  have hwt : ∀ μ, ∀ y ∈ lieWeightSpace M.lie μ,
      e.toLinearEquiv y ∈ lieWeightSpace N.lie μ := by
    intro μ y hy j
    rw [← e.map_lie, hy j, map_smul]
  refine units_induction (P := fun g => ∀ x : M, e.toLinearEquiv (π g x) =
    σ g (e.toLinearEquiv x)) ?_ ?_ ?_ ?_ g x
  · intro x
    rw [map_one, map_one, Module.End.one_apply, Module.End.one_apply]
  · intro g g' hg hg' x
    rw [map_mul, Module.End.mul_apply, hg, hg', map_mul, Module.End.mul_apply]
  · intro a b hab t x
    obtain ⟨N₀, hN₀⟩ := hM.nilpotent hab x
    have hN₀' : (N.lie (Matrix.single a b 1) ^ N₀) (e.toLinearEquiv x) = 0 := by
      rw [← hpow, hN₀, map_zero]
    rw [hM.transvection hab t x N₀ hN₀, hN.transvection hab t _ N₀ hN₀', map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, hpow]
  · intro t x
    have hx : x ∈ ⨆ μ : Weight n, lieWeightSpace M.lie μ := by
      rw [M.weight_span]
      exact Submodule.mem_top
    induction hx using Submodule.iSup_induction' with
    | mem μ y hy =>
      rw [hM.diagonal μ t y hy, map_smul, hN.diagonal μ t _ (hwt μ y hy)]
    | zero => rw [map_zero, map_zero, map_zero]
    | add y z _ _ hy hz => rw [map_add, map_add, hy, hz, map_add, map_add]

/-- If an integrating representation is irreducible, so is the `GLModule`. -/
theorem isIrreducible (h : M.Integrates π) (hπ : π.IsIrreducible) : M.IsIrreducible := by
  refine ⟨?_, fun W hW => ?_⟩
  · by_contra hsub
    rw [not_nontrivial_iff_subsingleton] at hsub
    obtain ⟨A, B, hAB⟩ := (inferInstance : Nontrivial (Subrepresentation π))
    apply hAB
    apply Subrepresentation.toSubmodule_injective
    exact Subsingleton.elim _ _
  · rcases eq_bot_or_eq_top (⟨W, fun g x hx => h.stable W hW g x hx⟩ : Subrepresentation π) with
      hb | ht
    · left
      exact congrArg Subrepresentation.toSubmodule hb
    · right
      exact congrArg Subrepresentation.toSubmodule ht

end GLModule.Integrates

/-! ### The flag-minor representation -/

/-- The flag-minor span as a Mathlib representation of `GL_n(ℂ)`. -/
def flagOrbitRepresentation (m : ColumnShape n) :
    _root_.Representation ℂ (GL (Fin n) ℂ) (flagOrbitSpan m) :=
  (⟨flagOrbitSpan m, fun g _ hp => flagOrbitSpan_stable m g hp⟩ :
    Subrepresentation (polynomialGL n : _root_.Representation ℂ (GL (Fin n) ℂ) _)).toRepresentation

@[simp] theorem flagOrbitRepresentation_val (m : ColumnShape n) (g : GL (Fin n) ℂ)
    (p : flagOrbitSpan m) : (flagOrbitRepresentation m g p).val = polynomialGL n g p.val := rfl

/-- The flag-minor span is an irreducible representation of `GL_n(ℂ)`. -/
theorem flagOrbitRepresentation_isIrreducible (m : ColumnShape n) :
    (flagOrbitRepresentation m).IsIrreducible := by
  have hne : (⊥ : Submodule ℂ (flagOrbitSpan m)) ≠ ⊤ := by
    intro h
    have hv : (⟨highestFlag m, highestFlag_mem_orbitSpan m⟩ : flagOrbitSpan m) ∈
        (⊥ : Submodule ℂ (flagOrbitSpan m)) := by rw [h]; exact Submodule.mem_top
    rw [Submodule.mem_bot] at hv
    exact highestFlag_ne_zero m (congrArg Subtype.val hv)
  have hnt : Nontrivial (Subrepresentation (flagOrbitRepresentation m)) :=
    ⟨⟨⊥, ⊤, fun h => hne (congrArg Subrepresentation.toSubmodule h)⟩⟩
  suffices hW : ∀ W : Subrepresentation (flagOrbitRepresentation m), W = ⊥ ∨ W = ⊤ from
    { toNontrivial := hnt, eq_bot_or_eq_top := hW }
  intro W
  let W' : Submodule ℂ (MatrixPolynomial n) := W.toSubmodule.map (flagOrbitSpan m).subtype
  have hG : IsGLStable W' := by
    rintro g _ ⟨x, hx, rfl⟩
    exact ⟨_, W.apply_mem_toSubmodule g hx, rfl⟩
  have hinj := Submodule.map_injective_of_injective (flagOrbitSpan m).injective_subtype
  rcases flagOrbitSpan_irreducible m W' (by rintro _ ⟨x, _, rfl⟩; exact x.2) hG with h | h
  · left
    apply Subrepresentation.toSubmodule_injective
    apply hinj
    exact h.trans (Submodule.map_bot _).symm
  · right
    apply Subrepresentation.toSubmodule_injective
    apply hinj
    exact h.trans (Submodule.map_subtype_top _).symm

theorem flagOrbitLie_pow_val (m : ColumnShape n) (a b : Fin n) (k : ℕ) (p : flagOrbitSpan m) :
    ((flagOrbitLie m (Matrix.single a b 1) ^ k) p).val =
      derivationIter (matrixUnitDerivation a b) k p.val := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ', Module.End.mul_apply, derivationIter_succ, ← ih]; rfl

theorem flagOrbitModule_lie_pow_val (m : ColumnShape n) (a b : Fin n) (k : ℕ)
    (p : flagOrbitSpan m) :
    (((flagOrbitModule m).lie (Matrix.single a b 1) ^ k) p).val =
      derivationIter (matrixUnitDerivation a b) k p.val :=
  flagOrbitLie_pow_val m a b k p

/-- The representation of `GL_n(ℂ)` on the flag-minor span integrates its `gl_n`-action. -/
theorem flagOrbitModule_integrates (m : ColumnShape n) :
    (flagOrbitModule m).Integrates (flagOrbitRepresentation m) where
  nilpotent := by
    intro a b hab p
    refine ⟨(rootSubstitution a b p.val).natDegree + 1, Subtype.ext ?_⟩
    rw [flagOrbitModule_lie_pow_val, ← rootSubstitution_coeff a b hab,
      _root_.Polynomial.coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_self _), smul_zero]
    rfl
  transvection := by
    intro a b hab t p N hN
    apply Subtype.ext
    have hN' : derivationIter (matrixUnitDerivation a b) N p.val = 0 := by
      rw [← flagOrbitModule_lie_pow_val, hN]
      rfl
    have hvanish' : ∀ j, derivationIter (matrixUnitDerivation a b) (N + j) p.val = 0 := by
      intro j
      induction j with
      | zero => exact hN'
      | succ j ih => rw [← add_assoc, derivationIter_succ, ih, map_zero]
    have hvanish : ∀ k, N ≤ k → derivationIter (matrixUnitDerivation a b) k p.val = 0 := by
      intro k hk
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
      exact hvanish' j
    have hcoeff : ∀ k, (rootSubstitution a b p.val).coeff k =
        ((k.factorial : ℂ))⁻¹ • derivationIter (matrixUnitDerivation a b) k p.val := by
      intro k
      have hk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
      rw [← rootSubstitution_coeff a b hab, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
        inv_mul_cancel₀ hk, one_smul]
    change rowAction (1 + t • Matrix.single a b 1) p.val = _
    rw [← rootSubstitution_eval, _root_.Polynomial.eval_eq_sum_range, Submodule.coe_sum]
    set D := (rootSubstitution a b p.val).natDegree
    have hterm : ∀ k, (rootSubstitution a b p.val).coeff k * MvPolynomial.C t ^ k =
        (t ^ k / (k.factorial : ℂ)) • derivationIter (matrixUnitDerivation a b) k p.val := by
      intro k
      rw [← map_pow, mul_comm, ← MvPolynomial.smul_eq_C_mul, hcoeff, smul_smul, div_eq_mul_inv]
    simp_rw [hterm]
    have hsum : ∀ K, D + 1 ≤ K → ∑ k ∈ Finset.range (D + 1),
        (t ^ k / (k.factorial : ℂ)) • derivationIter (matrixUnitDerivation a b) k p.val =
        ∑ k ∈ Finset.range K,
          (t ^ k / (k.factorial : ℂ)) • derivationIter (matrixUnitDerivation a b) k p.val := by
      intro K hK
      apply Finset.sum_subset (Finset.range_subset_range.mpr hK)
      intro k _ hk
      rw [Finset.mem_range, not_lt] at hk
      have h0 : (rootSubstitution a b p.val).coeff k = 0 :=
        _root_.Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      rw [← hterm, h0, zero_mul]
    rw [hsum (D + 1 + N) (by omega)]
    symm
    trans ∑ k ∈ Finset.range N,
      (t ^ k / (k.factorial : ℂ)) • derivationIter (matrixUnitDerivation a b) k p.val
    · exact Finset.sum_congr rfl fun k _ => by rw [Submodule.coe_smul, flagOrbitLie_pow_val]
    apply Finset.sum_subset (Finset.range_subset_range.mpr (by omega))
    intro k _ hk
    rw [Finset.mem_range, not_lt] at hk
    rw [hvanish k hk, smul_zero]
  diagonal := by
    intro μ t p hp
    apply Subtype.ext
    change polynomialTorus n t p.val = integerWeightScalar μ t • p.val
    ext d
    rw [polynomialTorus_coeff_weight, MvPolynomial.coeff_smul, smul_eq_mul]
    by_cases hd : p.val.coeff d = 0
    · rw [hd, mul_zero, mul_zero]
    · congr 2
      funext j
      have h := congrArg Subtype.val (hp j)
      have hc := congrArg (fun q : MatrixPolynomial n => q.coeff d) h
      simp only [flagOrbitLie_val, Submodule.coe_smul, MvPolynomial.coeff_smul, smul_eq_mul] at hc
      change (rowDerivation (Matrix.single j j 1) p.val).coeff d = _ at hc
      rw [show rowDerivation (Matrix.single j j 1) p.val = matrixUnitDerivation j j p.val from rfl,
        matrixUnitDerivation_diag_coeff] at hc
      exact_mod_cast mul_right_cancel₀ hd hc

/-- E7 for Mathlib representations: an irreducible representation of `GL_n(ℂ)` that integrates a
`GLModule` with a highest-weight vector of weight `λ = shapeWeight m` is equivalent to the
flag-minor representation. -/
theorem nonempty_equiv_flagOrbitRepresentation (M : GLModule n)
    (π : _root_.Representation ℂ (GL (Fin n) ℂ) M) (hπ : M.Integrates π)
    (hirr : π.IsIrreducible) (m : ColumnShape n) (v : M) (hv : v ≠ 0)
    (hwt : v ∈ lieWeightSpace M.lie (dominantWeight m))
    (hinv : ∀ a b : Fin n, a < b → M.lie (Matrix.single a b 1) v = 0) :
    Nonempty (π.Equiv (flagOrbitRepresentation m)) := by
  obtain ⟨e⟩ := nonempty_iso_flagOrbitModule M (hπ.isIrreducible hirr) m v hv hwt hinv
  refine ⟨_root_.Representation.Equiv.mk e.toLinearEquiv fun g => LinearMap.ext fun x => ?_⟩
  exact hπ.intertwining (flagOrbitModule_integrates m) e g x

end
end Schubert.RS.HighestWeight
