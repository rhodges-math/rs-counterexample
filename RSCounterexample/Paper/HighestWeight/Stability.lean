import RSCounterexample.Paper.HighestWeight.RootSpan
import RSCounterexample.Paper.JosephPolo.OrbitSpan
import RSCounterexample.Paper.Representation.FlagWeyl
import RSCounterexample.Paper.PolynomialDiagonalWeights
import Mathlib.LinearAlgebra.Matrix.Transvection

/-!
# Group and Lie-algebra stability of polynomial subspaces

A subspace `S ⊆ ℂ[X_{rc}]` is stable under `GL_n(ℂ)` (acting on the row index) iff it is stable
under every matrix-unit derivation `E_ab` (`isGLStable_iff_isLieStable`). No finiteness is
needed: each `E_ab` with `a ≠ b` is locally nilpotent, and
`rowAction (1 + t E_ab) = Σ_k t^k E_ab^k / k!` (the Taylor expansion `rootSubstitution`). A
subspace stable under the diagonal derivations `E_aa` is spanned by torus weight vectors, and
every invertible matrix is a product of transvections and a diagonal matrix.

In particular the flag-minor span `flagOrbitSpan m` is `gl_n`-stable (E1), and it contains every
Demazure module `flagDemazure m w` (`flagDemazure_le_flagOrbitSpan`).
-/

namespace Schubert.RS.HighestWeight

open Schubert.RS.Representation

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : ℕ}

/-- `S` is stable under the action of `GL_n(ℂ)` on the row index. -/
def IsGLStable (S : Submodule ℂ (MatrixPolynomial n)) : Prop :=
  ∀ g : (Square n)ˣ, ∀ p ∈ S, polynomialGL n g p ∈ S

/-- `S` is stable under every matrix-unit derivation `E_ab`, i.e. under `gl_n`. -/
def IsLieStable (S : Submodule ℂ (MatrixPolynomial n)) : Prop :=
  ∀ a b : Fin n, ∀ p ∈ S, matrixUnitDerivation a b p ∈ S

/-! ### Units: transvections and diagonal matrices -/

/-- The transvection `1 + t E_ab` (`a ≠ b`) as a unit. -/
def transvectionUnit {a b : Fin n} (hab : a ≠ b) (t : ℂ) : (Square n)ˣ where
  val := 1 + t • Matrix.single a b 1
  inv := 1 - t • Matrix.single a b 1
  val_inv := by
    rw [add_mul, one_mul, mul_sub, mul_one, smul_mul_smul_comm,
      Matrix.single_mul_single_of_ne (h := hab.symm), smul_zero]
    abel
  inv_val := by
    rw [sub_mul, one_mul, mul_add, mul_one, smul_mul_smul_comm,
      Matrix.single_mul_single_of_ne (h := hab.symm), smul_zero]
    abel

/-- An invertible diagonal matrix, from a point of the diagonal torus. -/
def diagonalUnit (t : DiagonalTorus n) : (Square n)ˣ where
  val := Matrix.diagonal fun i => (t i : ℂ)
  inv := Matrix.diagonal fun i => ((t i)⁻¹ : ℂˣ)
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]

theorem polynomialGL_transvectionUnit {a b : Fin n} (hab : a ≠ b) (t : ℂ)
    (p : MatrixPolynomial n) :
    polynomialGL n (transvectionUnit hab t) p = rowAction (1 + t • Matrix.single a b 1) p := rfl

theorem polynomialGL_diagonalUnit (t : DiagonalTorus n) (p : MatrixPolynomial n) :
    polynomialGL n (diagonalUnit t) p = polynomialTorus n t p := rfl

/-! ### From the group to the Lie algebra -/

/-- If all transvections `1 + t E_ab` map `p` into `S`, then `E_ab p ∈ S` (`a ≠ b`): the
coefficient of `t` in `rowAction (1 + t E_ab) p` is `E_ab p`. -/
theorem matrixUnitDerivation_mem_of_rowActions_mem (S : Submodule ℂ (MatrixPolynomial n))
    {a b : Fin n} (hab : a ≠ b) (p : MatrixPolynomial n)
    (h : ∀ t : ℂ, rowAction (1 + t • Matrix.single a b (1 : ℂ)) p ∈ S) :
    matrixUnitDerivation a b p ∈ S := by
  let : Infinite ℂ := Infinite.of_injective (fun k : ℕ => (k : ℂ)) Nat.cast_injective
  have hc : (rootSubstitution a b p).coeff 1 ∈ S :=
    polynomial_coeff_mem_of_eval_mem S _ (fun t => by
      change (rootSubstitution a b p).eval (MvPolynomial.C t) ∈ S
      rw [rootSubstitution_eval]
      exact h t) 1
  have he := rootSubstitution_coeff a b hab p 1
  have he' : (rootSubstitution a b p).coeff 1 = matrixUnitDerivation a b p := by
    simpa [derivationIter_succ] using he
  rwa [he'] at hc

/-- A `GL_n`-stable subspace is stable under the diagonal torus. -/
theorem IsGLStable.torus_stable {S : Submodule ℂ (MatrixPolynomial n)} (hS : IsGLStable S)
    (t : DiagonalTorus n) : ∀ p ∈ S, polynomialTorus n t p ∈ S :=
  fun p hp => hS (diagonalUnit t) p hp

/-- A torus-stable subspace is stable under the diagonal derivations `E_aa`: it is spanned by
weight vectors, on which `E_aa` acts by a scalar. -/
theorem diagonal_stable_of_torus_stable {S : Submodule ℂ (MatrixPolynomial n)}
    (hS : ∀ t, ∀ p ∈ S, polynomialTorus n t p ∈ S) (a : Fin n) :
    ∀ p ∈ S, matrixUnitDerivation a a p ∈ S := by
  intro p hp
  rw [← polynomialWeightSpan_eq S (fun t p hp => hS t p hp)] at hp ⊢
  induction hp using Submodule.span_induction with
  | mem q hq =>
    obtain ⟨hqS, v, hv⟩ := hq
    rw [diagonalDerivation_of_weight a q v hv]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨hqS, v, hv⟩)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [(matrixUnitDerivation a a).map_smul]; exact Submodule.smul_mem _ c hx

/-- `GL_n`-stability implies `gl_n`-stability. -/
theorem isLieStable_of_isGLStable {S : Submodule ℂ (MatrixPolynomial n)} (hS : IsGLStable S) :
    IsLieStable S := by
  intro a b p hp
  by_cases hab : a = b
  · subst hab
    exact diagonal_stable_of_torus_stable hS.torus_stable a p hp
  · exact matrixUnitDerivation_mem_of_rowActions_mem S hab p
      (fun t => hS (transvectionUnit hab t) p hp)

/-! ### From the Lie algebra to the group -/

/-- `E_aa` multiplies the coefficient of a monomial by its row-`a` degree. -/
theorem matrixUnitDerivation_diag_coeff (a : Fin n) (p : MatrixPolynomial n)
    (d : (Fin n × Fin n) →₀ ℕ) :
    (matrixUnitDerivation a a p).coeff d = (matrixMonomialWeight d a : ℂ) * p.coeff d := by
  have he := basis_coord_eigenmap (MvPolynomial.basisMonomials (Fin n × Fin n) ℂ)
    (matrixUnitDerivation a a).toLinearMap (fun d => (matrixMonomialWeight d a : ℂ))
    (diagonalDerivation_monomial a) d p
  change (matrixUnitDerivation a a p).coeff d =
    (matrixMonomialWeight d a : ℂ) * p.coeff d at he
  exact he

/-- The filter `(x - y)⁻¹ (E_aa - y)`, which keeps the monomials of row-`a` degree `x` and kills
those of row-`a` degree `y`. -/
def diagonalFilter (a : Fin n) (x y : ℂ) (p : MatrixPolynomial n) : MatrixPolynomial n :=
  (x - y)⁻¹ • (matrixUnitDerivation a a p - y • p)

theorem diagonalFilter_coeff (a : Fin n) (x y : ℂ) (p : MatrixPolynomial n)
    (d : (Fin n × Fin n) →₀ ℕ) :
    (diagonalFilter a x y p).coeff d =
      (x - y)⁻¹ * ((matrixMonomialWeight d a : ℂ) - y) * p.coeff d := by
  rw [diagonalFilter, MvPolynomial.coeff_smul, MvPolynomial.coeff_sub, MvPolynomial.coeff_smul,
    matrixUnitDerivation_diag_coeff, smul_eq_mul, smul_eq_mul]
  ring

/-- A subspace stable under all `E_aa` is spanned by the torus weight vectors it contains. -/
theorem mem_polynomialWeightSpan_of_diagonal_stable (S : Submodule ℂ (MatrixPolynomial n))
    (hS : ∀ a, ∀ p ∈ S, matrixUnitDerivation a a p ∈ S) (p : MatrixPolynomial n)
    (hp : p ∈ S) : p ∈ polynomialWeightSpan S := by
  classical
  by_cases hp0 : p = 0
  · rw [hp0]; exact Submodule.zero_mem _
  have hsupport : p.support.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro hz
    exact hp0 (MvPolynomial.support_eq_empty.mp hz)
  obtain ⟨d, hd⟩ := hsupport
  by_cases hh : ∀ e ∈ p.support, matrixMonomialWeight e = matrixMonomialWeight d
  · apply Submodule.subset_span
    refine ⟨hp, matrixMonomialWeight d, fun t => ?_⟩
    ext e
    rw [polynomialTorus_coeff_weight, MvPolynomial.coeff_smul, smul_eq_mul]
    by_cases he : e ∈ p.support
    · rw [hh e he]
    · rw [MvPolynomial.notMem_support_iff.mp he, mul_zero, mul_zero]
  · push Not at hh
    obtain ⟨e, he, hweight⟩ := hh
    obtain ⟨a, ha⟩ : ∃ a, matrixMonomialWeight e a ≠ matrixMonomialWeight d a := by
      by_contra hn
      push Not at hn
      exact hweight (funext hn)
    set x : ℂ := (matrixMonomialWeight d a : ℂ)
    set y : ℂ := (matrixMonomialWeight e a : ℂ)
    have hxy : x - y ≠ 0 := by
      rw [sub_ne_zero]
      intro h
      exact ha (Int.cast_injective h).symm
    let q := diagonalFilter a x y p
    have hq : q ∈ S := S.smul_mem _ (S.sub_mem (hS a p hp) (S.smul_mem _ hp))
    have hr : p - q ∈ S := S.sub_mem hp hq
    have hq_sub : q.support ⊆ p.support.erase e := by
      intro f hf
      rw [MvPolynomial.mem_support_iff, diagonalFilter_coeff] at hf
      refine Finset.mem_erase.mpr ⟨fun hfe => ?_, ?_⟩
      · subst hfe
        exact hf (by simp [y])
      · rw [MvPolynomial.mem_support_iff]
        intro hz
        exact hf (by rw [hz, mul_zero])
    have hr_sub : (p - q).support ⊆ p.support.erase d := by
      intro f hf
      rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_sub, diagonalFilter_coeff] at hf
      refine Finset.mem_erase.mpr ⟨fun hfd => ?_, ?_⟩
      · subst hfd
        apply hf
        rw [show ((matrixMonomialWeight f a : ℤ) : ℂ) = x from rfl, inv_mul_cancel₀ hxy, one_mul,
          sub_self]
      · rw [MvPolynomial.mem_support_iff]
        intro hz
        exact hf (by rw [hz, mul_zero, sub_zero])
    have hq_lt : q.support.card < p.support.card :=
      (Finset.card_le_card hq_sub).trans_lt (Finset.card_erase_lt_of_mem he)
    have hr_lt : (p - q).support.card < p.support.card :=
      (Finset.card_le_card hr_sub).trans_lt (Finset.card_erase_lt_of_mem hd)
    have hqm := mem_polynomialWeightSpan_of_diagonal_stable S hS q hq
    have hrm := mem_polynomialWeightSpan_of_diagonal_stable S hS (p - q) hr
    have heq : p = q + (p - q) := by abel
    rw [heq]
    exact Submodule.add_mem _ hqm hrm
termination_by p.support.card

/-- A subspace stable under all `E_aa` is stable under the diagonal torus. -/
theorem torus_stable_of_diagonal_stable {S : Submodule ℂ (MatrixPolynomial n)}
    (hS : ∀ a, ∀ p ∈ S, matrixUnitDerivation a a p ∈ S) (t : DiagonalTorus n) :
    ∀ p ∈ S, polynomialTorus n t p ∈ S := by
  intro p hp
  have hw := mem_polynomialWeightSpan_of_diagonal_stable S hS p hp
  clear hp
  induction hw using Submodule.span_induction with
  | mem q hq =>
    obtain ⟨hqS, v, hv⟩ := hq
    rw [hv t]
    exact S.smul_mem _ hqS
  | zero => rw [map_zero]; exact S.zero_mem
  | add x y _ _ hx hy => rw [map_add]; exact S.add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact S.smul_mem c hx

/-- A subspace stable under `E_ab` (`a ≠ b`) is stable under the transvections `1 + t E_ab`:
`rowAction (1 + t E_ab) p = Σ_k t^k E_ab^k p / k!`. -/
theorem rowAction_transvection_mem {S : Submodule ℂ (MatrixPolynomial n)} {a b : Fin n}
    (hab : a ≠ b) (hS : ∀ p ∈ S, matrixUnitDerivation a b p ∈ S) (t : ℂ) :
    ∀ p ∈ S, rowAction (1 + t • Matrix.single a b 1) p ∈ S := by
  intro p hp
  have hiter : ∀ k, ∀ q ∈ S, derivationIter (matrixUnitDerivation a b) k q ∈ S := by
    intro k
    induction k with
    | zero => intro q hq; exact hq
    | succ k ih => intro q hq; rw [derivationIter_succ]; exact hS _ (ih q hq)
  have hcoeff : ∀ k, (rootSubstitution a b p).coeff k ∈ S := by
    intro k
    have he := rootSubstitution_coeff a b hab p k
    have hk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
    have hc : (rootSubstitution a b p).coeff k =
        ((k.factorial : ℂ))⁻¹ • derivationIter (matrixUnitDerivation a b) k p := by
      rw [← he, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hk, one_smul]
    rw [hc]
    exact S.smul_mem _ (hiter k p hp)
  rw [← rootSubstitution_eval, _root_.Polynomial.eval_eq_sum_range]
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [← map_pow, mul_comm, ← MvPolynomial.smul_eq_C_mul]
  exact S.smul_mem _ (hcoeff k)

/-- `gl_n`-stability implies `GL_n`-stability. -/
theorem isGLStable_of_isLieStable {S : Submodule ℂ (MatrixPolynomial n)} (hS : IsLieStable S) :
    IsGLStable S := by
  classical
  have htv : ∀ L : List (Matrix.TransvectionStruct (Fin n) ℂ), ∀ p ∈ S,
      rowAction (L.map Matrix.TransvectionStruct.toMatrix).prod p ∈ S := by
    intro L
    induction L with
    | nil => intro p hp; rw [List.map_nil, List.prod_nil, rowAction_one]; exact hp
    | cons x L ih =>
      intro p hp
      rw [List.map_cons, List.prod_cons, rowAction_mul, AlgHom.comp_apply]
      have hx : x.toMatrix = 1 + x.c • Matrix.single x.i x.j 1 := by
        rw [Matrix.TransvectionStruct.toMatrix, Matrix.transvection, Matrix.smul_single,
          smul_eq_mul, mul_one]
      rw [hx]
      exact rowAction_transvection_mem x.hij (hS x.i x.j) x.c _ (ih p hp)
  intro g p hp
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
  let t : DiagonalTorus n := fun i => Units.mk0 (D i) (hD i)
  have hdiag : rowAction (Matrix.diagonal D) = rowAction (Matrix.diagonal fun i => (t i : ℂ)) :=
    rfl
  change rowAction g.val p ∈ S
  rw [hg, rowAction_mul, rowAction_mul, AlgHom.comp_apply, AlgHom.comp_apply, hdiag]
  apply htv
  exact torus_stable_of_diagonal_stable (fun a => hS a a) t _ (htv L' p hp)

theorem isGLStable_iff_isLieStable (S : Submodule ℂ (MatrixPolynomial n)) :
    IsGLStable S ↔ IsLieStable S :=
  ⟨isLieStable_of_isGLStable, isGLStable_of_isLieStable⟩

/-! ### The flag-minor span -/

theorem flagOrbitSpan_isGLStable (m : ColumnShape n) : IsGLStable (flagOrbitSpan m) :=
  fun g _ hp => flagOrbitSpan_stable m g hp

/-- E1: the flag-minor span is stable under `gl_n`. -/
theorem flagOrbitSpan_isLieStable (m : ColumnShape n) : IsLieStable (flagOrbitSpan m) :=
  isLieStable_of_isGLStable (flagOrbitSpan_isGLStable m)

theorem flagOrbitSpan_torus_stable (m : ColumnShape n) (t : DiagonalTorus n) :
    ∀ p ∈ flagOrbitSpan m, polynomialTorus n t p ∈ flagOrbitSpan m :=
  (flagOrbitSpan_isGLStable m).torus_stable t

/-- Every Demazure module lies in the flag-minor span. -/
theorem flagDemazure_le_flagOrbitSpan (m : ColumnShape n) (w : Equiv.Perm (Fin n)) :
    flagDemazure m w ≤ flagOrbitSpan m :=
  upperCyclic_le_of_root_stable _ _ (extremalFlag_mem_orbitSpan m w)
    (fun _ q hq => flagOrbitSpan_isLieStable m _ _ q hq)

end
end Schubert.RS.HighestWeight
