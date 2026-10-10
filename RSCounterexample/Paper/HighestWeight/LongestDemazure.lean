import RSCounterexample.Paper.HighestWeight.Stability
import RSCounterexample.Paper.Representation.HighestAnnihilation
import RSCounterexample.Paper.Representation.FlagWeights

/-!
# The flag-minor span is the longest Demazure module and is `U(𝔫⁻)`-cyclic

Let `V = flagOrbitSpan m` be the `GL_n`-span of the highest flag polynomial `v_λ`,
`λ = shapeWeight m`.

* `matrixUnitDerivation_highestFlag_eq_zero`: `E_ab v_λ = 0` unless `b < a` and `λ_a < λ_b`.
  In particular `v_λ` is killed by `𝔫⁺`. For `w` with weakly increasing extremal weight
  `w·λ`, the extremal vector `rowRename w v_λ` is killed by `𝔫⁻`.
* E2 (`flagOrbitSpan_eq_flagDemazure_of_monotone`, `flagOrbitSpan_eq_flagDemazure_longest`):
  `V = U(𝔫⁺)·rowRename w v_λ` for every such `w`, in particular for the longest element `w₀`.
* E3 (`flagOrbitSpan_eq_lowerCyclic`): `V = U(𝔫⁻)·v_λ`.

The proofs use `rootSpan_lie_stable` (a cyclic span under one family of root operators is
`gl_n`-stable) and `isGLStable_of_isLieStable` (a `gl_n`-stable subspace is `GL_n`-stable).
-/

namespace Schubert.RS.HighestWeight

open Schubert.RS.Representation

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : ℕ}

/-! ### Matrix units on flag polynomials -/

theorem polynomialLie_single (a b : Fin n) (p : MatrixPolynomial n) :
    polynomialLie n (Matrix.single a b 1) p = matrixUnitDerivation a b p := rfl

/-- Conjugating by a row permutation relabels matrix units:
`w ∘ E_ab = E_{w a, w b} ∘ w`. -/
theorem rowRename_matrixUnitDerivation (w : Equiv.Perm (Fin n)) (a b : Fin n)
    (p : MatrixPolynomial n) :
    rowRename w (matrixUnitDerivation a b p) =
      matrixUnitDerivation (w a) (w b) (rowRename w p) := by
  have hX : ∀ rc : Fin n × Fin n, rowRename w (matrixUnitDerivation a b (MvPolynomial.X rc)) =
      matrixUnitDerivation (w a) (w b) (rowRename w (MvPolynomial.X rc)) := by
    rintro ⟨r, c⟩
    have hr : rowRename w (MvPolynomial.X (r, c)) = MvPolynomial.X (w r, c) :=
      MvPolynomial.rename_X _ _
    rw [hr, matrixUnitDerivation_X, matrixUnitDerivation_X]
    by_cases h : r = b
    · subst h
      rw [ite_eq_left rfl, ite_eq_left rfl]
      exact MvPolynomial.rename_X _ _
    · rw [ite_eq_right h, ite_eq_right (w.injective.ne h), map_zero]
  induction p using MvPolynomial.induction_on with
  | C c =>
    rw [← MvPolynomial.algebraMap_eq, Derivation.map_algebraMap, map_zero, AlgHom.commutes,
      Derivation.map_algebraMap]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add]
  | mul_X p rc hp =>
    rw [Derivation.leibniz, map_mul, Derivation.leibniz]
    simp only [smul_eq_mul, map_add, map_mul, hp, hX]

theorem rowRename_inv_rowRename (w : Equiv.Perm (Fin n)) (p : MatrixPolynomial n) :
    rowRename w⁻¹ (rowRename w p) = p := by
  rw [rowRename, rowRename, MvPolynomial.rename_rename]
  have h : ((fun rc : Fin n × Fin n => (w⁻¹ rc.1, rc.2)) ∘ fun rc => (w rc.1, rc.2)) = id := by
    funext rc
    simp
  rw [h, MvPolynomial.rename_id_apply]

theorem polynomialGL_rowPermutationUnit (w : Equiv.Perm (Fin n)) (p : MatrixPolynomial n) :
    polynomialGL n (rowPermutationUnit w) p = rowRename w p := by
  change rowAction (rowPermutationMatrix w) p = _
  rw [rowAction_permutation]

/-- `shapeWeight m a + m k ≤ shapeWeight m b` when `b ≤ k < a`. -/
theorem shapeWeight_add_le {m : ColumnShape n} {a b k : Fin n} (hbk : b ≤ k) (hka : k < a) :
    shapeWeight m a + m k ≤ shapeWeight m b := by
  have key : ∀ j, (if a ≤ j then m j else 0) + (if j = k then m k else 0) ≤
      (if b ≤ j then m j else 0) := by
    intro j
    by_cases hjk : j = k
    · subst hjk
      rw [ite_eq_right (not_le.mpr hka), ite_eq_left rfl, ite_eq_left hbk, zero_add]
    · rw [ite_eq_right hjk, add_zero]
      by_cases haj : a ≤ j
      · rw [ite_eq_left haj, ite_eq_left (hbk.trans (hka.le.trans haj))]
      · rw [ite_eq_right haj]
        exact Nat.zero_le _
  calc shapeWeight m a + m k
      = ∑ j, ((if a ≤ j then m j else 0) + (if j = k then m k else 0)) := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ k, ite_eq_left
          (Finset.mem_univ k)]
        rfl
    _ ≤ shapeWeight m b := Finset.sum_le_sum fun j _ => key j

/-- `E_ab v_λ = 0` unless `b < a` and `λ_a < λ_b` (`a ≠ b`). -/
theorem matrixUnitDerivation_highestFlag_eq_zero (m : ColumnShape n) {a b : Fin n}
    (hab : a ≠ b) (h : ¬ (b < a ∧ shapeWeight m a < shapeWeight m b)) :
    matrixUnitDerivation a b (highestFlag m) = 0 := by
  apply derivation_prod_zero
  intro k _
  rw [Derivation.leibniz_pow]
  by_cases hmk : m k = 0
  · rw [hmk, zero_smul]
  · have hf : matrixUnitDerivation a b (flagMinor k) = 0 := by
      by_cases hbk : k < b
      · exact matrixUnitDerivation_minor_absent a b k hbk
      · push Not at hbk
        by_cases hak : a ≤ k
        · exact matrixUnitDerivation_minor_present a b k hab hak hbk
        · push Not at hak
          exfalso
          apply h
          refine ⟨lt_of_le_of_lt hbk hak, ?_⟩
          have := shapeWeight_add_le (m := m) hbk hak
          omega
    rw [hf, smul_zero, smul_zero]

/-- `v_λ` is killed by `𝔫⁺`. -/
theorem highestFlag_upper_invariant (m : ColumnShape n) (a b : Fin n) (h : a < b) :
    matrixUnitDerivation a b (highestFlag m) = 0 :=
  matrixUnitDerivation_highestFlag_eq_zero m h.ne (fun h' => lt_asymm h h'.1)

theorem matrixUnitDerivation_highestFlag_diag (m : ColumnShape n) (a : Fin n) :
    matrixUnitDerivation a a (highestFlag m) = (shapeWeight m a : ℂ) • highestFlag m := by
  rw [diagonalDerivation_of_weight a (highestFlag m) _ (highestFlag_weight m)]
  norm_cast

/-- For `w` whose extremal weight `w·λ` is weakly increasing, `rowRename w v_λ` is killed
by `𝔫⁻`. -/
theorem matrixUnitDerivation_extremalFlag_eq_zero (m : ColumnShape n) (w : Equiv.Perm (Fin n))
    (hw : Monotone (extremalWeight m w)) {a b : Fin n} (hba : b < a) :
    matrixUnitDerivation a b (extremalFlag m w) = 0 := by
  have h := rowRename_matrixUnitDerivation w (w.symm a) (w.symm b) (highestFlag m)
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
  change matrixUnitDerivation a b (rowRename w (highestFlag m)) = 0
  rw [← h, matrixUnitDerivation_highestFlag_eq_zero m (w.symm.injective.ne hba.ne'), map_zero]
  rintro ⟨-, hlt⟩
  have := hw hba.le
  simp only [extremalWeight] at this
  omega

theorem matrixUnitDerivation_extremalFlag_diag (m : ColumnShape n) (w : Equiv.Perm (Fin n))
    (a : Fin n) :
    matrixUnitDerivation a a (extremalFlag m w) =
      (extremalWeight m w a : ℂ) • extremalFlag m w := by
  rw [diagonalDerivation_of_weight a (extremalFlag m w) _ (extremalFlag_weight m w)]
  norm_cast

/-! ### Cyclic spans -/

/-- The `U(𝔫⁺)`-cyclic span is the root span for `a < b`. -/
theorem upperCyclic_eq_rootSpan (p : MatrixPolynomial n) :
    upperCyclic p = rootSpan (polynomialLie n) (fun a b => a < b) p := by
  apply le_antisymm
  · exact upperCyclic_le_of_root_stable p _ (mem_rootSpan_self _ _ p)
      (fun r _ hq => rootSpan_stable (polynomialLie n) _ p r.property hq)
  · exact rootSpan_le _ _ p (upperCyclic_seed p)
      (fun a b hab _ hq => upperCyclic_root_stable p ⟨(a, b), hab⟩ hq)

/-- `U(𝔫⁻)·p`: the smallest subspace containing `p` and stable under `E_ab` for `b < a`. -/
def lowerCyclic (p : MatrixPolynomial n) : Submodule ℂ (MatrixPolynomial n) :=
  rootSpan (polynomialLie n) (fun a b => b < a) p

theorem mem_lowerCyclic_self (p : MatrixPolynomial n) : p ∈ lowerCyclic p :=
  mem_rootSpan_self _ _ p

theorem lowerCyclic_stable (p : MatrixPolynomial n) {a b : Fin n} (hba : b < a)
    {q : MatrixPolynomial n} (hq : q ∈ lowerCyclic p) :
    matrixUnitDerivation a b q ∈ lowerCyclic p :=
  rootSpan_stable (polynomialLie n) (fun a b => b < a) p hba hq

theorem lowerCyclic_le (p : MatrixPolynomial n) {S : Submodule ℂ (MatrixPolynomial n)}
    (hp : p ∈ S) (hS : ∀ a b, b < a → ∀ q ∈ S, matrixUnitDerivation a b q ∈ S) :
    lowerCyclic p ≤ S :=
  rootSpan_le _ _ p hp hS

theorem isLieStable_rootSpan (P : Fin n → Fin n → Prop) (v : MatrixPolynomial n)
    (hv : ∀ a b, ¬ P a b → ∃ c : ℂ, matrixUnitDerivation a b v = c • v) :
    IsLieStable (rootSpan (polynomialLie n) P v) :=
  fun a b q hq => rootSpan_lie_stable (polynomialLie n) P v hv (Matrix.single a b 1) q hq

/-- A `GL_n`-stable subspace containing `v_λ` contains the flag-minor span. -/
theorem flagOrbitSpan_le_of_isGLStable (m : ColumnShape n) {S : Submodule ℂ (MatrixPolynomial n)}
    (hS : IsGLStable S) (hv : highestFlag m ∈ S) : flagOrbitSpan m ≤ S :=
  Submodule.span_le.mpr (by rintro _ ⟨g, rfl⟩; exact hS g _ hv)

/-! ### E2 and E3 -/

/-- E2: for `w` with weakly increasing extremal weight, `V = U(𝔫⁺)·rowRename w v_λ`. -/
theorem flagOrbitSpan_eq_flagDemazure_of_monotone (m : ColumnShape n) (w : Equiv.Perm (Fin n))
    (hw : Monotone (extremalWeight m w)) : flagOrbitSpan m = flagDemazure m w := by
  refine le_antisymm ?_ (flagDemazure_le_flagOrbitSpan m w)
  have hL : IsLieStable (flagDemazure m w) := by
    change IsLieStable (upperCyclic (extremalFlag m w))
    rw [upperCyclic_eq_rootSpan]
    apply isLieStable_rootSpan
    intro a b hab
    rcases lt_trichotomy a b with h | h | h
    · exact absurd h hab
    · subst h
      exact ⟨_, matrixUnitDerivation_extremalFlag_diag m w a⟩
    · exact ⟨0, by rw [zero_smul]; exact matrixUnitDerivation_extremalFlag_eq_zero m w hw h⟩
  have hG := isGLStable_of_isLieStable hL
  apply flagOrbitSpan_le_of_isGLStable m hG
  have hv : highestFlag m = polynomialGL n (rowPermutationUnit w⁻¹) (extremalFlag m w) := by
    rw [polynomialGL_rowPermutationUnit, extremalFlag, rowRename_inv_rowRename]
  rw [hv]
  exact hG _ _ (upperCyclic_seed _)

/-- The longest permutation `w₀ = (i ↦ n - 1 - i)`. -/
def longestPerm (n : ℕ) : Equiv.Perm (Fin n) := Fin.revPerm

theorem extremalWeight_longestPerm (m : ColumnShape n) (i : Fin n) :
    extremalWeight m (longestPerm n) i = shapeWeight m (Fin.rev i) := rfl

theorem extremalWeight_longestPerm_monotone (m : ColumnShape n) :
    Monotone (extremalWeight m (longestPerm n)) := by
  intro i j hij
  rw [extremalWeight_longestPerm, extremalWeight_longestPerm]
  exact shapeWeight_antitone m (Fin.rev_le_rev.mpr hij)

/-- E2: the flag-minor span is the longest Demazure module `D_{w₀}(λ)`. -/
theorem flagOrbitSpan_eq_flagDemazure_longest (m : ColumnShape n) :
    flagOrbitSpan m = flagDemazure m (longestPerm n) :=
  flagOrbitSpan_eq_flagDemazure_of_monotone m _ (extremalWeight_longestPerm_monotone m)

/-- E3: the flag-minor span is `U(𝔫⁻)·v_λ`. -/
theorem flagOrbitSpan_eq_lowerCyclic (m : ColumnShape n) :
    flagOrbitSpan m = lowerCyclic (highestFlag m) := by
  have hL : IsLieStable (lowerCyclic (highestFlag m)) := by
    apply isLieStable_rootSpan
    intro a b hab
    rcases lt_trichotomy a b with h | h | h
    · exact ⟨0, by rw [zero_smul]; exact highestFlag_upper_invariant m a b h⟩
    · subst h
      exact ⟨_, matrixUnitDerivation_highestFlag_diag m a⟩
    · exact absurd h hab
  refine le_antisymm (flagOrbitSpan_le_of_isGLStable m (isGLStable_of_isLieStable hL)
    (mem_lowerCyclic_self _)) ?_
  exact lowerCyclic_le _ (highestFlag_mem_orbitSpan m)
    (fun a b _ q hq => flagOrbitSpan_isLieStable m a b q hq)

end
end Schubert.RS.HighestWeight
