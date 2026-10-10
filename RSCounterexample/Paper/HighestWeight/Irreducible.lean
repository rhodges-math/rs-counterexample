import RSCounterexample.Paper.HighestWeight.HighestWeightData
import RSCounterexample.Paper.HighestWeight.FischerForm

/-!
# Irreducibility of the flag-minor span (E6)

* `flagOrbitSpan_upperInvariants`: the `𝔫⁺`-invariants of `V = flagOrbitSpan m` are exactly
  `ℂ·v_λ`. By E3, `V = ℂ·v_λ + Σ_{b<a} E_ab V`, and a `𝔫⁺`-invariant vector is Fischer-orthogonal
  to every `E_ab x` with `b < a`, because the adjoint of `E_ab` is `E_ba` (E5). Writing an
  invariant `w` as `c·v_λ + l`, both `w` and `v_λ` are orthogonal to `l`, so `⟨l, l⟩ = 0`.
* `flagOrbitSpan_irreducible_lie`, `flagOrbitSpan_irreducible`: a nonzero `gl_n`-stable (or
  `GL_n`-stable) subspace `W ⊆ V` contains a weight vector of least depth. That vector is
  killed by `𝔫⁺`, so it is a nonzero multiple of `v_λ`. Hence `W ∋ v_λ`, and `W = V`.
-/

namespace Schubert.RS.HighestWeight

open Schubert.RS.Representation

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : ℕ}

/-- The span of the lowered vectors `E_ab x` (`b < a`, `x ∈ V`). -/
def loweredSpan (m : ColumnShape n) : Submodule ℂ (MatrixPolynomial n) :=
  Submodule.span ℂ
    {y | ∃ a b : Fin n, b < a ∧ ∃ x ∈ flagOrbitSpan m, y = matrixUnitDerivation a b x}

/-- A `𝔫⁺`-invariant vector is Fischer-orthogonal to all lowered vectors. -/
theorem fischer_loweredSpan_eq_zero (m : ColumnShape n) {u : MatrixPolynomial n}
    (hu : ∀ a b : Fin n, a < b → matrixUnitDerivation a b u = 0) {y : MatrixPolynomial n}
    (hy : y ∈ loweredSpan m) : fischer u y = 0 := by
  have hker : loweredSpan m ≤ LinearMap.ker (fischerRight u) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, b, hba, x, _, rfl⟩
    change fischer u (matrixUnitDerivation a b x) = 0
    rw [← fischer_matrixUnitDerivation b a u x, hu b a hba, fischer_zero_left]
  exact hker hy

/-- `V = ℂ·v_λ + Σ_{b<a} E_ab V`. -/
theorem flagOrbitSpan_le_sup (m : ColumnShape n) :
    flagOrbitSpan m ≤ (ℂ ∙ highestFlag m) ⊔ loweredSpan m := by
  have hsupV : (ℂ ∙ highestFlag m) ⊔ loweredSpan m ≤ flagOrbitSpan m :=
    sup_le ((Submodule.span_singleton_le_iff_mem _ _).mpr (highestFlag_mem_orbitSpan m))
      (Submodule.span_le.mpr (by
        rintro _ ⟨a, b, _, x, hx, rfl⟩
        exact flagOrbitSpan_isLieStable m a b x hx))
  rw [flagOrbitSpan_eq_lowerCyclic]
  refine lowerCyclic_le _ (Submodule.mem_sup_left (Submodule.mem_span_singleton_self _)) ?_
  intro a b hba q hq
  refine Submodule.mem_sup_right (Submodule.subset_span ⟨a, b, hba, q, ?_, rfl⟩)
  exact hsupV hq

/-- E6: the `𝔫⁺`-invariants of the flag-minor span are the line `ℂ·v_λ`. -/
theorem flagOrbitSpan_upperInvariants (m : ColumnShape n) (w : MatrixPolynomial n)
    (hw : w ∈ flagOrbitSpan m)
    (hinv : ∀ a b : Fin n, a < b → matrixUnitDerivation a b w = 0) :
    w ∈ ℂ ∙ highestFlag m := by
  obtain ⟨y, hy, l, hl, rfl⟩ := Submodule.mem_sup.mp (flagOrbitSpan_le_sup m hw)
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
  have hl0 : l = 0 := by
    apply fischer_self_eq_zero
    have h1 := fischer_loweredSpan_eq_zero m hinv hl
    have h2 := fischer_loweredSpan_eq_zero m (highestFlag_upper_invariant m) hl
    rw [fischer_add_left, fischer_smul_left, h2, mul_zero, zero_add] at h1
    exact h1
  rw [hl0, add_zero]
  exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self _)

/-- A nonzero weight vector has a weight of nonnegative depth. -/
theorem weightDepth_nonneg {w : MatrixPolynomial n} (hw : w ≠ 0) {μ : Weight n}
    (hμ : w ∈ torusWeightSpace (polynomialTorus n) μ) : 0 ≤ weightDepth μ := by
  obtain ⟨e, he⟩ := MvPolynomial.support_nonempty.mpr hw
  rw [← support_weight_of_mem_weightSpace hμ he]
  refine Finset.sum_nonneg fun i _ => mul_nonneg (Int.natCast_nonneg _) ?_
  exact Int.natCast_nonneg _

/-- A nonzero `gl_n`-stable subspace contains a nonzero torus weight vector. -/
theorem exists_weightVector {W : Submodule ℂ (MatrixPolynomial n)} (hL : IsLieStable W)
    (hne : W ≠ ⊥) :
    ∃ w ∈ W, w ≠ 0 ∧ ∃ μ, w ∈ torusWeightSpace (polynomialTorus n) μ := by
  by_contra hno
  push Not at hno
  apply hne
  have htorus := torus_stable_of_diagonal_stable (fun a => hL a a)
  rw [← polynomialWeightSpan_eq W (fun t p hp => htorus t p hp), eq_bot_iff]
  apply Submodule.span_le.mpr
  rintro q ⟨hqW, μ, hμ⟩
  rw [SetLike.mem_coe, Submodule.mem_bot]
  by_contra hq
  exact hno q hqW hq μ hμ

/-- E6: the flag-minor span is irreducible as a `gl_n`-module. -/
theorem flagOrbitSpan_irreducible_lie (m : ColumnShape n) (W : Submodule ℂ (MatrixPolynomial n))
    (hW : W ≤ flagOrbitSpan m) (hL : IsLieStable W) : W = ⊥ ∨ W = flagOrbitSpan m := by
  classical
  by_cases hne : W = ⊥
  · exact Or.inl hne
  right
  apply le_antisymm hW
  have hex : ∃ k : ℕ, ∃ w ∈ W, w ≠ 0 ∧
      ∃ μ, w ∈ torusWeightSpace (polynomialTorus n) μ ∧ weightDepth μ = k := by
    obtain ⟨w, hwW, hw0, μ, hμ⟩ := exists_weightVector hL hne
    exact ⟨(weightDepth μ).toNat, w, hwW, hw0, μ, hμ,
      (Int.toNat_of_nonneg (weightDepth_nonneg hw0 hμ)).symm⟩
  obtain ⟨w, hwW, hw0, μ, hμ, hk⟩ := Nat.find_spec hex
  have hinv : ∀ a b : Fin n, a < b → matrixUnitDerivation a b w = 0 := by
    intro a b hab
    by_contra hne'
    have hμ' := matrixUnitDerivation_mem_weightSpace a b hμ
    have hdepth := weightDepth_rootShift μ a b
    have h0 := weightDepth_nonneg hne' hμ'
    have hab' : (a : ℤ) < b := by exact_mod_cast hab
    have hlt : (weightDepth (μ + (Pi.single a 1 - Pi.single b 1))).toNat < Nat.find hex := by
      omega
    exact Nat.find_min hex hlt ⟨_, hL a b w hwW, hne', _, hμ', (Int.toNat_of_nonneg h0).symm⟩
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp
    (flagOrbitSpan_upperInvariants m w (hW hwW) hinv)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc
    exact hw0 hc.symm
  have hv : highestFlag m ∈ W := by
    have h : highestFlag m = c⁻¹ • w := by rw [← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    rw [h]
    exact W.smul_mem _ hwW
  exact flagOrbitSpan_le_of_isGLStable m (isGLStable_of_isLieStable hL) hv

/-- E6: the flag-minor span is irreducible as a `GL_n(ℂ)`-module. -/
theorem flagOrbitSpan_irreducible (m : ColumnShape n) (W : Submodule ℂ (MatrixPolynomial n))
    (hW : W ≤ flagOrbitSpan m) (hG : IsGLStable W) : W = ⊥ ∨ W = flagOrbitSpan m :=
  flagOrbitSpan_irreducible_lie m W hW (isLieStable_of_isGLStable hG)

end
end Schubert.RS.HighestWeight
