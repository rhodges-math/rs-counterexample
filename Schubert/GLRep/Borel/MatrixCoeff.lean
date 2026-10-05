import Schubert.GLRep.Borel.Vanishing

/-!
# Matrix coefficients and orbit spans

For a rational representation `ρ` of `GL_n(K)` (`K` infinite) and a vector `v`, the matrix
coefficients `g ↦ φ(ρ(g) v)`, `φ ∈ V^∨`, are regular functions (`GLRep.matrixCoeff`). If `v` is a
`B`-eigenvector, `ρ(b) v = η(b)⁻¹ v`, they lie in `ind_B^G(η)`, and `φ ↦ (g ↦ φ(ρ(g) v))` is a map
of representations `V^∨ → ind_B^G(η)` (`GLRep.dualToInducedRep`).

A matrix coefficient vanishes on a set `Z ⊆ GL_n(K)` exactly when `φ` annihilates the span
`⟨ρ(g) v : g ∈ Z⟩` (`GLRep.orbitSpan`, `GLRep.matrixCoeff_mem_vanishingIdeal_iff`); for `Z` stable
under left multiplication by `B`, this span is a subrepresentation of the restriction to `B`
(`GLRep.orbitSubrep`). These are the Demazure modules of `FlagVarieties.demazureSubrep`.
-/

namespace GLRep

open Module TauCeti

noncomputable section

variable {K : Type*} [Field K] {n : ℕ}
variable {W : Type*} [AddCommGroup W] [Module K W] {ρ : Representation K (GL (Fin n) K) W}

/-! ### Orbit spans -/

variable (ρ) in
/-- The span `⟨ρ(g) v : g ∈ Z⟩`. -/
def orbitSpan (v : W) (Z : Set (GL (Fin n) K)) : Submodule K W :=
  Submodule.span K ((fun g => ρ g v) '' Z)

theorem apply_mem_orbitSpan {v : W} {Z : Set (GL (Fin n) K)} {g : GL (Fin n) K} (hg : g ∈ Z) :
    ρ g v ∈ orbitSpan ρ v Z :=
  Submodule.subset_span ⟨g, hg, rfl⟩

theorem mem_dualAnnihilator_orbitSpan_iff {v : W} {Z : Set (GL (Fin n) K)} {φ : Dual K W} :
    φ ∈ (orbitSpan ρ v Z).dualAnnihilator ↔ ∀ g ∈ Z, φ (ρ g v) = 0 := by
  rw [Submodule.mem_dualAnnihilator]
  constructor
  · exact fun h g hg => h _ (apply_mem_orbitSpan hg)
  · intro h w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨g, hg, rfl⟩ := hw
      exact h g hg
    | zero => exact map_zero φ
    | add w w' _ _ hw hw' => rw [map_add, hw, hw', add_zero]
    | smul c w _ hw => rw [map_smul, hw, smul_zero]

theorem orbitSpan_univ_eq_top_of_isIrreducible (hirr : ρ.IsIrreducible) {v : W} (hv : v ≠ 0) :
    orbitSpan ρ v Set.univ = ⊤ := by
  let U : Subrepresentation ρ := ⟨orbitSpan ρ v Set.univ, fun g w hw => by
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨h, -, rfl⟩ := hw
      rw [← Module.End.mul_apply, ← map_mul]
      exact apply_mem_orbitSpan (Set.mem_univ _)
    | zero => rw [map_zero]; exact zero_mem _
    | add w w' _ _ hw hw' => rw [map_add]; exact add_mem hw hw'
    | smul c w _ hw => rw [map_smul]; exact Submodule.smul_mem _ c hw⟩
  rcases IsSimpleOrder.eq_bot_or_eq_top U with h | h
  · exfalso
    have h1 : v ∈ U.toSubmodule := by
      have := apply_mem_orbitSpan (ρ := ρ) (v := v) (Set.mem_univ (1 : GL (Fin n) K))
      rwa [map_one, Module.End.one_apply] at this
    have h2 : U.toSubmodule = ⊥ := congrArg Subrepresentation.toSubmodule h
    rw [h2, Submodule.mem_bot] at h1
    exact hv h1
  · exact congrArg Subrepresentation.toSubmodule h

/-- An orbit span over a set stable under left multiplication by `B` is a subrepresentation of
the restriction to `B`. -/
def orbitSubrep (v : W) (Z : Set (GL (Fin n) K))
    (hZ : ∀ b : borel K n, ∀ g ∈ Z, (b : GL (Fin n) K) * g ∈ Z) :
    Subrepresentation (ρ.comp (borel K n).subtype) :=
  ⟨orbitSpan ρ v Z, fun b w hw => by
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨g, hg, rfl⟩ := hw
      change ρ b (ρ g v) ∈ _
      rw [← Module.End.mul_apply, ← map_mul]
      exact apply_mem_orbitSpan (hZ b g hg)
    | zero => rw [map_zero]; exact zero_mem _
    | add w w' _ _ hw hw' => rw [map_add]; exact add_mem hw hw'
    | smul c w _ hw => rw [map_smul]; exact Submodule.smul_mem _ c hw⟩

@[simp]
theorem toSubmodule_orbitSubrep (v : W) (Z : Set (GL (Fin n) K))
    (hZ : ∀ b : borel K n, ∀ g ∈ Z, (b : GL (Fin n) K) * g ∈ Z) :
    (orbitSubrep (ρ := ρ) v Z hZ).toSubmodule = orbitSpan ρ v Z :=
  rfl

/-! ### Matrix coefficients -/

variable [Infinite K]


/-- The matrix coefficients `g ↦ φ(ρ(g) v)` of a rational representation, as regular functions. -/
def matrixCoeff (hρ : IsRationalRep ρ) (v : W) : Dual K W →ₗ[K] GLCoord K n where
  toFun φ := (glEvalEquiv K n).symm
    ⟨fun g => φ (ρ g v), hρ.hasCoeffsIn_glRegularFunctions.coeff_mem φ v⟩
  map_add' φ ψ := glCoord_ext fun g => by
    rw [map_add, glEval_glEvalEquiv_symm, glEval_glEvalEquiv_symm, glEval_glEvalEquiv_symm]
    rfl
  map_smul' c φ := glCoord_ext fun g => by
    rw [map_smul, glEval_glEvalEquiv_symm, glEval_glEvalEquiv_symm]
    rfl

theorem glEval_matrixCoeff (hρ : IsRationalRep ρ) (v : W) (φ : Dual K W) (g : GL (Fin n) K) :
    glEval g (matrixCoeff hρ v φ) = φ (ρ g v) :=
  glEval_glEvalEquiv_symm _ g

/-- Left translation of matrix coefficients is the dual action. -/
theorem leftTranslHom_matrixCoeff (hρ : IsRationalRep ρ) (v : W) (g : GL (Fin n) K)
    (φ : Dual K W) :
    leftTranslHom K n g (matrixCoeff hρ v φ) = matrixCoeff hρ v (ρ.dual g φ) :=
  glCoord_ext fun x => by
    rw [glEval_leftTranslHom, glEval_matrixCoeff, glEval_matrixCoeff, Representation.dual_apply,
      map_mul]
    rfl

/-- The matrix coefficients of a `B`-eigenvector lie in `ind_B^G(η)`. -/
theorem matrixCoeff_mem_indBorelSubrep (hρ : IsRationalRep ρ) {v : W} {η : Fin n → ℤ}
    (hv : ∀ b : borel K n, ρ b v = (((borelChar K n η b)⁻¹ : Kˣ) : K) • v) (φ : Dual K W) :
    matrixCoeff hρ v φ ∈ (indBorelSubrep K n η).toSubmodule := by
  rw [mem_indBorelSubrep_iff_glEval]
  intro g b
  rw [glEval_matrixCoeff, glEval_matrixCoeff, map_mul, Module.End.mul_apply, hv b, map_smul,
    map_smul, smul_eq_mul]

/-- **`V^∨ → ind_B^G(η)`, `φ ↦ (g ↦ φ(ρ(g) v))`**, for a `B`-eigenvector `v`. -/
def dualToInducedRep (hρ : IsRationalRep ρ) {v : W} {η : Fin n → ℤ}
    (hv : ∀ b : borel K n, ρ b v = (((borelChar K n η b)⁻¹ : Kˣ) : K) • v) :
    ρ.dual.IntertwiningMap (indBorelRep K n η) where
  toLinearMap := (matrixCoeff hρ v).codRestrict _ (matrixCoeff_mem_indBorelSubrep hρ hv)
  isIntertwining' g := LinearMap.ext fun φ =>
    Subtype.ext (leftTranslHom_matrixCoeff hρ v g φ).symm

@[simp]
theorem coe_dualToInducedRep_apply (hρ : IsRationalRep ρ) {v : W} {η : Fin n → ℤ}
    (hv : ∀ b : borel K n, ρ b v = (((borelChar K n η b)⁻¹ : Kˣ) : K) • v) (φ : Dual K W) :
    (dualToInducedRep hρ hv φ : GLCoord K n) = matrixCoeff hρ v φ :=
  rfl

/-- **A matrix coefficient vanishes on `Z` iff `φ` annihilates `⟨ρ(g) v : g ∈ Z⟩`.** -/
theorem matrixCoeff_mem_vanishingIdeal_iff (hρ : IsRationalRep ρ) {v : W}
    {Z : Set (GL (Fin n) K)} {φ : Dual K W} :
    matrixCoeff hρ v φ ∈ vanishingIdeal Z ↔ φ ∈ (orbitSpan ρ v Z).dualAnnihilator := by
  rw [mem_dualAnnihilator_orbitSpan_iff, mem_vanishingIdeal]
  simp only [glEval_matrixCoeff]

/-- If the `ρ(g) v` span `V`, the matrix coefficients of `v` determine `φ`. -/
theorem matrixCoeff_injective (hρ : IsRationalRep ρ) {v : W} (hv : orbitSpan ρ v Set.univ = ⊤) :
    Function.Injective (matrixCoeff hρ v) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro φ hφ
  have h : matrixCoeff hρ v φ ∈ vanishingIdeal (Set.univ : Set (GL (Fin n) K)) := by
    rw [LinearMap.mem_ker.mp hφ]
    exact zero_mem _
  rw [matrixCoeff_mem_vanishingIdeal_iff, hv, Submodule.dualAnnihilator_top] at h
  exact h

end

end GLRep
