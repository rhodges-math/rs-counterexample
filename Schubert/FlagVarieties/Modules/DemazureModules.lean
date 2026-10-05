import Schubert.FlagVarieties.Modules.JosephCharacter
import Schubert.FlagVarieties.Modules.BorelWeil
import Schubert.FlagVarieties.PointModel.Complex.ClosureRelation
import Schubert.GLRep.Borel.MatrixCoeff

/-!
# Demazure modules and sections over Schubert unions

Let `V` be a rational representation of `GL_n(ℂ)` and `v ∈ V` a `B`-eigenvector,
`ρ(b) v = η(b)⁻¹ v`, such that `φ ↦ (g ↦ φ(ρ(g) v))` maps `V^∨` onto `ind_B^G(η) = H⁰(G/B, 𝓛(η))`
(for `V = V(λ)` and a highest weight vector, `η = −λ`: `FlagVarieties.exists_highestWeightVector`).
For a set `S` of permutations the **Demazure module** is

  `D_S = ⟨ρ(g) v : g ∈ π⁻¹X_S⟩ ⊆ V` (`FlagVarieties.demazureSubrep`),

a representation of `B`; for `S = {u ≤ w}` it is the `B`-span of the extremal vector `ẇ v`
(`FlagVarieties.demazureSubrep_lowerSet`). Then, for a Bruhat ideal `S` and antidominant `η`,

  **`H⁰(X_S, 𝓛(η)) ≅ D_S^∨` as representations of `B`** (`FlagVarieties.sectionDemazureEquiv`):

the restriction `V^∨ → H⁰(X_S, 𝓛(η))`, `φ ↦ (g ↦ φ(ρ(g) v))|_{X_S}`, is onto (projective normality,
`FlagVarieties.SectionRep.sectionRestrict_surjective`) with kernel the annihilator of `D_S`.

For GLRep's `V(λ) = ratIrrep λ` this is `H⁰(X_S, 𝓛(−λ)) ≅ D_S(λ)^∨`
(`FlagVarieties.nonempty_sectionDemazureEquiv_ratIrrep`), with no hypothesis (the equality
`Γ(X_w, 𝒪) = ℂ` is `FlagVarieties.globalSectionsConstant_complex`).
-/

open Schubert GLRep TauCeti Module Demazure.SchubertUnions FinPermutation

namespace FlagVarieties

open PointModel.Complex SectionRep

noncomputable section

variable {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ (GL (Fin n) ℂ) W}

/-! ### Demazure modules -/

variable (ρ) in
/-- **The Demazure module** `D_S = ⟨ρ(g) v : g ∈ π⁻¹X_S⟩`, a representation of `B`. -/
def demazureSubrep (v : W) (S : Finset (Equiv.Perm (Fin n))) :
    Subrepresentation (ρ.comp (borel ℂ n).subtype) :=
  orbitSubrep v (orbitSet S) fun b _ hg => borel_mul_mem_orbitSet hg b.2

variable (ρ) in
/-- The representation of `B` on the Demazure module `D_S`. -/
abbrev demazureRep (v : W) (S : Finset (Equiv.Perm (Fin n))) :
    Representation ℂ (borel ℂ n) (demazureSubrep ρ v S).toSubmodule :=
  (demazureSubrep ρ v S).toRepresentation

theorem toSubmodule_demazureSubrep (v : W) (S : Finset (Equiv.Perm (Fin n))) :
    (demazureSubrep ρ v S).toSubmodule = orbitSpan ρ v (orbitSet S) :=
  rfl

theorem cellIdeal_eq_vanishingIdeal (w : Equiv.Perm (Fin n)) :
    cellIdeal w = vanishingIdeal (bruhatCell w) := by
  ext t
  exact Iff.rfl

section Eigenvector

variable (ρ) in
/-- The span of the vectors `ρ(b ẇ) v`, `b ∈ B`: the `B`-span of the extremal vector `ẇ v`. -/
def extremalSpan (v : W) (w : Equiv.Perm (Fin n)) : Submodule ℂ W :=
  orbitSpan ρ v ((fun b : GL (Fin n) ℂ => b * permGL w) '' (borel ℂ n : Set (GL (Fin n) ℂ)))

variable {v : W} {η : Fin n → ℤ}

/-- The span over a Bruhat cell is the span of `ρ(b ẇ) v`, `b ∈ B`. -/
theorem orbitSpan_bruhatCell
    (hv : ∀ b : borel ℂ n, ρ b v = (((borelChar ℂ n η b)⁻¹ : ℂˣ) : ℂ) • v)
    (w : Equiv.Perm (Fin n)) :
    orbitSpan ρ v (bruhatCell w) = extremalSpan ρ v w := by
  refine le_antisymm (Submodule.span_le.mpr ?_) (Submodule.span_le.mpr ?_)
  · rintro _ ⟨g, ⟨b₁, b₂, hb₁, hb₂, rfl⟩, rfl⟩
    change ρ (b₁ * permGL w * b₂) v ∈ _
    rw [map_mul, Module.End.mul_apply]
    have := hv ⟨b₂, hb₂⟩
    change ρ b₂ v = _ at this
    rw [this, map_smul]
    exact Submodule.smul_mem _ _ (apply_mem_orbitSpan ⟨b₁, hb₁, rfl⟩)
  · rintro _ ⟨g, ⟨b, hb, rfl⟩, rfl⟩
    exact apply_mem_orbitSpan ⟨b, 1, hb, isBorel_one, by rw [mul_one]⟩

/-- **`D_w`, the Demazure module of `X_w`, is the `B`-span of the extremal vector `ẇ v`.** -/
theorem demazureSubrep_lowerSet (hρ : IsRationalRep ρ)
    (hv : ∀ b : borel ℂ n, ρ b v = (((borelChar ℂ n η b)⁻¹ : ℂˣ) : ℂ) • v)
    (w : Equiv.Perm (Fin n)) :
    (demazureSubrep ρ v (lowerSet w)).toSubmodule = extremalSpan ρ v w := by
  rw [← orbitSpan_bruhatCell hv, toSubmodule_demazureSubrep, ← Subspace.dualAnnihilator_inj]
  ext φ
  rw [← matrixCoeff_mem_vanishingIdeal_iff hρ, ← matrixCoeff_mem_vanishingIdeal_iff hρ,
    ← orbitIdeal_eq_vanishingIdeal, orbitIdeal_lowerSet, cellIdeal_eq_vanishingIdeal]

theorem mk_matrixCoeff_mem_sectionSubrep (hρ : IsRationalRep ρ)
    (hv : ∀ b : borel ℂ n, ρ b v = (((borelChar ℂ n η b)⁻¹ : ℂˣ) : ℂ) • v)
    (S : Finset (Equiv.Perm (Fin n))) (φ : Dual ℂ W) :
    Ideal.Quotient.mk (orbitIdeal S) (matrixCoeff hρ v φ) ∈ (sectionSubrep S η).toSubmodule := by
  have h := mem_indBorelSubrep_iff_glEval.mp (matrixCoeff_mem_indBorelSubrep hρ hv φ)
  exact (mk_mem_sectionSubrep_iff S η _).mpr fun g _ b => h g b

/-- The restriction `V^∨ → H⁰(X_S, 𝓛(η))`, `φ ↦ (g ↦ φ(ρ(g) v))|_{X_S}`, as a linear map. -/
def dualToSectionLin (hρ : IsRationalRep ρ)
    (hv : ∀ b : borel ℂ n, ρ b v = (((borelChar ℂ n η b)⁻¹ : ℂˣ) : ℂ) • v)
    (S : Finset (Equiv.Perm (Fin n))) :
    Dual ℂ W →ₗ[ℂ] (sectionSubrep S η).toSubmodule where
  toFun φ := ⟨Ideal.Quotient.mk (orbitIdeal S) (matrixCoeff hρ v φ),
    mk_matrixCoeff_mem_sectionSubrep hρ hv S φ⟩
  map_add' φ ψ := Subtype.ext <| by
    change Ideal.Quotient.mk (orbitIdeal S) (matrixCoeff hρ v (φ + ψ)) =
      Ideal.Quotient.mk (orbitIdeal S) (matrixCoeff hρ v φ) +
        Ideal.Quotient.mk (orbitIdeal S) (matrixCoeff hρ v ψ)
    rw [map_add, map_add]
  map_smul' c φ := Subtype.ext <| by
    change Ideal.Quotient.mk (orbitIdeal S) (matrixCoeff hρ v (c • φ)) =
      c • Ideal.Quotient.mk (orbitIdeal S) (matrixCoeff hρ v φ)
    rw [map_smul]
    exact map_smul (Ideal.Quotient.mkₐ ℂ (orbitIdeal S)) c (matrixCoeff hρ v φ)

theorem coe_dualToSectionLin_apply (hρ : IsRationalRep ρ)
    (hv : ∀ b : borel ℂ n, ρ b v = (((borelChar ℂ n η b)⁻¹ : ℂˣ) : ℂ) • v)
    (S : Finset (Equiv.Perm (Fin n))) (φ : Dual ℂ W) :
    (dualToSectionLin hρ hv S φ : GLCoord ℂ n ⧸ orbitIdeal S) =
      Ideal.Quotient.mk (orbitIdeal S) (matrixCoeff hρ v φ) :=
  rfl

/-- **The restriction `V^∨ → H⁰(X_S, 𝓛(η))`**, `φ ↦ (g ↦ φ(ρ(g) v))|_{X_S}`, a map of
representations of `B`. -/
def dualToSection (hρ : IsRationalRep ρ)
    (hv : ∀ b : borel ℂ n, ρ b v = (((borelChar ℂ n η b)⁻¹ : ℂˣ) : ℂ) • v)
    (S : Finset (Equiv.Perm (Fin n))) :
    Representation.IntertwiningMap (ρ.dual.comp (borel ℂ n).subtype) (sectionRep S η) where
  toLinearMap := dualToSectionLin hρ hv S
  isIntertwining' b := by
    refine LinearMap.ext fun φ => Subtype.ext ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, coe_dualToSectionLin_apply]
    change _ = Ideal.Quotient.mk (orbitIdeal S) (leftTranslHom ℂ n b (matrixCoeff hρ v φ))
    rw [leftTranslHom_matrixCoeff]
    rfl

theorem coe_dualToSection_apply (hρ : IsRationalRep ρ)
    (hv : ∀ b : borel ℂ n, ρ b v = (((borelChar ℂ n η b)⁻¹ : ℂˣ) : ℂ) • v)
    (S : Finset (Equiv.Perm (Fin n))) (φ : Dual ℂ W) :
    (dualToSection hρ hv S φ : GLCoord ℂ n ⧸ orbitIdeal S) =
      Ideal.Quotient.mk (orbitIdeal S) (matrixCoeff hρ v φ) :=
  rfl

/-- **The kernel of the restriction is the annihilator of `D_S`.** -/
theorem dualToSection_eq_zero_iff (hρ : IsRationalRep ρ)
    (hv : ∀ b : borel ℂ n, ρ b v = (((borelChar ℂ n η b)⁻¹ : ℂˣ) : ℂ) • v)
    (S : Finset (Equiv.Perm (Fin n))) (φ : Dual ℂ W) :
    dualToSection hρ hv S φ = 0 ↔ φ ∈ (demazureSubrep ρ v S).toSubmodule.dualAnnihilator := by
  rw [← Subtype.coe_inj, coe_dualToSection_apply, Submodule.coe_zero,
    Ideal.Quotient.eq_zero_iff_mem, orbitIdeal_eq_vanishingIdeal,
    matrixCoeff_mem_vanishingIdeal_iff, toSubmodule_demazureSubrep]

/-- **Projective normality, in terms of `V^∨`**: if `V^∨ → H⁰(G/B, 𝓛(η))` is onto, so is the
restriction to any Schubert union. -/
theorem dualToSection_surjective (hρ : IsRationalRep ρ)
    (hv : ∀ b : borel ℂ n, ρ b v = (((borelChar ℂ n η b)⁻¹ : ℂˣ) : ℂ) • v)
    {S : Finset (Equiv.Perm (Fin n))} (hS : BruhatLower S) (hη : IsAntidominant η)
    (hΨ : Function.Surjective (dualToInducedRep hρ hv)) :
    Function.Surjective (dualToSection hρ hv S) := by
  intro s
  obtain ⟨⟨q, hq⟩, hs⟩ := sectionRestrict_surjective (Finset.subset_univ S) hS hη s
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective q
  have ht : t ∈ (indBorelSubrep ℂ n η).toSubmodule := by
    rw [mem_indBorelSubrep_iff_glEval]
    intro g b
    exact (mk_mem_sectionSubrep_iff _ η t).mp hq g (by rw [orbitSet_univ]; exact Set.mem_univ g) b
  obtain ⟨φ, hφ⟩ := hΨ ⟨t, ht⟩
  refine ⟨φ, ?_⟩
  rw [← hs]
  refine Subtype.ext ?_
  have hφ' : matrixCoeff hρ v φ = t := congrArg Subtype.val hφ
  rw [coe_dualToSection_apply, hφ']
  rfl

/-- The extension-by-zero description of the restriction: on `D_S^∨`. -/
def dualDemazureToSection (hρ : IsRationalRep ρ)
    (hv : ∀ b : borel ℂ n, ρ b v = (((borelChar ℂ n η b)⁻¹ : ℂˣ) : ℂ) • v)
    (S : Finset (Equiv.Perm (Fin n))) :
    Dual ℂ (demazureSubrep ρ v S).toSubmodule →ₗ[ℂ] (sectionSubrep S η).toSubmodule :=
  (dualToSection hρ hv S).toLinearMap ∘ₗ Subspace.dualLift (demazureSubrep ρ v S).toSubmodule

theorem dualDemazureToSection_dualRestrict (hρ : IsRationalRep ρ)
    (hv : ∀ b : borel ℂ n, ρ b v = (((borelChar ℂ n η b)⁻¹ : ℂˣ) : ℂ) • v)
    (S : Finset (Equiv.Perm (Fin n))) (φ : Dual ℂ W) :
    dualDemazureToSection hρ hv S ((demazureSubrep ρ v S).toSubmodule.dualRestrict φ) =
      dualToSection hρ hv S φ := by
  have hk : dualToSection hρ hv S (Subspace.dualLift (demazureSubrep ρ v S).toSubmodule
      ((demazureSubrep ρ v S).toSubmodule.dualRestrict φ) - φ) = 0 := by
    rw [dualToSection_eq_zero_iff, Submodule.mem_dualAnnihilator]
    intro w hw
    rw [LinearMap.sub_apply, Subspace.dualLift_of_mem hw, Submodule.dualRestrict_apply, sub_self]
  rw [map_sub, sub_eq_zero] at hk
  exact hk

theorem dualDemazureToSection_bijective (hρ : IsRationalRep ρ)
    (hv : ∀ b : borel ℂ n, ρ b v = (((borelChar ℂ n η b)⁻¹ : ℂˣ) : ℂ) • v)
    {S : Finset (Equiv.Perm (Fin n))} (hS : BruhatLower S) (hη : IsAntidominant η)
    (hΨ : Function.Surjective (dualToInducedRep hρ hv)) :
    Function.Bijective (dualDemazureToSection hρ hv S) := by
  refine ⟨?_, fun s => ?_⟩
  · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro ψ hψ
    rw [Submodule.mem_bot]
    have h0 : dualToSection hρ hv S (Subspace.dualLift (demazureSubrep ρ v S).toSubmodule ψ) = 0 :=
      LinearMap.mem_ker.mp hψ
    rw [dualToSection_eq_zero_iff, Submodule.mem_dualAnnihilator] at h0
    ext w
    rw [← Subspace.dualLift_of_subtype (W := (demazureSubrep ρ v S).toSubmodule) w, h0 _ w.2,
      LinearMap.zero_apply]
  · obtain ⟨φ, rfl⟩ := dualToSection_surjective hρ hv hS hη hΨ s
    exact ⟨_, dualDemazureToSection_dualRestrict hρ hv S φ⟩

/-- **`H⁰(X_S, 𝓛(η)) ≅ D_S^∨` as representations of `B`** (`S` a Bruhat ideal, `η`
antidominant). -/
def sectionDemazureEquiv (hρ : IsRationalRep ρ)
    (hv : ∀ b : borel ℂ n, ρ b v = (((borelChar ℂ n η b)⁻¹ : ℂˣ) : ℂ) • v)
    {S : Finset (Equiv.Perm (Fin n))} (hS : BruhatLower S) (hη : IsAntidominant η)
    (hΨ : Function.Surjective (dualToInducedRep hρ hv)) :
    (demazureRep ρ v S).dual.Equiv (sectionRep S η) :=
  .mk (LinearEquiv.ofBijective _ (dualDemazureToSection_bijective hρ hv hS hη hΨ))
    fun b => LinearMap.ext fun ψ => by
      obtain ⟨φ, rfl⟩ :=
        Subspace.dualRestrict_surjective (W := (demazureSubrep ρ v S).toSubmodule) ψ
      have hb : (demazureRep ρ v S).dual b ((demazureSubrep ρ v S).toSubmodule.dualRestrict φ) =
          (demazureSubrep ρ v S).toSubmodule.dualRestrict (ρ.dual b φ) := by
        ext w
        rfl
      change dualDemazureToSection hρ hv S ((demazureRep ρ v S).dual b _) =
        sectionRep S η b (dualDemazureToSection hρ hv S _)
      rw [hb, dualDemazureToSection_dualRestrict, dualDemazureToSection_dualRestrict]
      exact LinearMap.congr_fun ((dualToSection hρ hv S).isIntertwining' b) φ

end Eigenvector

/-! ### `V(λ)` -/

/-- **A highest weight vector of `V(λ)`**: a `B`-eigenvector `v` of weight `λ` whose matrix
coefficients exhaust `H⁰(G/B, 𝓛(−λ))`. -/
theorem exists_highestWeightVector
    (l : DominantWeight n) :
    ∃ (v : IrrepSpace ℂ n l.detShiftShape)
      (hv : ∀ b : borel ℂ n, ratIrrep ℂ n l b v = (((borelChar ℂ n (-l.1) b)⁻¹ : ℂˣ) : ℂ) • v),
      Function.Surjective (dualToInducedRep (isRationalRep_ratIrrep l) hv) := by
  obtain ⟨E⟩ := borelWeil_ratIrrep l
  have := (isRationalRep_ratIrrep (K := ℂ) (n := n) l).finiteDimensional
  set ρ := ratIrrep ℂ n l
  let ev : Dual ℂ (indBorelSubrep ℂ n (-l.1)).toSubmodule :=
    (glEval (1 : GL (Fin n) ℂ)).toLinearMap ∘ₗ (indBorelSubrep ℂ n (-l.1)).toSubmodule.subtype
  let v : IrrepSpace ℂ n l.detShiftShape :=
    (evalEquiv ℂ (IrrepSpace ℂ n l.detShiftShape)).symm (ev ∘ₗ E.symm.toLinearMap)
  have hv0 : ∀ φ : Dual ℂ (IrrepSpace ℂ n l.detShiftShape), φ v = ev (E.symm φ) := fun φ =>
    apply_evalEquiv_symm_apply ℂ _ φ _
  have hEs : ∀ (g : GL (Fin n) ℂ) (φ : Dual ℂ (IrrepSpace ℂ n l.detShiftShape)),
      E.symm (ρ.dual g φ) = indBorelRep ℂ n (-l.1) g (E.symm φ) := fun g φ =>
    LinearMap.congr_fun (E.symm.toIntertwiningMap.isIntertwining' g) φ
  -- `φ(ρ(g) v) = (E⁻¹ φ)(g)`
  have hcoeff : ∀ (g : GL (Fin n) ℂ) (φ : Dual ℂ (IrrepSpace ℂ n l.detShiftShape)),
      φ (ρ g v) = glEval g (E.symm φ : GLCoord ℂ n) := by
    intro g φ
    have h1 : φ (ρ g v) = ρ.dual g⁻¹ φ v := by
      rw [Representation.dual_apply, inv_inv]
      rfl
    rw [h1, hv0, hEs]
    change glEval 1 (leftTranslHom ℂ n g⁻¹ (E.symm φ : GLCoord ℂ n)) = _
    rw [glEval_leftTranslHom, inv_inv, mul_one]
  have hv : ∀ b : borel ℂ n, ρ b v = (((borelChar ℂ n (-l.1) b)⁻¹ : ℂˣ) : ℂ) • v := by
    intro b
    refine (evalEquiv ℂ (IrrepSpace ℂ n l.detShiftShape)).injective (LinearMap.ext fun φ => ?_)
    change φ (ρ b v) = φ ((((borelChar ℂ n (-l.1) b)⁻¹ : ℂˣ) : ℂ) • v)
    rw [hcoeff, map_smul, smul_eq_mul, hv0]
    have h1 := mem_indBorelSubrep_iff_glEval.mp (E.symm φ).2 1 b
    rw [one_mul] at h1
    exact h1
  refine ⟨v, hv, fun f => ⟨E f, Subtype.ext (glCoord_ext fun g => ?_)⟩⟩
  rw [coe_dualToInducedRep_apply, glEval_matrixCoeff, hcoeff, E.symm_apply_apply]

/-- **`H⁰(X_S, 𝓛(−λ)) ≅ D_S(λ)^∨`** for GLRep's `V(λ) = ratIrrep λ`, with `D_S(λ) ⊆ V(λ)` the
Demazure module of a highest weight vector. -/
theorem nonempty_sectionDemazureEquiv_ratIrrep (l : DominantWeight n) :
    ∃ v : IrrepSpace ℂ n l.detShiftShape,
      (∀ b : borel ℂ n, ratIrrep ℂ n l b v = (((borelChar ℂ n (-l.1) b)⁻¹ : ℂˣ) : ℂ) • v) ∧
      ∀ {S : Finset (Equiv.Perm (Fin n))}, BruhatLower S →
        Nonempty ((demazureRep (ratIrrep ℂ n l) v S).dual.Equiv (sectionRep S (-l.1))) := by
  obtain ⟨v, hv, hΨ⟩ := exists_highestWeightVector l
  have hη : IsAntidominant (-l.1) := fun _ _ hij => neg_le_neg (l.2 hij)
  exact ⟨v, hv, fun hS =>
    ⟨sectionDemazureEquiv (isRationalRep_ratIrrep l) hv hS hη hΨ⟩⟩

end

end FlagVarieties
