import Schubert.GLRep.Levi.Curry

/-!
# Multiplicities for Levi groups

Let `L = ∏_{p < s} GL_{d_p}(K)` be a Levi group over a field `K` of characteristic zero. For Young
diagrams `μ = (μ_p)_p` with at most `d_p` rows, `GLRep.leviIrrep K d μ = ⊠_p V(μ_p)` is the external
tensor product of the irreducible representations of the blocks; its character is
`∏_p s_{μ_p}(x_{p,·})` (`GLRep.leviCharacter_leviIrrep`). For a polynomial representation `ρ` of
`L`, the character of `ρ` is the sum of these products weighted by the multiplicities
`dim Hom_L(⊠_p V(μ_p), ρ)` (`GLRep.IsPolynomialLeviRep.exists_leviCharacter_eq_sum`):

`ch ρ = ∑_μ dim Hom_L(⊠_p V(μ_p), ρ) · ∏_p s_{μ_p}(x_{p,·})`.

The proof is an induction on the number of blocks. Write `L = GL_{d_0}(K) × L'`. Currying
identifies `Hom_L(V(μ_0) ⊠ V', ρ)` with `Hom_{L'}(V', U_{μ_0})`, where
`U_{μ_0} = Hom_{GL_{d_0}}(V(μ_0), ρ)` is the multiplicity space (`GLRep.curryEquiv`). The weight
space of `η` in `U_{μ_0}` is `Hom_{GL_{d_0}}(V(μ_0), W_η)`, where `W_η` is the weight space of the
torus of `L'`. Splitting the trace of the torus of `L` along the `W_η`, and expanding each `W_η`
as a representation of `GL_{d_0}(K)`, gives `ch ρ = ∑_{ν} s_ν(x_{0,·}) · ch U_ν(x')`; the
induction hypothesis applies to the `U_ν`.

## Main definitions

* `GLRep.leviIrrep K d μ`, `GLRep.leviSchur d μ`, `GLRep.leviMultiplicity ρ μ`.

## Main results

* `GLRep.isPolynomialLeviRep_leviIrrep`, `GLRep.leviCharacter_leviIrrep`.
* `GLRep.IsPolynomialLeviRep.exists_leviCharacter_eq_sum`.
-/

namespace GLRep

open Module Representation TauCeti

noncomputable section

universe u w

variable {K : Type u} [Field K] [CharZero K]

/-! ### The irreducible representations of the Levi group -/

section Defs

variable {s : ℕ} (d : Fin s → ℕ)

variable (K) in
/-- The irreducible representation `⊠_p V(μ_p)` of the Levi group `∏_p GL_{d_p}(K)`. -/
abbrev leviIrrep (μ : Fin s → YoungDiagram) :
    Representation K (LeviGroup K d) (PiTensorProduct K fun p => IrrepSpace K (d p) (μ p)) :=
  extTensor fun p => irrep K (d p) (μ p)

/-- The product `∏_p s_{μ_p}(x_{p,·})` of Schur polynomials in the blocks of variables. -/
def leviSchur (μ : Fin s → YoungDiagram) : MvPolynomial (Σ p : Fin s, Fin (d p)) ℤ :=
  ∏ p, MvPolynomial.rename (blockVar p) (TauCeti.diagramSchurPoly (d p) ℤ (μ p))

variable {d}

theorem isPolynomialLeviRep_leviIrrep (μ : Fin s → YoungDiagram) :
    IsPolynomialLeviRep (leviIrrep K d μ) :=
  isPolynomialLeviRep_extTensor fun p => isPolynomialRep_irrep (μ p)

/-- **The character of `⊠_p V(μ_p)`** is `∏_p s_{μ_p}(x_{p,·})`. -/
theorem leviCharacter_leviIrrep {μ : Fin s → YoungDiagram} (hμ : ∀ p, (μ p).colLen 0 ≤ d p) :
    leviCharacter (leviIrrep K d μ) = leviSchur d μ := by
  rw [leviCharacter_extTensor fun p => isPolynomialRep_irrep (μ p)]
  exact Finset.prod_congr rfl fun p _ => by rw [character_irrep (hμ p)]

variable {W : Type*} [AddCommGroup W] [Module K W]

variable (ρ : Representation K (LeviGroup K d) W) in
/-- The **multiplicity** `dim Hom_L(⊠_p V(μ_p), ρ)`. -/
def leviMultiplicity (μ : Fin s → YoungDiagram) : ℕ :=
  finrank K (IntertwiningMap (leviIrrep K d μ) ρ)

theorem leviMultiplicity_eq_zero_of_subsingleton {ρ : Representation K (LeviGroup K d) W}
    [Subsingleton W] (μ : Fin s → YoungDiagram) : leviMultiplicity ρ μ = 0 := by
  have : Subsingleton (IntertwiningMap (leviIrrep K d μ) ρ) :=
    ⟨fun f g => IntertwiningMap.ext (LinearMap.ext fun _ => Subsingleton.elim _ _)⟩
  exact Module.finrank_zero_of_subsingleton

end Defs

/-! ### No blocks -/

theorem exists_leviCharacter_eq_sum_zero {d : Fin 0 → ℕ} {W : Type*} [AddCommGroup W]
    [Module K W] {ρ : Representation K (LeviGroup K d) W} (h : IsPolynomialLeviRep ρ) :
    ∃ S : Finset (Fin 0 → YoungDiagram), (∀ μ ∈ S, ∀ p, (μ p).colLen 0 ≤ d p) ∧
      (∀ μ : Fin 0 → YoungDiagram, (∀ p, (μ p).colLen 0 ≤ d p) → μ ∉ S →
        leviMultiplicity ρ μ = 0) ∧
      leviCharacter ρ = ∑ μ ∈ S, (leviMultiplicity ρ μ : ℤ) • leviSchur d μ := by
  have := h.finiteDimensional
  let μ₀ : Fin 0 → YoungDiagram := Fin.elim0
  have hμ₀ : ∀ μ : Fin 0 → YoungDiagram, μ = μ₀ := fun μ => funext fun p => p.elim0
  have htriv : ∀ g, ρ g = 1 := fun g => by rw [Subsingleton.elim g 1, map_one]
  have htriv' : ∀ g, leviIrrep K d μ₀ g = 1 := fun g => by rw [Subsingleton.elim g 1, map_one]
  have hmult : leviMultiplicity ρ μ₀ = finrank K W := by
    let E := PiTensorProduct.isEmptyEquiv (R := K) (s := fun p => IrrepSpace K (d p) (μ₀ p))
      (Fin 0)
    let e : IntertwiningMap (leviIrrep K d μ₀) ρ ≃ₗ[K] W :=
      { toFun := fun f => f (E.symm 1)
        invFun := fun w => ⟨LinearMap.toSpanSingleton K W w ∘ₗ E.toLinearMap, fun g => by
          rw [htriv, htriv']
          rfl⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl
        left_inv := fun f => IntertwiningMap.ext (LinearMap.ext fun x => by
          change E x • f (E.symm 1) = f x
          rw [← map_smul, ← map_smul, smul_eq_mul, mul_one, LinearEquiv.symm_apply_apply])
        right_inv := fun w => by
          change E (E.symm 1) • w = w
          rw [LinearEquiv.apply_symm_apply, one_smul] }
    exact e.finrank_eq
  refine ⟨{μ₀}, fun μ _ p => p.elim0, fun μ _ hμS => absurd (Finset.mem_singleton.mpr (hμ₀ μ))
    hμS, ?_⟩
  rw [Finset.sum_singleton, hmult]
  have hschur : leviSchur d μ₀ = 1 := Finset.prod_of_isEmpty _
  rw [hschur]
  refine (eq_leviCharacter_of_forall_trace_eq h _ fun t => ?_).symm
  rw [htriv, LinearMap.trace_one]
  simp

/-! ### Splitting off the first block -/

/-- The trace formula from the weights of a polynomial representation of a split torus. -/
theorem trace_eq_sum_weight {κ : Type*} [Fintype κ] {U : Type*} [AddCommGroup U] [Module K U]
    {π : Representation K (κ → Kˣ) U} (hπ : HasCoeffsIn (coordFunctions K (torusCoord K κ)) π)
    (F : Finset (κ → ℤ)) (hF : ∀ η, torusWeightSpace π η ≠ ⊥ → η ∈ F) (t : κ → Kˣ) :
    LinearMap.trace K U (π t) =
      ∑ η ∈ F, weightCharHom K η t * finrank K (torusWeightSpace π η) := by
  have := hπ.finiteDimensional
  have h := trace_mul_eq_sum_weight hπ 1 (fun t => by rw [one_mul, mul_one]) F hF t
  rw [one_mul] at h
  rw [h]
  refine Finset.sum_congr rfl fun η _ => ?_
  rw [show LinearMap.restrict (1 : Module.End K U) _ = LinearMap.id from
    LinearMap.ext fun _ => rfl, LinearMap.trace_id]

section Succ

variable {s : ℕ} {d : Fin (s + 1) → ℕ} {W : Type*} [AddCommGroup W] [Module K W]
  {ρ : Representation K (LeviGroup K d) W}

/-- **Multiplicities through the multiplicity spaces of the first block.** -/
theorem leviMultiplicity_eq_tail (μ : Fin (s + 1) → YoungDiagram) :
    leviMultiplicity ρ μ = leviMultiplicity (multRep ρ (irrep K (d 0) (μ 0))) (Fin.tail μ) :=
  (curryEquiv (ρ := ρ) fun p => irrep K (d p) (μ p)).finrank_eq

/-- The weights of the multiplicity space of `V(ν)`. -/
theorem finrank_multRep_weight (ν : YoungDiagram) (η : (Σ q : Fin s, Fin (Fin.tail d q)) → ℤ) :
    finrank K (torusWeightSpace ((multRep ρ (irrep K (d 0) ν)).comp
      (leviTorus K (Fin.tail d))) η) = multiplicity (tailWeightSubrep ρ η).toRepresentation ν :=
  (finrank_tailWeightSubrep _ η).symm

theorem renameTail_leviSchur (μ : Fin s → YoungDiagram) :
    MvPolynomial.rename tailVar (leviSchur (Fin.tail d) μ) =
      ∏ q : Fin s, MvPolynomial.rename (blockVar q.succ)
        (TauCeti.diagramSchurPoly (d q.succ) ℤ (μ q)) := by
  rw [leviSchur, map_prod]
  exact Finset.prod_congr rfl fun q _ => MvPolynomial.rename_rename _ _ _

theorem leviSchur_cons (ν : YoungDiagram) (μ : Fin s → YoungDiagram) :
    leviSchur d (Fin.cons ν μ : Fin (s + 1) → YoungDiagram) =
      MvPolynomial.rename (blockVar 0) (TauCeti.diagramSchurPoly (d 0) ℤ ν) *
        MvPolynomial.rename tailVar (leviSchur (Fin.tail d) μ) := by
  rw [renameTail_leviSchur, leviSchur, Fin.prod_univ_succ]
  rfl

end Succ

/-! ### The induction step -/

/-- The **Levi expansion** of the character of a representation of the Levi group: it is the sum
of the products of Schur polynomials weighted by the multiplicities, over a finite set of tuples
of Young diagrams outside which the multiplicities vanish. -/
def LeviExpansion {s : ℕ} {d : Fin s → ℕ} {W : Type*} [AddCommGroup W] [Module K W]
    (ρ : Representation K (LeviGroup K d) W) : Prop :=
  ∃ S : Finset (Fin s → YoungDiagram), (∀ μ ∈ S, ∀ p, (μ p).colLen 0 ≤ d p) ∧
    (∀ μ : Fin s → YoungDiagram, (∀ p, (μ p).colLen 0 ≤ d p) → μ ∉ S →
      leviMultiplicity ρ μ = 0) ∧
    leviCharacter ρ = ∑ μ ∈ S, (leviMultiplicity ρ μ : ℤ) • leviSchur d μ

section Step

variable {s : ℕ} {d : Fin (s + 1) → ℕ} {W : Type*} [AddCommGroup W] [Module K W]
  {ρ : Representation K (LeviGroup K d) W}

theorem IsPolynomialLeviRep.multRep_irrep (h : IsPolynomialLeviRep ρ) (ν : YoungDiagram) :
    IsPolynomialLeviRep (GLRep.multRep ρ (irrep K (d 0) ν)) := by
  have := (isPolynomialRep_irrep (K := K) (n := d 0) ν).finiteDimensional
  exact h.multRep _

/-- **The induction step**: the Levi expansion of `ρ` follows from the Levi expansions of its
multiplicity spaces. -/
theorem leviExpansion_succ (h : IsPolynomialLeviRep ρ)
    (ih : ∀ ν : YoungDiagram, LeviExpansion (multRep ρ (irrep K (d 0) ν))) :
    LeviExpansion ρ := by
  classical
  have := h.finiteDimensional
  -- the torus of the other blocks and its weights
  set π := (tailRep ρ).comp (leviTorus K (Fin.tail d))
  have hπ : HasCoeffsIn (coordFunctions K (torusCoord K _)) π := h.comp_leviTail.comp_leviTorus
  set H := (finite_torusWeightSpace_ne_bot π).toFinset
  have hH : ∀ η, torusWeightSpace π η ≠ ⊥ → η ∈ H := fun η hη =>
    (Set.Finite.mem_toFinset _).mpr hη
  -- the weight spaces as representations of the first block
  have hsub : ∀ η, IsPolynomialRep (tailWeightSubrep ρ η).toRepresentation := fun η =>
    (h.comp_leviBlock 0).subrepresentation _
  choose S8 hS8n hS8z hS8χ using fun η => (hsub η).exists_character_eq_sum
  set S0 := H.biUnion S8
  have hS0n : ∀ ν ∈ S0, ν.colLen 0 ≤ d 0 := by
    intro ν hν
    obtain ⟨η, -, hη⟩ := Finset.mem_biUnion.mp hν
    exact hS8n η ν hη
  have hsingle : ∀ η, η ∉ H → Subsingleton (tailWeightSubrep ρ η).toSubmodule := by
    intro η hη
    refine Submodule.subsingleton_iff_eq_bot.mpr ?_
    by_contra h'
    exact hη (hH η h')
  have hmult0 : ∀ η ν, ν.colLen 0 ≤ d 0 → ν ∉ S0 →
      multiplicity (tailWeightSubrep ρ η).toRepresentation ν = 0 := by
    intro η ν hν hνS
    by_cases hη : η ∈ H
    · exact hS8z η ν hν fun h' => hνS (Finset.mem_biUnion.mpr ⟨η, hη, h'⟩)
    · have := hsingle η hη
      exact multiplicity_eq_zero_of_subsingleton ν
  have hU := IsPolynomialLeviRep.multRep_irrep h
  have hUweights : ∀ ν η, torusWeightSpace ((multRep ρ (irrep K (d 0) ν)).comp
      (leviTorus K (Fin.tail d))) η ≠ ⊥ → η ∈ H := by
    intro ν η hne
    by_contra hη
    apply hne
    have := hsingle η hη
    have := (hU ν).finiteDimensional
    rw [← Submodule.finrank_eq_zero, finrank_multRep_weight, multiplicity_eq_zero_of_subsingleton]
  -- the character identity
  have hchar : leviCharacter ρ = ∑ ν ∈ S0, MvPolynomial.rename (blockVar 0)
      (TauCeti.diagramSchurPoly (d 0) ℤ ν) *
        MvPolynomial.rename tailVar (leviCharacter (multRep ρ (irrep K (d 0) ν))) := by
    refine (eq_leviCharacter_of_forall_trace_eq h _ fun t => ?_).symm
    have hsplit : LinearMap.trace K W (ρ (leviTorus K d t)) = ∑ η ∈ H,
        weightCharHom K η (tailTorus t) * LinearMap.trace K _
          ((tailWeightSubrep ρ η).toRepresentation (diagGL (headTorus t))) := by
      rw [leviTorus_eq_mul, map_mul]
      exact trace_mul_eq_sum_weight hπ (headRep ρ (diagGL (headTorus t)))
        (fun t' => headRep_mul_tailRep _ _) H hH (tailTorus t)
    have hterm : ∀ η ∈ H, LinearMap.trace K _
        ((tailWeightSubrep ρ η).toRepresentation (diagGL (headTorus t))) =
        ∑ ν ∈ S0, (multiplicity (tailWeightSubrep ρ η).toRepresentation ν : K) *
          MvPolynomial.eval₂ (Int.castRingHom K) (fun i => (headTorus t i : K))
            (TauCeti.diagramSchurPoly (d 0) ℤ ν) := by
      intro η hη
      rw [trace_diagGL_eq_eval_character (hsub η), hS8χ η, MvPolynomial.eval₂_sum]
      rw [Finset.sum_subset (Finset.subset_biUnion_of_mem S8 hη) fun ν hνS0 hνS8 => by
        rw [hS8z η ν (hS0n ν hνS0) hνS8, Nat.cast_zero, zero_smul, MvPolynomial.eval₂_zero]]
      refine Finset.sum_congr rfl fun ν _ => ?_
      rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C]
      simp
    have hUtrace : ∀ ν, MvPolynomial.eval₂ (Int.castRingHom K) (fun x => (tailTorus t x : K))
        (leviCharacter (multRep ρ (irrep K (d 0) ν))) = ∑ η ∈ H, weightCharHom K η (tailTorus t) *
          (multiplicity (tailWeightSubrep ρ η).toRepresentation ν : K) := by
      intro ν
      rw [← trace_leviTorus_eq_eval_leviCharacter (hU ν)]
      refine (trace_eq_sum_weight (hU ν).comp_leviTorus H (hUweights ν) (tailTorus t)).trans ?_
      exact Finset.sum_congr rfl fun η _ => by rw [finrank_multRep_weight]
    have hrhs : ∑ η ∈ H, weightCharHom K η (tailTorus t) * LinearMap.trace K _
        ((tailWeightSubrep ρ η).toRepresentation (diagGL (headTorus t))) =
        ∑ η ∈ H, weightCharHom K η (tailTorus t) *
          ∑ ν ∈ S0, (multiplicity (tailWeightSubrep ρ η).toRepresentation ν : K) *
            MvPolynomial.eval₂ (Int.castRingHom K) (fun i => (headTorus t i : K))
              (TauCeti.diagramSchurPoly (d 0) ℤ ν) :=
      Finset.sum_congr rfl fun η hη => by rw [hterm η hη]
    rw [hsplit, hrhs]
    simp only [MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_rename]
    change ∑ ν ∈ S0, MvPolynomial.eval₂ (Int.castRingHom K) (fun i => (headTorus t i : K))
        (TauCeti.diagramSchurPoly (d 0) ℤ ν) * MvPolynomial.eval₂ (Int.castRingHom K)
          (fun x => (tailTorus t x : K)) (leviCharacter (multRep ρ (irrep K (d 0) ν))) = _
    simp only [hUtrace, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun η _ => Finset.sum_congr rfl fun ν _ => ?_
    ring
  -- assembling the expansion
  clear_value S0
  choose S₁ hS₁n hS₁z hS₁χ using ih
  refine ⟨S0.biUnion fun ν => (S₁ ν).image (Fin.cons ν), ?_, ?_, ?_⟩
  · intro μ hμ p
    obtain ⟨ν, hν, hmem⟩ := Finset.mem_biUnion.mp hμ
    obtain ⟨μ₁, hμ₁, rfl⟩ := Finset.mem_image.mp hmem
    induction p using Fin.cases with
    | zero => exact hS0n ν hν
    | succ q => exact hS₁n ν μ₁ hμ₁ q
  · intro μ hμb hμS
    rw [leviMultiplicity_eq_tail]
    by_cases hν : μ 0 ∈ S0
    · refine hS₁z (μ 0) (Fin.tail μ) (fun q => hμb q.succ) fun hmem => hμS ?_
      exact Finset.mem_biUnion.mpr ⟨μ 0, hν, Finset.mem_image.mpr ⟨Fin.tail μ, hmem,
        Fin.cons_self_tail μ⟩⟩
    · have := (hU (μ 0)).finiteDimensional
      have hzero : Subsingleton (IntertwiningMap (irrep K (d 0) (μ 0)) (headRep ρ)) := by
        refine subsingleton_of_forall_eq 0 fun x => ?_
        have hx : x ∈ ⨆ η, torusWeightSpace ((multRep ρ (irrep K (d 0) (μ 0))).comp
            (leviTorus K (Fin.tail d))) η := by
          rw [(hU (μ 0)).comp_leviTorus.iSup_torusWeightSpace_eq_top]
          exact Submodule.mem_top
        have hbot : ∀ η, torusWeightSpace ((multRep ρ (irrep K (d 0) (μ 0))).comp
            (leviTorus K (Fin.tail d))) η = ⊥ := fun η => by
          rw [← Submodule.finrank_eq_zero, finrank_multRep_weight, hmult0 η _ (hμb 0) hν]
        simp only [hbot, iSup_bot, Submodule.mem_bot] at hx
        exact hx
      exact leviMultiplicity_eq_zero_of_subsingleton _
  · rw [hchar, Finset.sum_biUnion]
    · refine Finset.sum_congr rfl fun ν _ => ?_
      rw [hS₁χ ν, map_sum, Finset.mul_sum, Finset.sum_image]
      swap
      · intro x _ y _ hxy
        funext q
        simpa using congrFun hxy q.succ
      refine Finset.sum_congr rfl fun μ₁ _ => ?_
      rw [leviSchur_cons, leviMultiplicity_eq_tail, Fin.cons_zero, Fin.tail_cons, map_zsmul,
        mul_smul_comm]
    · intro ν _ ν₂ _ hνν
      refine Finset.disjoint_left.mpr fun μ hμ hμ₂ => hνν ?_
      obtain ⟨_, -, rfl⟩ := Finset.mem_image.mp hμ
      obtain ⟨_, -, h₂⟩ := Finset.mem_image.mp hμ₂
      have := congrFun h₂ 0
      simpa using this.symm

end Step

/-- The Levi expansion for representations in a universe above that of `K`; the induction
passes through the multiplicity spaces, which live in such a universe. -/
theorem IsPolynomialLeviRep.leviExpansion_max :
    ∀ {s : ℕ} {d : Fin s → ℕ} {W : Type (max u w)} [AddCommGroup W] [Module K W]
      {ρ : Representation K (LeviGroup K d) W}, IsPolynomialLeviRep ρ → LeviExpansion ρ
  | 0, _, _, _, _, _, h => exists_leviCharacter_eq_sum_zero h
  | _ + 1, _, _, _, _, _, h => leviExpansion_succ h fun ν =>
      IsPolynomialLeviRep.leviExpansion_max (IsPolynomialLeviRep.multRep_irrep h ν)

/-! ### Changing universes -/

section Transport

variable {G : Type*} [Monoid G] {W : Type*} [AddCommGroup W] [Module K W] {V : Type*}
  [AddCommGroup V] [Module K V]

/-- A representation transported along a linear equivalence. -/
def transportRep (ρ : Representation K G W) (e : W ≃ₗ[K] V) : Representation K G V where
  toFun g := e.toLinearMap ∘ₗ ρ g ∘ₗ e.symm.toLinearMap
  map_one' := by
    ext v
    simp
  map_mul' g h := by
    ext v
    simp

/-- A representation is equivalent to its transport. -/
def transportEquiv (ρ : Representation K G W) (e : W ≃ₗ[K] V) : ρ.Equiv (transportRep ρ e) :=
  .mk e fun g => by
    ext w
    simp [transportRep]

end Transport

/-- The Levi expansion is invariant under equivalence. -/
theorem LeviExpansion.of_equiv {s : ℕ} {d : Fin s → ℕ} {W : Type*} [AddCommGroup W]
    [Module K W] {V : Type*} [AddCommGroup V] [Module K V]
    {ρ : Representation K (LeviGroup K d) W} {σ : Representation K (LeviGroup K d) V}
    (hρ : IsPolynomialLeviRep ρ) (hσ : IsPolynomialLeviRep σ) (e : ρ.Equiv σ)
    (h : LeviExpansion ρ) : LeviExpansion σ := by
  obtain ⟨S, hSn, hSz, hSχ⟩ := h
  have hm : ∀ μ, leviMultiplicity ρ μ = leviMultiplicity σ μ := fun μ =>
    (intertwiningMapCongrRight e).finrank_eq
  refine ⟨S, hSn, fun μ hμ hμS => (hm μ).symm.trans (hSz μ hμ hμS), ?_⟩
  rw [← leviCharacter_eq_of_equiv hρ hσ e, hSχ]
  exact Finset.sum_congr rfl fun μ _ => by rw [hm μ]

/-- **The character of a polynomial representation of a Levi group** is the sum of the products
`∏_p s_{μ_p}(x_{p,·})` weighted by the multiplicities `dim Hom_L(⊠_p V(μ_p), ρ)`, over a finite
set of tuples of Young diagrams outside which the multiplicities vanish. -/
theorem IsPolynomialLeviRep.exists_leviCharacter_eq_sum {s : ℕ} {d : Fin s → ℕ}
    {W : Type w} [AddCommGroup W] [Module K W] {ρ : Representation K (LeviGroup K d) W}
    (h : IsPolynomialLeviRep ρ) : LeviExpansion ρ := by
  let e : W ≃ₗ[K] ULift.{u} W := ULift.moduleEquiv.symm
  have h' : IsPolynomialLeviRep (transportRep ρ e) := HasCoeffsIn.of_equiv h (transportEquiv ρ e)
  exact (IsPolynomialLeviRep.leviExpansion_max.{u, w} h').of_equiv h' h
    (transportEquiv ρ e).symm

end

end GLRep
