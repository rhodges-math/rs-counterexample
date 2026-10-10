import RSCounterexample.Paper.Statements.GLCharacterMultiplicity
import RSCounterexample.Paper.GL.Twist
import RSCounterexample.Paper.HighestWeight.Integration
import RSCounterexample.Paper.Quiver.Schur.Cauchy
import RSCounterexample.Paper.Quiver.Levi
import RSCounterexample.GLRep.Levi.Multiplicity
import RSCounterexample.GLRep.Rational.Twist

/-!
# Characters determine multiplicities: proof of `GLCharacterMultiplicity`

This file proves the standard result `Schubert.RS.GLCharacterMultiplicity`
(`Schubert.RS.glCharacterMultiplicity_holds`) from the representation theory of `GL_n` and of its
Levi subgroups developed in `Schubert.GLRep`.

* A polynomial representation of `L = ∏_p GL_{d_p}(ℂ)` in the sense of RS is polynomial in the
  sense of the library (`Schubert.RS.GL.isPolynomialLeviRep_glRep`), and its RS character is its
  library character with the variables `x_{p,i}` placed at the positions `Levi.pos d p i`
  (`Schubert.RS.GL.eq_rename_leviCharacter`).
* The library expands the character as `∑_μ dim Hom_L(⊠_p V(μ_p), ρ) ∏_p s_{μ_p}(x_{p,·})`.
  Under `toLaurent`, `∏_p s_{μ_p}(x_{p,·})` is RS's `Levi.leviSchur` of the weights of the `μ_p`
  (`Schubert.RS.GL.toLaurent_rename_leviSchur`), so the Levi Weyl projector reads off the
  multiplicity (`Levi.schurCoeff_sum_leviSchur`).
* RS's irreducible representation `ratLeviIrrep d λ` is equivalent to the library's
  `⊠_p V(λ_p)` (`Schubert.RS.GL.nonempty_equiv_ratLeviIrrep`). Block by block, the flag-minor
  model of `λ_p − c_p` is the Weyl module of `λ_p − c_p` by RS's uniqueness theorem
  (`Schubert.RS.HighestWeight.nonempty_equiv_flagOrbitRepresentation`), and twisting by
  `det^{c_p}` gives `V(λ_p)` (`GLRep.nonempty_equiv_scaledRep_irrep`).
-/

open Schubert.RS.Quiver

namespace Schubert.RS.GL

noncomputable section

open Module

variable {s : ℕ} {d : Fin s → ℕ}

/-! ### Polynomial representations and characters -/

/-- An RS polynomial representation of the Levi group is polynomial in the sense of the
library. -/
theorem isPolynomialLeviRep_glRep {W : Type*} [AddCommGroup W] [Module ℂ W]
    {ρ : _root_.Representation ℂ (LeviGroup d) W} (h : IsPolynomialLeviRep d ρ) :
    GLRep.IsPolynomialLeviRep (K := ℂ) (d := d) ρ := by
  obtain ⟨b, P, hP⟩ := h
  exact (GLRep.hasCoeffsIn_iff_toMatrix b).mpr fun i j =>
    GLRep.mem_coordFunctions.mpr ⟨P i j, fun g => hP g i j⟩

/-- The positions of the variables of the Levi torus. -/
def sigmaPos (d : Fin s → ℕ) : (Σ p : Fin s, Fin (d p)) ≃ Fin (Levi.total d) := finSigmaFinEquiv

theorem leviTorus_eq_glRep (t : (Σ p : Fin s, Fin (d p)) → ℂˣ) :
    leviTorus d (t ∘ (sigmaPos d).symm) = GLRep.leviTorus ℂ d t := by
  funext p
  simp only [leviTorus, GLRep.leviTorus_apply, Function.comp_apply, Levi.pos, sigmaPos,
    Equiv.symm_apply_apply]

/-- **The RS character is the library character**, with the variables `x_{p,i}` at the positions
`Levi.pos d p i`. -/
theorem eq_rename_leviCharacter {W : Type*} [AddCommGroup W] [Module ℂ W]
    {ρ : _root_.Representation ℂ (LeviGroup d) W} (h : IsPolynomialLeviRep d ρ)
    {χ : Schubert.RS.Polynomial (Levi.total d)} (hχ : IsLeviCharacter d ρ χ) :
    χ = MvPolynomial.rename (sigmaPos d) (GLRep.leviCharacter (K := ℂ) ρ) := by
  have h' := isPolynomialLeviRep_glRep h
  have hsymm : MvPolynomial.rename (sigmaPos d).symm χ = GLRep.leviCharacter (K := ℂ) ρ := by
    refine GLRep.eq_leviCharacter_of_forall_trace_eq h' _ fun t => ?_
    rw [MvPolynomial.eval₂_rename, ← leviTorus_eq_glRep, hχ]
    rfl
  rw [← hsymm, MvPolynomial.rename_rename, Equiv.self_comp_symm, MvPolynomial.rename_id_apply]

/-! ### Products of Schur polynomials -/

theorem toLaurent_rename_blockVar (p : Fin s) (P : MvPolynomial (Fin (d p)) ℤ) :
    toLaurent (MvPolynomial.rename (sigmaPos d ∘ GLRep.blockVar p) P) =
      Levi.embedBlock d p (toLaurent P) := by
  have h : (toLaurent (n := Levi.total d)).comp
      (MvPolynomial.rename (sigmaPos d ∘ GLRep.blockVar p)).toRingHom =
      (Levi.embedBlock d p).comp toLaurent := by
    refine MvPolynomial.ringHom_ext (fun z => ?_) fun i => ?_
    · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, MvPolynomial.rename_C]
      rw [← MvPolynomial.monomial_zero', ← MvPolynomial.monomial_zero', toLaurent_monomial,
        toLaurent_monomial, Levi.embedBlock_single, map_zero, map_zero, Pi.single_zero, map_zero]
    · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, MvPolynomial.rename_X]
      rw [MvPolynomial.X, MvPolynomial.X, toLaurent_monomial, toLaurent_monomial,
        Levi.embedBlock_single]
      congr 1
      rw [show exponentWeight (Finsupp.single i 1) = Pi.single i (1 : ℤ) from ?_,
        Levi.blockSplit_single_single]
      · funext j
        simp [exponentWeight, Finsupp.single_apply, Pi.single_apply, eq_comm, sigmaPos,
          GLRep.blockVar, Levi.pos]
      · funext j
        simp [exponentWeight, Finsupp.single_apply, Pi.single_apply, eq_comm]
  exact congrArg (fun f : MvPolynomial (Fin (d p)) ℤ →+* Laurent (Levi.total d) => f P) h

/-- **The library's `∏_p s_{μ_p}(x_{p,·})` is RS's `Levi.leviSchur`.** -/
theorem toLaurent_rename_leviSchur {μ : Fin s → YoungDiagram} (hμ : ∀ p, (μ p).colLen 0 ≤ d p) :
    toLaurent (MvPolynomial.rename (sigmaPos d) (GLRep.leviSchur d μ)) =
      Levi.leviSchur d fun p => TauCeti.weightOfShape (d p) (μ p) := by
  rw [GLRep.leviSchur, map_prod, map_prod, Levi.leviSchur]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [MvPolynomial.rename_rename, toLaurent_rename_blockVar,
    Schur.toLaurent_diagramSchurPoly_eq_ratSchur (μ p) (hμ p)]

/-! ### Flag-minor models and Weyl modules -/

section Flag

open Schubert.RS.HighestWeight

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : ℕ}

theorem weightSpace_irrep_le_lieWeightSpace (ν : YoungDiagram) (μ : Weight n) :
    GLRep.weightSpace (GLRep.irrep ℂ n ν) μ ≤
      lieWeightSpace (GLRep.isPolynomialRep_irrep (K := ℂ) (n := n) ν).lie μ := fun _ hx j =>
  (GLRep.isPolynomialRep_irrep ν).lie_apply_of_mem_weightSpace hx j

/-- The `gl_n`-module of the Weyl module `V(ν)`, as an RS `GLModule`. -/
abbrev irrepGLModule (ν : YoungDiagram) : GLModule n where
  carrier := GLRep.IrrepSpace ℂ n ν
  instFiniteDimensional := (GLRep.isPolynomialRep_irrep (K := ℂ) (n := n) ν).finiteDimensional
  lie := (GLRep.isPolynomialRep_irrep (K := ℂ) (n := n) ν).lie
  weight_span := by
    refine top_le_iff.mp ?_
    rw [← (GLRep.isPolynomialRep_irrep (K := ℂ) (n := n) ν).comp_diagGL
      |>.iSup_torusWeightSpace_eq_top]
    exact iSup_mono fun μ => weightSpace_irrep_le_lieWeightSpace ν μ

theorem weightCharHom_eq_integerWeightScalar (μ : Weight n) (t : Fin n → ℂˣ) :
    TauCeti.weightCharHom ℂ μ t = Schubert.RS.Representation.integerWeightScalar μ t := by
  rw [TauCeti.weightCharHom_apply, TauCeti.weightChar_apply, TauCeti.torusCharacter_def,
    Units.coe_prod, Schubert.RS.Representation.integerWeightScalar]
  exact Finset.prod_congr rfl fun i _ => Units.val_zpow_eq_zpow_val _ _

/-- The Weyl module integrates its `gl_n`-module. -/
theorem integrates_irrepGLModule (ν : YoungDiagram) :
    (irrepGLModule (n := n) ν).Integrates (GLRep.irrep ℂ n ν) := by
  have h := GLRep.isPolynomialRep_irrep (K := ℂ) (n := n) ν
  refine ⟨fun {a b} hab x => ?_, fun {a b} hab t x N hN => ?_, fun μ t x hx => ?_⟩
  · obtain ⟨N, hN⟩ := h.isNilpotent_lie (GLRep.single_mul_single_of_ne hab)
    exact ⟨N, by
      change (h.lie (Matrix.single a b 1) ^ N) x = 0
      rw [hN, LinearMap.zero_apply]⟩
  · have hE := GLRep.single_mul_single_of_ne (K := ℂ) hab
    have hunit : transvectionUnit hab t =
        GLRep.lineGL (Matrix.single a b 1) t (GLRep.det_one_add_smul_of_sq_eq_zero hE t) :=
      Units.ext rfl
    set M := max N (h.curveDegree (Matrix.single a b 1) + 1)
    rw [hunit, h.rho_lineGL_eq_exp hE t (lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)),
      LinearMap.sum_apply]
    change ∑ k ∈ Finset.range M, ((t ^ k * (k.factorial : ℂ)⁻¹) • h.lie (Matrix.single a b 1) ^ k)
      x = ∑ k ∈ Finset.range N, (t ^ k / (k.factorial : ℂ)) • (h.lie (Matrix.single a b 1) ^ k) x
    have hN' : (h.lie (Matrix.single a b 1) ^ N) x = 0 := hN
    have hsub : Finset.range N ⊆ Finset.range M := Finset.range_mono (le_max_left _ _)
    have hzero : ∀ k ∈ Finset.range M, k ∉ Finset.range N →
        ((t ^ k * (k.factorial : ℂ)⁻¹) • h.lie (Matrix.single a b 1) ^ k) x = 0 := by
      intro k _ hkN
      have hk : N ≤ k := by simpa using hkN
      obtain ⟨j, rfl⟩ : ∃ j, k = j + N := ⟨k - N, by omega⟩
      rw [LinearMap.smul_apply, pow_add (h.lie (Matrix.single a b 1)), Module.End.mul_apply, hN',
        map_zero, smul_zero]
    rw [← Finset.sum_subset hsub hzero]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [LinearMap.smul_apply, div_eq_mul_inv]
  · have hunit : diagonalUnit t = TauCeti.diagGL t := Units.ext (TauCeti.diagGL_coe t).symm
    have hw : x ∈ GLRep.weightSpace (GLRep.irrep ℂ n ν) μ := by
      have hmem : h.toLieRep x ∈ GLRep.glWeightSpace ℂ h.LieRep μ := by
        refine GLRep.mem_glWeightSpace.mpr fun i => ?_
        rw [h.lie_toLieRep]
        exact congrArg h.toLieRep (hx i)
      rw [← h.map_weightSpace] at hmem
      obtain ⟨y, hy, hyx⟩ := hmem
      rwa [show y = x from h.toLieRep.injective hyx] at hy
    rw [hunit, ← weightCharHom_eq_integerWeightScalar]
    exact GLRep.apply_of_mem_torusWeightSpace hw t

/-- **The Weyl module `V(ν)` is the flag-minor model** of the same highest weight. -/
theorem nonempty_equiv_flagOrbitRepresentation_irrep {m : Schubert.RS.Representation.ColumnShape n}
    {ν : YoungDiagram} (hν : ν.colLen 0 ≤ n)
    (hm : ∀ i : Fin n, ν.rowLen i = Schubert.RS.Representation.shapeWeight m i) :
    Nonempty ((GLRep.irrep ℂ n ν).Equiv (flagOrbitRepresentation m)) := by
  have h := GLRep.isPolynomialRep_irrep (K := ℂ) (n := n) ν
  have hv := GLRep.isGlHighestWeightVector_irrepHighestVector (K := ℂ) hν
  refine nonempty_equiv_flagOrbitRepresentation (irrepGLModule ν) (GLRep.irrep ℂ n ν)
    (integrates_irrepGLModule ν) (GLRep.isIrreducible_irrep hν) m
    (GLRep.irrepHighestVector ℂ n ν hν) (GLRep.irrepHighestVector_ne_zero hν) ?_ ?_
  · intro j
    have := hv.lie_single_self_eq_smul j
    rw [h.lie_toLieRep] at this
    change h.lie (Matrix.single j j 1) (GLRep.irrepHighestVector ℂ n ν hν) = _
    have h2 := h.toLieRep.injective (this.trans (map_smul h.toLieRep _ _).symm)
    rw [h2, dominantWeight, hm j]
    norm_cast
  · intro a b hab
    have := hv.lie_single_eq_zero hab
    rw [h.lie_toLieRep] at this
    exact h.toLieRep.injective (this.trans (map_zero _).symm)

end Flag

/-! ### The irreducible representations of the Levi group -/

section Levi

open Schubert.RS.HighestWeight

/-- Block by block: the flag-minor model of `λ − λ_n`, twisted by `det^{λ_n}`, is `V(λ)`. -/
theorem nonempty_equiv_block {m : ℕ} {l : TauCeti.DominantWeight m} (hl : l.IsPolynomial) :
    Nonempty ((GLRep.scaledRep (flagOrbitRepresentation (polyShape l))
      (GLRep.detPow ℂ m l.detShift.toNat)).Equiv (GLRep.irrep ℂ m l.shape)) := by
  obtain ⟨e₁⟩ := nonempty_equiv_flagOrbitRepresentation_irrep (m := polyShape l)
    (ν := l.detShiftShape) (TauCeti.DominantWeight.colLen_zero_shape_le _) fun i => by
      rw [TauCeti.DominantWeight.rowLen_detShiftShape, shapeWeight_polyShape]
  obtain ⟨e₂⟩ := GLRep.nonempty_equiv_scaledRep_detShiftShape (K := ℂ) hl
  exact ⟨(GLRep.scaledRepEquiv e₁.symm _).trans e₂⟩

theorem extTensor_tprod_rs {V : Fin s → Type*} [∀ p, AddCommMonoid (V p)] [∀ p, Module ℂ (V p)]
    (ρ : (p : Fin s) → _root_.Representation ℂ (GL (Fin (d p)) ℂ) (V p)) (g : LeviGroup d)
    (v : (p : Fin s) → V p) :
    extTensor d ρ g (PiTensorProduct.tprod ℂ v) =
      PiTensorProduct.tprod ℂ fun p => ρ p (g p) (v p) := by
  simp [extTensor, PiTensorProduct.mapMonoidHom, PiTensorProduct.map_tprod]

/-- **RS's irreducible representation `⊗_p V_p^{λ^{(p)}}` is the library's `⊠_p V(λ^{(p)})`**,
for a polynomial dominant weight `λ`. -/
theorem nonempty_equiv_ratLeviIrrep (lam : (p : Fin s) → TauCeti.DominantWeight (d p))
    (hlam : ∀ p, (lam p).IsPolynomial) :
    Nonempty ((ratLeviIrrep d lam).Equiv (GLRep.leviIrrep ℂ d fun p => (lam p).shape)) := by
  let E := fun p => (nonempty_equiv_block (hlam p)).some
  let L := (TensorProduct.rid ℂ _).trans (PiTensorProduct.congr fun p => (E p).toLinearEquiv)
  have hk : ∀ p, 0 ≤ (lam p).detShift := fun p =>
    (TauCeti.DominantWeight.isPolynomial_iff_zero_le_detShift _).mp (hlam p)
  refine ⟨.mk L fun g => ?_⟩
  -- the scalar of the twist
  have hc : ((leviDetCharacter d (fun p => (lam p).detShift) g : ℂˣ) : ℂ) =
      ∏ p, (GLRep.detPow ℂ (d p) (lam p).detShift.toNat (g p) : ℂ) := by
    rw [leviDetCharacter_apply, Units.coe_prod]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [GLRep.detPow, MonoidHom.pow_apply, ← zpow_natCast, Int.toNat_of_nonneg (hk p)]
  -- on the untwisted tensor product
  have key : (PiTensorProduct.congr fun p => (E p).toLinearEquiv).toLinearMap ∘ₗ
      (((leviDetCharacter d (fun p => (lam p).detShift) g : ℂˣ) : ℂ) •
        extTensor d (fun p => flagOrbitRepresentation (polyShape (lam p))) g) =
      GLRep.leviIrrep ℂ d (fun p => (lam p).shape) g ∘ₗ
        (PiTensorProduct.congr fun p => (E p).toLinearEquiv).toLinearMap := by
    refine PiTensorProduct.ext (MultilinearMap.ext fun v => ?_)
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.smul_apply, LinearEquiv.coe_coe, extTensor_tprod_rs, map_smul,
      PiTensorProduct.congr_tprod, GLRep.extTensor_tprod]
    have hE : ∀ p, GLRep.irrep ℂ (d p) (lam p).shape (g p) ((E p).toLinearEquiv (v p)) =
        (GLRep.detPow ℂ (d p) (lam p).detShift.toNat (g p) : ℂ) •
          (E p).toLinearEquiv (flagOrbitRepresentation (polyShape (lam p)) (g p) (v p)) := by
      intro p
      rw [← map_smul]
      exact (LinearMap.congr_fun ((E p).toIntertwiningMap.isIntertwining' (g p)) (v p)).symm
    simp only [hE]
    rw [MultilinearMap.map_smul_univ, hc]
  refine LinearMap.ext fun x => ?_
  change PiTensorProduct.congr _ (TensorProduct.rid ℂ _ (ratLeviIrrep d lam g x)) =
    GLRep.leviIrrep ℂ d (fun p => (lam p).shape) g (PiTensorProduct.congr _
      (TensorProduct.rid ℂ _ x))
  rw [ratLeviIrrep, leviTwist, leviDetChar, rid_tprod_ofLinearCharacter]
  exact LinearMap.congr_fun key _

end Levi

end

end Schubert.RS.GL

namespace Schubert.RS

open Module Schubert.RS.GL

/-! ### The proof -/

/-- **`GLCharacterMultiplicity` holds**: for a polynomial representation `ρ` of
`L = ∏_p GL_{d_p}(ℂ)` with character `χ` and a polynomial dominant weight `λ`,
`dim Hom_L(⊗_p V_p^{λ^{(p)}}, ρ)` is the coefficient of `∏_p s_{λ^{(p)}}(x_{I_p})` in `χ`. -/
theorem glCharacterMultiplicity_holds : GLCharacterMultiplicity := by
  classical
  intro s d W _ _ ρ χ hpoly hχ lam hlam
  have h := isPolynomialLeviRep_glRep hpoly
  -- the RS irreducible is the library's
  obtain ⟨e⟩ := nonempty_equiv_ratLeviIrrep lam hlam
  rw [show finrank ℂ ((ratLeviIrrep d lam).IntertwiningMap ρ) =
      GLRep.leviMultiplicity ρ (fun p => (lam p).shape) by
    rw [GLRep.leviMultiplicity]
    exact finrank_intertwiningMap_congr e (_root_.Representation.Equiv.refl ρ)]
  -- the Levi expansion of the character
  obtain ⟨S, hSn, hSz, hSχ⟩ := GLRep.IsPolynomialLeviRep.exists_leviCharacter_eq_sum h
  have hexp : toLaurent χ = ∑ μ ∈ S, ((GLRep.leviMultiplicity ρ μ : ℤ) : Laurent (Levi.total d)) *
      Levi.leviSchur d fun p => TauCeti.weightOfShape (d p) (μ p) := by
    rw [eq_rename_leviCharacter hpoly hχ, hSχ, map_sum, map_sum]
    refine Finset.sum_congr rfl fun μ hμ => ?_
    rw [map_zsmul, map_zsmul, toLaurent_rename_leviSchur (hSn μ hμ), zsmul_eq_mul]
  rw [hexp, Levi.schurCoeff_sum_leviSchur d S _ _ _ fun p => (lam p).2]
  -- only `μ = λ` contributes
  have hcond : ∀ μ ∈ S, ((fun p => (TauCeti.weightOfShape (d p) (μ p)).1) =
      fun p => (lam p).1) ↔ μ = fun p => (lam p).shape := by
    intro μ hμ
    constructor
    · intro hml
      funext p
      have : TauCeti.weightOfShape (d p) (μ p) = lam p := Subtype.ext (congrFun hml p)
      rw [← this, TauCeti.shape_weightOfShape (hSn μ hμ p)]
    · rintro rfl
      funext p
      rw [TauCeti.weightOfShape_shape (hlam p)]
  rw [Finset.sum_congr rfl fun μ hμ => by rw [if_congr (hcond μ hμ) rfl rfl], Finset.sum_ite_eq']
  split_ifs with hmem
  · rfl
  · rw [hSz _ (fun p => TauCeti.DominantWeight.colLen_zero_shape_le _) hmem, Nat.cast_zero]

end Schubert.RS
