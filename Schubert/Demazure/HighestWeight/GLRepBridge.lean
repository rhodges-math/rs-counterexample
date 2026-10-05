import Schubert.Demazure.HighestWeight.Integration
import Schubert.GLRep.HighestWeight.WeylModule
import Schubert.GLRep.Lie.Exponential

/-!
# The flag-minor model of `V(λ)` and the Weyl module of `Schubert.GLRep`

The Weyl module `GLRep.irrep ℂ n ν` of `Schubert.GLRep` is a `GLModule` that integrates to its own
representation (`integrates_irrepGLModule`). By the uniqueness theorem
`Demazure.HighestWeight.nonempty_equiv_flagOrbitRepresentation`, it is therefore equivalent to the
flag-minor model `flagOrbitRepresentation m` of the same highest weight
(`nonempty_equiv_flagOrbitRepresentation_irrep`). So the two models of the irreducible polynomial
representations of `GL_n` over `ℂ`, by highest weight vectors and by flag minors, agree.
-/

open Schubert

namespace Demazure.HighestWeight

open FlagModule

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : ℕ}

theorem weightSpace_irrep_le_lieWeightSpace (ν : YoungDiagram) (μ : Weight n) :
    GLRep.weightSpace (GLRep.irrep ℂ n ν) μ ≤
      lieWeightSpace (GLRep.isPolynomialRep_irrep (K := ℂ) (n := n) ν).lie μ := fun _ hx j =>
  (GLRep.isPolynomialRep_irrep ν).lie_apply_of_mem_weightSpace hx j

/-- The `gl_n`-module of the Weyl module `V(ν)`, as a `GLModule`. -/
noncomputable abbrev irrepGLModule (ν : YoungDiagram) : GLModule n where
  carrier := GLRep.IrrepSpace ℂ n ν
  instFiniteDimensional := (GLRep.isPolynomialRep_irrep (K := ℂ) (n := n) ν).finiteDimensional
  lie := (GLRep.isPolynomialRep_irrep (K := ℂ) (n := n) ν).lie
  weight_span := by
    refine top_le_iff.mp ?_
    rw [← (GLRep.isPolynomialRep_irrep (K := ℂ) (n := n) ν).comp_diagGL
      |>.iSup_torusWeightSpace_eq_top]
    exact iSup_mono fun μ => weightSpace_irrep_le_lieWeightSpace ν μ

theorem weightCharHom_eq_integerWeightScalar (μ : Weight n) (t : Fin n → ℂˣ) :
    TauCeti.weightCharHom ℂ μ t = integerWeightScalar μ t := by
  rw [TauCeti.weightCharHom_apply, TauCeti.weightChar_apply, TauCeti.torusCharacter_def,
    Units.coe_prod, integerWeightScalar]
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
theorem nonempty_equiv_flagOrbitRepresentation_irrep {m : ColumnShape n}
    {ν : YoungDiagram} (hν : ν.colLen 0 ≤ n)
    (hm : ∀ i : Fin n, ν.rowLen i = shapeWeight m i) :
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

end Demazure.HighestWeight
