import Schubert.FlagVarieties.Modules.DemazureModules
import Schubert.GLRep.Borel.Generation
import Schubert.Demazure.JosephPolo.OrbitSpan
import Schubert.Demazure.JosephPolo.RootSubstitution
import Schubert.Demazure.Representation.FlagWeights

/-!
# Demazure modules in the flag-minor model

In the flag-minor model `V(λ) = flagOrbitSpan m ⊆ ℂ[x_ij]` of the `Demazure` library
(`Demazure.HighestWeight.flagOrbitRepresentation`), with `GL_n(ℂ)` acting by the row action:

* the highest flag polynomial `v_λ` is a `B`-eigenvector of weight `λ`
  (`FlagVarieties.polynomialGL_highestFlag`);
* the Demazure module `flagDemazure m w` (the `𝔫⁺`-cyclic span of the extremal flag polynomial)
  is `B`-stable (`FlagVarieties.polynomialGL_mem_flagDemazure`) and is the `B`-span of the
  extremal vector `ẇ v_λ` (`FlagVarieties.map_extremalSpan_flagModel`);
* hence the Demazure module `D_S` of `FlagVarieties.demazureSubrep` is
  `Demazure.Filtrations.demazureUnion m S`
  (`FlagVarieties.map_demazureSubrep_flagModel`), and
  **`H⁰(X_S, 𝓛(−λ)) ≅ D_S^∨` with `D_S = demazureUnion m S`**
  (`FlagVarieties.flagModelSectionEquiv`).
-/

open Schubert GLRep TauCeti Module Demazure.FlagModule Demazure.HighestWeight
  Demazure.SchubertUnions Demazure.Filtrations FinPermutation

namespace FlagVarieties

open PointModel.Complex SectionRep

noncomputable section

variable {n : ℕ}

/-! ### The row action of `B` -/

theorem polynomialGL_diagGL (t : Fin n → ℂˣ) (p : MatrixPolynomial n) :
    polynomialGL n (diagGL t) p = polynomialTorus n t p :=
  rfl

theorem polynomialGL_transvectionGL {a b : Fin n} (hab : a ≠ b) (t : ℂ) (p : MatrixPolynomial n) :
    polynomialGL n (transvectionGL hab t) p = rowAction (1 + t • Matrix.single a b 1) p :=
  rfl

/-- An upper transvection fixes the highest flag polynomial. -/
theorem rowAction_transvection_highestFlag (m : ColumnShape n) {a b : Fin n} (hab : a < b)
    (t : ℂ) : rowAction (1 + t • Matrix.single a b 1) (highestFlag m) = highestFlag m := by
  have hiter : ∀ k, derivationIter (matrixUnitDerivation a b) (k + 1) (highestFlag m) = 0 := by
    intro k
    induction k with
    | zero => rw [derivationIter_succ, derivationIter_zero, highestFlag_upper_invariant m a b hab]
    | succ k ih => rw [derivationIter_succ, ih, map_zero]
  have hpoly : rootSubstitution a b (highestFlag m) = Polynomial.C (highestFlag m) := by
    ext1 k
    rcases k with _ | k
    · rw [Polynomial.coeff_C_zero, Polynomial.coeff_zero_eq_eval_zero,
        rootSubstitution_eval_zero]
    · rw [Polynomial.coeff_C_succ]
      have h := rootSubstitution_coeff a b hab.ne (highestFlag m) (k + 1)
      rw [hiter k] at h
      exact (smul_eq_zero.mp h).resolve_left (Nat.factorial_ne_zero _)
  rw [← rootSubstitution_eval, hpoly, Polynomial.eval_C]

/-- **`v_λ` is a `B`-eigenvector of weight `λ`.** -/
theorem polynomialGL_highestFlag (m : ColumnShape n) (b : borel ℂ n) :
    polynomialGL n (b : GL (Fin n) ℂ) (highestFlag m) =
      ((borelChar ℂ n (shapeWeightZ m) b : ℂˣ) : ℂ) • highestFlag m := by
  obtain ⟨g, hg⟩ := b
  have key := borel_induction (K := ℂ) (P := fun g => g ∈ borel ℂ n ∧ ∀ hg : g ∈ borel ℂ n,
      polynomialGL n g (highestFlag m) =
        ((borelChar ℂ n (shapeWeightZ m) ⟨g, hg⟩ : ℂˣ) : ℂ) • highestFlag m)
    (fun g h hPg hPh => ⟨mul_mem hPg.1 hPh.1, fun hgh => by
      have e : (⟨g * h, hgh⟩ : borel ℂ n) = ⟨g, hPg.1⟩ * ⟨h, hPh.1⟩ := rfl
      rw [map_mul, Module.End.mul_apply, hPh.2 hPh.1, map_smul, hPg.2 hPg.1, smul_smul, e,
        map_mul, Units.val_mul, mul_comm]⟩)
    (fun {a b} hab t => ⟨transvectionGL_mem_borel hab t, fun _ => by
      rw [polynomialGL_transvectionGL, rowAction_transvection_highestFlag m hab,
        borelChar_transvectionGL hab, Units.val_one, one_smul]⟩)
    (fun t => ⟨(borelTorus ℂ n t).2, fun ht => by
      have e : (⟨diagGL t, ht⟩ : borel ℂ n) = borelTorus ℂ n t := rfl
      rw [polynomialGL_diagGL, highestFlag_weight, e, borelChar_borelTorus, weightChar_apply,
        torusCharacter_def, Units.coe_prod]
      congr 1⟩) hg
  exact key.2 hg

/-- **The Demazure modules `flagDemazure m w` are `B`-stable.** -/
theorem polynomialGL_mem_flagDemazure (m : ColumnShape n) (w : Equiv.Perm (Fin n))
    (b : borel ℂ n) {p : MatrixPolynomial n} (hp : p ∈ flagDemazure m w) :
    polynomialGL n (b : GL (Fin n) ℂ) p ∈ flagDemazure m w := by
  obtain ⟨g, hg⟩ := b
  refine borel_induction (K := ℂ) (P := fun g => ∀ p ∈ flagDemazure m w,
      polynomialGL n g p ∈ flagDemazure m w) ?_ ?_ ?_ hg p hp
  · intro g h hPg hPh p hp
    rw [map_mul, Module.End.mul_apply]
    exact hPg _ (hPh p hp)
  · intro a b hab t p hp
    rw [polynomialGL_transvectionGL]
    rw [flagDemazure_eq_upperRowOrbitSpan] at hp ⊢
    exact upperRowOrbitSpan_stable _ ⟨(a, b), hab⟩ t hp
  · intro t p hp
    rw [polynomialGL_diagGL]
    exact flagDemazure_torus_stable m w t hp

/-- The product of the transvections of an upper word, an element of `B`. -/
def upperWordGL : List (PositiveRoot n × ℂ) → GL (Fin n) ℂ
  | [] => 1
  | (r, t) :: z => transvectionGL r.2.ne t * upperWordGL z

theorem upperWordGL_mem_borel : ∀ z : List (PositiveRoot n × ℂ), upperWordGL z ∈ borel ℂ n
  | [] => one_mem _
  | (r, t) :: z => mul_mem (transvectionGL_mem_borel r.2 t) (upperWordGL_mem_borel z)

theorem upperRowWord_eq_polynomialGL :
    ∀ (z : List (PositiveRoot n × ℂ)) (p : MatrixPolynomial n),
      upperRowWord z p = polynomialGL n (upperWordGL z) p
  | [], p => by rw [upperWordGL, map_one]; rfl
  | (r, t) :: z, p => by
    rw [upperWordGL, map_mul, Module.End.mul_apply, ← upperRowWord_eq_polynomialGL z p,
      polynomialGL_transvectionGL]
    rfl

theorem polynomialGL_permGL_highestFlag (m : ColumnShape n) (w : Equiv.Perm (Fin n)) :
    polynomialGL n (permGL w) (highestFlag m) = extremalFlag m w :=
  polynomialGL_rowPermutationUnit w (highestFlag m)

/-! ### The flag-minor model of `V(λ)` -/

theorem exists_youngDiagram (m : ColumnShape n) :
    ∃ ν : YoungDiagram, ν.colLen 0 ≤ n ∧ ∀ i : Fin n, ν.rowLen i = shapeWeight m i := by
  let l : DominantWeight n := ⟨fun i => (shapeWeight m i : ℤ), fun i j hij => by
    show (shapeWeight m j : ℤ) ≤ shapeWeight m i
    exact_mod_cast shapeWeight_antitone m hij⟩
  refine ⟨l.shape, DominantWeight.colLen_zero_shape_le l, fun i => ?_⟩
  rw [DominantWeight.rowLen_shape]
  exact Int.toNat_natCast _

theorem isRationalRep_flagOrbitRepresentation (m : ColumnShape n) :
    IsRationalRep (flagOrbitRepresentation m) := by
  obtain ⟨ν, hν, hm⟩ := exists_youngDiagram m
  obtain ⟨e⟩ := nonempty_equiv_flagOrbitRepresentation_irrep hν hm
  exact (isPolynomialRep_irrep (K := ℂ) (n := n) ν).isRationalRep.of_equiv e

/-- The highest flag polynomial as a vector of the flag-minor model. -/
def highestFlagVec (m : ColumnShape n) : flagOrbitSpan m :=
  ⟨highestFlag m, highestFlag_mem_orbitSpan m⟩

theorem flagOrbitRepresentation_highestFlagVec (m : ColumnShape n) (b : borel ℂ n) :
    flagOrbitRepresentation m b (highestFlagVec m) =
      (((borelChar ℂ n (-shapeWeightZ m) b)⁻¹ : ℂˣ) : ℂ) • highestFlagVec m := by
  refine Subtype.ext ?_
  rw [flagOrbitRepresentation_val, Submodule.coe_smul, borelChar_neg, MonoidHom.inv_apply, inv_inv]
  exact polynomialGL_highestFlag m b

/-- **The Demazure module `flagDemazure m w` is the `B`-span of the extremal vector `ẇ v_λ`.** -/
theorem map_extremalSpan_flagModel (m : ColumnShape n) (w : Equiv.Perm (Fin n)) :
    (extremalSpan (flagOrbitRepresentation m) (highestFlagVec m) w).map
      (flagOrbitSpan m).subtype = flagDemazure m w := by
  rw [extremalSpan, orbitSpan, Submodule.map_span, ← Set.image_comp, ← Set.image_comp]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨b, hb, rfl⟩
    change polynomialGL n (b * permGL w) (highestFlag m) ∈ flagDemazure m w
    rw [map_mul, Module.End.mul_apply, polynomialGL_permGL_highestFlag]
    refine polynomialGL_mem_flagDemazure m w ⟨b, hb⟩ ?_
    rw [flagDemazure_eq_upperRowOrbitSpan]
    exact upperRowOrbitSpan_seed _
  · rw [flagDemazure_eq_upperRowOrbitSpan, upperRowOrbitSpan, Submodule.span_le]
    rintro _ ⟨z, rfl⟩
    refine Submodule.subset_span ⟨upperWordGL z, upperWordGL_mem_borel z, ?_⟩
    change polynomialGL n (upperWordGL z * permGL w) (highestFlag m) =
      upperRowWord z (extremalFlag m w)
    rw [map_mul, Module.End.mul_apply, polynomialGL_permGL_highestFlag,
      upperRowWord_eq_polynomialGL]

/-- **The Demazure module `D_S` of the flag-minor model is `demazureUnion m S`.** -/
theorem map_demazureSubrep_flagModel (m : ColumnShape n) (S : Finset (Equiv.Perm (Fin n))) :
    (demazureSubrep (flagOrbitRepresentation m) (highestFlagVec m) S).toSubmodule.map
      (flagOrbitSpan m).subtype = demazureUnion m S := by
  rw [toSubmodule_demazureSubrep, orbitSpan, orbitSet, Set.image_iUnion₂, Submodule.span_iUnion₂]
  simp only [Submodule.map_iSup]
  rw [demazureUnion, iSup_subtype']
  refine iSup_congr fun w => ?_
  change Submodule.map _ (orbitSpan (flagOrbitRepresentation m) (highestFlagVec m)
    (bruhatCell (w : Equiv.Perm (Fin n)))) = _
  rw [orbitSpan_bruhatCell (flagOrbitRepresentation_highestFlagVec m),
    map_extremalSpan_flagModel]

/-- In the flag-minor model, `V^∨ → H⁰(G/B, 𝓛(−λ))` is onto. -/
theorem dualToInducedRep_flagModel_surjective
    (m : ColumnShape n) :
    Function.Surjective (dualToInducedRep (isRationalRep_flagOrbitRepresentation m)
      (flagOrbitRepresentation_highestFlagVec m)) := by
  have := (isRationalRep_flagOrbitRepresentation m).finiteDimensional
  let e := (flagOrbitEquivInducedRep m).toLinearEquiv
  have : FiniteDimensional ℂ (indBorelSubrep ℂ n (-shapeWeightZ m)).toSubmodule :=
    LinearEquiv.finiteDimensional e
  have hfin : finrank ℂ (Dual ℂ (flagOrbitSpan m)) =
      finrank ℂ (indBorelSubrep ℂ n (-shapeWeightZ m)).toSubmodule := by
    rw [Subspace.dual_finrank_eq, ← e.finrank_eq]
  have hv0 : highestFlagVec m ≠ 0 := fun h => highestFlag_ne_zero m (congrArg Subtype.val h)
  have hinj := matrixCoeff_injective (isRationalRep_flagOrbitRepresentation m)
    (orbitSpan_univ_eq_top_of_isIrreducible (flagOrbitRepresentation_isIrreducible m) hv0)
  change Function.Surjective (dualToInducedRep (isRationalRep_flagOrbitRepresentation m)
    (flagOrbitRepresentation_highestFlagVec m)).toLinearMap
  rw [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin]
  intro φ ψ h
  exact hinj (congrArg Subtype.val h)

/-- **`H⁰(X_S, 𝓛(−λ)) ≅ D_S^∨` with `D_S = demazureUnion m S` the Demazure union** (as
representations of `B`; the space of `D_S` maps onto `demazureUnion m S` by
`FlagVarieties.map_demazureSubrep_flagModel`). -/
def flagModelSectionEquiv
    (m : ColumnShape n) {S : Finset (Equiv.Perm (Fin n))} (hS : BruhatLower S) :
    (demazureRep (flagOrbitRepresentation m) (highestFlagVec m) S).dual.Equiv
      (sectionRep S (-shapeWeightZ m)) :=
  sectionDemazureEquiv (isRationalRep_flagOrbitRepresentation m)
    (flagOrbitRepresentation_highestFlagVec m) hS
    (fun i j hij => by
      show -(shapeWeight m i : ℤ) ≤ -(shapeWeight m j : ℤ)
      exact neg_le_neg (by exact_mod_cast shapeWeight_antitone m hij))
    (dualToInducedRep_flagModel_surjective m)

end

end FlagVarieties
