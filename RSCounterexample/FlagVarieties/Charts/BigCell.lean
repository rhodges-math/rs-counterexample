import RSCounterexample.FlagVarieties.Charts.AdaptedBasis
import RSCounterexample.FlagVarieties.LineBundle.Model
import RSCounterexample.FlagVarieties.Flag.Action
import RSCounterexample.FlagVarieties.Foundations.Schemes.SelectedFlagMorphismLocalCharts
import RSCounterexample.FlagVarieties.Foundations.Schemes.SelectedQuotientMorphismPresentation

/-!
# Big cells of the flag scheme

For a permutation `v` of `Fin n`, the big cell `bigCell v ⊆ Flₙ` is the incidence chart of the
foundations whose selected coordinates at step `j` are `v(j), …, v(n-1)`. A flag `V•` over a ring
`A` lies in it iff `Vⱼ ⊕ span(e_{v(j)}, …, e_{v(n-1)}) = Aⁿ` for every `j`
(`ofRingFlag_factors_bigCellChart_iff`).

On the big cell the orbit map has a section (`bigCellSection v`): the universal flag of the chart
has an adapted basis `w_k = e_{v(k)} + (lower terms)`, i.e. its basis matrix is `v · u` with `u`
lower unitriangular, and `π(v · u) = V•`.
-/

noncomputable section

namespace FlagVarieties

open AlgebraicGeometry CategoryTheory
open Foundations Foundations.QuotientCharts

universe u

variable {A : Type u} [CommRing A] {n : ℕ}

/-! ### The coordinate selection of a big cell -/

/-- The selected coordinates `v(j), …, v(n-1)` of the big cell of `v` at step `j`. -/
def bigCellSelection (v : Equiv.Perm (Fin n)) (j : Fin (n + 1)) : Fin (n - j.val) ↪ Fin n where
  toFun i := v ⟨j.val + i.val, by omega⟩
  inj' i i' h := by
    have h' := congrArg Fin.val (v.injective h)
    simp only at h'
    exact Fin.ext (by omega)

theorem range_coordinateInclusion_bigCellSelection (v : Equiv.Perm (Fin n)) (j : Fin (n + 1)) :
    LinearMap.range (coordinateInclusion (R := A) (bigCellSelection v j)) = tailSpan v j.val := by
  rw [LinearMap.range_eq_map, ← (Pi.basisFun A (Fin (n - j.val))).span_eq, Submodule.map_span,
    ← Set.range_comp, tailSpan]
  congr 1
  ext x
  simp only [Set.mem_range, Function.comp_apply, Pi.basisFun_apply, coordinateInclusion_basis,
    Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨⟨j.val + i.val, by omega⟩, by simp, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    refine ⟨⟨k.val - j.val, by omega⟩, ?_⟩
    have hk' : (⟨j.val + (k.val - j.val), by omega⟩ : Fin n) = k := Fin.ext (by simp only; omega)
    change (Pi.single (v ⟨j.val + (k.val - j.val), _⟩) (1 : A) : Fin n → A) = _
    rw [hk']

theorem coordinateInclusion_injective {d : ℕ} (a : Fin d ↪ Fin n) :
    Function.Injective (coordinateInclusion (R := A) a) := by
  intro x y h
  funext i
  have := congrFun h (a i)
  have hx : coordinateInclusion (R := A) a x (a i) = x i := by
    conv_lhs => rw [← (Pi.basisFun A (Fin d)).sum_repr x]
    simp [map_sum, Pi.single_apply, a.injective.eq_iff]
  have hy : coordinateInclusion (R := A) a y (a i) = y i := by
    conv_lhs => rw [← (Pi.basisFun A (Fin d)).sum_repr y]
    simp [map_sum, Pi.single_apply, a.injective.eq_iff]
  rw [← hx, ← hy, this]

/-- For an injective `i`, the composite `M →ᵢ N ⟶ N ⧸ P` is bijective iff `P` and the range of
`i` are complements. -/
theorem bijective_mkQ_comp_iff_isCompl {M N : Type*} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (P : Submodule A N) (i : M →ₗ[A] N)
    (hi : Function.Injective i) :
    Function.Bijective (P.mkQ.comp i) ↔ IsCompl P (LinearMap.range i) := by
  have hsurj : Function.Surjective (P.mkQ.comp i) ↔ Codisjoint P (LinearMap.range i) := by
    rw [← LinearMap.range_eq_top, LinearMap.range_comp, codisjoint_iff,
      Submodule.map_mkQ_eq_top]
  have hinj : Function.Injective (P.mkQ.comp i) ↔ Disjoint P (LinearMap.range i) := by
    rw [Submodule.disjoint_def]
    constructor
    · rintro h x hxP ⟨y, rfl⟩
      have : y = 0 := h (by simp [Submodule.Quotient.mk_eq_zero, hxP])
      rw [this, map_zero]
    · intro h y y' hyy'
      simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.eq] at hyy'
      have h0 := h (i y - i y') hyy' ⟨y - y', map_sub i y y'⟩
      exact hi (sub_eq_zero.mp h0)
  rw [Function.Bijective, hinj, hsurj, isCompl_iff]

/-! ### Flags in the big cell -/

/-- A coordinate flag lies in the big cell of `v` if `Vⱼ ⊕ span(e_{v(j)}, …) = Aⁿ` for all `j`. -/
def InBigCell (v : Equiv.Perm (Fin n)) (P : CoordinateFlag A n) : Prop :=
  ∀ j : Fin (n + 1), IsCompl (P.step j).toSubmodule (tailSpan v j.val)

theorem inBigCell_iff_bijective (v : Equiv.Perm (Fin n)) (P : CoordinateFlag A n) :
    InBigCell v P ↔ ∀ j : Fin (n + 1),
      Function.Bijective ((P.step j).toSubmodule.mkQ.comp
        (coordinateInclusion (bigCellSelection v j))) := by
  refine forall_congr' fun j => ?_
  rw [bijective_mkQ_comp_iff_isCompl _ _ (coordinateInclusion_injective _),
    range_coordinateInclusion_bigCellSelection]

/-- The point of a selected chart satisfies the chart condition. -/
theorem selectedChartPoint_bijective {R' : Type u} [CommRing R'] [Algebra R' A] {d : ℕ}
    (a : Fin d ↪ Fin n) (f : MvPolynomial (Fin d × Fin (n - d)) R' →ₐ[R'] A) :
    Function.Bijective ((selectedChartPoint R' a f).toSubmodule.mkQ.comp
      (coordinateInclusion a)) := by
  rw [← selectedCoordinate_chartCondition_iff]
  have h := (matrixGrassmannianChartEquiv (matrixEvaluationEquiv R' d (n - d) A f)).property
  convert h using 2
  rw [selectedChartPoint, grassmannianTransport_submodule, ← Submodule.map_comp]
  simp

/-! ### Points of `GLₙ` given by invertible matrices -/

variable (R : Type u) [CommRing R]

theorem pointMatrix_glPointOfMatrix [Algebra R A] (g : Matrix (Fin n) (Fin n) A)
    (hg : IsUnit g.det) : GLScheme.pointMatrix R n (glPointOfMatrix R g hg) = g :=
  genericMatrix_map_glPointOfMatrix R g hg

/-! ### Big cells -/

/-- The affine incidence chart of the big cell of `v`. -/
abbrev bigCellChartScheme (v : Equiv.Perm (Fin n)) : Scheme.{u} :=
  selectedFlagIncidenceChart R (bigCellSelection v)

/-- The coordinate ring of the big cell chart. -/
abbrev bigCellRing (v : Equiv.Perm (Fin n)) : Type u :=
  MvPolynomial (FlagChartVariable n) R ⧸ selectedFlagIncidenceIdeal R (bigCellSelection v)

/-- The open immersion of the big cell chart into `Flₙ`. -/
abbrev bigCellChart (v : Equiv.Perm (Fin n)) : bigCellChartScheme R v ⟶ FlagScheme R n :=
  selectedFlagChartSchemeChart R n (bigCellSelection v)

/-- The big cell of `v`: the open subset of flags `V•` with `Vⱼ ⊕ span(e_{v(j)}, …) = 𝒪ⁿ`. -/
def bigCell (v : Equiv.Perm (Fin n)) : (FlagScheme R n).Opens :=
  (bigCellChart R v).opensRange

/-- The universal flag on the big cell chart. -/
abbrev bigCellUniversalFlag (v : Equiv.Perm (Fin n)) : CoordinateFlag (bigCellRing R v) n :=
  selectedFlagChartUniversal R (bigCellSelection v)

variable {R}

/-- A chart point map classifies its chart flag. -/
theorem selectedFlagChartPointMap_eq_ofRingFlag [Algebra R A]
    (a : (j : Fin (n + 1)) → Fin (n - j.val) ↪ Fin n)
    (k : MvPolynomial (FlagChartVariable n) R →ₐ[R] A)
    (hk : selectedFlagIncidenceIdeal R a ≤ RingHom.ker k.toRingHom) :
    selectedFlagChartPointMap R a k hk =
      FlagScheme.ofRingFlag R (selectedFlagChartRingFlag R a k hk) := by
  apply FlagScheme.hom_ext_of_steps
  intro j
  rw [selectedFlagChartPointMap_step, FlagScheme.ofRingFlag, simultaneousFlagRelativeMorphism_step,
    selectedFlagChartRingFlag_step, ← selectedQuotientMorphism_selectedChartPoint]
  rfl

variable (R) in
theorem bigCellChart_eq_ofRingFlag (v : Equiv.Perm (Fin n)) :
    bigCellChart R v = FlagScheme.ofRingFlag R (bigCellUniversalFlag R v) := by
  have h0 : selectedFlagIncidenceIdeal R (bigCellSelection v) ≤ RingHom.ker
      (Ideal.Quotient.mkₐ R (selectedFlagIncidenceIdeal R (bigCellSelection v))).toRingHom :=
    fun _ hp => Ideal.Quotient.eq_zero_iff_mem.mpr hp
  have he : selectedFlagIncidenceEvaluation R (bigCellSelection v)
      (Ideal.Quotient.mkₐ R _) h0 = AlgHom.id R _ := by
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro x
    rfl
  have hc : bigCellChart R v = selectedFlagChartPointMap R (bigCellSelection v)
      (Ideal.Quotient.mkₐ R _) h0 := by
    rw [selectedFlagChartPointMap, he, AlgHom.toRingHom_eq_coe, AlgHom.id_toRingHom,
      CommRingCat.ofHom_id, Spec.map_id]
    exact (Category.id_comp (bigCellChart R v)).symm
  rw [hc, selectedFlagChartPointMap_eq_ofRingFlag]
  rfl

/-- A flag whose classifying point factors through the big cell chart lies in the big cell. -/
theorem inBigCell_of_factors [Algebra R A] (v : Equiv.Perm (Fin n)) (P : CoordinateFlag A n)
    (g : Spec (CommRingCat.of A) ⟶ bigCellChartScheme R v)
    (hg : g ≫ bigCellChart R v = FlagScheme.ofRingFlag R P) : InBigCell v P := by
  have hgR : g ≫ selectedFlagIncidenceChartToSpec R (bigCellSelection v) =
      Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
    rw [← selectedFlagChartSchemeChart_toSpec, ← Category.assoc, hg, FlagScheme.ofRingFlag_toSpec]
  obtain ⟨k, hk, he⟩ := selectedFlagAffineChart_exists_parameters R (bigCellSelection v) g hgR
  have hP : selectedFlagChartRingFlag R (bigCellSelection v) k hk = P := by
    apply FlagScheme.ofRingFlag_injective (R := R)
    rw [← hg, ← he, selectedFlagChartPointMap_eq_ofRingFlag]
  rw [inBigCell_iff_bijective]
  intro j
  rw [← hP, selectedFlagChartRingFlag_step]
  exact selectedChartPoint_bijective _ _

/-- The normalized chart matrix of step `j` of a flag in the big cell. -/
def bigCellStepMatrix {v : Equiv.Perm (Fin n)} {P : CoordinateFlag A n}
    (hP : InBigCell v P) (j : Fin (n + 1)) : Matrix (Fin (n - j.val)) (Fin (n - (n - j.val))) A :=
  (grassmannian_existsUnique_selectedMatrix (P.step j) _
    ((inBigCell_iff_bijective v P).mp hP j)).exists.choose

theorem bigCellStepMatrix_spec {v : Equiv.Perm (Fin n)} {P : CoordinateFlag A n}
    (hP : InBigCell v P) (j : Fin (n + 1)) :
    (matrixGrassmannianChartEquiv (bigCellStepMatrix hP j)).val =
      grassmannianTransport (P.step j) (selectedCoordinateEquiv (bigCellSelection v j)) :=
  (grassmannian_existsUnique_selectedMatrix (P.step j) _
    ((inBigCell_iff_bijective v P).mp hP j)).exists.choose_spec

variable (R) in
/-- The chart parameters of a flag in the big cell. -/
def bigCellParameters [Algebra R A] {v : Equiv.Perm (Fin n)} {P : CoordinateFlag A n}
    (hP : InBigCell v P) : MvPolynomial (FlagChartVariable n) R →ₐ[R] A :=
  MvPolynomial.aeval fun x => bigCellStepMatrix hP x.1 x.2.1 x.2.2

theorem bigCellParameters_step [Algebra R A] {v : Equiv.Perm (Fin n)} {P : CoordinateFlag A n}
    (hP : InBigCell v P) (j : Fin (n + 1)) :
    selectedFlagChartStep R (bigCellSelection v) (bigCellParameters R hP) j = P.step j := by
  have hkj : (bigCellParameters R hP).comp (selectedFlagChartVariables R j) =
      (matrixEvaluationEquiv R (n - j.val) (n - (n - j.val)) A).symm
        (bigCellStepMatrix hP j) := by
    apply MvPolynomial.algHom_ext
    intro x
    simp only [AlgHom.comp_apply, selectedFlagChartVariables, MvPolynomial.rename_X,
      bigCellParameters, MvPolynomial.aeval_X]
    change _ = MvPolynomial.aeval (fun ij => bigCellStepMatrix hP j ij.1 ij.2) (MvPolynomial.X x)
    rw [MvPolynomial.aeval_X]
  rw [selectedFlagChartStep, hkj, selectedChartPoint, Equiv.apply_symm_apply,
    bigCellStepMatrix_spec, grassmannianTransport_symm]

theorem bigCellParameters_le_ker [Algebra R A] {v : Equiv.Perm (Fin n)} {P : CoordinateFlag A n}
    (hP : InBigCell v P) :
    selectedFlagIncidenceIdeal R (bigCellSelection v) ≤
      RingHom.ker (bigCellParameters R hP).toRingHom := by
  rw [selectedFlagIncidenceIdeal_le_ker_iff]
  intro i j hij
  simp only [bigCellParameters_step]
  exact P.step_mono hij

variable (R) in
/-- **The big-cell coordinates of a flag in the big cell**: the `R`-algebra map out of the chart
ring classifying it. -/
def bigCellPoint [Algebra R A] {v : Equiv.Perm (Fin n)} {P : CoordinateFlag A n}
    (hP : InBigCell v P) : bigCellRing R v →ₐ[R] A :=
  selectedFlagIncidenceEvaluation R (bigCellSelection v) (bigCellParameters R hP)
    (bigCellParameters_le_ker hP)

theorem spec_bigCellPoint_bigCellChart [Algebra R A] {v : Equiv.Perm (Fin n)}
    {P : CoordinateFlag A n} (hP : InBigCell v P) :
    Spec.map (CommRingCat.ofHom (bigCellPoint R hP).toRingHom) ≫ bigCellChart R v =
      FlagScheme.ofRingFlag R P := by
  change selectedFlagChartPointMap R (bigCellSelection v) _ (bigCellParameters_le_ker hP) = _
  rw [selectedFlagChartPointMap_eq_ofRingFlag]
  congr 1
  exact RingFlag.ext fun j => by rw [selectedFlagChartRingFlag_step, bigCellParameters_step]

/-- A flag in the big cell is classified by a point of the big cell chart. -/
theorem exists_factor_of_inBigCell [Algebra R A] (v : Equiv.Perm (Fin n)) (P : CoordinateFlag A n)
    (hP : InBigCell v P) :
    ∃ g : Spec (CommRingCat.of A) ⟶ bigCellChartScheme R v,
      g ≫ bigCellChart R v = FlagScheme.ofRingFlag R P :=
  ⟨_, spec_bigCellPoint_bigCellChart hP⟩

variable (R) in
theorem inBigCell_bigCellUniversalFlag (v : Equiv.Perm (Fin n)) :
    InBigCell v (bigCellUniversalFlag R v) :=
  inBigCell_of_factors v _ (𝟙 _) ((Category.id_comp _).trans (bigCellChart_eq_ofRingFlag R v))

/-! ### The section of the orbit map over a big cell -/

/-- The steps of a coordinate flag, extended by `Aⁿ` beyond `n`. -/
def flagSteps (P : CoordinateFlag A n) (j : ℕ) : Submodule A (Fin n → A) :=
  if h : j ≤ n then (P.step ⟨j, Nat.lt_succ_of_le h⟩).toSubmodule else ⊤

theorem flagSteps_of_le (P : CoordinateFlag A n) {j : ℕ} (hj : j ≤ n) :
    flagSteps P j = (P.step ⟨j, Nat.lt_succ_of_le hj⟩).toSubmodule := by
  simp [flagSteps, hj]

theorem flagSteps_monotone (P : CoordinateFlag A n) : Monotone (flagSteps P) := by
  intro i j hij
  unfold flagSteps
  by_cases hj : j ≤ n
  · simp only [le_trans hij hj, hj, ↓reduceDIte]
    exact P.step_mono (Fin.mk_le_mk.mpr hij)
  · simp only [hj, ↓reduceDIte]
    exact le_top

theorem tailSpan_eq_bot (v : Equiv.Perm (Fin n)) {j : ℕ} (hj : n ≤ j) :
    tailSpan (A := A) v j = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [mem_tailSpan_iff] at hx
  rw [Submodule.mem_bot]
  funext i
  have := hx (v.symm i) (lt_of_lt_of_le (v.symm i).isLt hj)
  simpa using this

theorem isCompl_flagSteps {v : Equiv.Perm (Fin n)} {P : CoordinateFlag A n} (hP : InBigCell v P)
    (j : ℕ) : IsCompl (flagSteps P j) (tailSpan v j) := by
  unfold flagSteps
  by_cases hj : j ≤ n
  · simp only [hj, ↓reduceDIte]
    exact hP ⟨j, Nat.lt_succ_of_le hj⟩
  · simp only [hj, ↓reduceDIte]
    rw [tailSpan_eq_bot v (le_of_lt (not_le.mp hj))]
    exact isCompl_top_bot

/-- The adapted basis matrix `v · u` of a flag in the big cell of `v`. -/
def bigCellMatrix {v : Equiv.Perm (Fin n)} {P : CoordinateFlag A n} (hP : InBigCell v P) :
    Matrix (Fin n) (Fin n) A :=
  adaptedMatrix v (flagSteps P) (isCompl_flagSteps hP)

theorem isUnit_det_bigCellMatrix {v : Equiv.Perm (Fin n)} {P : CoordinateFlag A n}
    (hP : InBigCell v P) : IsUnit (bigCellMatrix hP).det :=
  isUnit_det_adaptedMatrix _ _ _

/-- The initial columns of the adapted matrix span the steps of the flag. -/
theorem transport_bigCellMatrix [Algebra R A] {v : Equiv.Perm (Fin n)} {P : CoordinateFlag A n}
    (hP : InBigCell v P) :
    (FlagScheme.standardRingFlag n A).transport
      (GLScheme.pointEquiv R n (glPointOfMatrix R _ (isUnit_det_bigCellMatrix hP))) = P := by
  apply RingFlag.ext
  intro j
  rw [FlagScheme.orbitMap_point_step, pointMatrix_glPointOfMatrix]
  have h := span_adaptedVector v (isCompl_flagSteps hP) (flagSteps_monotone P) j.val
  have hj : flagSteps P j.val = (P.step j).toSubmodule := by
    unfold flagSteps
    simp only [Nat.lt_succ_iff.mp j.isLt, ↓reduceDIte]
  rw [← hj, ← h]
  congr 1

variable (R) in
/-- The section of the orbit map over the big cell of `v`: `x ↦ v · u(x)`. -/
def bigCellSection (v : Equiv.Perm (Fin n)) : bigCellChartScheme R v ⟶ GLScheme R n :=
  GLScheme.point R n (glPointOfMatrix R _
    (isUnit_det_bigCellMatrix (inBigCell_bigCellUniversalFlag R v)))

theorem bigCellSection_orbitMap (v : Equiv.Perm (Fin n)) :
    bigCellSection R v ≫ FlagScheme.orbitMap R n = bigCellChart R v := by
  unfold bigCellSection
  exact (FlagScheme.orbitMap_point _).trans
    (by rw [transport_bigCellMatrix, bigCellChart_eq_ofRingFlag])

end FlagVarieties
