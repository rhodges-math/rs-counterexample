import RSCounterexample.FlagVarieties.Plucker.Morphism
import RSCounterexample.FlagVarieties.Plucker.Minors
import RSCounterexample.FlagVarieties.Plucker.AffineChart
import RSCounterexample.FlagVarieties.Flag.Proper

/-!
# The Plücker morphisms and the Plücker embedding of the flag scheme

Over a commutative ring `R`:

* `plucker R n k : Fl_n ⟶ ℙ(∧^{k+1} R^n)`, the **Plücker morphism of height `k`**: on the big cell
  of `v` it is given by the flag minors `Δ_T(ẇ u)` of the adapted matrix (`|T| = k + 1`), which
  generate the unit ideal since `Δ_{v{0..k}}(ẇ u) = ±1`.
* `pluckerSegre R n : Fl_n ⟶ ℙ(⊗_k ∧^{k+1} R^n)`, the **Segre–Plücker morphism**, with coordinates
  `∏_k Δ_{T_k}` indexed by `SegreIndex n` (one row set `T_k` of size `k + 1` for every `k`): the
  composite of `∏_k plucker R n k` with the Segre embedding.

Main results:

* `pluckerSegre_preimage_chart`: the preimage of the standard chart `D₊(X_{T_v})`,
  `T_v = (v{0..k})_k`, is the big cell of `v` (big cell criterion `inBigCell_matrixFlag_iff_minor`).
* `exists_chart_surjective`: on the big cell of `v` the morphism is `Spec` of a **surjective** ring
  map `R[X]_{(X_{T_v})} → C_v`: the coordinates `u_{ij}` of the big cell are ratios of Plücker
  coordinates (`entry_mul_segreSec`), and they generate `C_v` (`adjoin_chartMatrix_eq_top`).
* `pluckerSegre_toSpec`: it is a morphism over `Spec R`; since `Fl_n` is proper and `ℙ` is
  separated, its image is closed.
* **`isClosedImmersion_pluckerSegre`: the Segre–Plücker morphism is a closed immersion.**
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace FlagVarieties.Plucker

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits HomogeneousLocalization
open Foundations Foundations.QuotientCharts Demazure.FlagModule

universe u

variable (R : Type u) [CommRing R] (n : ℕ)

/-! ### The Plücker coordinates as matrix sections -/

/-- The index set of the Segre–Plücker coordinates: a row set `T_k` of size `k + 1` for each `k`. -/
abbrev SegreIndex : Type :=
  (k : Fin n) → FlagMinorRowSet k

variable {n}

/-- The Segre–Plücker coordinate `∏_k Δ_{T_k}(M)`. -/
def segreSec {A : Type u} [CommRing A] (M : Matrix (Fin n) (Fin n) A) (T : SegreIndex n) : A :=
  ∏ k, minor M (T k)

/-- The row sets `T_v = (v{0..k})_k`. -/
abbrev prefixTuple (v : Equiv.Perm (Fin n)) : SegreIndex n :=
  fun k => flagPrefixRows v k

theorem minorSec_map (k : Fin n) : ∀ {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    (M : Matrix (Fin n) (Fin n) A) (T : FlagMinorRowSet k), minor (M.map f) T = f (minor M T) :=
  fun f M T => minor_map f M T

theorem minorSec_mul (k : Fin n) : ∀ {A : Type u} [CommRing A] (M B : Matrix (Fin n) (Fin n) A),
    B.IsUpperTriangular → IsUnit B.det →
      ∃ c : Aˣ, ∀ T : FlagMinorRowSet k, minor (M * B) T = c * minor M T :=
  fun M B hB hdet => ⟨(isUnit_prod_prefix_diag hB hdet k).unit, fun T => by
    rw [minor_mul_upper M B hB, mul_comm, IsUnit.unit_spec]⟩

theorem minorSec_unit (k : Fin n) : ∀ (v : Equiv.Perm (Fin n)) {A : Type u} [CommRing A]
    (u : Matrix (Fin n) (Fin n) A), IsLowerUnitriangular u →
      ∃ T : FlagMinorRowSet k,
        IsUnit (minor ((v.symm.toPEquiv.toMatrix : Matrix (Fin n) (Fin n) A) * u) T) :=
  fun v _ _ _ hu => ⟨flagPrefixRows v k, isUnit_minor_perm_mul v hu k⟩

theorem segreSec_map : ∀ {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    (M : Matrix (Fin n) (Fin n) A) (T : SegreIndex n), segreSec (M.map f) T = f (segreSec M T) :=
  fun f M T => by simp only [segreSec, map_prod, minor_map]

theorem segreSec_mul : ∀ {A : Type u} [CommRing A] (M B : Matrix (Fin n) (Fin n) A),
    B.IsUpperTriangular → IsUnit B.det →
      ∃ c : Aˣ, ∀ T : SegreIndex n, segreSec (M * B) T = c * segreSec M T :=
  fun M B hB hdet => ⟨∏ k, (isUnit_prod_prefix_diag hB hdet k).unit, fun T => by
    simp only [segreSec, minor_mul_upper M B hB, Finset.prod_mul_distrib, Units.coe_prod,
      IsUnit.unit_spec]
    rw [mul_comm]⟩

theorem isUnit_segreSec_prefixTuple (v : Equiv.Perm (Fin n)) {A : Type u} [CommRing A]
    {u : Matrix (Fin n) (Fin n) A} (hu : IsLowerUnitriangular u) :
    IsUnit (segreSec ((v.symm.toPEquiv.toMatrix : Matrix (Fin n) (Fin n) A) * u)
      (prefixTuple v)) :=
  IsUnit.prod_univ_iff.mpr fun k => isUnit_minor_perm_mul v hu k

theorem segreSec_unit : ∀ (v : Equiv.Perm (Fin n)) {A : Type u} [CommRing A]
    (u : Matrix (Fin n) (Fin n) A), IsLowerUnitriangular u →
      ∃ T : SegreIndex n,
        IsUnit (segreSec ((v.symm.toPEquiv.toMatrix : Matrix (Fin n) (Fin n) A) * u) T) :=
  fun v _ _ _ hu => ⟨prefixTuple v, isUnit_segreSec_prefixTuple v hu⟩

/-! ### The morphisms -/

variable (n) in
/-- **The Plücker morphism of height `k`**, `Fl_n ⟶ ℙ(∧^{k+1} R^n)`: the coordinates are the flag
minors `Δ_T`, `|T| = k + 1`. -/
def plucker (k : Fin n) : FlagScheme R n ⟶ projSpace R (FlagMinorRowSet k) :=
  glued R (fun M T => minor M T) (minorSec_map k) (minorSec_mul k) (minorSec_unit k)

/-- On the big cell of `v`, the Plücker morphism is given by the minors of `ẇ u`. -/
theorem specChart_plucker (k : Fin n) (v : Equiv.Perm (Fin n)) :
    specChart R n v ≫ plucker R n k = chartMorphism R (fun M T => minor M T) (minorSec_unit k) v :=
  specChart_glued R _ (minorSec_map k) (minorSec_mul k) (minorSec_unit k) v

variable (n) in
/-- **The Segre–Plücker morphism** `Fl_n ⟶ ℙ(⊗_k ∧^{k+1} R^n)`, with coordinates
`∏_k Δ_{T_k}`. -/
def pluckerSegre : FlagScheme R n ⟶ projSpace R (SegreIndex n) :=
  glued R segreSec segreSec_map segreSec_mul segreSec_unit

theorem specChart_pluckerSegre (v : Equiv.Perm (Fin n)) :
    specChart R n v ≫ pluckerSegre R n = chartMorphism R segreSec segreSec_unit v :=
  specChart_glued R _ segreSec_map segreSec_mul segreSec_unit v

/-! ### Over `Spec R` -/

variable (n) in
/-- The Segre–Plücker morphism lies over `Spec R`. -/
theorem pluckerSegre_toSpec :
    pluckerSegre R n ≫ projToSpec R (SegreIndex n) = FlagScheme.toSpec R n := by
  refine (bigCellCover R n).hom_ext _ _ fun v => ?_
  change specChart R n v ≫ _ = specChart R n v ≫ _
  rw [← Category.assoc, specChart_pluckerSegre, chartMorphism, fromSections_toSpec,
    specChart_toSpec, ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp]
  congr 1
  ext r
  simp [chartStructure]

instance : UniversallyClosed (pluckerSegre R n) := by
  have : UniversallyClosed (pluckerSegre R n ≫ projToSpec R (SegreIndex n)) := by
    rw [pluckerSegre_toSpec]
    infer_instance
  exact UniversallyClosed.of_comp_of_isSeparated (pluckerSegre R n) (projToSpec R (SegreIndex n))

theorem isClosed_range_pluckerSegre : IsClosed (Set.range (pluckerSegre R n)) :=
  (pluckerSegre R n).isClosedMap.isClosed_range

/-! ### The chart coordinates are ratios of Plücker coordinates -/

theorem segreSec_update {A : Type u} [CommRing A] (M : Matrix (Fin n) (Fin n) A)
    (T : SegreIndex n) (j : Fin n) (T' : FlagMinorRowSet j) :
    segreSec M (Function.update T j T') * minor M (T j) = minor M T' * segreSec M T := by
  simp only [segreSec]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j),
    ← Finset.mul_prod_erase Finset.univ (fun k => minor M (T k)) (Finset.mem_univ j)]
  have h : ∀ k ∈ Finset.univ.erase j, minor M (Function.update T j T' k) = minor M (T k) :=
    fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  rw [Finset.prod_congr rfl h, Function.update_self]
  ring

/-- **The coordinates of the big cell are ratios of Plücker coordinates**: for `j < i`,
`u_{ij} · p_{T_v}(ẇ u) = ±p_T(ẇ u)` for a suitable `T`. -/
theorem entry_mul_segreSec (v : Equiv.Perm (Fin n)) {A : Type u} [CommRing A]
    {u : Matrix (Fin n) (Fin n) A} (hu : IsLowerUnitriangular u) {j i : Fin n} (hji : j < i) :
    ∃ (ε : ℤ) (T : SegreIndex n),
      u i j * segreSec ((v.symm.toPEquiv.toMatrix : Matrix (Fin n) (Fin n) A) * u)
          (prefixTuple v) =
        (ε : A) * segreSec ((v.symm.toPEquiv.toMatrix : Matrix (Fin n) (Fin n) A) * u) T := by
  obtain ⟨e, he⟩ := entry_eq_minor v hu hji
  set L := (v.symm.toPEquiv.toMatrix : Matrix (Fin n) (Fin n) A) * u
  set T' := rowSet (v ∘ hookRows j i) (v.injective.comp (hookRows_injective hji))
  have h1 := segreSec_update L (prefixTuple v) j T'
  have h2 := minor_flagPrefixRows v j L
  rw [det_prefix_perm_mul v hu j] at h2
  have hs := sign_cast_mul_self (A := A) (flagPrefixPermutation v j)
  refine ⟨(e : ℤ) * (Equiv.Perm.sign (flagPrefixPermutation v j) : ℤ),
    Function.update (prefixTuple v) j T', ?_⟩
  push_cast
  linear_combination (segreSec L (prefixTuple v)) * he - (e : A) * h1 -
    (e : A) * segreSec L (Function.update (prefixTuple v) j T') * minor L (prefixTuple v j) * hs +
    (e : A) * segreSec L (Function.update (prefixTuple v) j T') *
      ((Equiv.Perm.sign (flagPrefixPermutation v j) : ℤ) : A) * h2

/-! ### The chart rings are generated by the adapted matrix -/

/-- **The coordinate ring of the big cell of `v` is generated by the entries of the universal
adapted matrix `ẇ u`.** -/
theorem adjoin_chartMatrix_eq_top (v : Equiv.Perm (Fin n)) :
    Algebra.adjoin R (Set.range fun p : Fin n × Fin n => chartMatrix R n v p.1 p.2) = ⊤ := by
  set S := Algebra.adjoin R (Set.range fun p : Fin n × Fin n => chartMatrix R n v p.1 p.2)
  obtain ⟨u, hu, he⟩ := bigCellMatrix_eq_perm_mul (inBigCell_bigCellUniversalFlag R v)
  have hL : chartMatrix R n v =
      (v.symm.toPEquiv.toMatrix : Matrix (Fin n) (Fin n) (bigCellRing R v)) * u := he
  have hmem : ∀ a c, u a c ∈ S := fun a c => by
    have : u a c = chartMatrix R n v (v a) c := by
      rw [hL, perm_mul_eq_submatrix]
      simp
    rw [this]
    exact Algebra.subset_adjoin ⟨(v a, c), rfl⟩
  let u' : Matrix (Fin n) (Fin n) S := Matrix.of fun a c => ⟨u a c, hmem a c⟩
  have hu' : IsLowerUnitriangular u' :=
    ⟨fun a c h => Subtype.ext (hu.1 h), fun a => Subtype.ext (hu.2 a)⟩
  have hP := inBigCell_matrixFlag_perm_mul v hu'
  have h1 := map_bigCellPoint (R := R) v hP
  have h2 := bigCellMatrix_eq_of_perm_mul hP hu' rfl
  have hid : S.val.comp (bigCellPoint R hP) = AlgHom.id R (bigCellRing R v) := by
    apply bigCellRing_algHom_ext v
    rw [← map_map_algHom, h1, h2]
    ext a c
    change S.val (((v.symm.toPEquiv.toMatrix : Matrix (Fin n) (Fin n) S) * u') a c) =
      chartMatrix R n v a c
    rw [hL, perm_mul_eq_submatrix, perm_mul_eq_submatrix]
    rfl
  rw [eq_top_iff]
  intro x _
  have : S.val (bigCellPoint R hP x) = x := by
    rw [← AlgHom.comp_apply, hid, AlgHom.id_apply]
  rw [← this]
  exact (bigCellPoint R hP x).2

/-! ### The Segre–Plücker morphism on a big cell -/

theorem isUnit_chartSections_prefixTuple (v : Equiv.Perm (Fin n)) :
    IsUnit (chartSections R segreSec v (prefixTuple v)) := by
  obtain ⟨u, hu, he⟩ := bigCellMatrix_eq_perm_mul (inBigCell_bigCellUniversalFlag R v)
  rw [chartSections, chartMatrix, bigCellUniversalMatrix, he]
  exact (isUnit_segreSec_prefixTuple v hu).map _

theorem ΓSpecIso_hom_inv {C : CommRingCat.{u}} (x : C) :
    (Scheme.ΓSpecIso C).hom ((Scheme.ΓSpecIso C).inv x) = x :=
  (Scheme.ΓSpecIso C).inv_hom_id_apply x

/-- **On the big cell of `v`, the Segre–Plücker morphism is a closed immersion into the
standard chart `D₊(X_{T_v})`**: it is `Spec` of a surjective ring map. -/
theorem exists_chart_surjective (v : Equiv.Perm (Fin n)) :
    ∃ ψ : CommRingCat.of (Away (grading R (SegreIndex n)) (MvPolynomial.X (prefixTuple v))) ⟶
        ChartRing R n v,
      specChart R n v ≫ pluckerSegre R n = Spec.map ψ ≫
        Proj.awayι (grading R (SegreIndex n)) (MvPolynomial.X (prefixTuple v))
          (X_mem_grading_one _) Nat.one_pos ∧
      Function.Surjective ψ := by
  obtain ⟨ψ, hfac, hval⟩ := exists_fromSections_eq_awayι (chartStructure R v)
    (chartSections R segreSec v) (span_chartSections R segreSec segreSec_unit v)
    (prefixTuple v) (isUnit_chartSections_prefixTuple R v)
  refine ⟨ψ, by rw [specChart_pluckerSegre, chartMorphism, hfac], ?_⟩
  -- the values of `ψ` on the generators
  have hconst : ∀ r : R, algebraMap R (bigCellRing R v) r ∈ ψ.hom.range := fun r => by
    have h := hval 0 (MvPolynomial.C r) (MvPolynomial.isHomogeneous_C _ r)
    rw [pow_zero, mul_one, evalSections, MvPolynomial.eval₂Hom_C, chartStructure,
      RingHom.comp_apply] at h
    exact ⟨_, h.trans (ΓSpecIso_hom_inv _)⟩
  have hratio : ∀ T : SegreIndex n, ψ (Away.mk (grading R (SegreIndex n)) (X_mem_grading_one _) 1
      (MvPolynomial.X T) (by simpa using X_mem_grading_one T)) *
      segreSec (chartMatrix R n v) (prefixTuple v) = segreSec (chartMatrix R n v) T := by
    intro T
    have h := hval 1 (MvPolynomial.X T) (by simpa using X_mem_grading_one T)
    rw [pow_one, evalSections_X, chartSections, chartSections, ΓSpecIso_hom_inv,
      ΓSpecIso_hom_inv] at h
    exact h
  obtain ⟨u, hu, he⟩ := bigCellMatrix_eq_perm_mul (inBigCell_bigCellUniversalFlag R v)
  have hL : chartMatrix R n v =
      (v.symm.toPEquiv.toMatrix : Matrix (Fin n) (Fin n) (bigCellRing R v)) * u := he
  have hunit : IsUnit (segreSec (chartMatrix R n v) (prefixTuple v)) := by
    rw [hL]
    exact isUnit_segreSec_prefixTuple v hu
  have hentry : ∀ a c, u a c ∈ ψ.hom.range := by
    intro a c
    rcases lt_trichotomy a c with hac | rfl | hca
    · rw [hu.1 hac]
      exact zero_mem _
    · rw [hu.2 a]
      exact one_mem _
    · obtain ⟨ε, T, hεT⟩ := entry_mul_segreSec v hu hca
      rw [← hL, ← hratio T, ← mul_assoc] at hεT
      rw [hunit.mul_right_cancel hεT]
      exact mul_mem (intCast_mem _ ε) ⟨_, rfl⟩
  intro x
  have hx : x ∈ Algebra.adjoin R (Set.range fun p : Fin n × Fin n => chartMatrix R n v p.1 p.2) :=
    (adjoin_chartMatrix_eq_top R v).symm ▸ Algebra.mem_top
  have hrange : x ∈ ψ.hom.range := by
    induction hx using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨⟨r, c⟩, rfl⟩ := hy
      simp only
      rw [hL, perm_mul_eq_submatrix]
      exact hentry _ _
    | algebraMap r => exact hconst r
    | add y z _ _ hy hz => exact add_mem hy hz
    | mul y z _ _ hy hz => exact mul_mem hy hz
  obtain ⟨y, hy⟩ := hrange
  exact ⟨y, hy⟩

end FlagVarieties.Plucker
