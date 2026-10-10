import RSCounterexample.FlagVarieties.Foundations.Schemes.ProjectiveLineNaturality
import RSCounterexample.FlagVarieties.Foundations.Schemes.ProjectiveLineScaling
import Mathlib.RingTheory.MvPolynomial.Ideal

/-!
# The standard charts of the projective line

For the projective line `ℙ¹_R = Proj R[X₀, X₁]` (`FlagVarieties.Foundations.ProjectiveLine.scheme`):

* `FlagVarieties.ProjectiveLineCharts.chartι R k : Spec (R[X₀,X₁]_{(X_k)}) ⟶ ℙ¹`, the open immersion
  of the chart `X_k ≠ 0`; the two charts cover `ℙ¹` (`iSup_chart_eq_top`);
* `chartFrac R k j = X_j / X_k`, so the chart `k` carries the pair `(X₀ / X_k, X₁ / X_k)`;
* **`chartι_eq_fromPair`**: the chart inclusion is the morphism `fromPair` defined by the pair
  `(X₀ / X_k, X₁ / X_k)` of global functions on the chart;
* `evaluation_chartFrac`: evaluating a homogeneous `p` of degree `d` at `(X₀ / X_k, X₁ / X_k)` gives
  `p / X_k^d`.
-/

noncomputable section

namespace FlagVarieties.ProjectiveLineCharts

open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open Foundations.ProjectiveLine

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R]

theorem X_mem (k : Fin 2) : (MvPolynomial.X k : MvPolynomial (Fin 2) R) ∈ grading R 1 :=
  MvPolynomial.isHomogeneous_X R k

theorem X_mem' (k : Fin 2) : (MvPolynomial.X k : MvPolynomial (Fin 2) R) ∈ grading R (1 • 1) := by
  simpa using X_mem R k

/-- The ring `R[X₀, X₁]_{(X_k)}` of the chart `X_k ≠ 0`. -/
abbrev ChartRing (k : Fin 2) : Type u :=
  Away (grading R) (MvPolynomial.X k : MvPolynomial (Fin 2) R)

/-- The open immersion of the chart `X_k ≠ 0`. -/
def chartι (k : Fin 2) : Spec (CommRingCat.of (ChartRing R k)) ⟶ scheme R :=
  Proj.awayι (grading R) (MvPolynomial.X k) (X_mem R k) Nat.one_pos

instance (k : Fin 2) : IsOpenImmersion (chartι R k) := by
  unfold chartι
  infer_instance

theorem opensRange_chartι (k : Fin 2) : (chartι R k).opensRange = chart R k :=
  Proj.opensRange_awayι _ _ _ _

/-- `X_j / X_k` on the chart `X_k ≠ 0`. -/
def chartFrac (k j : Fin 2) : ChartRing R k :=
  Away.mk (grading R) (X_mem R k) 1 (MvPolynomial.X j) (X_mem' R j)

theorem chartFrac_self (k : Fin 2) : chartFrac R k k = 1 := by
  apply val_injective
  rw [chartFrac, Away.val_mk, val_one, Localization.mk_eq_mk', IsLocalization.mk'_eq_iff_eq_mul]
  simp

/-- The structure map `R → R[X₀, X₁]_{(X_k)}`. -/
def chartStructure (k : Fin 2) : R →+* ChartRing R k :=
  (fromZeroRingHom (grading R) _).comp (constants R)

theorem val_chartStructure (k : Fin 2) (r : R) :
    (chartStructure R k r).val =
      algebraMap (MvPolynomial (Fin 2) R) (Localization.Away (MvPolynomial.X k :
        MvPolynomial (Fin 2) R)) (MvPolynomial.C r) := by
  change Localization.mk (MvPolynomial.C r) 1 = _
  exact Localization.mk_one_eq_algebraMap _

/-- **Evaluating at `(X₀ / X_k, X₁ / X_k)`** a homogeneous polynomial `p` of degree `d` gives
`p / X_k^d`. -/
theorem evaluation_chartFrac (k : Fin 2) {d : ℕ} (p : MvPolynomial (Fin 2) R)
    (hp : p ∈ grading R (d • 1)) :
    evaluation (chartStructure R k) (chartFrac R k 0) (chartFrac R k 1) p =
      Away.mk (grading R) (X_mem R k) d p hp := by
  apply val_injective
  rw [Away.val_mk]
  set L := Localization.Away (MvPolynomial.X k : MvPolynomial (Fin 2) R)
  let v : ChartRing R k →+* L := algebraMap (ChartRing R k) L
  have hv : v (evaluation (chartStructure R k) (chartFrac R k 0) (chartFrac R k 1) p) =
      evaluation ((algebraMap (MvPolynomial (Fin 2) R) L).comp MvPolynomial.C) (chartFrac R k 0).val
        (chartFrac R k 1).val p := by
    change v (MvPolynomial.eval₂ _ _ p) = MvPolynomial.eval₂ _ _ p
    rw [MvPolynomial.eval₂_comp_left]
    congr 1
    funext j
    fin_cases j <;> rfl
  change v _ = _
  rw [hv]
  set u : L := algebraMap (MvPolynomial (Fin 2) R) L (MvPolynomial.X k)
  have hu : IsUnit u := IsLocalization.Away.algebraMap_isUnit _
  have hfrac : ∀ j, u * (chartFrac R k j).val =
      algebraMap (MvPolynomial (Fin 2) R) L (MvPolynomial.X j) := by
    intro j
    have key : ∀ y : Submonoid.powers (MvPolynomial.X k : MvPolynomial (Fin 2) R),
        (y : MvPolynomial (Fin 2) R) = MvPolynomial.X k →
          algebraMap (MvPolynomial (Fin 2) R) L (MvPolynomial.X k) *
              IsLocalization.mk' L (MvPolynomial.X j) y =
            algebraMap (MvPolynomial (Fin 2) R) L (MvPolynomial.X j) := by
      rintro y hy
      have h := IsLocalization.mk'_spec' L (MvPolynomial.X j) y
      rw [hy] at h
      exact h
    rw [chartFrac, Away.val_mk, Localization.mk_eq_mk']
    exact key _ (pow_one _)
  have hscale := evaluation_scale_of_homogeneous
    ((algebraMap (MvPolynomial (Fin 2) R) L).comp MvPolynomial.C)
    (chartFrac R k 0).val (chartFrac R k 1).val u (by simpa using hp)
  have hfull : evaluation ((algebraMap (MvPolynomial (Fin 2) R) L).comp MvPolynomial.C)
      (u * (chartFrac R k 0).val)
      (u * (chartFrac R k 1).val) p = algebraMap _ L p := by
    rw [hfrac, hfrac]
    change MvPolynomial.eval₂ _ _ p = _
    have : (![algebraMap (MvPolynomial (Fin 2) R) L (MvPolynomial.X 0),
        algebraMap (MvPolynomial (Fin 2) R) L (MvPolynomial.X 1)] : Fin 2 → L) =
        (algebraMap (MvPolynomial (Fin 2) R) L) ∘ MvPolynomial.X := by
      funext j
      fin_cases j <;> rfl
    rw [this, ← MvPolynomial.eval₂_comp_left, MvPolynomial.eval₂_eta]
  rw [hfull] at hscale
  rw [Localization.mk_eq_mk', IsLocalization.eq_mk'_iff_mul_eq]
  rw [hscale, mul_comm]
  simp [u, map_pow]

/-! ### The charts cover `ℙ¹` -/

theorem irrelevant_le_span_X :
    (HomogeneousIdeal.irrelevant (grading R)).toIdeal ≤
      Ideal.span (Set.range (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) R)) := by
  intro p hp
  rw [← Set.image_univ, MvPolynomial.mem_ideal_span_X_image]
  intro m hm
  by_contra h
  push Not at h
  have hm0 : m = 0 := Finsupp.ext fun i => h i (Set.mem_univ i)
  have h0 : GradedAlgebra.proj (grading R) 0 p = 0 :=
    (HomogeneousIdeal.mem_irrelevant_iff _ _).mp hp
  have hc : p.coeff 0 = 0 := by
    have h1 : (GradedAlgebra.proj (grading R) 0 p) = MvPolynomial.homogeneousComponent 0 p :=
      MvPolynomial.decomposition.decompose'_apply p 0
    rw [h1, MvPolynomial.homogeneousComponent_zero, MvPolynomial.C_eq_zero] at h0
    exact h0
  rw [hm0, MvPolynomial.mem_support_iff] at hm
  exact hm hc

theorem iSup_chart_eq_top : ⨆ k : Fin 2, chart R k = ⊤ :=
  Proj.iSup_basicOpen_eq_top (grading R) (fun k : Fin 2 => MvPolynomial.X k)
    (irrelevant_le_span_X R)

/-! ### The chart inclusions as `fromPair` -/

/-- The global functions `(X₀ / X_k, X₁ / X_k)` and the structure map on the chart `k`. -/
abbrev chartΓ (k : Fin 2) : ChartRing R k →+* Γ(Spec (CommRingCat.of (ChartRing R k)), ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (ChartRing R k))).inv.hom

theorem isCoprime_chartFrac (k : Fin 2) :
    IsCoprime (chartΓ R k (chartFrac R k 0)) (chartΓ R k (chartFrac R k 1)) := by
  fin_cases k
  · simp only [Fin.zero_eta, Fin.isValue]
    rw [chartFrac_self, map_one]
    exact isCoprime_one_left
  · simp only [Fin.mk_one, Fin.isValue]
    rw [chartFrac_self, map_one]
    exact isCoprime_one_right

theorem evaluation_chartΓ (k : Fin 2) {d : ℕ} (p : MvPolynomial (Fin 2) R)
    (hp : p ∈ grading R (d • 1)) :
    evaluation ((chartΓ R k).comp (chartStructure R k)) (chartΓ R k (chartFrac R k 0))
        (chartΓ R k (chartFrac R k 1)) p =
      chartΓ R k (Away.mk (grading R) (X_mem R k) d p hp) := by
  rw [← evaluation_chartFrac R k p hp]
  change MvPolynomial.eval₂ _ _ p = chartΓ R k (MvPolynomial.eval₂ _ _ p)
  rw [MvPolynomial.eval₂_comp_left]
  congr 1
  funext j
  fin_cases j <;> rfl

theorem evaluation_chartΓ_X (k : Fin 2) :
    evaluation ((chartΓ R k).comp (chartStructure R k)) (chartΓ R k (chartFrac R k 0))
        (chartΓ R k (chartFrac R k 1)) (MvPolynomial.X k) = 1 := by
  rw [evaluation_chartΓ R k (MvPolynomial.X k) (X_mem' R k)]
  change chartΓ R k (chartFrac R k k) = 1
  rw [chartFrac_self, map_one]

/-- The chart map of `Proj` evaluated at a ring map `e` that dehomogenizes as `ψ`. -/
theorem evaluatedAwayMap_eq (k : Fin 2) {S : Type u} [CommRing S]
    (e : MvPolynomial (Fin 2) R →+* S) (ψ : ChartRing R k →+* S)
    (he : ∀ (d : ℕ) (p : MvPolynomial (Fin 2) R) (hp : p ∈ grading R (d • 1)),
      e p = ψ (Away.mk (grading R) (X_mem R k) d p hp))
    (heX : e (MvPolynomial.X k) = 1) :
    Foundations.ProjectiveChartCompatibility.evaluatedAwayMap (grading R) e (MvPolynomial.X k) =
      (algebraMap S (Localization.Away (e (MvPolynomial.X k)))).comp ψ := by
  refine RingHom.ext fun a => ?_
  obtain ⟨d, p, hp, rfl⟩ := Away.mk_surjective (grading R) (X_mem R k) a
  rw [RingHom.comp_apply, ← he d p hp]
  unfold Foundations.ProjectiveChartCompatibility.evaluatedAwayMap
  rw [RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply, Away.val_mk,
    Localization.mk_eq_mk', Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_mk',
    IsLocalization.mk'_eq_iff_eq_mul]
  simp [heX]

/-- On an affine scheme, the inclusion of a basic open is the canonical map to the localization. -/
theorem basicOpen_ι_eq_globalBasicOpenMap (A : CommRingCat.{u}) (x : Γ(Spec A, ⊤)) :
    ((Spec A).basicOpen x).ι =
      Foundations.ProjectiveChartCompatibility.globalBasicOpenMap (Spec A) x ≫
        Spec.map (CommRingCat.ofHom ((algebraMap Γ(Spec A, ⊤) (Localization.Away x)).comp
          (Scheme.ΓSpecIso A).inv.hom)) := by
  simp only [CommRingCat.ofHom_comp, Spec.map_comp,
    Foundations.ProjectiveChartCompatibility.globalBasicOpenMap, Category.assoc,
    basicOpenIsoSpecAway_hom_SpecMap_assoc, CommRingCat.ofHom_hom]
  erw [Scheme.Hom.resLE_comp_ι_assoc]
  rw [toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

/-- **The chart inclusion is `fromPair` of `(X₀ / X_k, X₁ / X_k)`.** -/
theorem chartι_eq_fromPair (k : Fin 2) :
    chartι R k = fromPair ((chartΓ R k).comp (chartStructure R k))
      (chartΓ R k (chartFrac R k 0)) (chartΓ R k (chartFrac R k 1)) (isCoprime_chartFrac R k) := by
  have heX := evaluation_chartΓ_X R k
  have hU : (Spec (CommRingCat.of (ChartRing R k))).basicOpen
      (evaluation ((chartΓ R k).comp (chartStructure R k)) (chartΓ R k (chartFrac R k 0))
        (chartΓ R k (chartFrac R k 1)) (MvPolynomial.X k)) = ⊤ := by
    rw [heX]
    exact Scheme.basicOpen_one _
  have hring := evaluatedAwayMap_eq R k
    (evaluation ((chartΓ R k).comp (chartStructure R k)) (chartΓ R k (chartFrac R k 0))
      (chartΓ R k (chartFrac R k 1))) (chartΓ R k) (fun d p hp => evaluation_chartΓ R k p hp) heX
  refine Scheme.hom_ext_of_forall _ _ fun y => ⟨(Spec (CommRingCat.of (ChartRing R k))).basicOpen
    (evaluation ((chartΓ R k).comp (chartStructure R k)) (chartΓ R k (chartFrac R k 0))
      (chartΓ R k (chartFrac R k 1)) (MvPolynomial.X k)), by rw [hU]; trivial, ?_⟩
  rw [fromPair, ← Scheme.Hom.resLE_comp_ι _
    (Proj.fromOfGlobalSections_preimage_basicOpen (grading R) _ _ Nat.one_pos (X_mem R k)).ge,
    Proj.fromOfGlobalSections_resLE (grading R) _ _ Nat.one_pos (X_mem R k),
    Foundations.ProjectiveChartCompatibility.toBasicOpen_ι_eq (grading R) _ (X_mem R k) Nat.one_pos,
    hring, ← Category.assoc, ← basicOpen_ι_eq_globalBasicOpenMap]
  rfl

end FlagVarieties.ProjectiveLineCharts
