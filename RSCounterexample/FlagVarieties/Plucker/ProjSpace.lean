import RSCounterexample.FlagVarieties.Foundations.Schemes.ProjectiveLineCompatibility
import RSCounterexample.FlagVarieties.Foundations.Schemes.ProjectiveLineNaturality

/-!
# Projective spaces and morphisms from unimodular families of sections

For a commutative ring `R` and an index type `σ`, `projSpace R σ = Proj R[X_i : i ∈ σ]` with the
total-degree grading: the projective space `ℙ(R^σ)` of rank-one quotients of `R^σ`. This file
generalizes the projective-line machinery of the foundations
(`Foundations/Schemes/ProjectiveLine*`) from two to arbitrarily many coordinates.

* `fromSections φ s h : X ⟶ ℙ(R^σ)`: the morphism attached to a family `s : σ → Γ(X, 𝒪)` of global
  sections generating the unit ideal (a trivialized rank-one quotient `𝒪^σ → 𝒪` together with the
  structure map `φ : R → Γ(X, 𝒪)`); it is Mathlib's `Proj.fromOfGlobalSections`.
* `fromSections_preimage_basicOpen`: the preimage of the standard chart `D₊(X_i)` is `D(s_i)`.
* `fromSections_naturality`: compatibility with pullback.
* `fromSections_unit_mul`: invariance under rescaling all sections by a common unit; so the
  morphism only depends on the rank-one quotient, and morphisms defined on the members of an open
  cover by locally unimodular families glue as soon as the families agree up to units on overlaps.
-/

noncomputable section

namespace FlagVarieties.Plucker

open AlgebraicGeometry CategoryTheory

universe u

variable (R : Type u) [CommRing R] (σ : Type)

/-- The total-degree grading of `R[X_i : i ∈ σ]`. -/
abbrev grading : ℕ → Submodule R (MvPolynomial σ R) :=
  MvPolynomial.homogeneousSubmodule σ R

instance : GradedAlgebra (grading R σ) :=
  MvPolynomial.gradedAlgebra

/-- **The projective space `ℙ(R^σ) = Proj R[X_i : i ∈ σ]`**. -/
abbrev projSpace : Scheme.{u} :=
  Proj (grading R σ)

/-- The standard chart `D₊(X_i)`. -/
def chart (i : σ) : (projSpace R σ).Opens :=
  Proj.basicOpen (grading R σ) (MvPolynomial.X i)

variable {R σ}

theorem X_mem_grading_one (i : σ) : (MvPolynomial.X i : MvPolynomial σ R) ∈ grading R σ 1 :=
  MvPolynomial.isHomogeneous_X R i

theorem X_mem_irrelevant (i : σ) :
    (MvPolynomial.X i : MvPolynomial σ R) ∈
      (HomogeneousIdeal.irrelevant (grading R σ)).toIdeal :=
  HomogeneousIdeal.mem_irrelevant_of_mem (grading R σ) (by decide : 0 < (1 : ℕ))
    (X_mem_grading_one i)

/-- Evaluation of the coordinates at a family of elements. -/
def evalSections {S : Type*} [CommRing S] (φ : R →+* S) (s : σ → S) :
    MvPolynomial σ R →+* S :=
  MvPolynomial.eval₂Hom φ s

@[simp]
theorem evalSections_X {S : Type*} [CommRing S] (φ : R →+* S) (s : σ → S) (i : σ) :
    evalSections φ s (MvPolynomial.X i) = s i :=
  MvPolynomial.eval₂Hom_X' _ _ _

/-- A unimodular family puts `1` in the image of the irrelevant ideal. -/
theorem map_irrelevant_eq_top {S : Type*} [CommRing S] (φ : R →+* S) (s : σ → S)
    (h : Ideal.span (Set.range s) = ⊤) :
    (HomogeneousIdeal.irrelevant (grading R σ)).toIdeal.map (evalSections φ s) = ⊤ := by
  rw [eq_top_iff, ← h, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  rw [← evalSections_X φ s i]
  exact Ideal.mem_map_of_mem _ (X_mem_irrelevant i)

/-- Homogeneous polynomials scale with their degree. -/
theorem evalSections_smul_of_mem {S : Type*} [CommRing S] (φ : R →+* S) (s : σ → S) (c : S)
    {d : ℕ} {p : MvPolynomial σ R} (hp : p ∈ grading R σ d) :
    evalSections φ (fun i => c * s i) p = c ^ d * evalSections φ s p := by
  have hp' : p.IsHomogeneous d := hp
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  simp only [evalSections, map_sum, Finset.mul_sum, MvPolynomial.coe_eval₂Hom,
    MvPolynomial.eval₂_monomial]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg : ∑ i ∈ m.support, m i = d := by
    have := hp' (MvPolynomial.mem_support_iff.mp hm)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib]
  rw [Finset.prod_pow_eq_pow_sum, hdeg]
  ring

variable {X : Scheme.{u}}

/-- **The morphism to projective space attached to a unimodular family of global sections**. -/
def fromSections (φ : R →+* Γ(X, ⊤)) (s : σ → Γ(X, ⊤)) (h : Ideal.span (Set.range s) = ⊤) :
    X ⟶ projSpace R σ :=
  Proj.fromOfGlobalSections (grading R σ) (evalSections φ s) (map_irrelevant_eq_top φ s h)

/-- The preimage of the standard chart `D₊(X_i)` is `D(s_i)`. -/
theorem fromSections_preimage_chart (φ : R →+* Γ(X, ⊤)) (s : σ → Γ(X, ⊤))
    (h : Ideal.span (Set.range s) = ⊤) (i : σ) :
    fromSections φ s h ⁻¹ᵁ chart R σ i = X.basicOpen (s i) := by
  rw [fromSections, chart, Proj.fromOfGlobalSections_preimage_basicOpen _ _ _
    (by decide : 0 < (1 : ℕ)) (X_mem_grading_one i), evalSections_X]

theorem span_range_mul_unit {S : Type*} [CommRing S] (s : σ → S)
    (h : Ideal.span (Set.range s) = ⊤) (c : Sˣ) :
    Ideal.span (Set.range fun i => (c : S) * s i) = ⊤ := by
  rw [eq_top_iff, ← h, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  have : s i = ((c⁻¹ : Sˣ) : S) * ((c : S) * s i) := by
    rw [← mul_assoc, Units.inv_mul, one_mul]
  rw [this]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

/-- **Rescaling by a common unit does not change the morphism.** -/
theorem fromSections_unit_mul (φ : R →+* Γ(X, ⊤)) (s : σ → Γ(X, ⊤))
    (h : Ideal.span (Set.range s) = ⊤) (c : Γ(X, ⊤)ˣ) :
    fromSections φ (fun i => (c : Γ(X, ⊤)) * s i) (span_range_mul_unit s h c) =
      fromSections φ s h :=
  (Foundations.ProjectiveChartCompatibility.fromOfGlobalSections_eq_of_homogeneous_unit_scale
    (grading R σ) (evalSections φ s) (map_irrelevant_eq_top φ s h)
    (evalSections φ fun i => (c : Γ(X, ⊤)) * s i)
    (map_irrelevant_eq_top φ _ (span_range_mul_unit s h c)) c
    fun _ _ hp => evalSections_smul_of_mem φ s _ hp).symm

/-- `fromSections` only depends on the family up to a common unit. -/
theorem fromSections_eq_of_unit (φ : R →+* Γ(X, ⊤)) (s t : σ → Γ(X, ⊤))
    (hs : Ideal.span (Set.range s) = ⊤) (ht : Ideal.span (Set.range t) = ⊤) (c : Γ(X, ⊤)ˣ)
    (hst : ∀ i, t i = (c : Γ(X, ⊤)) * s i) :
    fromSections φ t ht = fromSections φ s hs := by
  have : t = fun i => (c : Γ(X, ⊤)) * s i := funext hst
  subst this
  exact fromSections_unit_mul φ s hs c

theorem evalSections_comp {S T : Type*} [CommRing S] [CommRing T] (φ : R →+* S) (s : σ → S)
    (g : S →+* T) : g.comp (evalSections φ s) = evalSections (g.comp φ) (fun i => g (s i)) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [evalSections]
  · intro i
    simp [evalSections]

theorem span_range_map {S T : Type*} [CommRing S] [CommRing T] (s : σ → S)
    (h : Ideal.span (Set.range s) = ⊤) (g : S →+* T) :
    Ideal.span (Set.range fun i => g (s i)) = ⊤ := by
  have := congrArg (Ideal.map g) h
  rwa [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at this

/-- **Naturality**: pulling back the sections pulls back the morphism. -/
theorem fromSections_naturality {Y : Scheme.{u}} (φ : R →+* Γ(X, ⊤)) (s : σ → Γ(X, ⊤))
    (h : Ideal.span (Set.range s) = ⊤) (f : Y ⟶ X) :
    f ≫ fromSections φ s h =
      fromSections (f.appTop.hom.comp φ) (fun i => f.appTop (s i))
        (span_range_map s h f.appTop.hom) := by
  rw [fromSections, Foundations.ProjectiveChartCompatibility.fromOfGlobalSections_naturality,
    fromSections]
  congr 1
  exact evalSections_comp φ s f.appTop.hom

end FlagVarieties.Plucker
