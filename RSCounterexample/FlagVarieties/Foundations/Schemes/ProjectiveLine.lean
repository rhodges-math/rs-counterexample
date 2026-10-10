import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import RSCounterexample.FlagVarieties.Foundations.Schemes.ProjectiveLineAlgebra

/-!
# The projective line and morphisms from a framed quotient

The target is the scheme `Proj R[X₀,X₁]` with its standard grading.
A unimodular ordered pair of global sections evaluates `X₀` and `X₁` and
therefore defines a scheme morphism through Mathlib's `fromOfGlobalSections`.
The order is the order of the two inputs to the quotient; no dualization or
coordinate swap is inserted. Global coprimality is an explicit premise: generation of a
trivial quotient sheaf on a nonaffine scheme does not by itself give
Bézout coefficients in the ring of global sections.

The affine-local passage from a framed quotient to such a pair is
`Schemes/QuotientPairOpenFrames.lean` and `Schemes/QuotientPairScheme.lean`;
invariance under a common unit is `Schemes/ProjectiveLineCompatibility.lean`,
and the morphism attached to a quotient line sheaf, independent of the
frame cover, is `Schemes/QuotientLineSheafGlobal.lean`.
-/

noncomputable section

namespace FlagVarieties.Foundations.ProjectiveLine

open AlgebraicGeometry CategoryTheory

universe u

variable (R : Type u) [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The projective line `Proj R[X₀,X₁]`. -/
abbrev scheme : Scheme.{u} := Proj (grading R)

/-- The chart where the `i`th quotient coordinate generates the line. -/
def chart (i : Fin 2) : (scheme R).Opens :=
  Proj.basicOpen (grading R) (MvPolynomial.X i)

/-- The structure morphism to the coefficient-ring spectrum. -/
def toSpec : scheme R ⟶ Spec (CommRingCat.of R) :=
  Proj.toSpecZero (grading R) ≫ Spec.map (CommRingCat.ofHom (constants R))

variable {R} {X : Scheme.{u}} (φ : R →+* Γ(X, ⊤)) (δ ε : Γ(X, ⊤))

/-- A framed unimodular quotient pair defines a scheme morphism. -/
def fromPair (h : IsCoprime δ ε) : X ⟶ scheme R :=
  Proj.fromOfGlobalSections (grading R) (evaluation φ δ ε)
    (map_irrelevant_eq_top φ δ ε h)

/-- The inverse image of the `i`th standard chart is the locus where its
quotient coordinate is invertible. -/
theorem fromPair_preimage_chart (h : IsCoprime δ ε) (i : Fin 2) :
    fromPair φ δ ε h ⁻¹ᵁ chart R i = X.basicOpen (![δ, ε] i) := by
  simpa only [fromPair, chart, evaluation_X] using
    Proj.fromOfGlobalSections_preimage_basicOpen (grading R) (evaluation φ δ ε)
      (map_irrelevant_eq_top φ δ ε h) (by decide : 0 < (1 : ℕ))
      (MvPolynomial.isHomogeneous_X R i)

@[simp] theorem fromPair_preimage_chart_zero (h : IsCoprime δ ε) :
    fromPair φ δ ε h ⁻¹ᵁ chart R 0 = X.basicOpen δ := by
  simpa using fromPair_preimage_chart φ δ ε h 0

@[simp] theorem fromPair_preimage_chart_one (h : IsCoprime δ ε) :
    fromPair φ δ ε h ⁻¹ᵁ chart R 1 = X.basicOpen ε := by
  simpa using fromPair_preimage_chart φ δ ε h 1

/-- The local map on a standard chart, including its structure-sheaf map. -/
def fromPairOnChart (i : Fin 2) :
    (X.basicOpen (![δ, ε] i)).toScheme ⟶ (chart R i).toScheme :=
  Proj.toBasicOpenOfGlobalSections (grading R) (evaluation φ δ ε)
    (evaluation_X φ δ ε i) (by decide : 0 < (1 : ℕ))
    (MvPolynomial.isHomogeneous_X R i)

/-- The global morphism restricts to the chart construction. -/
theorem fromPair_resLE_chart (h : IsCoprime δ ε) (i : Fin 2) :
    (fromPair φ δ ε h).resLE (chart R i) (X.basicOpen (![δ, ε] i))
      (fromPair_preimage_chart φ δ ε h i).ge = fromPairOnChart φ δ ε i := by
  have hpre : fromPair φ δ ε h ⁻¹ᵁ chart R i =
      X.basicOpen (evaluation φ δ ε (MvPolynomial.X i)) :=
    Proj.fromOfGlobalSections_preimage_basicOpen (grading R) (evaluation φ δ ε)
      (map_irrelevant_eq_top φ δ ε h) (by decide : 0 < (1 : ℕ))
      (MvPolynomial.isHomogeneous_X R i)
  have aux (x : Γ(X, ⊤)) (hx : evaluation φ δ ε (MvPolynomial.X i) = x) :
      (fromPair φ δ ε h).resLE (chart R i) (X.basicOpen x)
        (hpre.trans (congrArg X.basicOpen hx)).ge =
      Proj.toBasicOpenOfGlobalSections (grading R) (evaluation φ δ ε) hx
        (by decide : 0 < (1 : ℕ)) (MvPolynomial.isHomogeneous_X R i) := by
    subst x
    exact Proj.fromOfGlobalSections_resLE (grading R) (evaluation φ δ ε)
      (map_irrelevant_eq_top φ δ ε h) (by decide : 0 < (1 : ℕ))
      (MvPolynomial.isHomogeneous_X R i)
  exact aux (![δ, ε] i) (evaluation_X φ δ ε i)

/-- The ordered-pair morphism lies over the given map on coefficients. -/
@[reassoc] theorem fromPair_toSpec (h : IsCoprime δ ε) :
    fromPair φ δ ε h ≫ toSpec R =
      X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ) := by
  rw [toSpec, ← Category.assoc, fromPair,
    Proj.fromOfGlobalSections_toSpecZero, Category.assoc, ← Spec.map_comp]
  congr 2
  ext r
  exact evaluation_C φ δ ε r

end FlagVarieties.Foundations.ProjectiveLine
