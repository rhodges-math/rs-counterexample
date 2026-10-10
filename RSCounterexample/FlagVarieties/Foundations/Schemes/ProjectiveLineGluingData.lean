import RSCounterexample.FlagVarieties.Foundations.Schemes.ProjectiveLineNaturality

/-!
# Local ordered-pair data on open subschemes

Each pair is globally coprime on its own open. On each intersection,
both pulled-back coordinates differ by the same supplied unit. These data
assert no existence of quotient-sheaf frames or global pair on the source.
-/

noncomputable section

namespace FlagVarieties.Foundations.ProjectiveLine

open AlgebraicGeometry CategoryTheory

universe u v

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {ι : Type v}

/-- Restrict a single coefficient homomorphism to an open subscheme. -/
def coefficientsOn (φ : R →+* Γ(X, ⊤)) (U : X.Opens) :
    R →+* Γ(U.toScheme, ⊤) := U.ι.appTop.hom.comp φ

theorem coefficientsOn_restrict (φ : R →+* Γ(X, ⊤)) {U V : X.Opens} (h : V ≤ U) :
    (X.homOfLE h).appTop.hom.comp (coefficientsOn φ U) = coefficientsOn φ V := by
  unfold coefficientsOn
  rw [← RingHom.comp_assoc, ← CommRingCat.hom_comp, ← Scheme.Hom.comp_appTop,
    Scheme.homOfLE_ι]

/-- Explicit ordered pairs and common units on the pairwise intersections. -/
structure OpenPairData (U : ι → X.Opens) where
  /-- The first coordinate on `U i`. -/
  delta : ∀ i, Γ((U i).toScheme, ⊤)
  /-- The second coordinate on `U i`. -/
  epsilon : ∀ i, Γ((U i).toScheme, ⊤)
  coprime : ∀ i, IsCoprime (delta i) (epsilon i)
  /-- The common unit relating the coordinates on `U i` and on `U j` over `U i ⊓ U j`. -/
  transition : ∀ i j, Γ((U i ⊓ U j).toScheme, ⊤)ˣ
  delta_transition : ∀ i j,
    (X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).appTop (delta i) =
      (transition i j : Γ((U i ⊓ U j).toScheme, ⊤)) *
        (X.homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).appTop (delta j)
  epsilon_transition : ∀ i j,
    (X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).appTop (epsilon i) =
      (transition i j : Γ((U i ⊓ U j).toScheme, ⊤)) *
        (X.homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).appTop (epsilon j)

namespace OpenPairData

variable {U : ι → X.Opens} (D : OpenPairData U) (φ : R →+* Γ(X, ⊤))

/-- The existing Proj morphism on a member of the cover. -/
def localMap (i : ι) : (U i).toScheme ⟶ scheme R :=
  fromPair (coefficientsOn φ (U i)) (D.delta i) (D.epsilon i) (D.coprime i)

set_option backward.isDefEq.respectTransparency false in
theorem localMap_overlap (i j : ι) :
    X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i) ≫ D.localMap φ i =
      X.homOfLE (inf_le_right : U i ⊓ U j ≤ U j) ≫ D.localMap φ j := by
  unfold localMap
  rw [fromPair_naturality, fromPair_naturality]
  simp only [coefficientsOn_restrict]
  simp only [D.delta_transition i j, D.epsilon_transition i j]
  exact fromPair_unit_mul (coefficientsOn φ (U i ⊓ U j)) _ _
    ((D.coprime j).map (X.homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).appTop.hom)
    (D.transition i j)

end OpenPairData

end FlagVarieties.Foundations.ProjectiveLine
