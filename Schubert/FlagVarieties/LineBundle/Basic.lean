import Schubert.FlagVarieties.LineBundle.SemiInvariant
import Schubert.FlagVarieties.Flag.Stabilizer

/-!
# The line bundles `𝓛(η)` and their sections

Over a commutative ring `R`, with `π : GLₙ ⟶ Flₙ` the orbit map of the standard flag and `B` the
upper triangular Borel subgroup acting on `GLₙ` by right multiplication `m : GLₙ ×_R B ⟶ GLₙ`:

* **`FlagVarieties.lineBundle R n η`** (`𝓛(η) = GLₙ ×^B R_η`): the sheaf of `𝒪_{Flₙ}`-modules whose
  sections over `V ⊆ Flₙ` are the functions `f` on `π⁻¹(V)` with `f(g b) = η(b)⁻¹ f(g)`. It is the
  equalizer of the two maps `π_* 𝒪_{GLₙ} ⇉ (π ∘ pr₁)_* 𝒪_{GLₙ × B}`, `f ↦ m^* f` and
  `f ↦ pr₁^* f · pr₂^* η⁻¹`.
* **`FlagVarieties.sections R n I η`** (`H⁰(X, 𝓛(η))`): for a closed subscheme `X ⊆ Flₙ` with ideal
  sheaf `I` and closed immersion `i : X ⟶ Flₙ`, the global sections `Γ(X, i^* 𝓛(η))`.
-/

noncomputable section

namespace FlagVarieties

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open Foundations Foundations.QuotientCharts
open scoped TensorProduct

universe u

variable (R : Type u) [CommRing R] (n : ℕ)

/-! ### The right action of `B` on `GLₙ` -/

/-- The product scheme `GLₙ ×_R B`. -/
abbrev GLBorel : Scheme.{u} :=
  pullback (GLOver R n).hom (BorelScheme.toSpec R n)

theorem glBorelSpec_condition₁ : (GLOver R n).hom ≫ 𝟙 (Spec (CommRingCat.of R)) =
    (TauCeti.GeneralLinear.groupSchemeSpecIso R n).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (GLCoord R n))) := by
  simpa only [Category.comp_id] using TauCeti.GeneralLinear.groupScheme_X_hom R n

theorem glBorelSpec_condition₂ : BorelScheme.toSpec R n ≫ 𝟙 (Spec (CommRingCat.of R)) =
    𝟙 (BorelScheme R n) ≫ BorelScheme.toSpec R n := by
  rw [Category.comp_id, Category.id_comp]

/-- The coordinate presentation of the first factor of `GLₙ ×_R B`. -/
def glBorelSpecMap : GLBorel R n ⟶ pullback
    (Spec.map (CommRingCat.ofHom (algebraMap R (GLCoord R n)))) (BorelScheme.toSpec R n) :=
  pullback.map (GLOver R n).hom (BorelScheme.toSpec R n)
    (Spec.map (CommRingCat.ofHom (algebraMap R (GLCoord R n)))) (BorelScheme.toSpec R n)
    (TauCeti.GeneralLinear.groupSchemeSpecIso R n).hom (𝟙 _) (𝟙 _)
    (glBorelSpec_condition₁ R n) (glBorelSpec_condition₂ R n)

instance : IsIso (glBorelSpecMap R n) := by
  let : IsIso (𝟙 (BorelScheme R n)) := IsIso.id _
  let : IsIso (𝟙 (Spec (CommRingCat.of R))) := IsIso.id _
  unfold glBorelSpecMap
  exact Limits.pullback.map_isIso _ _ _ _ _ _ _ _ _

@[reassoc] theorem glBorelSpecMap_fst :
    glBorelSpecMap R n ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ (TauCeti.GeneralLinear.groupSchemeSpecIso R n).hom :=
  pullback.lift_fst _ _ _

@[reassoc] theorem glBorelSpecMap_snd :
    glBorelSpecMap R n ≫ pullback.snd _ _ = pullback.snd _ _ := by
  simp [glBorelSpecMap]

/-- `GLₙ ×_R B` is the spectrum of `𝒪(GLₙ) ⊗_R 𝒪(B)`. -/
def glBorelSpecIso : GLBorel R n ≅ Spec (CommRingCat.of (GLCoord R n ⊗[R] BorelCoord R n)) :=
  asIso (glBorelSpecMap R n) ≪≫ pullbackSpecIso R (GLCoord R n) (BorelCoord R n)

@[reassoc] theorem glBorelSpecIso_inv_fst :
    (glBorelSpecIso R n).inv ≫ pullback.fst _ _ =
      GLScheme.point R n (Algebra.TensorProduct.includeLeft :
        GLCoord R n →ₐ[R] GLCoord R n ⊗[R] BorelCoord R n) := by
  have h : inv (glBorelSpecMap R n) ≫ pullback.fst (GLOver R n).hom (BorelScheme.toSpec R n) =
      pullback.fst _ _ ≫ (TauCeti.GeneralLinear.groupSchemeSpecIso R n).inv := by
    rw [IsIso.inv_comp_eq, glBorelSpecMap_fst_assoc, Iso.hom_inv_id, Category.comp_id]
  simp only [glBorelSpecIso, Iso.trans_inv, asIso_inv, Category.assoc, h]
  rw [pullbackSpecIso_inv_fst_assoc]
  rfl

@[reassoc] theorem glBorelSpecIso_inv_snd :
    (glBorelSpecIso R n).inv ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
        BorelCoord R n →ₐ[R] GLCoord R n ⊗[R] BorelCoord R n).toRingHom) := by
  have h : inv (glBorelSpecMap R n) ≫ pullback.snd (GLOver R n).hom (BorelScheme.toSpec R n) =
      pullback.snd _ _ := by
    rw [IsIso.inv_comp_eq, glBorelSpecMap_snd]
  simp only [glBorelSpecIso, Iso.trans_inv, asIso_inv, Category.assoc, h]
  rw [pullbackSpecIso_inv_snd]
  rfl

/-- The right multiplication `m : GLₙ ×_R B ⟶ GLₙ`, `(g, b) ↦ g b`. -/
def mulRight : GLBorel R n ⟶ GLScheme R n :=
  (glBorelSpecIso R n).hom ≫ Spec.map (CommRingCat.ofHom (rightCoaction R n).toRingHom) ≫
    (TauCeti.GeneralLinear.groupSchemeSpecIso R n).inv

/-! ### The sheaf `𝓛(η)` -/

/-- The orbit map is constant on right `B`-cosets: `π ∘ m = π ∘ pr₁`. -/
theorem mulRight_orbitMap :
    mulRight R n ≫ FlagScheme.orbitMap R n =
      pullback.fst (GLOver R n).hom (BorelScheme.toSpec R n) ≫ FlagScheme.orbitMap R n := by
  rw [← cancel_epi (glBorelSpecIso R n).inv]
  have h1 : (glBorelSpecIso R n).inv ≫ mulRight R n = GLScheme.point R n (rightCoaction R n) := by
    rw [mulRight, Iso.inv_hom_id_assoc]
    rfl
  rw [← Category.assoc, h1, ← Category.assoc, glBorelSpecIso_inv_fst]
  refine (orbitMap_point_eq_of_mul _ _ ((borelMatrix R n).map
    (Algebra.TensorProduct.includeRight : BorelCoord R n →ₐ[R] _)) ?_ ?_).symm
  · exact (borelMatrix_blockTriangular R n).map _
  · exact map_rightCoaction_genericMatrix R n

/-- `GLₙ` over `Flₙ` (via the orbit map), with `B` acting by right multiplication. -/
def glBorelAction : BorelAction R n (FlagScheme R n) where
  P := GLScheme R n
  q := FlagScheme.orbitMap R n
  toSpec := (GLOver R n).hom
  act := mulRight R n
  act_q := mulRight_orbitMap R n

/-- **The line bundle `𝓛(η) = GLₙ ×^B R_η` on `Flₙ`**.

Its sections over an open `V ⊆ Flₙ` are the functions `f` on `π⁻¹(V) ⊆ GLₙ` that are
semi-invariant of weight `η` under right multiplication by `B`: `f(g b) = η(b)⁻¹ f(g)`
(Jantzen I.5.8). Formally it is the equalizer (the kernel of the difference) of the two maps of
`𝒪_{Flₙ}`-modules `π_* 𝒪_{GLₙ} ⇉ (π ∘ pr₁)_* 𝒪_{GLₙ ×_R B}` given by `f ↦ m^* f` and
`f ↦ pr₁^* f · pr₂^* η⁻¹`, where `m` is the right multiplication
(`BorelAction.semiInvariantSheaf` for `glBorelAction`). -/
def lineBundle (η : Fin n → ℤ) : (FlagScheme R n).Modules :=
  (glBorelAction R n).semiInvariantSheaf η

/-- The inclusion `𝓛(η) ⟶ π_* 𝒪_{GLₙ}`. -/
def lineBundleι (η : Fin n → ℤ) : lineBundle R n η ⟶ (glBorelAction R n).directImage :=
  (glBorelAction R n).semiInvariantι η

/-! ### Sections over closed subschemes -/

/-- **The sections `H⁰(X, 𝓛(η))`**.

For a closed subscheme `X ⊆ Flₙ` with ideal sheaf `I` and closed immersion `i : X ⟶ Flₙ`, the
global sections `Γ(X, i^* 𝓛(η))` of the pullback of `𝓛(η)` to `X`. -/
abbrev sections (I : (FlagScheme R n).IdealSheafData) (η : Fin n → ℤ) : Type u :=
  Γ((Scheme.Modules.pullback I.subschemeι).obj (lineBundle R n η), ⊤)

/-- A closed subscheme of `Flₙ` lies over `Spec R`. -/
instance instSubschemeOverSpec (I : (FlagScheme R n).IdealSheafData) :
    I.subscheme.Over (Spec (CommRingCat.of R)) :=
  ⟨I.subschemeι ≫ FlagScheme.toSpec R n⟩

/-- `H⁰(X, 𝓛(η))` is an `R`-module, through `R → Γ(X, 𝒪_X)`. -/
example (I : (FlagScheme R n).IdealSheafData) (η : Fin n → ℤ) : Module R (sections R n I η) :=
  inferInstance

end FlagVarieties
