import Schubert.FlagVarieties.Schubert.Basic
import TauCeti.AlgebraicGeometry.Modules.GlobalSections
import TauCeti.AlgebraicGeometry.Modules.Pullback

/-!
# Sheaves of semi-invariant functions

Let `q : P ⟶ T` be a morphism of schemes and let the Borel subgroup `B` act on `P` from the right,
`a : P ×_R B ⟶ P`, preserving the fibres of `q` (`a ≫ q = pr₁ ≫ q`). For a weight `η`,
`semiInvariantSheaf E η` is the sheaf of `𝒪_T`-modules whose sections over `V ⊆ T` are the
functions `f` on `q⁻¹(V)` with `f(x b) = η(b)⁻¹ f(x)`: the equalizer of
`q_* 𝒪_P ⇉ (q ∘ pr₁)_* 𝒪_{P ×_R B}`, `f ↦ a^* f` and `f ↦ pr₁^* f · pr₂^* η⁻¹`.

For the orbit map `π : GLₙ ⟶ Flₙ` with `B` acting by right multiplication this is the line bundle
`𝓛(η) = GLₙ ×^B R_η` (`FlagVarieties.lineBundle`).
-/

noncomputable section

namespace FlagVarieties

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u

variable (R : Type u) [CommRing R] (n : ℕ)

/-- A scheme `P` over `T` with a right action of the Borel subgroup `B` that preserves the fibres
of `P ⟶ T`. -/
structure BorelAction (T : Scheme.{u}) where
  /-- The total space. -/
  P : Scheme.{u}
  /-- The projection to the base. -/
  q : P ⟶ T
  /-- The structure morphism over `Spec R`. -/
  toSpec : P ⟶ Spec (CommRingCat.of R)
  /-- The right action `P ×_R B ⟶ P`. -/
  act : pullback toSpec (BorelScheme.toSpec R n) ⟶ P
  /-- The action preserves the fibres of `q`. -/
  act_q : act ≫ q = pullback.fst toSpec (BorelScheme.toSpec R n) ≫ q

namespace BorelAction

variable {R n} {T : Scheme.{u}} (E : BorelAction R n T)

/-- The product `P ×_R B`. -/
abbrev actionDomain : Scheme.{u} :=
  pullback E.toSpec (BorelScheme.toSpec R n)

/-- The projection `pr₁ : P ×_R B ⟶ P`. -/
abbrev actionFst : E.actionDomain ⟶ E.P :=
  pullback.fst E.toSpec (BorelScheme.toSpec R n)

/-- The projection `pr₂ : P ×_R B ⟶ B`. -/
abbrev actionSnd : E.actionDomain ⟶ BorelScheme R n :=
  pullback.snd E.toSpec (BorelScheme.toSpec R n)

/-- The global function `pr₂^* η⁻¹` on `P ×_R B`. -/
def twist (η : Fin n → ℤ) : Γ(E.actionDomain, ⊤) :=
  E.actionSnd.appTop ((Scheme.ΓSpecIso (CommRingCat.of (BorelCoord R n))).inv
    (((borelCharacterUnit R n η)⁻¹ : (BorelCoord R n)ˣ) : BorelCoord R n))

/-- `q_* 𝒪_P`. -/
abbrev directImage : T.Modules :=
  (Scheme.Modules.pushforward E.q).obj (𝟙_ E.P.Modules)

/-- `(q ∘ pr₁)_* 𝒪_{P ×_R B}`. -/
abbrev directImageProd : T.Modules :=
  (Scheme.Modules.pushforward (E.actionFst ≫ E.q)).obj (𝟙_ E.actionDomain.Modules)

/-- The map `f ↦ a^* f`. -/
def pullbackAct : E.directImage ⟶ E.directImageProd :=
  (Scheme.Modules.pushforward E.q).map
      (SheafOfModules.unitToPushforwardObjUnit E.act.toRingCatSheafHom) ≫
    (Scheme.Modules.pushforwardComp E.act E.q).hom.app _ ≫
    (Scheme.Modules.pushforwardCongr E.act_q).hom.app _

/-- The map `f ↦ pr₁^* f · pr₂^* η⁻¹`. -/
def pullbackTwist (η : Fin n → ℤ) : E.directImage ⟶ E.directImageProd :=
  (Scheme.Modules.pushforward E.q).map
      (SheafOfModules.unitToPushforwardObjUnit E.actionFst.toRingCatSheafHom) ≫
    (Scheme.Modules.pushforwardComp E.actionFst E.q).hom.app _ ≫
    (Scheme.Modules.pushforward (E.actionFst ≫ E.q)).map
      (Scheme.Modules.globalSectionsSmul _ (E.twist η))

/-- **The sheaf of `η`-semi-invariant functions** on the fibres of `q`: the kernel of
`f ↦ a^* f - pr₁^* f · pr₂^* η⁻¹`, i.e. the equalizer of the two maps. -/
def semiInvariantSheaf (η : Fin n → ℤ) : T.Modules :=
  kernel (E.pullbackAct - E.pullbackTwist η)

/-- The inclusion of the semi-invariant functions into `q_* 𝒪_P`. -/
def semiInvariantι (η : Fin n → ℤ) : E.semiInvariantSheaf η ⟶ E.directImage :=
  kernel.ι _

end BorelAction

end FlagVarieties
