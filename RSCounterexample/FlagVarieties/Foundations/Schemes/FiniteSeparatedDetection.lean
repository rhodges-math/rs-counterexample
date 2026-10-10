import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Separatedness detected by finitely many morphisms

A finite family of maps into separated schemes factors through a separated
scheme (their iterated binary product). If that family detects equality of
all scheme morphisms, the factor map is a monomorphism, so its source is
separated. No reducedness or condition only on field-valued points suffices
or is used here.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

theorem separated_binaryProduct (X Y : Scheme.{u})
    [X.IsSeparated] [Y.IsSeparated] : (X ⨯ Y).IsSeparated := by
  have : IsSeparated (prod.snd : X ⨯ Y ⟶ Y) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasBinaryProduct' X Y)
      (inferInstance : IsSeparated (terminal.from X))
  constructor
  rw [← terminal.comp_from (prod.snd : X ⨯ Y ⟶ Y)]
  infer_instance

theorem finiteFamily_factors_through_separated {X : Scheme.{u}} {n : ℕ}
    (Y : Fin n → Scheme.{u}) [∀ i, (Y i).IsSeparated]
    (f : ∀ i, X ⟶ Y i) :
    ∃ (Z : Scheme.{u}) (g : X ⟶ Z), Z.IsSeparated ∧
      ∀ i, ∃ p : Z ⟶ Y i, g ≫ p = f i := by
  induction n with
  | zero =>
    exact ⟨⊤_ Scheme, terminal.from X, ⟨inferInstance⟩, fun i => Fin.elim0 i⟩
  | succ n ih =>
    obtain ⟨Z, g, hZ, hp⟩ := ih (fun i => Y i.succ) (fun i => f i.succ)
    let := hZ
    refine ⟨Y 0 ⨯ Z, prod.lift (f 0) g, separated_binaryProduct (Y 0) Z, ?_⟩
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact ⟨prod.fst, by simp⟩
    · obtain ⟨p, h⟩ := hp j
      exact ⟨prod.snd ≫ p, by simpa using h⟩

/-- Detection on all sources, including nonreduced schemes, implies separatedness. -/
theorem separated_of_finite_jointly_mono {X : Scheme.{u}} {n : ℕ}
    (Y : Fin n → Scheme.{u}) [∀ i, (Y i).IsSeparated]
    (f : ∀ i, X ⟶ Y i)
    (h : ∀ (T : Scheme.{u}) (a b : T ⟶ X),
      (∀ i, a ≫ f i = b ≫ f i) → a = b) : X.IsSeparated := by
  obtain ⟨Z, g, hZ, hp⟩ := finiteFamily_factors_through_separated Y f
  let := hZ
  have : Mono g := ⟨by
    intro T a b hab
    apply h T a b
    intro i
    obtain ⟨p, hi⟩ := hp i
    rw [← hi]
    simpa only [← Category.assoc] using congrArg (fun k => k ≫ p) hab⟩
  constructor
  rw [← terminal.comp_from g]
  infer_instance

end FlagVarieties.Foundations
