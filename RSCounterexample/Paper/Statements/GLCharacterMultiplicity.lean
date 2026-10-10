import RSCounterexample.Paper.GL.Basic

/-!
# Multiplicities of irreducible polynomial representations from characters

STATUS: proved in this library: `Schubert.RS.glCharacterMultiplicity_holds`
(`RSCounterexample/Paper/GL/CharacterMultiplicity.lean`, from the library `RSCounterexample/GLRep`).

For a polynomial representation `ρ` of `L = GL_{d_0}(ℂ) × ⋯ × GL_{d_{s−1}}(ℂ)` with character `χ`
and a polynomial dominant weight `λ = (λ^{(p)})_p`, the dimension of
`Hom_L(⊗_p V_p^{λ^{(p)}}, ρ)` is the coefficient of `∏_p s_{λ^{(p)}}(x_{I_p})` in the Schur
expansion of `χ`.

This combines three classical facts: finite-dimensional polynomial representations of `L` are
completely reducible, the irreducible ones are the `⊗_p V_p^{μ^{(p)}}` with characters
`∏_p s_{μ^{(p)}}(x_{I_p})`, and Schur's lemma (W. Fulton, J. Harris, *Representation Theory*,
Lectures 6 and 15; R. Stanley, *Enumerative Combinatorics 2*, Appendix 2, Theorem A2.4). The
irreducible representations are the external tensor products of flag-minor models
(`Schubert.RS.GL.ratLeviIrrep`). The coefficient is read off by the Levi Weyl projector
`Schubert.RS.Quiver.Levi.schurCoeff` (`Schubert.RS.Quiver.Levi.schurCoeff_leviSchur`).
-/

open Schubert.RS.Quiver

namespace Schubert.RS

/-- **Characters determine multiplicities** for polynomial representations of
`L = GL_{d_0}(ℂ) × ⋯ × GL_{d_{s−1}}(ℂ)`. Let `ρ` be a polynomial representation of `L` whose
character (the trace on the diagonal torus) is `χ`, and let `lam` be a polynomial dominant weight,
whose irreducible representation `⊗_p V_p^{λ^{(p)}}` is realized by flag-minor models
(`Schubert.RS.GL.ratLeviIrrep`). Then `dim Hom_L(⊗_p V_p^{λ^{(p)}}, ρ)` is the coefficient of
`∏_p s_{λ^{(p)}}(x_{I_p})` in the Schur expansion of `χ`. -/
def GLCharacterMultiplicity : Prop :=
  ∀ (s : ℕ) (d : Fin s → ℕ) (W : Type) [AddCommGroup W] [Module ℂ W]
    (ρ : _root_.Representation ℂ (Schubert.RS.GL.LeviGroup d) W)
    (χ : Schubert.RS.Polynomial (Levi.total d)),
    Schubert.RS.GL.IsPolynomialLeviRep d ρ → Schubert.RS.GL.IsLeviCharacter d ρ χ →
    ∀ lam : (p : Fin s) → TauCeti.DominantWeight (d p), (∀ p, (lam p).IsPolynomial) →
      (Module.finrank ℂ
          (_root_.Representation.IntertwiningMap (Schubert.RS.GL.ratLeviIrrep d lam) ρ) : ℤ) =
        Levi.schurCoeff d (toLaurent χ) fun p => (lam p).1

end Schubert.RS
