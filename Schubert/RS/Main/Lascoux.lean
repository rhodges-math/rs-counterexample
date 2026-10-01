import Schubert.RS.Family.LascouxCorollary
import Schubert.RS.Lascoux.Examples

/-!
# Endpoints: Corollary 1.3 (Lascoux polynomials and Lascoux atoms)

Definitions, namespace `Schubert.RS` (files `Lascoux/*.lean`):
* `betaIsobaric`: `πᵢ^{(β)} f = πᵢ((1 + β x_{i+1}) f)`; `betaAtomOperator`: `πᵢ^{(β)} - 1`;
* `lascoux`, `lascouxAtom`: the Lascoux polynomials and Lascoux atoms;
* `LascouxAtomPositive`: an expansion in Lascoux atoms with coefficients in `ℤ_{≥0}[β]`.

Statements:
* `πᵢ^{(β)} = 1 + x_{i+1}(1 + β xᵢ)∂ᵢ`: `Schubert.RS.betaIsobaric_eq`.
* Sign check of `β`: `𝔏_{01} = x₁ + x₂ + β x₁ x₂` and `𝔏̄_{01} = x₂ + β x₁ x₂`
  (`Schubert.RS.lascoux_zero_one`, `Schubert.RS.lascouxAtom_zero_one`).
* At `β = 0`, keys and Demazure atoms: `Schubert.RS.betaZero_lascoux`,
  `Schubert.RS.betaZero_lascouxAtom`.
* Corollary 1.3, coefficients in `ℤ_{≥0}[β]`: `Schubert.RS.Family.not_lascouxAtomPositive`.
* Corollary 1.3, stronger form (coefficients in `ℤ[β]`, nonnegative at `β = 0`):
  `Schubert.RS.Family.no_lascouxExpansion_nonnegAtZero`.
* The rank-28 example, both forms: `Schubert.RS.Family.rank28_not_lascouxAtomPositive`,
  `Schubert.RS.Family.rank28_no_lascouxExpansion_nonnegAtZero`.
* Monical–Pechenik–Searles, Conjecture 4.25 (operator form), is false:
  `Schubert.RS.Family.lascoux_product_positivity_false`.
-/
