import Schubert.RS.Laurent
import Mathlib.Algebra.BigOperators.Fin

/-!
# Blocks of a standard Levi subgroup

For block sizes `d_0, …, d_{s−1}` with `n = ∑_p d_p`, the variables `x_0, …, x_{n−1}` are split into
consecutive blocks `I_0, …, I_{s−1}`, the variables of the standard Levi subgroup
`GL_{d_0} × ⋯ × GL_{d_{s−1}}`. This file defines the positions of the variables, the product of
the blockwise Weyl factors `∏_p Δ_{d_p}(x_{I_p})`, and the Levi Weyl projector, which reads off
the coefficient of `∏_p s_{λ^{(p)}}(x_{I_p})` (Theorem 5.3 of the paper).

## Main definitions

* `Schubert.RS.Quiver.Levi.total`: `n = ∑_p d_p`.
* `Schubert.RS.Quiver.Levi.pos`: the position of the `i`-th variable of block `p`.
* `Schubert.RS.Quiver.Levi.weylFactor`: `∏_p Δ_{d_p}(x_{I_p})`, with the paper's
  `Δ_d(z) = ∏_{i<j} (1 − z_i/z_j)`.
* `Schubert.RS.Quiver.Levi.blockWeight`: the paper's `ν`, the weight whose restriction to the block
  `I_p = {i_1 < ⋯ < i_d}` is `(λ^{(p)}_d, …, λ^{(p)}_1)`.
* `Schubert.RS.Quiver.Levi.schurCoeff`: `f ↦ [x^ν] (∏_p Δ_{d_p}(x_{I_p})) f`.
-/

namespace Schubert.RS.Quiver.Levi

noncomputable section

variable {s : ℕ} (d : Fin s → ℕ)

/-- The number of variables, `n = ∑_p d_p`. -/
abbrev total : ℕ := ∑ p, d p

/-- The position of the `i`-th variable of block `p`: the blocks are consecutive, in order. -/
def pos (p : Fin s) (i : Fin (d p)) : Fin (total d) := finSigmaFinEquiv ⟨p, i⟩

/-- The product of the blockwise Weyl factors, `∏_p Δ_{d_p}(x_{I_p})`, where
`Δ_d(z) = ∏_{i<j} (1 − z_i/z_j)`. -/
def weylFactor : Laurent (total d) :=
  ∏ p, ∏ i : Fin (d p), ∏ j ∈ Finset.univ.filter (i < ·),
    (1 - AddMonoidAlgebra.single (positiveRoot (pos d p i) (pos d p j)) 1)

/-- The weight `ν` attached to block weights `λ^{(p)}`: on the block `I_p = {i_1 < ⋯ < i_d}` it is
`(λ^{(p)}_d, …, λ^{(p)}_1)`, i.e. `λ^{(p)}` reversed. -/
def blockWeight (lam : (p : Fin s) → Fin (d p) → ℤ) : Weight (total d) :=
  fun k => lam (finSigmaFinEquiv.symm k).1 (Fin.rev (finSigmaFinEquiv.symm k).2)

/-- The Levi Weyl projector `f ↦ [x^ν] (∏_p Δ_{d_p}(x_{I_p})) f`: for a Laurent polynomial that is
symmetric in each block, the coefficient of `∏_p s_{λ^{(p)}}(x_{I_p})` in its expansion in
products of rational Schur polynomials. -/
def schurCoeff (f : Laurent (total d)) (lam : (p : Fin s) → Fin (d p) → ℤ) : ℤ :=
  (weylFactor d * f).coeff (blockWeight d lam)

end

end Schubert.RS.Quiver.Levi
