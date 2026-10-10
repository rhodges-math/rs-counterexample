import RSCounterexample.Paper.Quiver.ForwardQuiver
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

/-!
# Quiver multiplicities

For a forward quiver `Q` with vertex spaces `V_p = ℂ^{dim p}`, the coordinate ring of the
representation space `⊕_{e : p → q} Hom(V_p, V_q)` is `R_Q = Sym(⊕_e V_p ⊗ V_q^*)` ((5.2) of the
paper), a representation of `L = ∏_p GL(V_p)`. Its graded piece of multidegree `ℓ = (ℓ_e)` is
`⊗_e Sym^{ℓ_e}(V_p ⊗ V_q^*)`, whose character is `∏_e h_{ℓ_e}({x_i/x_j : i ∈ I_p, j ∈ I_q})`.

The multiplicity of the irreducible `L`-module `⊗_p V_p^{λ^{(p)}}` in `R_Q` is, at the level of
characters, the sum over the graded pieces of the coefficient of `∏_p s_{λ^{(p)}}(x_{I_p})` in their
characters. By `Schubert.RS.Quiver.Schur.weylProjector_sum_ratSchur` this coefficient is the Levi
Weyl projector `Levi.schurCoeff`, so the multiplicity is defined as a finite sum of Laurent
coefficients. Only graded pieces satisfying the cut-degree equations (5.6) contribute, and their
degrees are bounded by `degreeBound`.

## Main definitions

* `Schubert.RS.Quiver.ForwardQuiver.gradedCharacter`: the character of `⊗_e Sym^{ℓ_e}(V_p ⊗ V_q^*)`.
* `Schubert.RS.Quiver.ForwardQuiver.schurCoeff`: the coefficient of `∏_p s_{λ^{(p)}}(x_{I_p})`.
* `Schubert.RS.Quiver.ForwardQuiver.multiplicity`: the multiplicity of `⊗_p V_p^{λ^{(p)}}` in `R_Q`.
-/

namespace Schubert.RS.Quiver.ForwardQuiver

noncomputable section

variable (Q : ForwardQuiver)

/-- The product of the vertex Weyl factors, `∏_p Δ_{dim p}(x_{I_p})`. -/
def leviWeylFactor : Laurent Q.n := Levi.weylFactor Q.dim

/-- The weight monomial `x_i/x_j` of the basis vector `v_i ⊗ w_j^*` of `V_p ⊗ V_q^*`, for an arrow
`e : p → q`, `i ∈ I_p` and `j ∈ I_q`. -/
def arrowMonomial (e : Q.Arrow) (ij : Fin (Q.dim (Q.src e)) × Fin (Q.dim (Q.tgt e))) :
    Laurent Q.n :=
  AddMonoidAlgebra.single (positiveRoot (Q.pos (Q.src e) ij.1) (Q.pos (Q.tgt e) ij.2)) 1

/-- The character of the graded piece `⊗_e Sym^{ℓ_e}(V_p ⊗ V_q^*)` of `R_Q`: the product over the
arrows of the complete homogeneous polynomials `h_{ℓ_e}` in the weights `x_i/x_j` of
`V_p ⊗ V_q^*`. -/
def gradedCharacter (ℓ : Q.Arrow → ℕ) : Laurent Q.n :=
  ∏ e, MvPolynomial.aeval (Q.arrowMonomial e)
    (MvPolynomial.hsymm (Fin (Q.dim (Q.src e)) × Fin (Q.dim (Q.tgt e))) ℤ (ℓ e))

/-- The coefficient of `∏_p s_{λ^{(p)}}(x_{I_p})` in a Laurent polynomial that is symmetric in the
variables of each vertex. -/
def schurCoeff (f : Laurent Q.n) (lam : Q.Weight) : ℤ := Levi.schurCoeff Q.dim f lam

/-- A bound for the degrees of the graded pieces that can contain `⊗_p V_p^{λ^{(p)}}`. -/
def degreeBound (lam : Q.Weight) : ℕ := ∑ p, ∑ i, (lam p i).natAbs

/-- **The multiplicity of `⊗_p V_p^{λ^{(p)}}` in `R_Q`**, summed over the graded pieces: the
coefficient of `∏_p s_{λ^{(p)}}(x_{I_p})` in the characters of the graded pieces
`⊗_e Sym^{ℓ_e}(V_p ⊗ V_q^*)`, over all multidegrees `ℓ` with every `ℓ_e ≤ degreeBound λ` (the
others contribute nothing). -/
def multiplicity (lam : Q.Weight) : ℤ :=
  ∑ ℓ ∈ Fintype.piFinset (fun _ : Q.Arrow => Finset.range (Q.degreeBound lam + 1)),
    Q.schurCoeff (Q.gradedCharacter ℓ) lam

end

end Schubert.RS.Quiver.ForwardQuiver
