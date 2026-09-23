import Schubert.RS.LaurentOperators
import Schubert.RS.Keys
import Schubert.RS.WeylDenominator

/-!
# The constant-term pairing and the local adjoint calculation

The global key–atom orthogonality theorem is not assumed here. This file
proves the algebraic adjoint step from the defining operator equations.
-/

namespace Schubert.RS

open FinPermutation
noncomputable section
variable {n : ℕ}

/-- Fu–Lascoux's type-A pairing in the manuscript's conventions. -/
def keyAtomPairing (f g : Polynomial n) : ℤ :=
  constantTerm (toLaurent f * reverseNeg (toLaurent g) * weylFactor n)

theorem keyAtomPairing_add_left (f g h : Polynomial n) :
    keyAtomPairing (f + g) h = keyAtomPairing f h + keyAtomPairing g h := by
  simp [keyAtomPairing, add_mul]

theorem keyAtomPairing_add_right (f g h : Polynomial n) :
    keyAtomPairing f (g + h) = keyAtomPairing f g + keyAtomPairing f h := by
  simp [keyAtomPairing, mul_add, add_mul]

/-- Local self-adjointness. The hypotheses are operator identities, proved
for the actual polynomial operators in `isobaric_laurent_identity`. The
remaining Weyl factors must be invariant under the adjacent swap. -/
theorem constantTerm_isobaric_adjoint (i : AdjacentPosition n)
    (p p' q q' D : Laurent n)
    (hp : (1 - AddMonoidAlgebra.single (positiveRoot i.left i.right) 1) * p' =
      laurentSwap i p - AddMonoidAlgebra.single (positiveRoot i.left i.right) 1 * p)
    (hq : (1 - AddMonoidAlgebra.single (positiveRoot i.left i.right) 1) * q' =
      laurentSwap i q - AddMonoidAlgebra.single (positiveRoot i.left i.right) 1 * q)
    (hD : laurentSwap i D = D) :
    constantTerm (p' * q * ((1 - AddMonoidAlgebra.single (positiveRoot i.left i.right) 1) * D)) =
      constantTerm (p * q' * ((1 - AddMonoidAlgebra.single (positiveRoot i.left i.right) 1) * D)) := by
  let t : Laurent n := AddMonoidAlgebra.single (positiveRoot i.left i.right) 1
  calc
    _ = constantTerm (((1 - t) * p') * q * D) := by congr 1; ring
    _ = constantTerm ((laurentSwap i p - t * p) * q * D) := by rw [hp]
    _ = constantTerm (laurentSwap i p * (q * D)) - constantTerm (t * p * q * D) := by
      rw [← constantTerm_sub]
      congr 1
      ring
    _ = constantTerm (p * (laurentSwap i q * D)) - constantTerm (t * p * q * D) := by
      rw [constantTerm_swap_transfer, map_mul, hD]
    _ = constantTerm (p * (laurentSwap i q - t * q) * D) := by
      rw [← constantTerm_sub]
      congr 1
      ring
    _ = constantTerm (p * ((1 - t) * q') * D) := by rw [hq]
    _ = _ := by congr 1; ring

/-- The previous algebraic step with the actual Weyl denominator. -/
theorem constantTerm_isobaric_adjoint_weyl (i : AdjacentPosition n)
    (p p' q q' : Laurent n)
    (hp : (1 - AddMonoidAlgebra.single (positiveRoot i.left i.right) 1) * p' =
      laurentSwap i p - AddMonoidAlgebra.single (positiveRoot i.left i.right) 1 * p)
    (hq : (1 - AddMonoidAlgebra.single (positiveRoot i.left i.right) 1) * q' =
      laurentSwap i q - AddMonoidAlgebra.single (positiveRoot i.left i.right) 1 * q) :
    constantTerm (p' * q * weylFactor n) = constantTerm (p * q' * weylFactor n) := by
  rw [weylFactor_split i]
  exact constantTerm_isobaric_adjoint i p p' q q' (weylRemainder i) hp hq
    (laurentSwap_weylRemainder i)

end
end Schubert.RS
