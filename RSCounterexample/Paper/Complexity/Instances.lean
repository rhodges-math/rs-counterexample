import RSCounterexample.Paper.Polyhedra.IntPolyhedron
import Complexitylib.Encoding.DataEncode

/-!
# Encodings of integers and integer linear systems

Instances of complexitylib's `Complexity.DataEncode` for the inputs of the feasibility statement:
an integer is encoded as its sign and the binary digits of its absolute value, and a system of
linear inequalities as the pair of its dimension and its list of rows. Through
`Complexity.DataEncode.bitstringEncode` these give bitstring encodings whose length is linear in
the usual binary size.
-/

namespace Schubert.RS.Algorithms

/-- An integer as its sign (`true` for negative) and the binary digits of its absolute value. -/
instance intDataEncode : Complexity.DataEncode ℤ where
  encode z := Complexity.DataEncode.encode (decide (z < 0), z.natAbs)
  h_inj := by
    intro a b h
    have h' := Complexity.DataEncode.h_inj h
    simp only [Prod.mk.injEq, decide_eq_decide] at h'
    omega

/-- A system of linear inequalities as its dimension and its list of rows. -/
instance intPolyhedronDataEncode : Complexity.DataEncode IntPolyhedron where
  encode P := Complexity.DataEncode.encode (P.dim, P.rows)
  h_inj := by
    rintro ⟨d₁, r₁⟩ ⟨d₂, r₂⟩ h
    have h' := Complexity.DataEncode.h_inj h
    simp only [Prod.mk.injEq] at h'
    rw [h'.1, h'.2]

end Schubert.RS.Algorithms
