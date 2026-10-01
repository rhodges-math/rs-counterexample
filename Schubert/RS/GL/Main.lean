import Schubert.RS.GL.HomDecomposition

/-!
# Endpoints: the Levi group, its irreducible representations and the quiver coordinate ring

Namespaces `Schubert.RS.GL` (the group and its representations) and
`Schubert.RS.Quiver.ForwardQuiver` (the coordinate ring of a quiver).

* The group: `LeviGroup d = ∏_p GL(d_p, ℂ)` and, for an interval partition, `IntervalLevi I`.
  Polynomial representations (`IsPolynomialLeviRep`) and characters as traces on the diagonal
  torus (`IsLeviCharacter`, `leviTorus`).
* The irreducible representations `V^λ = ⊗_p V_p^{λ^{(p)}}` (`ratLeviIrrep`): the external tensor
  product (`extTensor`) of the flag-minor models `flagOrbitRepresentation`, twisted by
  `∏_p det_p^{λ^{(p)}_{last}}` (`leviTwist`, `leviDetChar`).
* Twists: `finrank_intertwiningMap_leviTwist` (`dim Hom` is twist invariant),
  `ratLeviIrrepShiftEquiv` (`V^λ ⊗ det^c ≃ V^{λ + c}`),
  `finrank_intertwiningMap_ratLeviIrrep_shift`, `isLeviCharacter_leviTwist`,
  `isPolynomialLeviRep_leviTwist`, `schurCoeff_mul_blockDetMonomial`.
* The coordinate ring `R_Q` (`coordRing`) with the contragredient action (`coordRep`,
  `coordRep_X`), its graded pieces (`coordPiece`, finite-dimensional, with the monomial basis
  `pieceBasis`), and the torus action on monomials (`coordRep_leviTorus_monomial`).
* Pieces: `isPolynomialLeviRep_twist_coordPiece`, `isLeviCharacter_twist_coordPiece`,
  `toLaurent_twistedPieceCharacter`, and `gradedCharacter_eq_sum_monomials`.
* `Hom_L(V^λ, R_Q)`: the splitting over the pieces (`finrank_intertwiningMap_coordRep_eq_sum`),
  the central character obstruction (`intertwiningMap_coordPiece_eq_zero`), the restriction to
  multidegrees at most `degreeBound λ` (`finrank_intertwiningMap_ratLeviIrrep_coordRep`), and the
  multiplicity (`finrank_intertwiningMap_coordRep_eq_multiplicity`,
  `finrank_intertwiningMap_coordRep_eq_multiplicity_of`).
-/
