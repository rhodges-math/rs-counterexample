import RSCounterexample.Paper.Hall.Reduction

/-!
# Endpoints: Section 3, Hall polynomial extraction

Namespace `Schubert.RS.Hall`. Positions and indices are `0`-based in Lean.

* Lemma 3.1 (`lem:hall-determinant`): `hall_determinant`. For weakly increasing heights
  `ℓ_1 ≤ ⋯ ≤ ℓ_m` (rows `R_i` may be empty) and any truncation degree `B ≥ d` of the geometric
  series, `[x_1 ⋯ x_d] Δ_d(x) ∏_j ∏_{i ≤ ℓ_j} (1 − x_i t_j)^{−1}` (`hallProduct`) equals
  `det(h_{1+i−j}(R_i))` (`hallMatrix`, with `h_q` given by `completeH`), which equals the sum of
  `t_{j_1} ⋯ t_{j_d}` over the Hall-admissible subsets (`hallSum`, `IsHallAdmissible`). The
  coefficients `t_j` lie in an arbitrary commutative ring.
* Lemma 3.8 (`lem:hall-flags`): `hall_flags`, with the canonical flags (3.7) `hallFlag` and
  `firstAbove`; also `isHallAdmissible_iff_flags`.
* Definition 3.9 (`def:paired-target`): `HallPartition a b c N r` (an `r`-Hall partition for
  `(a, b, c)` with `c̄ = N·1 − c`) and `IsHallTriple`; independence of `N`: `HallPartition.changeN`,
  `isHallTriple_iff`.
* The notation of Proposition 3.11, for a Hall partition `P`: the non-distinguished positions
  `P.q`, the pairs `P.pairs` (`𝓔`), the heights `P.height` (`ℓ_{s,j}`), the flags `P.flag` and the
  Hall polynomials `P.blockPolynomial` ((3.10)); `HallPartition.m_eq_sum_card` (`m = ∑_s |B_s|`)
  and `HallPartition.blockPolynomial_eq_hallAdmissible`.
* Proposition 3.11 (`prop:paired-reduction`): `paired_reduction`,
  `[𝒜_c](κ_a κ_b) = [t_1 ⋯ t_m] ∏_s P_s(t) ∏_{(i,j) ∈ 𝓔} (1 − t_j/t_i)` in the Laurent
  polynomials in `t_1, …, t_m` (`tVar`).

Tools: `atomCoefficient_eq_finiteCmpFactor` (Proposition 2.13 with truncated geometric series),
`substitute` and `coeff_substitute` (the substitution `x_{q_j} = t_j^{−1}`),
`coeff_prod_mapDomain` (blockwise extraction), `HallPartition.substitute_rootProduct` (the first
equality of (3.14)).
-/
