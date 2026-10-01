import Schubert.RS.LR.Word

/-!
# Endpoints: the Littlewood–Richardson rule

Namespace `Schubert.RS.LR`. Alternants, the staircase `δ`, rational Schur polynomials and the
Weyl projector are those of `Schubert.RS.Quiver.Schur`. Tableaux are Tau Ceti's
`TauCeti.BoundedSSYT d ν` (letters `0, …, d − 1`), with weight `weightVec T`.

* The lattice condition:
  - row-count form `IsLattice κ T`: for every row `r` and letter `i`,
    `κ_{i+1} + #{i + 1 in rows ≤ r} ≤ κ_i + #{i in rows < r}` (`rowCount`, `countBelow`);
  - reading-word form `IsLatticeFrom κ (reverseRowWord T)`;
  - the two agree: `isLatticeFrom_iff`.
* **The Littlewood–Richardson rule**, alternant form, for weakly decreasing integer `κ`:
  `alternant_mul_schur` (row-count form) and `alternant_mul_schur_word` (reading-word form),
  `a_{κ + δ} · s_ν = ∑_{T lattice from κ} a_{κ + wt(T) + δ}`.
* With a determinant twist: `alternant_mul_shiftedSchur`.
* Coefficient form: `coeff_alternant_mul_schur`, the coefficient of `x^{λ + δ}` in `a_{κ + δ} s_ν`
  is `#{T lattice from κ : κ + wt(T) = λ}`.
* Projector form: `weylProjector_ratSchur_mul_schur`, the multiplicity of `s_λ` in `s_κ · s_ν`.
* The involution behind the proof:
  - `IsFirstViolation`, `lrSwap`, `isCut_lrCut`;
  - the boundary lemma `cutCol_lt`;
  - `lrSwap_lrSwap`, `isFirstViolation_lrSwap`, `weight_lrSwapB`.
-/
