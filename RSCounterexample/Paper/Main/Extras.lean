import RSCounterexample.Paper.Family.Extras

/-!
# Endpoints: Theorem 1.1 extras

All in namespace `Schubert.RS.Family` (files `Family/Narayana.lean`, `Family/Extras.lean`).

* (1.6), Narayana form: `atomCoefficient_eq_narayana`.
* (1.6), both displayed expressions, in `ℚ`: `atomCoefficient_eq_paper`.
* `N(p+q-1, p) = ((p+q-1)/(pq))·C(p+q-2, p-1)²`: `narayana_family`, `narayana_eq_rat`.
* `(p, q) = (3, 5)`, `(4, 4)`, `(5, 3)` give `-105`, `-350`, `-105` in `28` variables for every
  `δ ≥ 8`: `atomCoefficient_threeFive`, `atomCoefficient_fourFour`, `atomCoefficient_fiveThree`.
* A negative coefficient forces `p + q ≥ 8`: `eight_le_of_atomCoefficient_neg`.
* At `p + q = 8` exactly `(3, 5)`, `(4, 4)`, `(5, 3)` are negative:
  `atomCoefficient_neg_iff_of_sum_eight`.
* The first negative cases within the family occur in `28` variables: `isLeast_rank_of_negative`.
-/
