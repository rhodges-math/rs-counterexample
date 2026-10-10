import RSCounterexample.FlagVarieties.Bruhat.Order
import RSCounterexample.FlagVarieties.Bruhat.Schemes
import RSCounterexample.FlagVarieties.Bruhat.CoxeterBruhat
import RSCounterexample.FlagVarieties.Bruhat.Dimension.Schubert

/-!
# Bruhat cells and Bruhat orders

* `Order` (namespace `FlagVarieties.Bruhat`): the rank-matrix order `≤ᴮ` equals the subword order
  (`strongBruhatLE_iff_subwordLE`, any reduced word: `strongBruhatLE_iff_of_reduced`) and the
  tableau order (`strongBruhatLE_iff_galeLE`). The type-A reduced-subword criterion is in
  `RSCounterexample/TypeA/Permutations/RankSubwordCriterion`.
* `Coxeter` (namespace `FlagVarieties.Bruhat`): the Coxeter presentation of `S_{n+1}`,
  `permCoxeterSystem n : CoxeterSystem (CoxeterMatrix.A n) (Equiv.Perm (Fin (n + 1)))` (simple
  reflections the adjacent transpositions, `|W(A_n)| ≤ (n + 1)!` by a coset decomposition), with
  Coxeter length the number of inversions (`length_eq`), and the rank-matrix order as the
  reduced-subword order of this Coxeter system (`strongBruhatLE_iff_exists_reduced_sublist`).
* `Dimension/` (namespace `FlagVarieties.Dimension`): **`topologicalKrullDim_schubertVariety`:
  `dim X_w = ℓ(w)`** for the closed subscheme, over an algebraically closed field of characteristic
  `0`. General tools: `ringKrullDim_eq_of_isIntegral`, `exists_ringKrullDim_eq_trdeg` (affine
  domains: dimension = transcendence degree), `ringKrullDim_localization_eq`,
  `topologicalKrullDim_le_of_forall` (dimension is local), `topologicalKrullDim_eq_ringKrullDim`
  (an integral scheme locally of finite type over a field has the dimension of any nonempty affine
  open), `isIntegral_image`, `specIdeal_comap_spec_map`.
* `CoxeterBruhat`: **`bruhatLE_iff_strongBruhatLE`**: Tau Ceti's Coxeter Bruhat order
  `(permCoxeterSystem n).BruhatLE` is the rank-matrix order `≤ᴮ`.
* `Cells` (namespace `FlagVarieties.PointModel`, over a field `K`):
  disjointness of the cells (`eq_of_mem_bruhatCell`); `π⁻¹ X_w(K) = ⊔_{v ≤ w} B v̇ B`
  (`forall_cellIdeal_iff`); `X_v ⊆ X_w ⟺ v ≤ w` (`cellIdeal_le_cellIdeal_iff`);
  `C_w(K) ≃ K^{ℓ(w)}` through the normal form `cellPoint w y · b` (`exists_cellPoint_mul`,
  `eq_of_cellPoint_mul`, `card_cellVar`); scheme-theoretically on the chart `ẇ U⁻`, `C_w` is the
  coordinate subspace (`map_kazhdanLusztigSubst_fultonIdeal_self`) with coordinate ring a polynomial
  ring in `ℓ(w)` variables (`cellRingEquiv`) and Krull dimension `ℓ(w)`
  (`ringKrullDim_kazhdanLusztigPatch_self`).
* `Schemes`: the same statements for the scheme-level Schubert varieties, using
  `preimageIdeal_schubertVariety_eq_schubertOrbitIdeal` and descent (`le_of_preimageIdeal_le`).
-/
