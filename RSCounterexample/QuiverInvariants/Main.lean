import RSCounterexample.QuiverInvariants.Generic
import RSCounterexample.QuiverInvariants.Basic
import RSCounterexample.QuiverInvariants.Ringel
import RSCounterexample.QuiverInvariants.HomParam
import RSCounterexample.QuiverInvariants.NormalForm
import RSCounterexample.QuiverInvariants.Schofield
import RSCounterexample.QuiverInvariants.King
import RSCounterexample.QuiverInvariants.Positivity
import RSCounterexample.QuiverInvariants.Determinantal
import RSCounterexample.QuiverInvariants.Saturation

/-!
# Semi-invariants of quivers and the saturation property

This library proves the theorem of Derksen and Weyman that the weights of semi-invariants of a
quiver without oriented cycles are saturated, following Baldoni, Vergne and Walter (*Quiver
subrepresentations and the Derksen–Weyman saturation property*, 2025), over any infinite field.
It depends only on Mathlib and on `RSCounterexample.GLRep.Polynomial.Functions`. This file imports all of
it and indexes the main results; `RSCounterexample/QuiverInvariants/Audit.lean` prints the axioms they
depend on.

Representations of a forward quiver `Q` live on typed vertex families `ι : Fin Q.s → Type`, and
a dimension vector is `n = dim ι`. "General" is understood in the Zariski-dense sense: a
property of general representations is one whose locus is not contained in the zero set of a
nonzero polynomial.

## Generic points

* Dense sets and principal open sets of affine space (`QuiverInvariants.ZariskiDense`,
  `QuiverInvariants.principalOpen`), and the filter of sets containing a nonempty principal open
  set (`QuiverInvariants.genericFilter`): a dense set meets every generic condition
  (`QuiverInvariants.ZariskiDense.exists_of_eventually`).
* Images under polynomial maps with dense image, products and projections
  (`QuiverInvariants.ZariskiDense.image`, `QuiverInvariants.IsPolynomialMap.tendsto_genericFilter`,
  `QuiverInvariants.ZariskiDense.sumElim`, `QuiverInvariants.ZariskiDense.preimage_comp`,
  `QuiverInvariants.eventually_exists_left`).
* A matrix has rank at least `r` if and only if one of its `r × r` minors is nonzero
  (`QuiverInvariants.le_rank_iff_exists_det_submatrix_ne_zero`), and a matrix of polynomials
  attains its generic rank on a nonempty principal open set
  (`QuiverInvariants.exists_minor_genericRank`, `QuiverInvariants.eventually_rank_eq_genericRank`).

## Representations, `hom` and `ext`

* Forward quivers, representations, the action of `∏_p GL(K^{ι p})`, semi-invariants and the
  Euler form (`QuiverInvariants.FQuiver`, `QuiverInvariants.FQuiver.act`,
  `QuiverInvariants.FQuiver.IsSemiInvariant`, `QuiverInvariants.FQuiver.euler`).
* Subrepresentations and quotients, and their general dimensions
  (`QuiverInvariants.FQuiver.HasQuotientOfDim`, `QuiverInvariants.FQuiver.GeneralQuot`).
* The Ringel map `d_{V,W}`, whose kernel and cokernel give `hom` and `ext`
  (`QuiverInvariants.FQuiver.ringel`, `QuiverInvariants.FQuiver.homDim`,
  `QuiverInvariants.FQuiver.extDim`), with `hom − ext = ⟨dim V, dim W⟩`
  (`QuiverInvariants.FQuiver.homDim_sub_extDim`).
* Generic values of `hom` and `ext`, and hom-generic pairs
  (`QuiverInvariants.FQuiver.genericHom`, `QuiverInvariants.FQuiver.genericExt`,
  `QuiverInvariants.FQuiver.IsHomGeneric`, `QuiverInvariants.FQuiver.eventually_isHomGeneric`).
* At a hom-generic pair, homomorphisms are unobstructed, and dividing by the image of a
  homomorphism does not change `ext`
  (`QuiverInvariants.FQuiver.IsHomGeneric.hom_mul_mem_range`,
  `QuiverInvariants.FQuiver.IsHomGeneric.extDim_blockRep_eq`).

## Schofield's formula for general extensions

* Normal forms of homomorphisms, transitivity of general quotients and the cokernel step
  (`QuiverInvariants.FQuiver.exists_normalForm`,
  `QuiverInvariants.FQuiver.GeneralQuot.of_generalSub`,
  `QuiverInvariants.FQuiver.exists_cokernelStep`).
* **Schofield's formula** `ext(α, β) = max {−⟨α, β″⟩ : β ↠ β″}`
  (`QuiverInvariants.FQuiver.exists_generalQuot_euler_add_extDim_nonpos`,
  `QuiverInvariants.FQuiver.neg_genericExt_le_euler`,
  `QuiverInvariants.FQuiver.isGreatest_genericExt`), and the criterion used below: if
  `⟨α, β″⟩ ≥ 0` whenever `β ↠ β″`, some Ringel map is onto
  (`QuiverInvariants.FQuiver.exists_extDim_eq_zero`). The proof uses only polynomial identities,
  ranks, minors and Zariski density.

## King's inequalities

A nonzero semi-invariant of weight `σ` on representations of dimension `n` satisfies
`∑_p σ_p n_p = 0` (`QuiverInvariants.FQuiver.IsSemiInvariant.sum_mul_card_eq_zero`) and
`∑_p σ_p β_p ≥ 0` for every general quotient dimension `β`
(`QuiverInvariants.FQuiver.IsSemiInvariant.sum_mul_nonneg_of_generalQuot`), proved with
one-parameter subgroups adapted to a subrepresentation
(`QuiverInvariants.FQuiver.act_oneParam`).

## Positivity

If `∑_p σ_p β_p ≥ 0` for every general quotient dimension `β`, the dimension vector attached to
`σ` is nonnegative (`QuiverInvariants.FQuiver.liftWeight_nonneg_of_generalQuot`; Lemma 4.4 of
Baldoni–Vergne–Walter, with vertices of dimension `0` allowed). The general quotients used are
those generated by a covector (`QuiverInvariants.FQuiver.generalQuot_genericQuotDim`).

## Determinantal semi-invariants

If `⟨dim ι, dim κ⟩ = 0`, the determinant `c^V(W) = det d_{V,W}` is a semi-invariant of weight
`L(dim ι)` (`QuiverInvariants.FQuiver.isSemiInvariant_detSemiInvariant`), nonzero when
`ext(V, W) = 0` for some `W` (`QuiverInvariants.FQuiver.detSemiInvariant_ne_zero`).

## Semi-invariants and saturation

* **Theorem 4.2 of Baldoni–Vergne–Walter**: a nonzero semi-invariant of weight `σ` exists if and
  only if `∑_p σ_p n_p = 0` and `∑_p σ_p β_p ≥ 0` for every general quotient dimension `β`
  (`QuiverInvariants.FQuiver.exists_semiInvariant_iff`). This is the equivalence of King's
  inequalities with the existence of a semi-invariant.
* **Saturation**: a nonzero semi-invariant of weight `N • σ`, `N > 0`, gives one of weight `σ`
  (`QuiverInvariants.FQuiver.exists_semiInvariant_of_nsmul`).
-/
