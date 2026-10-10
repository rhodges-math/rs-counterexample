import RSCounterexample.Paper.Filtrations.DemazureUnions
import RSCounterexample.Paper.JosephPolo.StandardMonomialBound

/-!
# Standard monomials on unions of orbits: the lower bound

Fix an ordered column sequence `h` and the shape `m = columnMultiplicity h`. For a finite set
`S` of permutations, `chainSet h S` is the set of tuples of row sets admitting a defining chain
bounded by some element of `S`.

The dual of `D_S = Σ_{w ∈ S} D_w` is the span of the restrictions of the flag-minor products to
the union of the orbits `U · w`, `w ∈ S` (`demazureUnionDuality`). The restricted products
indexed by `chainSet h S` are linearly independent (REL's standard-monomial independence on
unions). Hence `#chainSet h S ≤ dim D_S` (`card_chainSet_le_finrank`).
-/

namespace Schubert.RS.SchubertUnions

open Representation Filtrations FinPermutation

noncomputable section

variable {n d : ℕ}

/-- The tuples of row sets with a defining chain bounded by some element of `S`. -/
def chainSet (h : Fin d → Fin n) (S : Finset (FinPermutation n)) :
    Finset ((j : Fin d) → FlagMinorRowSet (h j)) := by
  classical exact Finset.univ.filter fun T => ∃ w ∈ S, HasFlagDefiningChain h T w

theorem mem_chainSet {h : Fin d → Fin n} {S : Finset (FinPermutation n)}
    {T : (j : Fin d) → FlagMinorRowSet (h j)} :
    T ∈ chainSet h S ↔ ∃ w ∈ S, HasFlagDefiningChain h T w := by
  classical
  unfold chainSet
  simp

/-- The union of the orbits `U · w`, `w ∈ S`: an element of `S` and a word of elementary upper
unitriangular matrices. -/
abbrev UnionOrbit (S : Finset (FinPermutation n)) := Σ _ : S, List (PositiveRoot n × ℂ)

/-- The orbit point `u_z · v_w` for `(w, z) ∈ UnionOrbit S`. -/
def unionOrbitVector (m : ColumnShape n) (S : Finset (FinPermutation n)) :
    UnionOrbit S → MatrixPolynomial n :=
  fun x => upperRowWord x.2 (extremalFlag m x.1)

theorem demazureUnion_eq_span (m : ColumnShape n) (S : Finset (FinPermutation n)) :
    demazureUnion m S = Submodule.span ℂ (Set.range (unionOrbitVector m S)) := by
  rw [Set.range_sigma_eq_iUnion_range, Submodule.span_iUnion, demazureUnion]
  refine iSup_congr fun w => ?_
  rw [flagDemazure_eq_upperRowOrbitSpan]
  rfl

/-- Restriction of polynomials to the union of orbits. -/
def unionRestriction (S : Finset (FinPermutation n)) :
    MatrixPolynomial n →ₗ[ℂ] (UnionOrbit S → ℂ) where
  toFun f x := flagOrbitRestriction x.1 f x.2
  map_add' f g := by funext x; simp
  map_smul' c f := by funext x; simp

/-- The dual of `D_S` is the span of the restricted flag-minor products. -/
def demazureUnionDuality (h : Fin d → Fin n) (S : Finset (FinPermutation n)) :
    Module.Dual ℂ (demazureUnion (columnMultiplicity h) S) ≃ₗ[ℂ]
      Submodule.span ℂ (Set.range fun T : (j : Fin d) → FlagMinorRowSet (h j) =>
        unionRestriction S (flagColumnProduct h T)) :=
  (LinearEquiv.ofEq _ _ (demazureUnion_eq_span (columnMultiplicity h) S)).symm.dualMap.trans
    (polynomialOrbitDuality (flagColumnProduct h) (flagColumnProduct_real_coeff h)
      (unionRestriction S) (unionOrbitVector (columnMultiplicity h) S)
      (fun x => upperRowWord_columnProduct_sum h x.1 x.2))

/-- The lower bound: the tuples with a defining chain below `S` are at most `dim D_S`. -/
theorem card_chainSet_le_finrank (h : Fin d → Fin n) (S : Finset (FinPermutation n)) :
    (chainSet h S).card ≤ Module.finrank ℂ (demazureUnion (columnMultiplicity h) S) := by
  classical
  let ι := {T // T ∈ chainSet h S}
  have hW : ∀ T : ι, ∃ w ∈ S, HasFlagDefiningChain h T.1 w := fun T => mem_chainSet.mp T.2
  choose W hWS hWc using hW
  have hind := flagColumnProduct_linearIndependent_on_union h (fun T : ι => T.1)
    Subtype.val_injective W hWc
  let Ψ : (UnionOrbit S → ℂ) →ₗ[ℂ] (ι → List (PositiveRoot n × ℂ) → ℂ) :=
    { toFun := fun F j z => F ⟨⟨W j, hWS j⟩, z⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let v : ι → UnionOrbit S → ℂ := fun T => unionRestriction S (flagColumnProduct h T.1)
  have hv : LinearIndependent ℂ v := LinearIndependent.of_comp Ψ hind
  let Sp := Submodule.span ℂ (Set.range fun T : (j : Fin d) → FlagMinorRowSet (h j) =>
    unionRestriction S (flagColumnProduct h T))
  let v' : ι → Sp := fun T => ⟨v T, Submodule.subset_span ⟨T.1, rfl⟩⟩
  have hv' : LinearIndependent ℂ v' := LinearIndependent.of_comp Sp.subtype hv
  let e := demazureUnionDuality h S
  have hv'' := hv'.map' e.symm.toLinearMap (LinearMap.ker_eq_bot.mpr e.symm.injective)
  have hcard := hv''.fintype_card_le_finrank
  rw [Subspace.dual_finrank_eq] at hcard
  simpa [ι, Fintype.card_coe] using hcard

end

end Schubert.RS.SchubertUnions
