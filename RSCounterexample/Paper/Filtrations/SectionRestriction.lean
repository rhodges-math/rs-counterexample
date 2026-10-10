import RSCounterexample.Paper.SchubertUnions.OrbitDuality
import RSCounterexample.Paper.Filtrations.SectionModules

/-!
# Sections over unions of Schubert varieties as restrictions of global sections

The section module `H⁰(X_S, 𝓛(k·1 − λ))` is modelled as the twisted dual of the sum
`D_S = Σ_{w ∈ S} D_w(λ)` of Demazure modules (`sectionModuleOf`). Let `h` be a column sequence
of shape `λ`. The flag-minor products `flagColumnProduct h T` span the global sections in the
Borel–Weil model, and the union of the orbits `U·w`, `w ∈ S`, is dense in `X_S`.

* The underlying space of the section module is the span of the restrictions of the flag-minor
  products to the union of the orbits (`sectionModuleOf_restrictionEquiv`).
* The identification sends a section to its values at the orbit points `u·v_w`
  (`sectionModuleOf_restrictionEquiv_apply`).
* It carries the restriction of sections from `X_S` to `X_{S'} ⊆ X_S` to evaluation at the
  orbit points of `S'` (`sectionModuleOf_restrictionEquiv_restrictSections`).
-/

namespace Schubert.RS.Filtrations

open Representation BModules FinPermutation SchubertUnions

noncomputable section

variable {n d : ℕ}

/-- **Sections over `X_S` as restrictions of global sections.** For a column sequence `h` of
shape `λ`, the underlying space of `H⁰(X_S, 𝓛(k·1 − λ))` is the span of the restrictions of the
flag-minor products `flagColumnProduct h T` to the union of the orbits `U·w`, `w ∈ S`. -/
def sectionModuleOf_restrictionEquiv (k : ℕ) (dom : Composition n) (h : Fin d → Fin n)
    (hm : columnMultiplicity h = columnsOfWeight dom) (S : Finset (FinPermutation n)) :
    sectionModuleOf k dom S ≃ₗ[ℂ]
      Submodule.span ℂ (Set.range fun T : (j : Fin d) → FlagMinorRowSet (h j) =>
        unionRestriction S (flagColumnProduct h T)) :=
  (LinearEquiv.ofEq _ _ (congrArg (demazureUnion · S) hm)).dualMap.trans
    (demazureUnionDuality h S)

/-- The identification of `sectionModuleOf_restrictionEquiv` evaluates a section at the orbit
points `u·v_w`. -/
theorem sectionModuleOf_restrictionEquiv_apply (k : ℕ) (dom : Composition n)
    (h : Fin d → Fin n) (hm : columnMultiplicity h = columnsOfWeight dom)
    (S : Finset (FinPermutation n)) (s : Module.Dual ℂ (demazureUnion (columnsOfWeight dom) S))
    (x : UnionOrbit S)
    (hx : unionOrbitVector (columnMultiplicity h) S x ∈ demazureUnion (columnsOfWeight dom) S) :
    (sectionModuleOf_restrictionEquiv k dom h hm S s : UnionOrbit S → ℂ) x = s ⟨_, hx⟩ :=
  rfl

/-- Restricting a section from `X_S` to `X_{S'}` and evaluating at an orbit point of `S'` is
evaluating the original section at that point. -/
theorem sectionModuleOf_restrictionEquiv_restrictSections (k : ℕ) (dom : Composition n)
    (h : Fin d → Fin n) (hm : columnMultiplicity h = columnsOfWeight dom)
    {S S' : Finset (FinPermutation n)}
    (hSS' : demazureUnion (columnsOfWeight dom) S' ≤ demazureUnion (columnsOfWeight dom) S)
    (s : Module.Dual ℂ (demazureUnion (columnsOfWeight dom) S)) (x : UnionOrbit S')
    (hx : unionOrbitVector (columnMultiplicity h) S' x ∈ demazureUnion (columnsOfWeight dom) S) :
    (sectionModuleOf_restrictionEquiv k dom h hm S'
        ((restrictSectionsOf k dom hSS').toLinearMap s) : UnionOrbit S' → ℂ) x = s ⟨_, hx⟩ :=
  rfl

/-- Every section module over a union of Schubert varieties is a space of restrictions of
flag-minor products to the union of the orbits. -/
theorem schubertSectionModule_restrictions (η : Weight n) (S : Finset (FinPermutation n)) :
    ∃ (d : ℕ) (h : Fin d → Fin n), columnMultiplicity h = columnsOfWeight (weightComplement η) ∧
      Nonempty (schubertSectionModule η S ≃ₗ[ℂ]
        Submodule.span ℂ (Set.range fun T : (j : Fin d) → FlagMinorRowSet (h j) =>
          unionRestriction S (flagColumnProduct h T))) := by
  obtain ⟨d, h, hm⟩ := exists_columnMultiplicity (columnsOfWeight (weightComplement η))
  exact ⟨d, h, hm, ⟨sectionModuleOf_restrictionEquiv _ _ h hm S⟩⟩

end

end Schubert.RS.Filtrations
