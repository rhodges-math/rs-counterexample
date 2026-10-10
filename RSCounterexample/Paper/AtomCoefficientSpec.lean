import RSCounterexample.Paper.AtomCoefficients
import RSCounterexample.Paper.JosephPolo.GeneralTheorem
import RSCounterexample.Paper.PBW.Theorem

/-!
# The atom coefficients

`Schubert.RS.atomCoefficient f u` is defined as an explicit sum of rectangle coefficients
(`Schubert.RS.integralAtomExpansion`). This file states what it means, with no hypotheses: every
polynomial is the `ℤ`-combination of atoms `𝒜_u` with coefficients `atomCoefficient f u`, and this
expansion is unique, so `atomCoefficient f u = [𝒜_u] f`. It also states Lemma 2.4 of the paper
(`atomCoefficient f c` is the rectangle coefficient in any box containing `c`) without hypotheses.

The general statements in `RSCounterexample.Paper.AtomCoefficients` take the Joseph–Polo presentation, the
Demazure character formula of the composition flag modules and the ordered PBW basis as arguments.
Here they are instantiated with the proved theorems
`Schubert.RS.Representation.compositionFlagJosephPolo`,
`Schubert.RS.Representation.compositionFlagDemazureCharacter` and
`Schubert.RS.PBW.orderedPBWBasis_exists`.

## Main results

* `Schubert.RS.atomCoefficient_spec`: `f = ∑_u [𝒜_u]f · 𝒜_u`.
* `Schubert.RS.eq_integralAtomExpansion_of_expansion`,
  `Schubert.RS.atomCoefficient_eq_of_expansion`: uniqueness of the atom expansion.
* `Schubert.RS.existsUnique_integralAtomExpansion`.
* `Schubert.RS.atomCoefficient_atom`: `[𝒜_u] 𝒜_v = δ_{uv}`.
* `Schubert.RS.atomCoefficient_eq_rectangleCoefficient'`: Lemma 2.4.
-/

namespace Schubert.RS

open Representation PBW

variable {n : ℕ}

/-- **Every polynomial is the `ℤ`-combination of atoms with coefficients `atomCoefficient f u`**:
`f = ∑_u [𝒜_u]f · 𝒜_u`. -/
theorem atomCoefficient_spec (f : Polynomial n) :
    f = (integralAtomExpansion f).sum (fun u z => z • atom u) :=
  integralAtomExpansion_spec (fun u => compositionFlagJosephPolo u)
    (fun u => compositionFlagDemazureCharacter u) (orderedPBWBasis_exists n) f

/-- **The atom expansion is unique.** -/
theorem eq_integralAtomExpansion_of_expansion (f : Polynomial n) (t : Composition n →₀ ℤ)
    (ht : f = t.sum (fun u z => z • atom u)) : t = integralAtomExpansion f :=
  integralAtomExpansion_unique (fun u => compositionFlagJosephPolo u)
    (fun u => compositionFlagDemazureCharacter u) (orderedPBWBasis_exists n) f t ht

/-- **`atomCoefficient f u` is the coefficient of `𝒜_u` in any `ℤ`-atom expansion of `f`.** -/
theorem atomCoefficient_eq_of_expansion (f : Polynomial n) (t : Composition n →₀ ℤ)
    (ht : f = t.sum (fun u z => z • atom u)) (u : Composition n) : atomCoefficient f u = t u := by
  rw [eq_integralAtomExpansion_of_expansion f t ht]
  rfl

/-- Every polynomial has a unique `ℤ`-atom expansion. -/
theorem existsUnique_integralAtomExpansion (f : Polynomial n) :
    ∃! t : Composition n →₀ ℤ, f = t.sum (fun u z => z • atom u) :=
  existsUnique_integral_atom_expansion (fun u => compositionFlagJosephPolo u)
    (fun u => compositionFlagDemazureCharacter u) (orderedPBWBasis_exists n) f

/-- The atom coefficients of an atom: `[𝒜_u] 𝒜_v = δ_{uv}`. -/
theorem atomCoefficient_atom (u v : Composition n) :
    atomCoefficient (atom v) u = if v = u then 1 else 0 := by
  rw [atomCoefficient_eq_of_expansion (atom v) (Finsupp.single v 1) (by simp) u,
    Finsupp.single_apply]

/-- **Lemma 2.4**: for every box `w` containing `c`, the atom coefficient `[𝒜_c] f` is the
rectangle coefficient of `f` in the box `w`. -/
theorem atomCoefficient_eq_rectangleCoefficient' (w : ℕ) (c : Composition n) (hc : ∀ i, c i ≤ w)
    (f : Polynomial n) : atomCoefficient f c = rectangleCoefficient w c f :=
  atomCoefficient_eq_rectangleCoefficient (fun u => compositionFlagJosephPolo u)
    (fun u => compositionFlagDemazureCharacter u) (orderedPBWBasis_exists n) w c hc f

end Schubert.RS
