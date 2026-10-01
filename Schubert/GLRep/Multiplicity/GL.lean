import Schubert.GLRep.Multiplicity.Hom
import Schubert.GLRep.HighestWeight.CompleteReducibility
import Schubert.GLRep.HighestWeight.WeylModule
import TauCeti.RepresentationTheory.Irreducible

/-!
# Multiplicities of the irreducible polynomial representations of `GL_n`

Let `ρ` be a polynomial representation of `GL_n(K)`, `K` a field of characteristic zero. The
**multiplicity** of `V(μ)` in `ρ` is `dim Hom(V(μ), ρ)` (`GLRep.multiplicity`). The character of
`ρ` is the sum of the Schur polynomials `s_μ` weighted by these multiplicities
(`GLRep.IsPolynomialRep.exists_character_eq_sum`):

`ch ρ = ∑_μ dim Hom(V(μ), ρ) · s_μ`.

The proof is an induction on the dimension: `ρ` is semisimple, so it is the product of an
irreducible subrepresentation, equivalent to some `V(μ₀)`, and a complement; multiplicities add
over products, and `dim Hom(V(μ), V(μ₀))` is `1` or `0` by Schur's lemma.

## Main definitions

* `GLRep.multiplicity ρ μ`: `dim Hom(V(μ), ρ)`.

## Main results

* `GLRep.multiplicity_prod`, `GLRep.multiplicity_eq_of_equiv`, `GLRep.multiplicity_irrep`.
* `GLRep.IsPolynomialRep.exists_character_eq_sum`.
-/

namespace GLRep

open Module Representation

noncomputable section

variable {K : Type*} [Field K] {n : ℕ}
variable {W : Type*} [AddCommGroup W] [Module K W] {ρ : Representation K (GL (Fin n) K) W}
variable {V : Type*} [AddCommGroup V] [Module K V] {σ : Representation K (GL (Fin n) K) V}

/-- The intertwining maps as a subspace of the linear maps. -/
def intertwiningMapToLinearMap {G V W : Type*} [Monoid G] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (ρ : Representation K G V) (σ : Representation K G W) :
    IntertwiningMap ρ σ →ₗ[K] V →ₗ[K] W where
  toFun f := f.toLinearMap
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance {G V W : Type*} [Monoid G] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [FiniteDimensional K V] [FiniteDimensional K W] (ρ : Representation K G V)
    (σ : Representation K G W) : FiniteDimensional K (IntertwiningMap ρ σ) :=
  FiniteDimensional.of_injective (intertwiningMapToLinearMap ρ σ) fun _ _ h =>
    IntertwiningMap.ext h

variable [CharZero K]

variable (ρ) in
/-- The **multiplicity** of `V(μ)` in `ρ`: the dimension of `Hom(V(μ), ρ)`. -/
def multiplicity (μ : YoungDiagram) : ℕ := finrank K ((irrep K n μ).IntertwiningMap ρ)

theorem multiplicity_eq_of_equiv (e : ρ.Equiv σ) (μ : YoungDiagram) :
    multiplicity ρ μ = multiplicity σ μ :=
  (intertwiningMapCongrRight e).finrank_eq

theorem multiplicity_prod [FiniteDimensional K W] [FiniteDimensional K V] (μ : YoungDiagram) :
    multiplicity (ρ.prod σ) μ = multiplicity ρ μ + multiplicity σ μ := by
  have := (isPolynomialRep_irrep (K := K) (n := n) μ).finiteDimensional
  exact finrank_intertwiningMap_prod

open Classical in
theorem multiplicity_irrep {μ ν : YoungDiagram} (hμ : μ.colLen 0 ≤ n) (hν : ν.colLen 0 ≤ n) :
    multiplicity (irrep K n ν) μ = if μ = ν then 1 else 0 := by
  split_ifs with h
  · subst h
    exact finrank_intertwiningMap_irrep_self hμ
  · exact finrank_intertwiningMap_irrep_of_ne hμ hν h

theorem multiplicity_eq_zero_of_subsingleton [Subsingleton W] (μ : YoungDiagram) :
    multiplicity ρ μ = 0 := by
  have : Subsingleton ((irrep K n μ).IntertwiningMap ρ) :=
    ⟨fun f g => IntertwiningMap.ext (LinearMap.ext fun _ => Subsingleton.elim _ _)⟩
  exact Module.finrank_zero_of_subsingleton

theorem character_eq_zero_of_subsingleton [Subsingleton W] (h : IsPolynomialRep ρ) :
    character ρ = 0 := by
  ext α
  rw [coeff_character h, Module.finrank_zero_of_subsingleton]
  simp

/-- **The character of a polynomial representation in the Schur basis**: it is the sum of the
Schur polynomials `s_μ` weighted by the multiplicities `dim Hom(V(μ), ρ)`. -/
theorem IsPolynomialRep.exists_character_eq_sum (h : IsPolynomialRep ρ) :
    ∃ S : Finset YoungDiagram, (∀ μ ∈ S, μ.colLen 0 ≤ n) ∧
      (∀ μ : YoungDiagram, μ.colLen 0 ≤ n → μ ∉ S → multiplicity ρ μ = 0) ∧
      character ρ = ∑ μ ∈ S, (multiplicity ρ μ : ℤ) • TauCeti.diagramSchurPoly n ℤ μ := by
  induction hd : finrank K W using Nat.strong_induction_on generalizing W with
  | _ d ih =>
  classical
  have := h.finiteDimensional
  by_cases hW : Subsingleton W
  · exact ⟨∅, by simp, fun μ _ _ => multiplicity_eq_zero_of_subsingleton μ,
      by rw [character_eq_zero_of_subsingleton h, Finset.sum_empty]⟩
  rw [not_subsingleton_iff_nontrivial] at hW
  -- an irreducible subrepresentation and a complement
  have : IsAtomic (Subrepresentation ρ) :=
    (OrderIso.isAtomic_iff h.subrepOrderIso).mpr inferInstance
  obtain ⟨U, hU⟩ : ∃ U : Subrepresentation ρ, IsAtom U := by
    rcases eq_bot_or_exists_atom_le (⊤ : Subrepresentation ρ) with htop | ⟨U, hU, -⟩
    · exfalso
      obtain ⟨w, hw⟩ := exists_ne (0 : W)
      have : w ∈ (⊤ : Subrepresentation ρ) := trivial
      rw [htop] at this
      exact hw this
    · exact ⟨U, hU⟩
  have : ComplementedLattice (Subrepresentation ρ) := h.isSemisimpleRepresentation
  obtain ⟨U', hUU'⟩ := exists_isCompl U
  have e := equivProdOfIsCompl hUU'
  have hUpoly := h.subrepresentation U
  have hU'poly := h.subrepresentation U'
  have hUirr := TauCeti.Representation.isIrreducible_toRepresentation_of_isAtom hU
  obtain ⟨μ₀, hμ₀, ⟨e₀⟩⟩ := IsPolynomialRep.exists_nonempty_equiv_irrep hUpoly hUirr
  -- the complement is smaller
  have hdim : finrank K U.toSubmodule + finrank K U'.toSubmodule = d := by
    rw [← hd, ← Module.finrank_prod, e.toLinearEquiv.finrank_eq]
  have hUpos : 0 < finrank K U.toSubmodule := by
    have : U.toSubmodule ≠ ⊥ := fun hb => hU.1 (Subrepresentation.toSubmodule_injective
      (hb.trans Subrepresentation.toSubmodule_bot.symm))
    exact Nat.pos_of_ne_zero fun h0 => this (Submodule.finrank_eq_zero.mp h0)
  obtain ⟨S', hS'n, hS'z, hS'χ⟩ := ih _ (by omega) hU'poly rfl
  -- multiplicities and characters
  have hmult : ∀ μ : YoungDiagram, μ.colLen 0 ≤ n →
      multiplicity ρ μ = (if μ = μ₀ then 1 else 0) + multiplicity U'.toRepresentation μ := by
    intro μ hμ
    rw [← multiplicity_eq_of_equiv e, multiplicity_prod, multiplicity_eq_of_equiv e₀,
      multiplicity_irrep hμ hμ₀]
  have hchar : character ρ = TauCeti.diagramSchurPoly n ℤ μ₀ + character U'.toRepresentation := by
    rw [← character_eq_of_equiv (hUpoly.prod hU'poly) h e, character_prod hUpoly hU'poly,
      character_eq_of_equiv hUpoly (isPolynomialRep_irrep μ₀) e₀, character_irrep hμ₀]
  refine ⟨insert μ₀ S', fun μ hμ => ?_, fun μ hμ hμS => ?_, ?_⟩
  · rcases Finset.mem_insert.mp hμ with rfl | hμ
    · exact hμ₀
    · exact hS'n μ hμ
  · have hne : μ ≠ μ₀ := fun h => hμS (h ▸ Finset.mem_insert_self _ _)
    rw [hmult μ hμ, hS'z μ hμ (fun h => hμS (Finset.mem_insert_of_mem h))]
    simp [hne]
  · rw [hchar, hS'χ]
    have hsum : ∑ μ ∈ insert μ₀ S', (multiplicity ρ μ : ℤ) • TauCeti.diagramSchurPoly n ℤ μ =
        ∑ μ ∈ insert μ₀ S', ((if μ = μ₀ then 1 else 0 : ℤ) • TauCeti.diagramSchurPoly n ℤ μ +
          (multiplicity U'.toRepresentation μ : ℤ) • TauCeti.diagramSchurPoly n ℤ μ) := by
      refine Finset.sum_congr rfl fun μ hμ => ?_
      have hμn : μ.colLen 0 ≤ n := by
        rcases Finset.mem_insert.mp hμ with rfl | hμ
        · exact hμ₀
        · exact hS'n μ hμ
      rw [hmult μ hμn, ← add_smul]
      push_cast
      split_ifs <;> simp
    rw [hsum, Finset.sum_add_distrib]
    simp only [ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_insert_self,
      ↓reduceIte]
    congr 1
    refine Finset.sum_subset (Finset.subset_insert μ₀ S') fun μ hμ hμS => ?_
    rw [hS'z μ ?_ hμS, Nat.cast_zero, zero_smul]
    rcases Finset.mem_insert.mp hμ with rfl | hμ'
    · exact hμ₀
    · exact absurd hμ' hμS

end

end GLRep
