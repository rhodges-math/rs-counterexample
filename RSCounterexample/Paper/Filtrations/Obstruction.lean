import RSCounterexample.Paper.Filtrations.Definitions
import RSCounterexample.Paper.Filtrations.SchubertLayerCharacters
import RSCounterexample.Paper.AtomExpansionCertificate

/-!
# The character obstruction to Schubert filtrations

If a `B`-module `M` whose character is a polynomial `f` admits a relative Schubert filtration,
or a Schubert filtration in Polo's sense, then `f` is a nonnegative integral combination of
Demazure atoms (`atomPositive_of_hasRelativeSchubertFiltration`,
`atomPositive_of_hasSchubertFiltration`). This is the argument of the proof of Corollary 1.2
(lines 1553–1577 of the paper; cf. Assaf):

* characters are additive along filtrations;
* the layers have characters `x^{c·1} Σ 𝒜_{u_j}` (shifted sums of atoms): for `Q(ν)` by (1.7),
  and for section modules over unions of Schubert varieties by van der Kallen's
  Proposition 2.3.11, in its character form `schubertSectionModule_hasCharacter`;
* the weights of a layer are weights of `M`, hence have nonpositive entries. Since an atom
  contains its own monomial, every shift lands on an honest weak composition, and each layer
  contributes a sum of atoms.
-/

namespace Schubert.RS

open Representation BModules FinPermutation SchubertUnions

noncomputable section

variable {n : ℕ}

/-! ### Atom positivity -/

theorem AtomPositive.zero : AtomPositive (0 : Polynomial n) := ⟨0, by simp⟩

theorem AtomPositive.add {f g : Polynomial n} (hf : AtomPositive f) (hg : AtomPositive g) :
    AtomPositive (f + g) := by
  obtain ⟨t, rfl⟩ := hf
  obtain ⟨s, rfl⟩ := hg
  refine ⟨t + s, ?_⟩
  rw [Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by simp [add_smul])]

theorem AtomPositive.atom (u : Composition n) : AtomPositive (atom u) :=
  ⟨Finsupp.single u 1, by rw [Finsupp.sum_single_index (by simp), one_smul]⟩

theorem AtomPositive.sum {ι : Type*} (s : Finset ι) (f : ι → Polynomial n)
    (h : ∀ i ∈ s, AtomPositive (f i)) : AtomPositive (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using AtomPositive.zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-! ### Supports of polynomials -/

/-- The Laurent coefficients of a polynomial vanish off the nonnegative orthant. -/
theorem nonneg_of_toLaurent_coeff_ne_zero (p : Polynomial n) (w : Weight n)
    (h : (toLaurent p).coeff w ≠ 0) (i : Fin n) : 0 ≤ w i := by
  by_contra hw
  apply h
  rw [MvPolynomial.as_sum p, map_sum, AddMonoidAlgebra.coeff_sum, Finset.sum_apply']
  refine Finset.sum_eq_zero fun d _ => ?_
  rw [toLaurent_monomial, AddMonoidAlgebra.coeff_single, Finsupp.single_apply, ite_eq_right]
  intro hd
  apply hw
  rw [← hd]
  exact Int.natCast_nonneg _

/-! ### Shifting atoms by multiples of `(1, …, 1)` -/

theorem compositionMonomial_add (a b : Composition n) :
    compositionMonomial (fun i => a i + b i) = compositionMonomial a * compositionMonomial b := by
  have h : (Finsupp.equivFunOnFinite.symm fun i => a i + b i) =
      Finsupp.equivFunOnFinite.symm a + Finsupp.equivFunOnFinite.symm b :=
    Finsupp.ext fun i => by simp
  rw [compositionMonomial, compositionMonomial, compositionMonomial,
    MvPolynomial.monomial_mul_monomial, mul_one, h]

theorem atomOperator_mul_symmetric (i : AdjacentPosition n) (p q : Polynomial n)
    (hp : Schubert.adjacentVariableSwap i p = p) :
    atomOperator i (p * q) = p * atomOperator i q := by
  rw [atomOperator, atomOperator, isobaric_mul_of_symmetric i p q hp, mul_sub]

/-- `𝒜_{u + c·1} = (x₁ ⋯ xₙ)^c 𝒜_u`. -/
theorem atom_add_const (u : Composition n) (c : ℕ) :
    atom (fun i => u i + c) = compositionMonomial (fun _ => c) * atom u := by
  induction u using (measure sortingMeasure).wf.induction with
  | h u ih =>
    by_cases ha : (ascentSet u).Nonempty
    · let i := firstAscent u ha
      have hi : u i.left < u i.right := firstAscent_lt u ha
      have hic : (fun j => u j + c) i.left < (fun j => u j + c) i.right := by
        simp only; omega
      have hswap : swapComposition (fun j => u j + c) i = fun j => swapComposition u i j + c :=
        rfl
      rw [atom_any_ascent _ i hic, hswap, ih _ (sortingMeasure_swap_lt u i hi),
        atom_any_ascent u i hi]
      exact atomOperator_mul_symmetric i _ _ (compositionMonomial_symmetric _ i rfl)
    · have hna : ¬ (ascentSet (fun j => u j + c)).Nonempty := by
        rintro ⟨j, hj⟩
        apply ha
        refine ⟨j, ?_⟩
        simp only [ascentSet, Finset.mem_filter] at hj ⊢
        exact ⟨hj.1, by omega⟩
      rw [atom_of_no_ascent _ hna, atom_of_no_ascent u ha, mul_comm]
      exact compositionMonomial_add u (fun _ => c)

theorem constWeight_add (a b : ℤ) :
    (BModule.constWeight a : Weight n) + BModule.constWeight b = BModule.constWeight (a + b) := rfl

/-- If `u' = u + c·(1,…,1)`, then `𝒜_{u'} = x^{c·1} 𝒜_u` as Laurent polynomials. -/
theorem toLaurent_atom_shift (u u' : Composition n) (c : ℤ) (h : ∀ i, (u' i : ℤ) = u i + c) :
    toLaurent (atom u') =
      AddMonoidAlgebra.single (BModule.constWeight c) 1 * toLaurent (atom u) := by
  rcases le_or_gt 0 c with hc | hc
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hc
    have hu' : u' = fun i => u i + k := funext fun i => by have := h i; omega
    rw [hu', atom_add_const, map_mul, toLaurent_compositionMonomial]
    rfl
  · let k := (-c).toNat
    have hk : (k : ℤ) = -c := Int.toNat_of_nonneg (by omega)
    have hu : u = fun i => u' i + k := funext fun i => by have := h i; omega
    rw [hu, atom_add_const, map_mul, toLaurent_compositionMonomial, ← mul_assoc,
      AddMonoidAlgebra.single_mul_single, mul_one]
    have : BModule.constWeight c + (fun _ => (k : ℤ)) = (0 : Weight n) := by
      funext i
      simp only [BModule.constWeight, Pi.add_apply, Pi.zero_apply, hk]
      ring
    rw [this, ← AddMonoidAlgebra.one_def, one_mul]

/-! ### Shifted sums of atoms -/

/-- A Laurent polynomial `x^{c·1} Σ_{τ ∈ J} 𝒜_{u τ}`. -/
def IsShiftedAtomSum (g : Laurent n) : Prop :=
  ∃ (c : ℤ) (J : Finset (FinPermutation n)) (u : FinPermutation n → Composition n),
    g = AddMonoidAlgebra.single (BModule.constWeight c) 1 * ∑ τ ∈ J, toLaurent (atom (u τ))

theorem IsShiftedAtomSum.shift {g : Laurent n} (hg : IsShiftedAtomSum g) (j : ℤ) :
    IsShiftedAtomSum (AddMonoidAlgebra.single (BModule.constWeight j) 1 * g) := by
  obtain ⟨c, J, u, rfl⟩ := hg
  refine ⟨j + c, J, u, ?_⟩
  rw [← mul_assoc, AddMonoidAlgebra.single_mul_single, mul_one, constWeight_add]

/-- A shifted sum of atoms supported in the nonnegative orthant is a sum of atoms. -/
theorem exists_atomPositive_of_isShiftedAtomSum {g : Laurent n} (hg : IsShiftedAtomSum g)
    (hsupp : ∀ w, g.coeff w ≠ 0 → ∀ i, 0 ≤ w i) : ∃ f, AtomPositive f ∧ g = toLaurent f := by
  classical
  obtain ⟨c, J, u, rfl⟩ := hg
  have hnn : ∀ τ ∈ J, ∀ i, 0 ≤ (u τ i : ℤ) + c := by
    intro τ hτ i
    have hcoeff : (AddMonoidAlgebra.single (BModule.constWeight c) 1 *
        ∑ τ ∈ J, toLaurent (atom (u τ))).coeff
          (BModule.constWeight c + fun i => (u τ i : ℤ)) ≠ 0 := by
      rw [laurent_coefficient_shift, AddMonoidAlgebra.coeff_sum, Finset.sum_apply']
      have hle := Finset.single_le_sum (f := fun τ' => (toLaurent (atom (u τ'))).coeff
        (fun i => (u τ i : ℤ))) (fun τ' _ => Filtrations.atom_coeff_nonneg (u τ') _) hτ
      rw [Filtrations.atom_coeff_self] at hle
      intro h0
      omega
    have := hsupp _ hcoeff i
    simp only [Pi.add_apply, BModule.constWeight] at this
    omega
  let u' : FinPermutation n → Composition n := fun τ i => ((u τ i : ℤ) + c).toNat
  refine ⟨∑ τ ∈ J, atom (u' τ), AtomPositive.sum _ _ fun τ _ => AtomPositive.atom _, ?_⟩
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ hτ => ?_
  refine (toLaurent_atom_shift (u τ) (u' τ) c fun i => ?_).symm
  exact Int.toNat_of_nonneg (hnn τ hτ i)

/-! ### The obstruction -/

/-- If every layer of a filtration of `M` has a shifted sum of atoms as character, and the
character of `M` is a polynomial `f`, then `f` is atom positive. -/
theorem atomPositive_of_filtration {M : BModule n} (F : BFiltration M) {f : Polynomial n}
    (hM : M.HasCharacter (toLaurent f))
    (hF : ∀ i < F.length, ∃ g, (F.layer i).HasCharacter g ∧ IsShiftedAtomSum g) :
    AtomPositive f := by
  classical
  choose! g hg hgs using hF
  have hsupp : ∀ i < F.length, ∀ w, (g i).coeff w ≠ 0 → ∀ j, 0 ≤ w j := by
    intro i hi w hw
    have h1 := hg i hi (-w)
    rw [neg_neg] at h1
    have hle := F.finrank_layer_weightSpace_le (-w) hi
    have h2 := hM (-w)
    rw [neg_neg] at h2
    apply nonneg_of_toLaurent_coeff_ne_zero f w
    rw [← h2]
    intro h0
    have : Module.finrank ℂ ((F.layer i).weightSpace (-w)) = 0 := by omega
    rw [this, Nat.cast_zero] at h1
    exact hw h1.symm
  choose! f' hf' hgf using fun i hi => exists_atomPositive_of_isShiftedAtomSum (hgs i hi)
    (hsupp i hi)
  have hsum := F.hasCharacter_sum g fun i hi => hg i hi
  have heq : toLaurent f = toLaurent (∑ i ∈ Finset.range F.length, f' i) := by
    rw [hM.unique hsum, map_sum]
    exact Finset.sum_congr rfl fun i hi => hgf i (Finset.mem_range.mp hi)
  rw [toLaurent_injective heq]
  exact AtomPositive.sum _ _ fun i hi => hf' i (Finset.mem_range.mp hi)

namespace Filtrations

theorem isShiftedAtomSum_minRelSchubert (ν : Weight n) :
    IsShiftedAtomSum (AddMonoidAlgebra.single (-BModule.constWeight (weightShift ν : ℤ)) 1 *
      toLaurent (atom (weightComplement ν))) :=
  ⟨-(weightShift ν : ℤ), {Equiv.refl _}, fun _ => weightComplement ν, by
    rw [Finset.sum_singleton]; rfl⟩

theorem isShiftedAtomSum_schubertSectionModule (η : Weight n)
    (S : Finset (FinPermutation n)) :
    IsShiftedAtomSum (AddMonoidAlgebra.single (-BModule.constWeight (weightShift η : ℤ)) 1 *
        ∑ τ ∈ (lowerClosure S).filter (IsMinCosetRep (weightComplement η)),
          toLaurent (atom (permAct τ (weightComplement η)))) :=
  ⟨-(weightShift η : ℤ), _, fun τ => permAct τ (weightComplement η), rfl⟩

/-- A layer isomorphic to some `Q(ν)` has a shifted sum of atoms as character. -/
theorem exists_isShiftedAtomSum_of_minRelSchubertLayer {L : BModule n}
    (hL : IsMinRelSchubertLayer L) : ∃ g, L.HasCharacter g ∧ IsShiftedAtomSum g := by
  obtain ⟨ν, ⟨e⟩⟩ := hL
  exact ⟨_, (minRelSchubert_hasCharacter_general ν).of_iso e.symm,
    isShiftedAtomSum_minRelSchubert ν⟩

/-- A layer isomorphic to a section module over a union of Schubert varieties has a shifted
sum of atoms as character. -/
theorem exists_isShiftedAtomSum_of_schubertLayer {L : BModule n} (hL : IsSchubertLayer L) :
    ∃ g, L.HasCharacter g ∧ IsShiftedAtomSum g := by
  obtain ⟨η, S, hη, -, ⟨e⟩⟩ := hL
  exact ⟨_, (schubertSectionModule_hasCharacter η hη S).of_iso e.symm,
    isShiftedAtomSum_schubertSectionModule η S⟩

/-- **Relative Schubert filtrations force atom positivity.** If `M` has character `f` and admits
a relative Schubert filtration, then `f` is a nonnegative integral combination of Demazure
atoms. -/
theorem atomPositive_of_hasRelativeSchubertFiltration {M : BModule n} {f : Polynomial n}
    (hM : M.HasCharacter (toLaurent f)) (hF : HasRelativeSchubertFiltration M) :
    AtomPositive f := by
  obtain ⟨F, hF⟩ := hF
  exact atomPositive_of_filtration F hM fun i hi =>
    exists_isShiftedAtomSum_of_minRelSchubertLayer (hF i hi)

/-- **Schubert filtrations in Polo's sense force atom positivity.** -/
theorem atomPositive_of_hasSchubertFiltration {M : BModule n} {f : Polynomial n}
    (hM : M.HasCharacter (toLaurent f)) (hF : HasSchubertFiltration M) : AtomPositive f := by
  obtain ⟨F, hF⟩ := hF
  exact atomPositive_of_filtration F hM fun i hi =>
    exists_isShiftedAtomSum_of_schubertLayer (hF i hi)

end Filtrations

end

end Schubert.RS
