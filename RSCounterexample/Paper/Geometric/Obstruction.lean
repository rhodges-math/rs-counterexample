import RSCounterexample.FlagVarieties.Modules.Character
import RSCounterexample.GLRep.Borel.SpecialLinear
import RSCounterexample.Paper.Filtrations.Obstruction

/-!
# The character obstruction for rational representations of the Borel subgroup

This is the argument of the proof of Corollary 1.2 of the paper (lines 1553–1577), for rational
representations of the Borel subgroup `B ⊆ GL_n(K)` (`GLRep.IsRationalBorelRep`) over an infinite
field and their filtrations by subrepresentations (`GLRep.RepFiltration`). It is the same argument
as `Schubert.RS.atomPositive_of_filtration` for RS's module model:

* characters are additive along filtrations (`FlagVarieties.RepFiltration.ch_eq_sum`);
* the weights of a layer are weights of the filtered representation, so if the character of the
  representation is a polynomial `f`, the character of each layer is supported in the
  nonnegative orthant;
* a shifted sum of atoms `x^{c·1} ∑ 𝒜_u` supported in the nonnegative orthant is a sum of atoms
  (`Schubert.RS.exists_atomPositive_of_isShiftedAtomSum`).

Characters are taken in the paper's convention `ch M = ∑_μ dim M_μ · x^{−μ}` (`FlagVarieties.ch`).

For the special linear group (lines 1579–1581 of the paper), filtrations of the restriction to
`B_SL = B ∩ SL_n` whose layers are equivalent over `B_SL` to representations of `B` with shifted
sums of atoms as characters also force atom positivity, provided all representations involved
have central characters (`Schubert.RS.Geometric.atomPositive_of_borelSL_filtration`).
-/

namespace Schubert.RS.Geometric

open Module GLRep FlagVarieties

noncomputable section

variable {K : Type*} [Field K] [Infinite K] {n : ℕ}
variable {W : Type*} [AddCommGroup W] [Module K W] {ρ : Representation K (borel K n) W}

/-- The weights of a layer of a filtration are weights of the filtered representation: the
coefficients of the character of a layer are bounded by those of the character. -/
theorem RepFiltration.coeff_ch_layer_le (F : RepFiltration ρ) (hρ : IsRationalBorelRep ρ)
    {i : ℕ} (hi : i < F.length) (w : Fin n → ℤ) :
    (ch (F.layer i)).coeff w ≤ (ch ρ).coeff w := by
  have := hρ.finiteDimensional
  rw [coeff_ch', coeff_ch']
  exact_mod_cast F.finrank_layer_borelWeightSpace_le hρ (-w) hi

/-- **Filtrations whose layers have shifted sums of atoms as characters force atom
positivity.** If a rational representation of `B` with polynomial character `f` has a filtration
whose layers have characters of the form `x^{c·1} ∑ 𝒜_u`, then `f` is a nonnegative integral
combination of Demazure atoms. -/
theorem atomPositive_of_repFiltration (hρ : IsRationalBorelRep ρ) (F : RepFiltration ρ)
    {f : Polynomial n} (hf : ch ρ = toLaurent f)
    (hF : ∀ i < F.length, IsShiftedAtomSum (ch (F.layer i))) : AtomPositive f := by
  classical
  have := hρ.finiteDimensional
  have hsupp : ∀ i < F.length, ∀ w, (ch (F.layer i)).coeff w ≠ 0 → ∀ j, 0 ≤ w j := by
    intro i hi w hw
    apply nonneg_of_toLaurent_coeff_ne_zero f w
    rw [← hf]
    have h1 := RepFiltration.coeff_ch_layer_le F hρ hi w
    have h2 := coeff_ch_nonneg (ρ := F.layer i) w
    omega
  choose! f' hf' hgf using fun i hi => exists_atomPositive_of_isShiftedAtomSum (hF i hi)
    (hsupp i hi)
  have heq : toLaurent f = toLaurent (∑ i ∈ Finset.range F.length, f' i) := by
    rw [← hf, FlagVarieties.RepFiltration.ch_eq_sum F hρ, map_sum]
    exact Finset.sum_congr rfl fun i hi => hgf i (Finset.mem_range.mp hi)
  rw [toLaurent_injective heq]
  exact AtomPositive.sum _ _ fun i hi => hf' i (Finset.mem_range.mp hi)

/-- The obstruction stated with `GLRep.HasFiltrationBy`: if every representation in the class `𝒞`
has a shifted sum of atoms as character, then a rational representation of `B` with polynomial
character `f` that has a filtration by `𝒞` has `f` atom positive. -/
theorem atomPositive_of_hasFiltrationBy
    {𝒞 : ∀ (V : Type _) [AddCommGroup V] [Module K V], Representation K (borel K n) V → Prop}
    (h𝒞 : ∀ (V : Type _) [AddCommGroup V] [Module K V] (σ : Representation K (borel K n) V),
      𝒞 V σ → IsShiftedAtomSum (ch σ))
    (hρ : IsRationalBorelRep ρ) (hF : HasFiltrationBy 𝒞 ρ) {f : Polynomial n}
    (hf : ch ρ = toLaurent f) : AtomPositive f := by
  obtain ⟨F, hF⟩ := hF
  exact atomPositive_of_repFiltration hρ F hf fun i hi => h𝒞 _ _ (hF i hi)

/-! ### The special linear group -/

section SpecialLinear

variable [IsAlgClosed K] [CharZero K] [NeZero n]

/-- **The obstruction over `B_SL = B ∩ SL_n`.** Let `ρ` be a rational representation of `B` with
a central character and polynomial character `f`. If the restriction of `ρ` to `B_SL` has a
filtration whose layers are equivalent, over `B_SL`, to restrictions of members of a family `σ`
of finite-dimensional representations of `B` with central characters and with shifted sums of
atoms as characters, then `f` is atom positive. -/
theorem atomPositive_of_borelSL_filtration {ι : Type*} {V : ι → Type*}
    [∀ k, AddCommGroup (V k)] [∀ k, Module K (V k)] [∀ k, FiniteDimensional K (V k)]
    (σ : ∀ k, Representation K (borel K n) (V k)) (dσ : ι → ℤ)
    (hσc : ∀ k, HasCentralCharacter (σ k) (dσ k)) (hσ : ∀ k, IsShiftedAtomSum (ch (σ k)))
    (hρ : IsRationalBorelRep ρ) {d : ℤ} (hc : HasCentralCharacter ρ d)
    (F : RepFiltration (ρ.comp (borelSL K n).subtype))
    (hF : ∀ i < F.length, ∃ k, Nonempty ((F.layer i).Equiv ((σ k).comp (borelSL K n).subtype)))
    {f : Polynomial n} (hf : ch ρ = toLaurent f) : AtomPositive f := by
  have := hρ.finiteDimensional
  refine atomPositive_of_repFiltration hρ (hc.toRepFiltration F) hf fun i hi => ?_
  obtain ⟨k, ⟨e⟩⟩ := hF i hi
  obtain ⟨j, hj⟩ := borelCharacter_eq_of_equiv_borelSL (hc.subquotient _ _) (hσc k)
    ((hc.layerEquiv F i).symm.trans e)
  have hch : ch ((hc.toRepFiltration F).layer i) =
      AddMonoidAlgebra.single (BModules.BModule.constWeight (-j)) 1 * ch (σ k) := by
    rw [ch, hj, map_mul, laurentInv_single, ch]
    rfl
  rw [hch]
  exact (hσ k).shift (-j)

end SpecialLinear

end

end Schubert.RS.Geometric
