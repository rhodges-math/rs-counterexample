import RSCounterexample.FlagVarieties.PointModel.Complex.ChainCount

/-!
# Vanishing ideals in the flag-minor algebra; the intersection identity

`vanishSpan m S = I_S^A ∩ A_m` is the space of elements of the flag-minor algebra `A_m` vanishing on
the orbits of `S`, equivalently (`mem_vanishSpan`) on `orbitSet S`.

* `finrank_vanishSpan_add`: for a Bruhat ideal `S` and a column sequence `h`,
  `dim (A_h ∩ I_S^A) + #chainSet h S = dim A_h` — the Demazure library's dimension count through its
  orbit duality.
* `vanishSpan_inter` (**intersection identity**): `I^A_{S₁ ∩ S₂} = I^A_{S₁} + I^A_{S₂}` in every
  column shape, for Bruhat ideals `S₁`, `S₂`.
-/

open Schubert Demazure.FlagModule Demazure.SchubertUnions FinPermutation

namespace FlagVarieties.PointModel.Complex

noncomputable section

variable {n : ℕ}

instance finiteDimensional_flagSpan {d : ℕ} (h : Fin d → Fin n) :
    FiniteDimensional ℂ (flagSpan h) :=
  FiniteDimensional.span_of_finite ℂ (Set.finite_range _)

instance finiteDimensional_minorSpan (m : ColumnShape n) : FiniteDimensional ℂ (minorSpan m) := by
  obtain ⟨d, h, rfl⟩ := exists_columnMultiplicity m
  rw [minorSpan_columnMultiplicity]
  infer_instance

/-- `I_S^A ∩ A_m`: elements of the flag-minor algebra of shape `m` vanishing on the orbits of `S`.
-/
def vanishSpan (m : ColumnShape n) (S : Finset (Equiv.Perm (Fin n))) :
    Submodule ℂ (MatrixPolynomial n) :=
  minorSpan m ⊓ LinearMap.ker (unionRestriction S)

instance finiteDimensional_vanishSpan (m : ColumnShape n) (S : Finset (Equiv.Perm (Fin n))) :
    FiniteDimensional ℂ (vanishSpan m S) :=
  Submodule.finiteDimensional_inf_left _ _

theorem mem_vanishSpan {m : ColumnShape n} {S : Finset (Equiv.Perm (Fin n))}
    {p : MatrixPolynomial n} :
    p ∈ vanishSpan m S ↔
      p ∈ minorSpan m ∧ ∀ g ∈ orbitSet S, evalAt (g : Matrix (Fin n) (Fin n) ℂ) p = 0 := by
  rw [vanishSpan, Submodule.mem_inf, LinearMap.mem_ker]
  constructor
  · rintro ⟨hp, hz⟩
    exact ⟨hp, (forall_evalAt_eq_zero_iff hp S).mpr hz⟩
  · rintro ⟨hp, hz⟩
    exact ⟨hp, (forall_evalAt_eq_zero_iff hp S).mp hz⟩

theorem vanishSpan_anti {m : ColumnShape n} {S S' : Finset (Equiv.Perm (Fin n))} (h : S ⊆ S') :
    vanishSpan m S' ≤ vanishSpan m S := fun p hp => by
  rw [mem_vanishSpan] at hp ⊢
  exact ⟨hp.1, fun g hg => hp.2 g (orbitSet_mono h hg)⟩

theorem vanishSpan_union (m : ColumnShape n) (S S' : Finset (Equiv.Perm (Fin n))) :
    vanishSpan m (S ∪ S') = vanishSpan m S ⊓ vanishSpan m S' := by
  ext p
  simp only [Submodule.mem_inf, mem_vanishSpan, orbitSet_union, Set.mem_union]
  constructor
  · rintro ⟨hp, hz⟩
    exact ⟨⟨hp, fun g hg => hz g (Or.inl hg)⟩, ⟨hp, fun g hg => hz g (Or.inr hg)⟩⟩
  · rintro ⟨⟨hp, hz⟩, ⟨-, hz'⟩⟩
    exact ⟨hp, fun g hg => hg.elim (hz g) (hz' g)⟩

/-! ### Dimension count -/

theorem finrank_map_unionRestriction {d : ℕ} (h : Fin d → Fin n)
    {S : Finset (Equiv.Perm (Fin n))} (hS : BruhatLower S) :
    Module.finrank ℂ ((flagSpan h).map (unionRestriction S)) = (chainSet h S).card := by
  have hspan : (flagSpan h).map (unionRestriction S) = Submodule.span ℂ
      (Set.range fun T : (j : Fin d) → FlagMinorRowSet (h j) =>
        unionRestriction S (flagColumnProduct h T)) := by
    rw [flagSpan, Submodule.map_span, ← Set.range_comp]
    rfl
  rw [hspan, ← LinearEquiv.finrank_eq (demazureUnionDuality h S), Subspace.dual_finrank_eq,
    finrank_demazureUnion_eq h S hS]

/-- **Dimension count**: `dim (I_S^A ∩ A_h) + #chainSet h S = dim A_h`. -/
theorem finrank_vanishSpan_add {d : ℕ} (h : Fin d → Fin n) {S : Finset (Equiv.Perm (Fin n))}
    (hS : BruhatLower S) :
    Module.finrank ℂ (vanishSpan (columnMultiplicity h) S) + (chainSet h S).card =
      Module.finrank ℂ (flagSpan h) := by
  let f := (unionRestriction S).comp (flagSpan h).subtype
  have hrn := LinearMap.finrank_range_add_finrank_ker f
  have hr : LinearMap.range f = (flagSpan h).map (unionRestriction S) := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have hk : Module.finrank ℂ (LinearMap.ker f) =
      Module.finrank ℂ (vanishSpan (columnMultiplicity h) S) := by
    rw [vanishSpan, minorSpan_columnMultiplicity, LinearMap.ker_comp,
      ← Submodule.map_comap_subtype]
    exact (Submodule.equivMapOfInjective _ (flagSpan h).injective_subtype _).finrank_eq
  rw [hr, finrank_map_unionRestriction h hS, hk] at hrn
  omega

/-! ### The intersection identity -/

theorem _root_.FlagVarieties.PointModel.bruhatLower_inter {J K : Finset (Equiv.Perm (Fin n))}
    (hJ : BruhatLower J)
    (hK : BruhatLower K) : BruhatLower (J ∩ K) := fun w hw v hv =>
  Finset.mem_inter.mpr ⟨hJ w (Finset.mem_inter.mp hw).1 v hv, hK w (Finset.mem_inter.mp hw).2 v hv⟩

theorem _root_.FlagVarieties.PointModel.bruhatLower_union {J K : Finset (Equiv.Perm (Fin n))}
    (hJ : BruhatLower J)
    (hK : BruhatLower K) : BruhatLower (J ∪ K) := by
  intro w hw v hv
  rcases Finset.mem_union.mp hw with hw | hw
  · exact Finset.mem_union.mpr (Or.inl (hJ w hw v hv))
  · exact Finset.mem_union.mpr (Or.inr (hK w hw v hv))

theorem _root_.FlagVarieties.PointModel.chainSet_union {d : ℕ} (h : Fin d → Fin n)
    (J K : Finset (Equiv.Perm (Fin n))) :
    chainSet h (J ∪ K) = chainSet h J ∪ chainSet h K := by
  ext T
  simp only [mem_chainSet, Finset.mem_union]
  constructor
  · rintro ⟨w, hw | hw, hc⟩
    · exact Or.inl ⟨w, hw, hc⟩
    · exact Or.inr ⟨w, hw, hc⟩
  · rintro (⟨w, hw, hc⟩ | ⟨w, hw, hc⟩)
    · exact ⟨w, Or.inl hw, hc⟩
    · exact ⟨w, Or.inr hw, hc⟩

/-- On Bruhat ideals, chain sets intersect: this is where the Demazure library's right keys enter.
-/
theorem _root_.FlagVarieties.PointModel.chainSet_inter {d : ℕ} (h : Fin d → Fin n)
    {J K : Finset (Equiv.Perm (Fin n))}
    (hJ : BruhatLower J) (hK : BruhatLower K) :
    chainSet h (J ∩ K) = chainSet h J ∩ chainSet h K := by
  ext T
  simp only [mem_chainSet, Finset.mem_inter]
  constructor
  · rintro ⟨w, ⟨hwJ, hwK⟩, hc⟩
    exact ⟨⟨w, hwJ, hc⟩, ⟨w, hwK, hc⟩⟩
  · rintro ⟨⟨w, hw, hc⟩, ⟨w', hw', hc'⟩⟩
    obtain ⟨κ, hκ⟩ := exists_rightKey h T ⟨w, hc⟩
    exact ⟨κ, ⟨hJ w hw κ ((hκ w).mp hc), hK w' hw' κ ((hκ w').mp hc')⟩,
      (hκ κ).mpr (strongBruhat_refl κ)⟩

/-- **Intersection identity**: for Bruhat ideals `J`, `K`, `I^A_{J ∩ K} = I^A_J + I^A_K` in every
column
shape. -/
theorem vanishSpan_inter (m : ColumnShape n) {J K : Finset (Equiv.Perm (Fin n))}
    (hJ : BruhatLower J) (hK : BruhatLower K) :
    vanishSpan m (J ∩ K) = vanishSpan m J ⊔ vanishSpan m K := by
  obtain ⟨d, h, rfl⟩ := exists_columnMultiplicity m
  refine (Submodule.eq_of_le_of_finrank_eq (sup_le (vanishSpan_anti Finset.inter_subset_left)
    (vanishSpan_anti Finset.inter_subset_right)) ?_).symm
  have h1 := finrank_vanishSpan_add h hJ
  have h2 := finrank_vanishSpan_add h hK
  have h3 := finrank_vanishSpan_add h (bruhatLower_union hJ hK)
  have h4 := finrank_vanishSpan_add h (bruhatLower_inter hJ hK)
  have h5 := Submodule.finrank_sup_add_finrank_inf_eq (vanishSpan (columnMultiplicity h) J)
    (vanishSpan (columnMultiplicity h) K)
  rw [← vanishSpan_union] at h5
  have h6 := Finset.card_union_add_card_inter (chainSet h J) (chainSet h K)
  rw [← chainSet_union, ← chainSet_inter h hJ hK] at h6
  omega

end

end FlagVarieties.PointModel.Complex
