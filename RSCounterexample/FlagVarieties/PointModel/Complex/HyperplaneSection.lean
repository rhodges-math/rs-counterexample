import RSCounterexample.FlagVarieties.PointModel.Complex.VanishingIntersection

/-!
# The hyperplane-section identity

Let `w` be a permutation, `k` a height, and `p_w = Δ_{w{0..k}}` the flag minor of height `k` with
rows `w{0, …, k}` (`prefixMinor w k`), of weight `ω_k`. With `D = hyperplaneSectionSet k w`:

* `prefixMinor_mem_vanishSpan`: `p_w` vanishes on the orbits of `D`;
* `mem_vanishSpan_of_prefixMinor_mul`: `p_w` is a nonzerodivisor modulo `I_w^A`
  (`p_w a ∈ I_w^A ⇒ a ∈ I_w^A`), from the Demazure library's closure relation on the flag-minor
  span;
* `vanishSpan_hyperplaneSectionSet` (**hyperplane-section identity**):
  `I_D^A = I_w^A + p_w · A` in every column shape `m' + ω_k`.
  The inclusion `⊇` is clear; equality is the dimension count `card_chainSet_lowerSet`.
-/

open Schubert Demazure.FlagModule Demazure.SchubertUnions FinPermutation

namespace FlagVarieties.PointModel.Complex

noncomputable section

variable {n : ℕ}

/-- The flag minor `p_w = Δ_{w{0..k}}` of height `k` whose rows are the prefix `w{0, …, k}`. -/
def prefixMinor (w : Equiv.Perm (Fin n)) (k : Fin n) : MatrixPolynomial n :=
  flagRowMinor k (flagPrefixRows w k).rows

theorem prefixMinor_mem_minorSpan (w : Equiv.Perm (Fin n)) (k : Fin n) :
    prefixMinor w k ∈ minorSpan (Pi.single k 1) :=
  flagRowMinor_mem_minorSpan _ _

theorem flagOrbitRestriction_prefixMinor_ne_zero (w : Equiv.Perm (Fin n)) (k : Fin n)
    (z : List (PositiveRoot n × ℂ)) : flagOrbitRestriction w (prefixMinor w k) z ≠ 0 :=
  flagOrbitRestriction_prefix_minor_ne_zero w k z

theorem prefixMinor_ne_zero (w : Equiv.Perm (Fin n)) (k : Fin n) : prefixMinor w k ≠ 0 := by
  intro h
  have := flagOrbitRestriction_prefixMinor_ne_zero w k []
  rw [h, map_zero] at this
  exact this rfl

/-- `p_w` vanishes on `π⁻¹ X_D`, `D = hyperplaneSectionSet k w`. -/
theorem prefixMinor_mem_vanishSpan (w : Equiv.Perm (Fin n)) (k : Fin n) :
    prefixMinor w k ∈ vanishSpan (Pi.single k 1) (hyperplaneSectionSet k w) := by
  refine Submodule.mem_inf.mpr ⟨prefixMinor_mem_minorSpan w k, LinearMap.mem_ker.mpr ?_⟩
  funext x
  obtain ⟨⟨v, hv⟩, z⟩ := x
  change flagOrbitRestriction v (prefixMinor w k) z = 0
  rw [mem_hyperplaneSectionSet] at hv
  rw [prefixMinor, flagOrbitRestriction_minor_zero v k (flagPrefixRows w k)
    (not_rows_le_of_le_of_ne hv.1 hv.2)]
  rfl

/-- **`p_w` is a nonzerodivisor modulo `I_w^A`.** -/
theorem mem_vanishSpan_of_prefixMinor_mul {m : ColumnShape n} {w : Equiv.Perm (Fin n)}
    {k : Fin n} {a : MatrixPolynomial n} (ha : a ∈ minorSpan m)
    (hpa : prefixMinor w k * a ∈ vanishSpan (m + Pi.single k 1) (lowerSet w)) :
    a ∈ vanishSpan m (lowerSet w) := by
  refine Submodule.mem_inf.mpr ⟨ha, LinearMap.mem_ker.mpr ?_⟩
  have hw : flagOrbitRestriction w a = 0 := by
    funext z
    have h1 := congrFun (LinearMap.mem_ker.mp (Submodule.mem_inf.mp hpa).2)
      ⟨⟨w, mem_lowerSet_self w⟩, z⟩
    change flagOrbitRestriction w (prefixMinor w k * a) z = 0 at h1
    rw [map_mul, Pi.mul_apply] at h1
    exact (mul_eq_zero.mp h1).resolve_left (flagOrbitRestriction_prefixMinor_ne_zero w k z)
  obtain ⟨d, h, hh⟩ := exists_columnMultiplicity m
  have ha' : a ∈ flagSpan h := by
    rw [← minorSpan_columnMultiplicity, hh]
    exact ha
  funext x
  obtain ⟨⟨v, hv⟩, z⟩ := x
  change flagOrbitRestriction v a z = 0
  rw [flagOrbitRestriction_zero_of_bruhat_columns h (mem_lowerSet.mp hv) a ha' hw]
  rfl

theorem prefixMinor_mul_mem_minorSpan {m : ColumnShape n} (w : Equiv.Perm (Fin n)) (k : Fin n)
    {a : MatrixPolynomial n} (ha : a ∈ minorSpan m) :
    prefixMinor w k * a ∈ minorSpan (m + Pi.single k 1) := by
  rw [add_comm]
  exact mul_mem_minorSpan (prefixMinor_mem_minorSpan w k) ha

theorem injective_mulLeft_prefixMinor (w : Equiv.Perm (Fin n)) (k : Fin n) :
    Function.Injective (LinearMap.mulLeft ℂ (prefixMinor w k)) :=
  fun _ _ hab => mul_left_cancel₀ (prefixMinor_ne_zero w k) hab

/-- **Hyperplane-section identity**: `I^A_{D_k(w)} = I^A_w + p_w · A` in column shape `m' + ω_k`. -/
theorem vanishSpan_hyperplaneSectionSet (m' : ColumnShape n) (k : Fin n) (w : Equiv.Perm (Fin n)) :
    vanishSpan (m' + Pi.single k 1) (hyperplaneSectionSet k w) =
      vanishSpan (m' + Pi.single k 1) (lowerSet w) ⊔
        (minorSpan m').map (LinearMap.mulLeft ℂ (prefixMinor w k)) := by
  obtain ⟨d, h', hh'⟩ := exists_columnMultiplicity m'
  let h : Fin (d + 1) → Fin n := Fin.snoc h' k
  have hlast : h (Fin.last d) = k := Fin.snoc_last (α := fun _ => Fin n) _ _
  have hcast : (fun j : Fin d => h j.castSucc) = h' :=
    funext fun j => Fin.snoc_castSucc (α := fun _ => Fin n) _ _ _
  have hm : columnMultiplicity h = m' + Pi.single k 1 := by
    rw [columnMultiplicity_castSucc, hcast, hlast, hh']
  have hcm : columnMultiplicity (fun j : Fin d => h j.castSucc) = m' := by
    rw [hcast, hh']
  have hcount := card_chainSet_lowerSet h w
  rw [hlast] at hcount
  have e1 := finrank_vanishSpan_add h (bruhatLower_lowerSet w)
  have e2 := finrank_vanishSpan_add h (bruhatLower_hyperplaneSectionSet (h (Fin.last d)) w)
  have e3 := finrank_vanishSpan_add (fun j : Fin d => h j.castSucc) (bruhatLower_lowerSet w)
  rw [← minorSpan_columnMultiplicity h, hm] at e1 e2
  rw [hlast] at e2
  rw [← minorSpan_columnMultiplicity (fun j : Fin d => h j.castSucc), hcm] at e3
  set V := vanishSpan (m' + Pi.single k 1) (lowerSet w) with hV
  set P := (minorSpan m').map (LinearMap.mulLeft ℂ (prefixMinor w k)) with hP
  have hle : V ⊔ P ≤ vanishSpan (m' + Pi.single k 1) (hyperplaneSectionSet k w) := by
    refine sup_le (vanishSpan_anti (hyperplaneSectionSet_subset k w)) ?_
    rintro _ ⟨a, ha, rfl⟩
    rw [mem_vanishSpan]
    refine ⟨prefixMinor_mul_mem_minorSpan w k ha, fun g hg => ?_⟩
    rw [LinearMap.mulLeft_apply, map_mul,
      (mem_vanishSpan.mp (prefixMinor_mem_vanishSpan w k)).2 g hg, zero_mul]
  refine (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
  have hinj := injective_mulLeft_prefixMinor w k
  have hPrank : Module.finrank ℂ P = Module.finrank ℂ (minorSpan m') :=
    (Submodule.equivMapOfInjective _ hinj _).finrank_eq.symm
  have hVP : V ⊓ P = (vanishSpan m' (lowerSet w)).map (LinearMap.mulLeft ℂ (prefixMinor w k)) := by
    ext x
    constructor
    · rintro ⟨hxV, ⟨a, ha, rfl⟩⟩
      exact ⟨a, mem_vanishSpan_of_prefixMinor_mul ha hxV, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      have ha' := mem_vanishSpan.mp ha
      refine ⟨?_, ⟨a, ha'.1, rfl⟩⟩
      rw [SetLike.mem_coe, hV, mem_vanishSpan]
      refine ⟨prefixMinor_mul_mem_minorSpan w k ha'.1, fun g hg => ?_⟩
      rw [LinearMap.mulLeft_apply, map_mul, ha'.2 g hg, mul_zero]
  have hVPrank : Module.finrank ℂ (V ⊓ P : Submodule ℂ (MatrixPolynomial n)) =
      Module.finrank ℂ (vanishSpan m' (lowerSet w)) := by
    rw [hVP]
    exact (Submodule.equivMapOfInjective _ hinj _).finrank_eq.symm
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq V P
  omega

end

end FlagVarieties.PointModel.Complex
