import RSCounterexample.FlagVarieties.PointModel.Basic
import RSCounterexample.FlagVarieties.PointModel.Complex.VanishingIntersection

/-!
# Standard-monomial inputs and identities U and H over a field

`vanishSpan K m S = I_S^A ∩ A_λ` (pointwise vanishing on `orbitSet K S`).

`StandardMonomialTheory K` bundles the two facts of standard-monomial theory that the proof of
projective normality uses about the flag-minor algebra over `K`:

* `dim`: for a Bruhat ideal `S`, `dim (I_S^A ∩ A_h) + #chainSet h S = dim A_h`;
* `closure`: an element of `A_h` vanishing on `U ẇ` vanishes on `U v̇` for `v ≤ w`.

They are proved over `ℂ` from the Demazure library (`PointModel/ComplexComparison.lean`) and
transferred to every field of characteristic `0` (`PointModel/Transfer.lean`). From them:

* `vanishSpan_inter` (**intersection identity**) and `vanishSpan_hyperplaneSectionSet`
  (**hyperplane-section identity**).
-/

open Schubert Demazure.FlagModule Demazure.SchubertUnions FinPermutation

namespace FlagVarieties.PointModel

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {K : Type*} [Field K] {n : ℕ}

/-- The polynomials vanishing on `orbitSet K S`. -/
def vanishing (K : Type*) [Field K] (S : Finset (Equiv.Perm (Fin n))) :
    Submodule K (MatrixEntryPolynomial K n) where
  carrier := {p | ∀ g ∈ orbitSet K S, evalAt (g : Matrix (Fin n) (Fin n) K) p = 0}
  add_mem' {a b} ha hb g hg := by rw [map_add, ha g hg, hb g hg, add_zero]
  zero_mem' g _ := map_zero _
  smul_mem' c a ha g hg := by rw [map_smul, ha g hg, smul_zero]

/-- `I_S^A ∩ A_λ`. -/
def vanishSpan (K : Type*) [Field K] (m : ColumnShape n) (S : Finset (Equiv.Perm (Fin n))) :
    Submodule K (MatrixEntryPolynomial K n) :=
  minorSpan K m ⊓ vanishing K S

instance finiteDimensional_vanishSpan (m : ColumnShape n) (S : Finset (Equiv.Perm (Fin n))) :
    FiniteDimensional K (vanishSpan K m S) :=
  Submodule.finiteDimensional_inf_left _ _

theorem mem_vanishSpan {m : ColumnShape n} {S : Finset (Equiv.Perm (Fin n))}
    {p : MatrixEntryPolynomial K n} :
    p ∈ vanishSpan K m S ↔
      p ∈ minorSpan K m ∧ ∀ g ∈ orbitSet K S, evalAt (g : Matrix (Fin n) (Fin n) K) p = 0 :=
  Iff.rfl

theorem vanishSpan_anti {m : ColumnShape n} {S S' : Finset (Equiv.Perm (Fin n))} (h : S ⊆ S') :
    vanishSpan K m S' ≤ vanishSpan K m S := fun _ hp =>
  ⟨hp.1, fun g hg => hp.2 g (orbitSet_mono h hg)⟩

theorem vanishSpan_union (m : ColumnShape n) (S S' : Finset (Equiv.Perm (Fin n))) :
    vanishSpan K m (S ∪ S') = vanishSpan K m S ⊓ vanishSpan K m S' := by
  ext p
  simp only [Submodule.mem_inf, mem_vanishSpan, orbitSet_union, Set.mem_union]
  constructor
  · rintro ⟨hp, hz⟩
    exact ⟨⟨hp, fun g hg => hz g (Or.inl hg)⟩, ⟨hp, fun g hg => hz g (Or.inr hg)⟩⟩
  · rintro ⟨⟨hp, hz⟩, ⟨-, hz'⟩⟩
    exact ⟨hp, fun g hg => hg.elim (hz g) (hz' g)⟩

/-- **The standard-monomial inputs** over `K`. -/
structure StandardMonomialTheory (K : Type*) [Field K] : Prop where
  /-- `dim (I_S^A ∩ A_h) + #chainSet h S = dim A_h` for Bruhat ideals `S`. -/
  dim : ∀ {n d : ℕ} (h : Fin d → Fin n) {S : Finset (Equiv.Perm (Fin n))}, BruhatLower S →
    Module.finrank K (vanishSpan K (columnMultiplicity h) S) + (chainSet h S).card =
      Module.finrank K (flagSpan K h)
  /-- The closure relation on the flag-minor algebra. -/
  closure : ∀ {n d : ℕ} (h : Fin d → Fin n) {v w : Equiv.Perm (Fin n)}, v ≤ᴮ w →
    ∀ p ∈ flagSpan K h,
      (∀ u : Matrix (Fin n) (Fin n) K, IsUnitriangular u → evalAt (u * permMat K w) p = 0) →
        ∀ u : Matrix (Fin n) (Fin n) K, IsUnitriangular u → evalAt (u * permMat K v) p = 0

/-! ### The intersection identity -/

/-- **Intersection identity** over `K`. -/
theorem vanishSpan_inter (hK : StandardMonomialTheory K) (m : ColumnShape n)
    {J L : Finset (Equiv.Perm (Fin n))} (hJ : BruhatLower J) (hL : BruhatLower L) :
    vanishSpan K m (J ∩ L) = vanishSpan K m J ⊔ vanishSpan K m L := by
  obtain ⟨d, h, rfl⟩ := exists_columnMultiplicity m
  refine (Submodule.eq_of_le_of_finrank_eq (sup_le (vanishSpan_anti Finset.inter_subset_left)
    (vanishSpan_anti Finset.inter_subset_right)) ?_).symm
  have h1 := hK.dim h hJ
  have h2 := hK.dim h hL
  have h3 := hK.dim h (bruhatLower_union hJ hL)
  have h4 := hK.dim h (bruhatLower_inter hJ hL)
  have h5 := Submodule.finrank_sup_add_finrank_inf_eq (vanishSpan K (columnMultiplicity h) J)
    (vanishSpan K (columnMultiplicity h) L)
  rw [← vanishSpan_union] at h5
  have h6 := Finset.card_union_add_card_inter (chainSet h J) (chainSet h L)
  rw [← chainSet_union, ← chainSet_inter h hJ hL] at h6
  omega

/-! ### Prefix minors -/

/-- `p_w = Δ_{w{0..k}}`. -/
def prefixMinor (K : Type*) [Field K] (w : Equiv.Perm (Fin n)) (k : Fin n) :
    MatrixEntryPolynomial K n :=
  rowMinor K k (flagPrefixRows w k).rows

theorem prefixMinor_mem_minorSpan (w : Equiv.Perm (Fin n)) (k : Fin n) :
    prefixMinor K w k ∈ minorSpan K (Pi.single k 1) :=
  rowMinor_mem_minorSpan _ _

/-- A sorted flag minor on `U v̇`. -/
theorem evalAt_unitriangular_mul_rowMinor {u : Matrix (Fin n) (Fin n) K} (v : Equiv.Perm (Fin n))
    (k : Fin n) (R : FlagMinorRowSet k) :
    evalAt (u * permMat K v) (rowMinor K k R.rows) =
      (Equiv.Perm.sign (flagPrefixPermutation v k) : K) *
        (u.submatrix R.rows (flagPrefixRows v k).rows).det := by
  rw [evalAt_rowMinor]
  have hm : (u * permMat K v).submatrix R.rows (prefixIndex k) =
      (u.submatrix R.rows (flagPrefixRows v k).rows).submatrix id (flagPrefixPermutation v k) := by
    ext i j
    simp only [Matrix.submatrix_apply, mul_permMat, id_eq, flagPrefixPermutation_spec]
  rw [hm, Matrix.det_permute']

theorem evalAt_unitriangular_mul_prefixMinor {u : Matrix (Fin n) (Fin n) K} (hu : IsUnitriangular u)
    (w : Equiv.Perm (Fin n)) (k : Fin n) :
    evalAt (u * permMat K w) (prefixMinor K w k) ≠ 0 := by
  rw [prefixMinor, evalAt_unitriangular_mul_rowMinor]
  have hup : (u.submatrix (flagPrefixRows w k).rows (flagPrefixRows w k).rows).IsUpperTriangular :=
    fun i j hij => hu.1 ((flagPrefixRows w k).rows.strictMono hij)
  rw [Matrix.det_of_isUpperTriangular hup]
  simp only [Matrix.submatrix_apply, hu.2, Finset.prod_const_one, mul_one]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (flagPrefixPermutation w k)) with h | h <;>
    simp [h]

theorem prefixMinor_ne_zero (w : Equiv.Perm (Fin n)) (k : Fin n) : prefixMinor K w k ≠ 0 := by
  intro h
  have := evalAt_unitriangular_mul_prefixMinor (K := K) (u := 1)
    ⟨Matrix.blockTriangular_one, fun i => Matrix.one_apply_eq i⟩ w k
  rw [h, map_zero] at this
  exact this rfl

/-- `p_w` vanishes on `π⁻¹ X_D`, `D = hyperplaneSectionSet k w`. -/
theorem prefixMinor_mem_vanishSpan (w : Equiv.Perm (Fin n)) (k : Fin n) :
    prefixMinor K w k ∈ vanishSpan K (Pi.single k 1) (hyperplaneSectionSet k w) := by
  refine ⟨prefixMinor_mem_minorSpan w k, ?_⟩
  change ∀ g ∈ orbitSet K (hyperplaneSectionSet k w), _
  rw [forall_mem_orbitSet_iff (prefixMinor_mem_minorSpan w k)]
  intro v hv u hu
  rw [mem_hyperplaneSectionSet] at hv
  rw [prefixMinor, evalAt_unitriangular_mul_rowMinor, upperTriangular_minor_zero _ hu.1 _ _
    (not_rows_le_of_le_of_ne hv.1 hv.2), mul_zero]

theorem prefixMinor_mul_mem_minorSpan {m : ColumnShape n} (w : Equiv.Perm (Fin n)) (k : Fin n)
    {a : MatrixEntryPolynomial K n} (ha : a ∈ minorSpan K m) :
    prefixMinor K w k * a ∈ minorSpan K (m + Pi.single k 1) := by
  rw [add_comm]
  exact mul_mem_minorSpan (prefixMinor_mem_minorSpan w k) ha

/-- **`p_w` is a nonzerodivisor modulo `I_w^A`.** -/
theorem mem_vanishSpan_of_prefixMinor_mul (hK : StandardMonomialTheory K) {m : ColumnShape n}
    {w : Equiv.Perm (Fin n)} {k : Fin n} {a : MatrixEntryPolynomial K n} (ha : a ∈ minorSpan K m)
    (hpa : prefixMinor K w k * a ∈ vanishSpan K (m + Pi.single k 1) (lowerSet w)) :
    a ∈ vanishSpan K m (lowerSet w) := by
  refine ⟨ha, ?_⟩
  change ∀ g ∈ orbitSet K (lowerSet w), _
  rw [forall_mem_orbitSet_iff ha]
  have hpa' := (forall_mem_orbitSet_iff (prefixMinor_mul_mem_minorSpan w k ha) _).mp hpa.2
  have hw : ∀ u : Matrix (Fin n) (Fin n) K, IsUnitriangular u →
      evalAt (u * permMat K w) a = 0 := by
    intro u hu
    have h1 := hpa' w (mem_lowerSet_self w) u hu
    rw [map_mul] at h1
    exact (mul_eq_zero.mp h1).resolve_left (evalAt_unitriangular_mul_prefixMinor hu w k)
  obtain ⟨d, h, hh⟩ := exists_columnMultiplicity m
  have ha' : a ∈ flagSpan K h := by
    rw [← minorSpan_columnMultiplicity, hh]
    exact ha
  intro v hv u hu
  exact hK.closure h (mem_lowerSet.mp hv) a ha' hw u hu

theorem injective_mulLeft_prefixMinor (w : Equiv.Perm (Fin n)) (k : Fin n) :
    Function.Injective (LinearMap.mulLeft K (prefixMinor K w k)) :=
  fun _ _ hab => mul_left_cancel₀ (prefixMinor_ne_zero w k) hab

/-! ### The hyperplane-section identity -/

/-- **Hyperplane-section identity** over `K`: `I^A_{D_k(w)} = I^A_w + p_w · A` in column shape
`m' + ω_k`. -/
theorem vanishSpan_hyperplaneSectionSet (hK : StandardMonomialTheory K) (m' : ColumnShape n)
    (k : Fin n)
    (w : Equiv.Perm (Fin n)) :
    vanishSpan K (m' + Pi.single k 1) (hyperplaneSectionSet k w) =
      vanishSpan K (m' + Pi.single k 1) (lowerSet w) ⊔
        (minorSpan K m').map (LinearMap.mulLeft K (prefixMinor K w k)) := by
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
  have e1 := hK.dim h (bruhatLower_lowerSet w)
  have e2 := hK.dim h (bruhatLower_hyperplaneSectionSet (h (Fin.last d)) w)
  have e3 := hK.dim (fun j : Fin d => h j.castSucc) (bruhatLower_lowerSet w)
  rw [← minorSpan_columnMultiplicity h, hm] at e1 e2
  rw [hlast] at e2
  rw [← minorSpan_columnMultiplicity (fun j : Fin d => h j.castSucc), hcm] at e3
  set V := vanishSpan K (m' + Pi.single k 1) (lowerSet w) with hV
  set P := (minorSpan K m').map (LinearMap.mulLeft K (prefixMinor K w k)) with hP
  have hle : V ⊔ P ≤ vanishSpan K (m' + Pi.single k 1) (hyperplaneSectionSet k w) := by
    refine sup_le (vanishSpan_anti (hyperplaneSectionSet_subset k w)) ?_
    rintro _ ⟨a, ha, rfl⟩
    refine ⟨prefixMinor_mul_mem_minorSpan w k ha, fun g hg => ?_⟩
    rw [LinearMap.mulLeft_apply, map_mul, (prefixMinor_mem_vanishSpan w k).2 g hg, zero_mul]
  refine (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
  have hinj := injective_mulLeft_prefixMinor (K := K) w k
  have hPrank : Module.finrank K P = Module.finrank K (minorSpan K m') :=
    (Submodule.equivMapOfInjective _ hinj _).finrank_eq.symm
  have hVP : V ⊓ P =
      (vanishSpan K m' (lowerSet w)).map (LinearMap.mulLeft K (prefixMinor K w k)) := by
    ext x
    constructor
    · rintro ⟨hxV, ⟨a, ha, rfl⟩⟩
      exact ⟨a, mem_vanishSpan_of_prefixMinor_mul hK ha hxV, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      refine ⟨?_, ⟨a, ha.1, rfl⟩⟩
      rw [SetLike.mem_coe, hV]
      refine ⟨prefixMinor_mul_mem_minorSpan w k ha.1, fun g hg => ?_⟩
      rw [LinearMap.mulLeft_apply, map_mul, ha.2 g hg, mul_zero]
  have hVPrank : Module.finrank K (V ⊓ P : Submodule K (MatrixEntryPolynomial K n)) =
      Module.finrank K (vanishSpan K m' (lowerSet w)) := by
    rw [hVP]
    exact (Submodule.equivMapOfInjective _ hinj _).finrank_eq.symm
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq V P
  omega

end

end FlagVarieties.PointModel
