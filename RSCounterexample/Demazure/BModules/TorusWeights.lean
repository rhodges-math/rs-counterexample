import RSCounterexample.Demazure.Representation.FullWeightSpaces
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.PrimeCounting

/-!
# Weight spaces of diagonal-torus representations

Let `ρ` be a representation of the diagonal torus `T = (ℂˣ)ⁿ` on a complex vector space `E`.
The integral weight spaces `torusWeightSpace ρ μ` are independent. When they span `E`,

* every `T`-stable subspace is the sum of its intersections with the weight spaces;
* the restriction of `ρ` to a `T`-stable subspace, and the induced representation on the
  quotient, again have spanning weight spaces;
* weight multiplicities are additive: `dim E_μ = dim N_μ + dim (E/N)_μ`.

All proofs use a single torus element whose coordinates are the first `n` primes. Its
eigenvalue on the weight space of `μ` is `∏ pᵢ ^ μᵢ`, which determines `μ`.
-/

open Schubert

namespace Demazure.BModules

open FlagModule

noncomputable section

variable {n : ℕ}

/-! ### A torus element separating all integral weights -/

/-- The `i`-th prime number. -/
def separatingPrime (i : Fin n) : ℕ := Nat.nth Nat.Prime i

theorem separatingPrime_prime (i : Fin n) : (separatingPrime i).Prime :=
  Nat.prime_nth_prime i

theorem separatingPrime_injective : Function.Injective (separatingPrime (n := n)) := by
  intro i j h
  exact Fin.ext (Nat.nth_injective Nat.infinite_setOfPred_prime h)

/-- The torus element whose `i`-th coordinate is the `i`-th prime. -/
def separatingTorus (n : ℕ) : DiagonalTorus n :=
  fun i => Units.mk0 ((separatingPrime i : ℕ) : ℂ)
    (by exact_mod_cast (separatingPrime_prime i).ne_zero)

/-- The rational number `∏ᵢ pᵢ ^ μᵢ`. -/
def primeMonomial (μ : Weight n) : ℚ := ∏ i, ((separatingPrime i : ℕ) : ℚ) ^ μ i

theorem integerWeightScalar_separatingTorus (μ : Weight n) :
    integerWeightScalar μ (separatingTorus n) = (primeMonomial μ : ℂ) := by
  simp [integerWeightScalar, separatingTorus, primeMonomial]

theorem padicValRat_primeMonomial (μ : Weight n) (j : Fin n) :
    padicValRat (separatingPrime j) (primeMonomial μ) = μ j := by
  have : Fact (separatingPrime j).Prime := ⟨separatingPrime_prime j⟩
  have hne : ∀ i, (((separatingPrime i : ℕ) : ℚ) ^ μ i) ≠ 0 := fun i =>
    zpow_ne_zero _ (by exact_mod_cast (separatingPrime_prime i).ne_zero)
  have key : ∀ s : Finset (Fin n),
      padicValRat (separatingPrime j) (∏ i ∈ s, ((separatingPrime i : ℕ) : ℚ) ^ μ i) =
        ∑ i ∈ s, padicValRat (separatingPrime j) (((separatingPrime i : ℕ) : ℚ) ^ μ i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha,
        padicValRat.mul (hne a) (Finset.prod_ne_zero_iff.mpr fun i _ => hne i), ih]
  rw [primeMonomial, key, Finset.sum_eq_single j]
  · rw [padicValRat.zpow, padicValRat.self (separatingPrime_prime j).one_lt, mul_one]
  · intro i _ hij
    have : Fact (separatingPrime i).Prime := ⟨separatingPrime_prime i⟩
    rw [padicValRat.zpow, padicValRat.of_nat,
      padicValNat_primes (separatingPrime_injective.ne (Ne.symm hij))]
    simp
  · simp

theorem primeMonomial_injective : Function.Injective (primeMonomial (n := n)) := by
  intro μ ν h
  funext j
  have hj := congrArg (padicValRat (separatingPrime j)) h
  rwa [padicValRat_primeMonomial, padicValRat_primeMonomial] at hj

/-- The separating element distinguishes all integral weights. -/
theorem integerWeightScalar_separatingTorus_injective :
    Function.Injective fun μ : Weight n => integerWeightScalar μ (separatingTorus n) := by
  intro μ ν h
  simp only [integerWeightScalar_separatingTorus] at h
  exact primeMonomial_injective (Rat.cast_injective h)

/-! ### Independence and spanning -/

section Representation

variable {E : Type*} [AddCommGroup E] [Module ℂ E] (ρ : DiagonalTorus n →* Module.End ℂ E)

/-- The eigenvalue of the separating element on the weight space of `μ`. -/
abbrev separatingValue (μ : Weight n) : ℂ := integerWeightScalar μ (separatingTorus n)

theorem torusWeightSpace_le_eigenspace (μ : Weight n) :
    torusWeightSpace ρ μ ≤ (ρ (separatingTorus n)).eigenspace (separatingValue μ) := by
  intro x hx
  rw [Module.End.mem_eigenspace_iff]
  exact hx _

/-- Weight spaces for distinct integral weights are independent. -/
theorem torusWeightSpace_iSupIndep : iSupIndep (torusWeightSpace ρ) :=
  ((Module.End.eigenspaces_iSupIndep (ρ (separatingTorus n))).comp
    integerWeightScalar_separatingTorus_injective).mono (torusWeightSpace_le_eigenspace ρ)

/-- The integral weight spaces of `ρ` span. -/
def IsWeightDiagonal : Prop := ⨆ μ : Weight n, torusWeightSpace ρ μ = ⊤

variable {ρ}

theorem eigenspace_separating_le (h : IsWeightDiagonal ρ) (a : ℂ) :
    (ρ (separatingTorus n)).eigenspace a ≤
      ⨆ (μ : Weight n) (_ : separatingValue μ = a), torusWeightSpace ρ μ := by
  intro x hx
  have hxt : x ∈ ⨆ μ : Weight n, torusWeightSpace ρ μ := by
    rw [h]; exact Submodule.mem_top
  rw [iSup_split _ (fun μ => separatingValue μ = a)] at hxt
  obtain ⟨w, hw, y, hy, rfl⟩ := Submodule.mem_sup.mp hxt
  have hle : (⨆ (μ : Weight n) (_ : separatingValue μ = a), torusWeightSpace ρ μ) ≤
      (ρ (separatingTorus n)).eigenspace a :=
    iSup₂_le fun μ hμ => by rw [← hμ]; exact torusWeightSpace_le_eigenspace ρ μ
  have hwV : w ∈ (ρ (separatingTorus n)).eigenspace a := hle hw
  have hyV : y ∈ (ρ (separatingTorus n)).eigenspace a := by
    have := Submodule.sub_mem _ hx hwV
    simpa using this
  have hle' : (⨆ (μ : Weight n) (_ : ¬separatingValue μ = a), torusWeightSpace ρ μ) ≤
      ⨆ (b : ℂ) (_ : b ≠ a), (ρ (separatingTorus n)).eigenspace b :=
    iSup₂_le fun μ hμ => (torusWeightSpace_le_eigenspace ρ μ).trans
      (le_iSup₂ (f := fun (b : ℂ) (_ : b ≠ a) => (ρ (separatingTorus n)).eigenspace b)
        (separatingValue μ) hμ)
  have hyO : y ∈ ⨆ (b : ℂ) (_ : b ≠ a), (ρ (separatingTorus n)).eigenspace b := hle' hy
  have hy0 : y = 0 := by
    have hd := (Module.End.eigenspaces_iSupIndep (ρ (separatingTorus n))) a
    exact (Submodule.disjoint_def.mp hd) y hyV hyO
  rw [hy0, add_zero]
  exact hw

/-- On a weight-diagonal representation, the eigenspace of the separating element for the
eigenvalue of `μ` is the weight space of `μ`. -/
theorem eigenspace_separating_eq (h : IsWeightDiagonal ρ) (μ : Weight n) :
    (ρ (separatingTorus n)).eigenspace (separatingValue μ) = torusWeightSpace ρ μ := by
  refine le_antisymm ((eigenspace_separating_le h _).trans (iSup₂_le fun ν hν => ?_))
    (torusWeightSpace_le_eigenspace ρ μ)
  rw [integerWeightScalar_separatingTorus_injective hν]

theorem eigenspace_separating_eq_bot (h : IsWeightDiagonal ρ) (a : ℂ)
    (ha : ∀ μ : Weight n, separatingValue μ ≠ a) :
    (ρ (separatingTorus n)).eigenspace a = ⊥ := by
  refine eq_bot_iff.mpr ((eigenspace_separating_le h a).trans (iSup₂_le fun μ hμ => ?_))
  exact absurd hμ (ha μ)

theorem iSup_eigenspace_separating (h : IsWeightDiagonal ρ) :
    ⨆ a : ℂ, (ρ (separatingTorus n)).eigenspace a = ⊤ := by
  refine eq_top_iff.mpr ?_
  rw [← h]
  exact iSup_le fun μ => (torusWeightSpace_le_eigenspace ρ μ).trans (le_iSup _ _)

/-- A torus-stable subspace of a weight-diagonal representation is the sum of its
intersections with the weight spaces. -/
theorem eq_iSup_inf_torusWeightSpace [FiniteDimensional ℂ E] (h : IsWeightDiagonal ρ)
    (N : Submodule ℂ E) (hN : ∀ t, ∀ x ∈ N, ρ t x ∈ N) :
    N = ⨆ μ : Weight n, N ⊓ torusWeightSpace ρ μ := by
  apply le_antisymm _ (iSup_le fun μ => inf_le_left)
  have h1 := Submodule.inf_iSup_genEigenspace (p := N) (f := ρ (separatingTorus n))
    (hN (separatingTorus n)) 1
  have h2 : N = N ⊓ ⨆ a : ℂ, (ρ (separatingTorus n)).genEigenspace a 1 := by
    change N = N ⊓ ⨆ a : ℂ, (ρ (separatingTorus n)).eigenspace a
    rw [iSup_eigenspace_separating h, inf_top_eq]
  have h3 : N ≤ ⨆ a : ℂ, N ⊓ (ρ (separatingTorus n)).genEigenspace a 1 := by
    rw [← h1]; exact h2.le
  refine h3.trans (iSup_le fun a => ?_)
  change N ⊓ (ρ (separatingTorus n)).eigenspace a ≤ _
  by_cases ha : ∃ μ : Weight n, separatingValue μ = a
  · obtain ⟨μ, rfl⟩ := ha
    rw [eigenspace_separating_eq h μ]
    exact le_iSup (fun μ => N ⊓ torusWeightSpace ρ μ) μ
  · simp only [not_exists] at ha
    rw [eigenspace_separating_eq_bot h a ha, inf_bot_eq]
    exact bot_le

end Representation

/-! ### Restriction and quotient -/

section Subquotient

variable {E : Type*} [AddCommGroup E] [Module ℂ E] (ρ : DiagonalTorus n →* Module.End ℂ E)
  (N : Submodule ℂ E) (hN : ∀ t, ∀ x ∈ N, ρ t x ∈ N)

/-- The restriction of `ρ` to a torus-stable subspace. -/
def restrictTorus : DiagonalTorus n →* Module.End ℂ N where
  toFun t := (ρ t).restrict (hN t)
  map_one' := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    simp
  map_mul' s t := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    simp [Module.End.mul_apply]

@[simp] theorem restrictTorus_apply (t : DiagonalTorus n) (x : N) :
    (restrictTorus ρ N hN t x : E) = ρ t x := rfl

/-- The representation induced by `ρ` on the quotient by a torus-stable subspace. -/
def quotientTorus : DiagonalTorus n →* Module.End ℂ (E ⧸ N) where
  toFun t := N.mapQ N (ρ t) (fun x hx => hN t x hx)
  map_one' := by
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H x => simp
  map_mul' s t := by
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H x => simp [Module.End.mul_apply]

@[simp] theorem quotientTorus_mk (t : DiagonalTorus n) (x : E) :
    quotientTorus ρ N hN t (Submodule.Quotient.mk x) = Submodule.Quotient.mk (ρ t x) := rfl

theorem torusWeightSpace_restrictTorus (μ : Weight n) :
    torusWeightSpace (restrictTorus ρ N hN) μ = (torusWeightSpace ρ μ).comap N.subtype := by
  ext x
  constructor
  · intro hx t
    exact congrArg Subtype.val (hx t)
  · intro hx t
    exact Subtype.ext (hx t)

theorem mkQ_mem_torusWeightSpace {μ : Weight n} {x : E} (hx : x ∈ torusWeightSpace ρ μ) :
    N.mkQ x ∈ torusWeightSpace (quotientTorus ρ N hN) μ := by
  intro t
  change Submodule.Quotient.mk (ρ t x) = _
  rw [hx t]
  rfl

theorem map_mkQ_torusWeightSpace_le (μ : Weight n) :
    (torusWeightSpace ρ μ).map N.mkQ ≤ torusWeightSpace (quotientTorus ρ N hN) μ := by
  rintro _ ⟨x, hx, rfl⟩
  exact mkQ_mem_torusWeightSpace ρ N hN hx

variable {ρ}

/-- The weight spaces of the quotient are the images of the weight spaces. -/
theorem exists_mkQ_eq_of_mem_torusWeightSpace (h : IsWeightDiagonal ρ) {μ : Weight n}
    {y : E ⧸ N} (hy : y ∈ torusWeightSpace (quotientTorus ρ N hN) μ) :
    ∃ x ∈ torusWeightSpace ρ μ, N.mkQ x = y := by
  obtain ⟨x, rfl⟩ := N.mkQ_surjective y
  have hxt : x ∈ ⨆ ν : Weight n, torusWeightSpace ρ ν := by
    rw [h]; exact Submodule.mem_top
  rw [iSup_split_single _ μ] at hxt
  obtain ⟨w, hw, z, hz, rfl⟩ := Submodule.mem_sup.mp hxt
  refine ⟨w, hw, ?_⟩
  have hzμ : N.mkQ z ∈ torusWeightSpace (quotientTorus ρ N hN) μ := by
    have := Submodule.sub_mem _ hy (mkQ_mem_torusWeightSpace ρ N hN hw)
    simpa using this
  have hzO : N.mkQ z ∈ ⨆ (ν : Weight n) (_ : ν ≠ μ), torusWeightSpace (quotientTorus ρ N hN) ν := by
    have hmap : (⨆ (ν : Weight n) (_ : ν ≠ μ), torusWeightSpace ρ ν).map N.mkQ ≤
        ⨆ (ν : Weight n) (_ : ν ≠ μ), torusWeightSpace (quotientTorus ρ N hN) ν := by
      rw [Submodule.map_iSup]
      refine iSup_mono fun ν => ?_
      rw [Submodule.map_iSup]
      exact iSup_mono fun _ => map_mkQ_torusWeightSpace_le ρ N hN ν
    exact hmap ⟨z, hz, rfl⟩
  have hz0 : N.mkQ z = 0 :=
    (Submodule.disjoint_def.mp (torusWeightSpace_iSupIndep (quotientTorus ρ N hN) μ)) _ hzμ hzO
  rw [map_add, hz0, add_zero]

theorem isWeightDiagonal_restrictTorus [FiniteDimensional ℂ E] (h : IsWeightDiagonal ρ) :
    IsWeightDiagonal (restrictTorus ρ N hN) := by
  refine eq_top_iff.mpr ?_
  rintro ⟨x, hxN⟩ -
  have hx : x ∈ ⨆ μ : Weight n, N ⊓ torusWeightSpace ρ μ := by
    rw [← eq_iSup_inf_torusWeightSpace h N hN]; exact hxN
  have hmap : (⨆ μ : Weight n, N ⊓ torusWeightSpace ρ μ) ≤
      (⨆ μ : Weight n, torusWeightSpace (restrictTorus ρ N hN) μ).map N.subtype := by
    refine iSup_le fun μ => ?_
    rintro y ⟨hyN, hyμ⟩
    refine ⟨⟨y, hyN⟩, ?_, rfl⟩
    refine (le_iSup (fun μ => torusWeightSpace (restrictTorus ρ N hN) μ) μ) ?_
    rw [torusWeightSpace_restrictTorus]
    exact hyμ
  obtain ⟨z, hz, hzx⟩ := hmap hx
  have : z = ⟨x, hxN⟩ := Subtype.ext hzx
  rw [← this]
  exact hz

theorem isWeightDiagonal_quotientTorus (h : IsWeightDiagonal ρ) :
    IsWeightDiagonal (quotientTorus ρ N hN) := by
  refine eq_top_iff.mpr ?_
  intro y _
  obtain ⟨x, rfl⟩ := N.mkQ_surjective y
  have hx : x ∈ ⨆ μ : Weight n, torusWeightSpace ρ μ := by rw [h]; exact Submodule.mem_top
  have hmap : (⨆ μ : Weight n, torusWeightSpace ρ μ).map N.mkQ ≤
      ⨆ μ : Weight n, torusWeightSpace (quotientTorus ρ N hN) μ := by
    rw [Submodule.map_iSup]
    exact iSup_mono fun μ => map_mkQ_torusWeightSpace_le ρ N hN μ
  exact hmap ⟨x, hx, rfl⟩

/-- The dimension of `(p.comap N.subtype)` is that of `N ⊓ p`. -/
theorem finrank_comap_subtype (p : Submodule ℂ E) :
    Module.finrank ℂ (p.comap N.subtype) = Module.finrank ℂ (N ⊓ p : Submodule ℂ E) := by
  rw [← Submodule.map_comap_subtype]
  exact (Submodule.equivMapOfInjective N.subtype N.injective_subtype _).finrank_eq

/-- Additivity of weight multiplicities along a torus-stable subspace. -/
theorem finrank_torusWeightSpace_eq_add [FiniteDimensional ℂ E] (h : IsWeightDiagonal ρ)
    (μ : Weight n) :
    Module.finrank ℂ (torusWeightSpace ρ μ) =
      Module.finrank ℂ (torusWeightSpace (restrictTorus ρ N hN) μ) +
        Module.finrank ℂ (torusWeightSpace (quotientTorus ρ N hN) μ) := by
  let W := torusWeightSpace ρ μ
  let Q := torusWeightSpace (quotientTorus ρ N hN) μ
  let φ : W →ₗ[ℂ] Q :=
    (N.mkQ.comp W.subtype).codRestrict Q (fun x => mkQ_mem_torusWeightSpace ρ N hN x.property)
  have hφ : Function.Surjective φ := by
    intro y
    obtain ⟨x, hx, hxy⟩ := exists_mkQ_eq_of_mem_torusWeightSpace N hN h y.property
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have hker : LinearMap.ker φ = N.comap W.subtype := by
    ext x
    simp [φ, LinearMap.mem_ker, Submodule.Quotient.mk_eq_zero]
  have hrn := φ.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hφ, finrank_top, hker, finrank_comap_subtype W N, inf_comm] at hrn
  rw [torusWeightSpace_restrictTorus, finrank_comap_subtype N, ← hrn, add_comm]

end Subquotient

end

end Demazure.BModules
