import Schubert.GLRep.Borel.Filtration

/-!
# Conventions for weights and characters of `B`-modules

This file fixes the conventions of the flag-variety library for the representations of the
upper-triangular Borel subgroup `B = GLRep.borel K n ⊆ G = GL_n(K)` that arise as spaces of
sections of line bundles on `G/B`. They are those of
[van der Kallen, *Lectures on Frobenius splittings and B-modules*, 2.3]:

* **Action on functions.** `B` (and `G`) act on functions on `G` by left translation,
  `(b · f)(g) = f(b⁻¹ g)`.
* **Line bundles.** A weight `η ∈ ℤⁿ` is the character `η(b) = ∏ᵢ b_ii^{ηᵢ}` of `B`
  (`GLRep.borelChar`). The sections of `𝓛(η) = G ×^B K_η` over an open `V ⊆ G/B` are the
  functions `f` on the preimage of `V` in `G` with `f(g b) = η(b)⁻¹ f(g)`.
* **Weights.** With these conventions a product of flag minors `Δ_R(g)` (rows `R`, first `|R|`
  columns) of column shape `λ` and row content `c ∈ ℕⁿ` is a section of `𝓛(−λ)` of `T`-weight
  `−c`.
* **Characters.** The character of a `B`-module records the weight `μ` by the monomial `x^{−μ}`:
  `ch M = ∑_μ dim M_μ · x^{−μ}` (`FlagVarieties.ch`). Thus `ch H⁰(X_w, 𝓛(−λ))` is a polynomial
  (the key polynomial `κ_{wλ}`). This is the image under the involution `x^μ ↦ x^{−μ}`
  (`FlagVarieties.laurentInv`) of the character `GLRep.borelCharacter` in the standard
  convention.
* **Antidominant weights** (for the upper-triangular Borel subgroup) are the weakly increasing
  ones (`FlagVarieties.IsAntidominant`). Every weight is `η = k·1 − λ` with
  `k = max(0, max η)` (`FlagVarieties.weightShift`) and `λ ∈ ℕⁿ`
  (`FlagVarieties.weightComplement`), and `λ` is dominant (weakly decreasing) when `η` is
  antidominant.

## Main results

* `FlagVarieties.coeff_ch`: `(ch M).coeff (−μ) = dim M_μ`; `FlagVarieties.ch_eq_iff`.
* `FlagVarieties.ch_eq_of_equiv`, `FlagVarieties.ch_prod`, `FlagVarieties.ch_tprod`,
  `FlagVarieties.ch_eq_add` (subrepresentation and quotient),
  `FlagVarieties.RepFiltration.ch_eq_sum` (filtrations).
* `FlagVarieties.ch_scaledRep`, `FlagVarieties.ch_borelCharRep`: `ch K_η = x^{−η}`.
-/

namespace FlagVarieties

open Module GLRep TauCeti

noncomputable section

/-! ### Laurent polynomials -/

/-- Laurent polynomials with integer coefficients in `x_0, …, x_{n-1}`, indexed by weights
`μ ∈ ℤⁿ`. This is `GLRep.TorusLaurent (Fin n)`, the same type as `Demazure.Laurent n`. -/
abbrev Laurent (n : ℕ) : Type := GLRep.TorusLaurent (Fin n)

variable {n : ℕ}

/-- The ring involution `x^μ ↦ x^{−μ}` of the Laurent polynomials. -/
def laurentInv : Laurent n ≃+* Laurent n :=
  AddMonoidAlgebra.mapDomainRingEquiv ℤ (AddEquiv.neg (Fin n → ℤ))

@[simp]
theorem laurentInv_single (μ : Fin n → ℤ) (c : ℤ) :
    laurentInv (AddMonoidAlgebra.single μ c) = AddMonoidAlgebra.single (-μ) c := by
  rw [laurentInv, AddMonoidAlgebra.mapDomainRingEquiv_single, AddEquiv.neg_apply]

theorem coeff_laurentInv (f : Laurent n) (μ : Fin n → ℤ) :
    (laurentInv f).coeff μ = f.coeff (-μ) := by
  rw [laurentInv, AddMonoidAlgebra.coeff_mapDomainRingEquiv, Finsupp.equivMapDomain_apply]
  rfl

@[simp]
theorem laurentInv_laurentInv (f : Laurent n) : laurentInv (laurentInv f) = f :=
  TorusLaurent.ext fun μ => by rw [coeff_laurentInv, coeff_laurentInv, neg_neg]

theorem laurentInv_symm : (laurentInv (n := n)).symm = laurentInv :=
  RingEquiv.ext fun f => by
    rw [RingEquiv.symm_apply_eq, laurentInv_laurentInv]

/-! ### Antidominant weights -/

/-- A weight `η ∈ ℤⁿ` is **antidominant** (for the upper-triangular Borel subgroup) when it is
weakly increasing. -/
def IsAntidominant (η : Fin n → ℤ) : Prop := Monotone η

/-- The shift `k = max(0, max η)` of a weight `η`. -/
def weightShift (η : Fin n → ℤ) : ℕ := Finset.univ.sup fun i => (η i).toNat

/-- The weight `λ = k·1 − η ∈ ℕⁿ`, with `k = weightShift η`, so that `η = k·1 − λ`. -/
def weightComplement (η : Fin n → ℤ) : Fin n → ℕ :=
  fun i => ((weightShift η : ℤ) - η i).toNat

theorem le_weightShift (η : Fin n → ℤ) (i : Fin n) : η i ≤ weightShift η := by
  have h : (η i).toNat ≤ weightShift η :=
    Finset.le_sup (f := fun i => (η i).toNat) (Finset.mem_univ i)
  have := Int.self_le_toNat (η i)
  omega

theorem weightComplement_cast (η : Fin n → ℤ) (i : Fin n) :
    (weightComplement η i : ℤ) = weightShift η - η i := by
  have := le_weightShift η i
  simp only [weightComplement]
  omega

/-- **`η = k·1 − λ`**, with `k = weightShift η` and `λ = weightComplement η`. -/
theorem eq_weightShift_sub_weightComplement (η : Fin n → ℤ) (i : Fin n) :
    η i = weightShift η - weightComplement η i := by
  rw [weightComplement_cast]
  ring

/-- For an antidominant `η`, the weight `λ` in `η = k·1 − λ` is dominant (weakly decreasing). -/
theorem IsAntidominant.antitone_weightComplement {η : Fin n → ℤ} (hη : IsAntidominant η) :
    Antitone (weightComplement η) := by
  intro i j hij
  have h1 := weightComplement_cast η i
  have h2 := weightComplement_cast η j
  have := hη hij
  omega

/-! ### Characters -/

variable {K : Type*} [Field K]
variable {W : Type*} [AddCommGroup W] [Module K W] {ρ : Representation K (borel K n) W}
variable {V : Type*} [AddCommGroup V] [Module K V] {σ : Representation K (borel K n) V}

variable (ρ) in
/-- The **character** `ch M = ∑_μ dim M_μ · x^{−μ}` of a representation of `B`, in the convention
used throughout: the weight `μ` is recorded by the monomial `x^{−μ}`. It is the image
of `GLRep.borelCharacter ρ` under `x^μ ↦ x^{−μ}`. -/
def ch : Laurent n := laurentInv (borelCharacter ρ)

theorem ch_eq_laurentInv : ch ρ = laurentInv (borelCharacter ρ) :=
  rfl

theorem borelCharacter_eq_laurentInv_ch : borelCharacter ρ = laurentInv (ch ρ) := by
  rw [ch, laurentInv_laurentInv]

/-- Equivalent representations of `B` have the same character. -/
theorem ch_eq_of_equiv (e : ρ.Equiv σ) : ch ρ = ch σ := by
  rw [ch, ch, borelCharacter_eq_of_equiv e]

/-- The character of the restriction to `B` of a representation of `GL_n(K)`. -/
theorem ch_restrictBorel (ρ : Representation K (GL (Fin n) K) W) :
    ch (ρ.comp (borel K n).subtype) = laurentInv (ratCharacter ρ) := by
  rw [ch, borelCharacter_restrictBorel]

variable [Infinite K]

/-- **The coefficient of `x^{−μ}` in `ch M` is the dimension of the weight space `M_μ`.** -/
theorem coeff_ch [FiniteDimensional K W] (μ : Fin n → ℤ) :
    (ch ρ).coeff (-μ) = finrank K (borelWeightSpace ρ μ) := by
  rw [ch, coeff_laurentInv, neg_neg, coeff_borelCharacter]

theorem coeff_ch' [FiniteDimensional K W] (μ : Fin n → ℤ) :
    (ch ρ).coeff μ = finrank K (borelWeightSpace ρ (-μ)) := by
  rw [← coeff_ch, neg_neg]

/-- **`f` is the character of `M`** exactly when its coefficient of `x^{−μ}` is `dim M_μ` for
every weight `μ`. -/
theorem ch_eq_iff [FiniteDimensional K W] {f : Laurent n} :
    ch ρ = f ↔ ∀ μ, (finrank K (borelWeightSpace ρ μ) : ℤ) = f.coeff (-μ) := by
  constructor
  · rintro rfl μ
    rw [coeff_ch]
  · intro h
    refine TorusLaurent.ext fun μ => ?_
    rw [coeff_ch', h, neg_neg]

/-- The coefficients of a character are nonnegative. -/
theorem coeff_ch_nonneg [FiniteDimensional K W] (μ : Fin n → ℤ) : 0 ≤ (ch ρ).coeff μ := by
  rw [coeff_ch']
  exact Int.natCast_nonneg _

/-- **The character of a representation with a basis of weight vectors** `bᵢ` of weights `wtᵢ`
is `∑ᵢ x^{−wtᵢ}`. -/
theorem ch_eq_sum_of_basis {ι : Type*} [Fintype ι] (b : Module.Basis ι K W) (wt : ι → Fin n → ℤ)
    (hb : ∀ t i, ρ (borelTorus K n t) (b i) = weightCharHom K (wt i) t • b i) :
    ch ρ = ∑ i, AddMonoidAlgebra.single (-wt i) 1 := by
  rw [ch, borelCharacter_eq_sum_of_basis b wt hb, map_sum]
  simp only [laurentInv_single]

/-- **Twisting by the character `η` multiplies the character by `x^{−η}`.** -/
theorem ch_scaledRep [FiniteDimensional K W] (η : Fin n → ℤ) :
    ch (scaledRep ρ (borelChar K n η)) = AddMonoidAlgebra.single (-η) 1 * ch ρ := by
  rw [ch, ch, borelCharacter_scaledRep, map_mul, laurentInv_single]

/-- **The character of `K_η` is `x^{−η}`.** -/
theorem ch_borelCharRep (η : Fin n → ℤ) :
    ch (borelCharRep K n η) = AddMonoidAlgebra.single (-η) 1 := by
  rw [ch, borelCharacter_borelCharRep, laurentInv_single]

/-- **Characters are additive on a subrepresentation and its quotient.** -/
theorem ch_eq_add (h : IsRationalBorelRep ρ) (U : Subrepresentation ρ) :
    ch ρ = ch U.toRepresentation + ch U.quotient := by
  rw [ch, ch, ch, h.borelCharacter_eq_add U, map_add]

/-- **Characters are additive along filtrations.** -/
theorem RepFiltration.ch_eq_sum (F : RepFiltration ρ) (h : IsRationalBorelRep ρ) :
    ch ρ = ∑ i ∈ Finset.range F.length, ch (F.layer i) := by
  rw [ch, F.borelCharacter_eq_sum h, map_sum]
  rfl

variable [CharZero K]

/-- The character of a product is the sum of the characters. -/
theorem ch_prod (hρ : IsRationalBorelRep ρ) (hσ : IsRationalBorelRep σ) :
    ch (ρ.prod σ) = ch ρ + ch σ := by
  rw [ch, ch, ch, borelCharacter_prod hρ hσ, map_add]

/-- The character of a tensor product is the product of the characters. -/
theorem ch_tprod (hρ : IsRationalBorelRep ρ) (hσ : IsRationalBorelRep σ) :
    ch (ρ.tprod σ) = ch ρ * ch σ := by
  rw [ch, ch, ch, borelCharacter_tprod hρ hσ, map_mul]

end

end FlagVarieties
