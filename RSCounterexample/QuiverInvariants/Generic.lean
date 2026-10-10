import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Order.Filter.Basic
import RSCounterexample.GLRep.Polynomial.Functions

/-!
# Generic points of affine space

Let `K` be an infinite field and `σ` a type of coordinates. A property holds for a *generic*
point of the affine space `σ → K` when it holds on a nonempty principal open set
`D(P) = {x | P(x) ≠ 0}`, `P ≠ 0`. A set of points is *Zariski dense* when no nonzero polynomial
vanishes on it. These two notions are all the algebraic geometry used by the theory of
semi-invariants of quivers in this folder: closed sets, irreducible varieties and dimension
theory never appear.

Generic properties are encoded by a filter, `QuiverInvariants.genericFilter K σ`, so that
intersections of generic conditions come for free:
* `∀ᶠ x in genericFilter K σ, p x` says that `p` holds on a nonempty principal open set;
* `∃ᶠ x in genericFilter K σ, p x` says that `{x | p x}` is Zariski dense.

## Main definitions

* `QuiverInvariants.principalOpen P`: the points at which the polynomial `P` does not vanish.
* `QuiverInvariants.ZariskiDense S`: no nonzero polynomial vanishes on `S`.
* `QuiverInvariants.genericFilter K σ`: the sets containing a nonempty principal open set.
* `QuiverInvariants.IsPolynomialMap φ`: every coordinate of `φ x` is a polynomial in `x`.
* `QuiverInvariants.genericRank M`: the largest rank of the values of a matrix of polynomials.

## Main results

* `QuiverInvariants.ZariskiDense.exists_of_eventually`: a dense set meets every generic
  condition.
* `QuiverInvariants.exists_polynomial_eval_add_smul`: the restriction of a polynomial to a line is
  a polynomial in one variable.
* `QuiverInvariants.IsPolynomialMap.tendsto_genericFilter`, `QuiverInvariants.ZariskiDense.image`:
  a polynomial map with dense image pulls generic conditions back to generic conditions and maps
  dense sets to dense sets.
* `QuiverInvariants.ZariskiDense.sumElim`, `QuiverInvariants.ZariskiDense.preimage_comp`: products
  of dense sets, and preimages of dense sets under coordinate projections, are dense.
* `QuiverInvariants.eventually_exists_left`, `QuiverInvariants.eventually_exists_right`: the
  projection of a generic condition on a product is a generic condition.
* `QuiverInvariants.le_rank_iff_exists_det_submatrix_ne_zero`: a matrix over a field has rank at
  least `r` if and only if one of its `r × r` minors is nonzero.
* `QuiverInvariants.exists_minor_genericRank`, `QuiverInvariants.eventually_rank_eq_genericRank`:
  a matrix of polynomials attains its generic rank wherever a suitable minor does not vanish.
-/

open MvPolynomial Filter

namespace QuiverInvariants

noncomputable section

/-! ### Principal open sets and dense sets -/

section Density

variable {K : Type*} [CommRing K] {σ : Type*}

/-- The **principal open set** `D(P)`: the points at which the polynomial `P` does not
vanish. -/
def principalOpen (P : MvPolynomial σ K) : Set (σ → K) :=
  {x | eval x P ≠ 0}

@[simp] theorem mem_principalOpen {P : MvPolynomial σ K} {x : σ → K} :
    x ∈ principalOpen P ↔ eval x P ≠ 0 :=
  Iff.rfl

/-- A set `S` of points of the affine space `σ → K` is **Zariski dense** when no nonzero
polynomial vanishes at every point of `S`. -/
def ZariskiDense (S : Set (σ → K)) : Prop :=
  ∀ P : MvPolynomial σ K, (∀ x ∈ S, eval x P = 0) → P = 0

/-- Two polynomials that agree on a dense set are equal. -/
theorem ZariskiDense.eq_of_eqOn {S : Set (σ → K)} (hS : ZariskiDense S)
    {P Q : MvPolynomial σ K} (h : ∀ x ∈ S, eval x P = eval x Q) : P = Q :=
  sub_eq_zero.mp (hS _ fun x hx => by rw [map_sub, h x hx, sub_self])

theorem zariskiDense_iff_exists_eval_ne_zero {S : Set (σ → K)} :
    ZariskiDense S ↔ ∀ P : MvPolynomial σ K, P ≠ 0 → ∃ x ∈ S, eval x P ≠ 0 := by
  refine ⟨fun hS P hP => ?_, fun h P hP => ?_⟩
  · by_contra hne
    exact hP (hS P fun x hx => by_contra fun hx' => hne ⟨x, hx, hx'⟩)
  · by_contra hne
    obtain ⟨x, hx, hPx⟩ := h P hne
    exact hPx (hP x hx)

/-- **A dense set meets every nonempty principal open set.** -/
theorem ZariskiDense.exists_eval_ne_zero {S : Set (σ → K)} (hS : ZariskiDense S)
    {P : MvPolynomial σ K} (hP : P ≠ 0) : ∃ x ∈ S, eval x P ≠ 0 :=
  zariskiDense_iff_exists_eval_ne_zero.mp hS P hP

theorem ZariskiDense.mono {S T : Set (σ → K)} (hS : ZariskiDense S) (hST : S ⊆ T) :
    ZariskiDense T :=
  fun P hP => hS P fun x hx => hP x (hST hx)

theorem ZariskiDense.nonempty [Nontrivial K] {S : Set (σ → K)} (hS : ZariskiDense S) :
    S.Nonempty := by
  obtain ⟨x, hx, -⟩ := hS.exists_eval_ne_zero (one_ne_zero (α := MvPolynomial σ K))
  exact ⟨x, hx⟩

/-- Density of a set is density of the coordinate system given by its points, in the sense of
`GLRep.IsZariskiDense`. -/
theorem zariskiDense_range_iff {G : Type*} {c : G → σ → K} :
    ZariskiDense (Set.range c) ↔ GLRep.IsZariskiDense c :=
  ⟨fun h P hP => h P (by rintro _ ⟨g, rfl⟩; exact hP g),
    fun h P hP => h P fun g => hP _ ⟨g, rfl⟩⟩

/-- Over an infinite integral domain the whole affine space is dense. -/
theorem zariskiDense_univ [IsDomain K] [Infinite K] :
    ZariskiDense (Set.univ : Set (σ → K)) :=
  fun P hP => MvPolynomial.funext fun x => by rw [hP x trivial, map_zero]

/-- The intersection of a dense set with a nonempty principal open set is dense. -/
theorem ZariskiDense.inter_principalOpen [IsDomain K] {S : Set (σ → K)} (hS : ZariskiDense S)
    {P : MvPolynomial σ K} (hP : P ≠ 0) : ZariskiDense (S ∩ principalOpen P) := by
  intro Q hQ
  have hPQ : P * Q = 0 := hS _ fun x hx => by
    by_cases hPx : eval x P = 0
    · rw [map_mul, hPx, zero_mul]
    · rw [map_mul, hQ x ⟨hx, hPx⟩, mul_zero]
  exact (mul_eq_zero.mp hPQ).resolve_left hP

/-- A nonempty principal open set is dense. -/
theorem zariskiDense_principalOpen [IsDomain K] [Infinite K] {P : MvPolynomial σ K}
    (hP : P ≠ 0) : ZariskiDense (principalOpen P) := by
  simpa using (zariskiDense_univ (K := K) (σ := σ)).inter_principalOpen hP

end Density

/-! ### The generic filter -/

section GenericFilter

variable (K : Type*) [CommRing K] [IsDomain K] (σ : Type*)

/-- The **generic filter** on the affine space `σ → K`: its members are the sets containing a
nonempty principal open set `D(P)`, `P ≠ 0`. A property holds *for generic `x`* when it holds
eventually along this filter. -/
def genericFilter : Filter (σ → K) where
  sets := {S | ∃ P : MvPolynomial σ K, P ≠ 0 ∧ principalOpen P ⊆ S}
  univ_sets := ⟨1, one_ne_zero, Set.subset_univ _⟩
  sets_of_superset := fun ⟨P, hP, hPS⟩ hST => ⟨P, hP, hPS.trans hST⟩
  inter_sets := fun ⟨P, hP, hPS⟩ ⟨Q, hQ, hQT⟩ =>
    ⟨P * Q, mul_ne_zero hP hQ, fun x hx => by
      simp only [mem_principalOpen, map_mul, ne_eq, mul_eq_zero, not_or] at hx
      exact ⟨hPS hx.1, hQT hx.2⟩⟩

variable {K σ}

theorem mem_genericFilter {S : Set (σ → K)} :
    S ∈ genericFilter K σ ↔ ∃ P : MvPolynomial σ K, P ≠ 0 ∧ principalOpen P ⊆ S :=
  Iff.rfl

theorem eventually_genericFilter {p : (σ → K) → Prop} :
    (∀ᶠ x in genericFilter K σ, p x) ↔
      ∃ P : MvPolynomial σ K, P ≠ 0 ∧ ∀ x, eval x P ≠ 0 → p x :=
  Iff.rfl

/-- A nonzero polynomial does not vanish at a generic point. -/
theorem eventually_eval_ne_zero {P : MvPolynomial σ K} (hP : P ≠ 0) :
    ∀ᶠ x in genericFilter K σ, eval x P ≠ 0 :=
  eventually_genericFilter.mpr ⟨P, hP, fun _ hx => hx⟩

/-- A set is dense if and only if it is met frequently along the generic filter. -/
theorem frequently_genericFilter_iff {p : (σ → K) → Prop} :
    (∃ᶠ x in genericFilter K σ, p x) ↔ ZariskiDense {x | p x} := by
  rw [Filter.Frequently, eventually_genericFilter, zariskiDense_iff_exists_eval_ne_zero]
  constructor
  · intro h P hP
    by_contra hne
    exact h ⟨P, hP, fun x hx hpx => hne ⟨x, hpx, hx⟩⟩
  · rintro h ⟨P, hP, hPS⟩
    obtain ⟨x, hx, hPx⟩ := h P hP
    exact hPS x hPx hx

theorem zariskiDense_iff_frequently {S : Set (σ → K)} :
    ZariskiDense S ↔ ∃ᶠ x in genericFilter K σ, x ∈ S :=
  frequently_genericFilter_iff.symm

/-- **A dense set meets every generic condition.** -/
theorem ZariskiDense.exists_of_eventually {S : Set (σ → K)} (hS : ZariskiDense S)
    {p : (σ → K) → Prop} (hp : ∀ᶠ x in genericFilter K σ, p x) : ∃ x ∈ S, p x := by
  obtain ⟨P, hP, hPp⟩ := eventually_genericFilter.mp hp
  obtain ⟨x, hx, hPx⟩ := hS.exists_eval_ne_zero hP
  exact ⟨x, hx, hPp x hPx⟩

/-- The points of a dense set satisfying a generic condition form a dense set. -/
theorem ZariskiDense.inter_eventually {S : Set (σ → K)} (hS : ZariskiDense S)
    {p : (σ → K) → Prop} (hp : ∀ᶠ x in genericFilter K σ, p x) :
    ZariskiDense {x | x ∈ S ∧ p x} :=
  frequently_genericFilter_iff.mp ((zariskiDense_iff_frequently.mp hS).and_eventually hp)

variable [Infinite K]

instance genericFilter_neBot : (genericFilter K σ).NeBot :=
  Filter.forall_mem_nonempty_iff_neBot.mp fun _ hS => by
    obtain ⟨P, hP, hPS⟩ := mem_genericFilter.mp hS
    obtain ⟨x, -, hx⟩ := zariskiDense_univ.exists_eval_ne_zero hP
    exact ⟨x, hPS hx⟩

/-- **A generic condition holds on a dense set.** -/
theorem zariskiDense_of_eventually {p : (σ → K) → Prop}
    (hp : ∀ᶠ x in genericFilter K σ, p x) : ZariskiDense {x | p x} :=
  frequently_genericFilter_iff.mp hp.frequently

end GenericFilter

/-! ### Polynomial maps -/

section PolynomialMap

variable {K : Type*} [CommRing K] {σ τ υ : Type*}

/-- A map `φ` between affine spaces is **polynomial** when every coordinate of `φ x` is given by a
polynomial in the coordinates of `x`. -/
def IsPolynomialMap (φ : (τ → K) → σ → K) : Prop :=
  ∀ s, ∃ P : MvPolynomial τ K, ∀ x, φ x s = eval x P

theorem isPolynomialMap_id : IsPolynomialMap (id : (σ → K) → σ → K) :=
  fun s => ⟨X s, fun x => by simp⟩

theorem isPolynomialMap_const (y : σ → K) : IsPolynomialMap fun _ : τ → K => y :=
  fun s => ⟨C (y s), fun x => by simp⟩

/-- Precomposition with a map of coordinate types, such as a coordinate projection or a
renaming of the coordinates, is polynomial. -/
theorem isPolynomialMap_comp_right (f : σ → τ) : IsPolynomialMap fun x : τ → K => x ∘ f :=
  fun s => ⟨X (f s), fun x => by simp⟩

/-- A map is polynomial when its coordinates lie in the algebra of polynomial functions, so that
sums, products and scalar multiples of polynomial coordinates are again polynomial. -/
theorem isPolynomialMap_iff_mem_coordFunctions {φ : (τ → K) → σ → K} :
    IsPolynomialMap φ ↔ ∀ s, (fun x => φ x s) ∈ GLRep.coordFunctions K fun x : τ → K => x := by
  simp only [IsPolynomialMap, GLRep.mem_coordFunctions]

/-- Pairing two polynomial maps gives a polynomial map to the product. -/
theorem IsPolynomialMap.sumElim {φ : (τ → K) → σ → K} {ψ : (τ → K) → υ → K}
    (hφ : IsPolynomialMap φ) (hψ : IsPolynomialMap ψ) :
    IsPolynomialMap fun x => Sum.elim (φ x) (ψ x)
  | Sum.inl s => hφ s
  | Sum.inr u => hψ u

/-- **Pulling back polynomials** along a polynomial map. -/
theorem IsPolynomialMap.exists_eval_comp {φ : (τ → K) → σ → K} (hφ : IsPolynomialMap φ)
    (Q : MvPolynomial σ K) : ∃ Q' : MvPolynomial τ K, ∀ x, eval (φ x) Q = eval x Q' := by
  choose F hF using hφ
  refine ⟨bind₁ F Q, fun x => ?_⟩
  change eval₂Hom (RingHom.id K) (φ x) Q = eval₂Hom (RingHom.id K) x (bind₁ F Q)
  rw [eval₂Hom_bind₁,
    show φ x = fun s => eval₂Hom (RingHom.id K) x (F s) from funext fun s => hF s x]

theorem IsPolynomialMap.comp {ψ : (σ → K) → υ → K} {φ : (τ → K) → σ → K}
    (hψ : IsPolynomialMap ψ) (hφ : IsPolynomialMap φ) : IsPolynomialMap (ψ ∘ φ) := fun u => by
  obtain ⟨P, hP⟩ := hψ u
  obtain ⟨Q, hQ⟩ := hφ.exists_eval_comp P
  exact ⟨Q, fun x => (hP (φ x)).trans (hQ x)⟩

/-- **Restriction to a line.** The restriction of a polynomial to an affine line
`c ↦ x₀ + c • x₁` is a polynomial in one variable. -/
theorem exists_polynomial_eval_add_smul (P : MvPolynomial σ K) (x₀ x₁ : σ → K) :
    ∃ p : Polynomial K, ∀ c : K, p.eval c = eval (x₀ + c • x₁) P := by
  induction P using MvPolynomial.induction_on with
  | C a => exact ⟨Polynomial.C a, fun c => by simp⟩
  | add P Q hP hQ =>
    obtain ⟨p, hp⟩ := hP
    obtain ⟨q, hq⟩ := hQ
    exact ⟨p + q, fun c => by simp [hp, hq]⟩
  | mul_X P i hP =>
    obtain ⟨p, hp⟩ := hP
    refine ⟨p * (Polynomial.C (x₀ i) + Polynomial.C (x₁ i) * Polynomial.X), fun c => ?_⟩
    simp [hp, mul_comm c]

/-- **Images of dense sets.** A polynomial map with dense image maps dense sets to dense sets. -/
theorem ZariskiDense.image {φ : (τ → K) → σ → K} (hφ : IsPolynomialMap φ)
    (hd : ZariskiDense (Set.range φ)) {S : Set (τ → K)} (hS : ZariskiDense S) :
    ZariskiDense (φ '' S) := by
  intro Q hQ
  obtain ⟨Q', hQ'⟩ := hφ.exists_eval_comp Q
  have h0 : Q' = 0 := hS Q' fun x hx => by rw [← hQ']; exact hQ _ ⟨x, hx, rfl⟩
  exact hd Q (by rintro _ ⟨x, rfl⟩; rw [hQ', h0, map_zero])

variable [IsDomain K]

/-- **Preimages of generic conditions.** A polynomial map with dense image pulls generic
conditions back to generic conditions. -/
theorem IsPolynomialMap.tendsto_genericFilter {φ : (τ → K) → σ → K} (hφ : IsPolynomialMap φ)
    (hd : ZariskiDense (Set.range φ)) : Tendsto φ (genericFilter K τ) (genericFilter K σ) := by
  refine Filter.tendsto_def.mpr fun S hS => ?_
  obtain ⟨Q, hQ, hQS⟩ := mem_genericFilter.mp hS
  obtain ⟨Q', hQ'⟩ := hφ.exists_eval_comp Q
  refine mem_genericFilter.mpr ⟨Q', fun h0 => hQ (hd Q ?_), fun x hx => hQS ?_⟩
  · rintro _ ⟨x, rfl⟩
    rw [hQ', h0, map_zero]
  · rw [mem_principalOpen, hQ']
    exact hx

/-- A map along which generic conditions pull back maps dense sets to dense sets. -/
theorem ZariskiDense.image_of_tendsto {φ : (τ → K) → σ → K}
    (h : Tendsto φ (genericFilter K τ) (genericFilter K σ)) {S : Set (τ → K)}
    (hS : ZariskiDense S) : ZariskiDense (φ '' S) :=
  frequently_genericFilter_iff.mp
    (h.frequently ((zariskiDense_iff_frequently.mp hS).mono fun x hx => ⟨x, hx, rfl⟩))

theorem zariskiDense_range_of_tendsto [Infinite K] {φ : (τ → K) → σ → K}
    (h : Tendsto φ (genericFilter K τ) (genericFilter K σ)) : ZariskiDense (Set.range φ) := by
  simpa using (zariskiDense_univ (K := K) (σ := τ)).image_of_tendsto h

variable [Infinite K]

/-- For an injective map `f` of coordinate types, the coordinate projection `z ↦ z ∘ f` is
surjective, so generic conditions pull back along it. -/
theorem tendsto_comp_right {f : σ → τ} (hf : Function.Injective f) :
    Tendsto (fun z : τ → K => z ∘ f) (genericFilter K τ) (genericFilter K σ) := by
  classical
  refine (isPolynomialMap_comp_right f).tendsto_genericFilter
    (zariskiDense_univ.mono fun x _ => ⟨Function.extend f x 0, ?_⟩)
  exact funext fun s => hf.extend_apply x 0 s

end PolynomialMap

/-! ### Products and projections -/

section Product

variable {K : Type*} [CommRing K] {σ τ : Type*}

/-- Evaluation at a point of the product `(σ ⊕ τ) → K`: the coordinates in `τ` are evaluated
inside the coefficients of `sumRingEquiv`, then those in `σ`. -/
theorem eval_sumElim (P : MvPolynomial (σ ⊕ τ) K) (y : σ → K) (x : τ → K) :
    eval (Sum.elim y x) P = eval y (map (eval x) (sumRingEquiv K σ τ P)) := by
  have h : (eval (Sum.elim y x) : MvPolynomial (σ ⊕ τ) K →+* K) =
      (eval₂Hom (eval x) y).comp (sumRingEquiv K σ τ).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) fun i => ?_
    · simp
    · cases i <;> simp
  rw [eval_map, ← coe_eval₂Hom]
  exact RingHom.congr_fun h P

/-- **Products of dense sets are dense.** -/
theorem ZariskiDense.sumElim {S : Set (σ → K)} {T : Set (τ → K)} (hS : ZariskiDense S)
    (hT : ZariskiDense T) :
    ZariskiDense {z : σ ⊕ τ → K | z ∘ Sum.inl ∈ S ∧ z ∘ Sum.inr ∈ T} := by
  intro P hP
  apply (sumRingEquiv K σ τ).injective
  rw [map_zero]
  by_contra hne
  obtain ⟨d, hd⟩ := ne_zero_iff.mp hne
  refine hd (hT _ fun x hx => ?_)
  have h0 : map (eval x) (sumRingEquiv K σ τ P) = 0 := hS _ fun y hy => by
    rw [← eval_sumElim]
    exact hP _ ⟨by simpa using hy, by simpa using hx⟩
  rw [← coeff_map, h0]
  simp

variable [IsDomain K] [Infinite K]

/-- **Projections of generic conditions.** If a property holds for a generic point `(y, x)` of
the product, then for generic `x` it holds for some `y`. -/
theorem eventually_exists_left {p : (σ ⊕ τ → K) → Prop}
    (h : ∀ᶠ z in genericFilter K (σ ⊕ τ), p z) :
    ∀ᶠ x in genericFilter K τ, ∃ y : σ → K, p (Sum.elim y x) := by
  obtain ⟨P, hP, hPp⟩ := eventually_genericFilter.mp h
  have hP' : sumRingEquiv K σ τ P ≠ 0 := fun h0 =>
    hP ((sumRingEquiv K σ τ).injective (h0.trans (map_zero _).symm))
  obtain ⟨d, hd⟩ := ne_zero_iff.mp hP'
  refine eventually_genericFilter.mpr ⟨_, hd, fun x hx => ?_⟩
  have hne : map (eval x) (sumRingEquiv K σ τ P) ≠ 0 :=
    ne_zero_iff.mpr ⟨d, by rwa [coeff_map]⟩
  obtain ⟨y, -, hy⟩ := zariskiDense_univ.exists_eval_ne_zero hne
  exact ⟨y, hPp _ (by rwa [eval_sumElim])⟩

/-- **Projections of generic conditions.** If a property holds for a generic point `(y, x)` of
the product, then for generic `y` it holds for some `x`. -/
theorem eventually_exists_right {p : (σ ⊕ τ → K) → Prop}
    (h : ∀ᶠ z in genericFilter K (σ ⊕ τ), p z) :
    ∀ᶠ y in genericFilter K σ, ∃ x : τ → K, p (Sum.elim y x) := by
  have h' : ∀ᶠ w in genericFilter K (τ ⊕ σ), p (w ∘ Sum.swap) :=
    (tendsto_comp_right (K := K) Sum.swap_leftInverse.injective).eventually h
  filter_upwards [eventually_exists_left h'] with y ⟨x, hx⟩
  exact ⟨x, by simpa using hx⟩

/-- **Preimages of dense sets under coordinate projections.** For an injective map `f` of
coordinate types, the points `z` with `z ∘ f` in a dense set form a dense set. -/
theorem ZariskiDense.preimage_comp {S : Set (σ → K)} (hS : ZariskiDense S) {f : σ → τ}
    (hf : Function.Injective f) : ZariskiDense {z : τ → K | z ∘ f ∈ S} := by
  classical
  let j : τ → σ ⊕ τ := fun t => if h : ∃ s, f s = t then Sum.inl h.choose else Sum.inr t
  have hj : ∀ s, j (f s) = Sum.inl s := fun s => by
    have h : ∃ s', f s' = f s := ⟨s, rfl⟩
    simp only [j, dite_eq_left h]
    exact congrArg Sum.inl (hf h.choose_spec)
  have hrange : ZariskiDense (Set.range fun z : σ ⊕ τ → K => z ∘ j) := by
    refine zariskiDense_univ.mono fun w _ => ⟨Sum.elim (w ∘ f) w, funext fun t => ?_⟩
    by_cases h : ∃ s, f s = t
    · simp only [Function.comp_apply, j, dite_eq_left h, Sum.elim_inl]
      exact congrArg w h.choose_spec
    · simp only [Function.comp_apply, j, dite_eq_right h, Sum.elim_inr]
  refine (ZariskiDense.image (isPolynomialMap_comp_right j) hrange
    (hS.sumElim (zariskiDense_univ (σ := τ)))).mono ?_
  rintro _ ⟨z, ⟨hz, -⟩, rfl⟩
  have : (z ∘ j) ∘ f = z ∘ Sum.inl := funext fun s => by simp [hj]
  simpa [this] using hz

end Product

/-! ### Rank and minors -/

section Rank

variable {K : Type*} [Field K] {m n : Type*} [Fintype m] [Fintype n]

/-- **Rank and minors.** A matrix over a field has rank at least `r` if and only if one of its
`r × r` minors is nonzero. -/
theorem le_rank_iff_exists_det_submatrix_ne_zero {M : Matrix m n K} {r : ℕ} :
    r ≤ M.rank ↔ ∃ (f : Fin r → m) (g : Fin r → n), (M.submatrix f g).det ≠ 0 := by
  classical
  constructor
  · intro hr
    -- `M.rank` linearly independent columns
    obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' K M.col
    have : Fintype κ := Fintype.ofInjective a ha
    have hκ : Fintype.card κ = M.rank := by
      rw [M.rank_eq_finrank_span_cols, linearIndependent_iff_card_eq_finrank_span.mp hli,
        Set.finrank, hspan]
    obtain ⟨e⟩ : Nonempty (Fin r ↪ κ) :=
      Function.Embedding.nonempty_of_card_le (by rw [Fintype.card_fin, hκ]; exact hr)
    -- the submatrix formed by `r` of them has rank `r`
    let N : Matrix m (Fin r) K := M.submatrix id (a ∘ e)
    have hN : N.rank = r := by
      have hrow : LinearIndependent K N.transpose.row := hli.comp e e.injective
      rw [← Matrix.rank_transpose, hrow.rank_matrix, Fintype.card_fin]
    -- `r` linearly independent rows of that submatrix
    obtain ⟨κ', a', ha', hspan', hli'⟩ := exists_linearIndependent' K N.row
    have : Fintype κ' := Fintype.ofInjective a' ha'
    have hκ' : Fintype.card κ' = r := by
      rw [linearIndependent_iff_card_eq_finrank_span.mp hli', Set.finrank, hspan',
        ← N.rank_eq_finrank_span_row, hN]
    let e' : Fin r ≃ κ' := (Fintype.equivFinOfCardEq hκ').symm
    refine ⟨a' ∘ e', a ∘ e, ?_⟩
    have hrow' : LinearIndependent K (M.submatrix (a' ∘ e') (a ∘ e)).row :=
      hli'.comp e' e'.injective
    exact ((Matrix.isUnit_iff_isUnit_det _).mp
      (Matrix.linearIndependent_rows_iff_isUnit.mp hrow')).ne_zero
  · rintro ⟨f, g, h⟩
    calc r = (M.submatrix f g).rank := by rw [Matrix.rank_of_det_ne_zero h, Fintype.card_fin]
      _ ≤ M.rank := Matrix.rank_submatrix_le M f g

end Rank

/-! ### Generic rank of a matrix of polynomials -/

section GenericRank

variable {K : Type*} [Field K] {σ : Type*} {m n : Type*}

/-- A minor of a matrix of polynomials, evaluated at a point, is the corresponding minor of the
evaluated matrix. -/
theorem eval_det_submatrix (M : Matrix m n (MvPolynomial σ K)) {r : ℕ} (f : Fin r → m)
    (g : Fin r → n) (x : σ → K) :
    eval x (M.submatrix f g).det = ((M.map (eval x)).submatrix f g).det := by
  rw [RingHom.map_det, RingHom.mapMatrix_apply, Matrix.submatrix_map]

variable [Fintype n]

/-- The **generic rank** of a matrix of polynomials: the largest rank of its values. -/
def genericRank (M : Matrix m n (MvPolynomial σ K)) : ℕ :=
  sSup (Set.range fun x : σ → K => (M.map (eval x)).rank)

theorem bddAbove_range_rank_map_eval (M : Matrix m n (MvPolynomial σ K)) :
    BddAbove (Set.range fun x : σ → K => (M.map (eval x)).rank) :=
  ⟨Fintype.card n, by rintro _ ⟨x, rfl⟩; exact Matrix.rank_le_card_width _⟩

theorem rank_map_eval_le_genericRank (M : Matrix m n (MvPolynomial σ K)) (x : σ → K) :
    (M.map (eval x)).rank ≤ genericRank M :=
  le_csSup (bddAbove_range_rank_map_eval M) ⟨x, rfl⟩

theorem exists_rank_map_eval_eq_genericRank (M : Matrix m n (MvPolynomial σ K)) :
    ∃ x : σ → K, (M.map (eval x)).rank = genericRank M :=
  Nat.sSup_mem (Set.range_nonempty _) (bddAbove_range_rank_map_eval M)

theorem le_genericRank_iff {M : Matrix m n (MvPolynomial σ K)} {r : ℕ} :
    r ≤ genericRank M ↔ ∃ x : σ → K, r ≤ (M.map (eval x)).rank := by
  refine ⟨fun h => ?_, fun ⟨x, hx⟩ => hx.trans (rank_map_eval_le_genericRank M x)⟩
  obtain ⟨x, hx⟩ := exists_rank_map_eval_eq_genericRank M
  exact ⟨x, hx ▸ h⟩

theorem genericRank_le_card_width (M : Matrix m n (MvPolynomial σ K)) :
    genericRank M ≤ Fintype.card n := by
  obtain ⟨x, hx⟩ := exists_rank_map_eval_eq_genericRank M
  exact hx ▸ Matrix.rank_le_card_width _

theorem genericRank_le_card_height [Fintype m] (M : Matrix m n (MvPolynomial σ K)) :
    genericRank M ≤ Fintype.card m := by
  obtain ⟨x, hx⟩ := exists_rank_map_eval_eq_genericRank M
  exact hx ▸ Matrix.rank_le_card_height _

/-- **The generic rank is attained on a nonempty principal open set**: there is a nonzero minor
of size `genericRank M` (as a polynomial), and the value of `M` has rank `genericRank M` at
every point where this minor does not vanish. -/
theorem exists_minor_genericRank [Fintype m] (M : Matrix m n (MvPolynomial σ K)) :
    ∃ (f : Fin (genericRank M) → m) (g : Fin (genericRank M) → n),
      (M.submatrix f g).det ≠ 0 ∧
        ∀ x : σ → K, eval x (M.submatrix f g).det ≠ 0 → (M.map (eval x)).rank = genericRank M := by
  obtain ⟨x₀, hx₀⟩ := exists_rank_map_eval_eq_genericRank M
  obtain ⟨f, g, hfg⟩ := le_rank_iff_exists_det_submatrix_ne_zero.mp hx₀.ge
  refine ⟨f, g, fun h => hfg ?_, fun x hx => le_antisymm (rank_map_eval_le_genericRank M x) ?_⟩
  · rw [← eval_det_submatrix, h, map_zero]
  · exact le_rank_iff_exists_det_submatrix_ne_zero.mpr ⟨f, g, by rwa [← eval_det_submatrix]⟩

/-- A matrix of polynomials attains its generic rank at a generic point. -/
theorem eventually_rank_eq_genericRank [Fintype m] (M : Matrix m n (MvPolynomial σ K)) :
    ∀ᶠ x in genericFilter K σ, (M.map (eval x)).rank = genericRank M := by
  obtain ⟨f, g, h0, h⟩ := exists_minor_genericRank M
  exact eventually_genericFilter.mpr ⟨_, h0, h⟩

/-- The generic rank is the rank at a generic point. -/
theorem genericRank_eq_of_eventually [Fintype m] [Infinite K]
    {M : Matrix m n (MvPolynomial σ K)} {r : ℕ}
    (h : ∀ᶠ x in genericFilter K σ, (M.map (eval x)).rank = r) : genericRank M = r := by
  obtain ⟨x, h1, h2⟩ := ((eventually_rank_eq_genericRank M).and h).exists
  rw [← h1, h2]

end GenericRank

end

end QuiverInvariants
