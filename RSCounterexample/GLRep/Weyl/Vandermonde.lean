import RSCounterexample.GLRep.Weyl.Laurent
import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Bialternant

/-!
# The Vandermonde product and the staircase alternant

For the staircase `δ = (n − 1, …, 1, 0)`, the alternant `a_δ` is the Vandermonde product
`∏_{a < b} (x_a − x_b)` (`GLRep.alternant_staircase_eq_vandermonde`). The proof is by induction on
the number of variables, through Tau Ceti's branching rule for alternants at the empty shape.

## Main definitions

* `GLRep.posPairs n`: the pairs `(a, b)` with `a < b`.
* `GLRep.vandermonde n R`: `∏_{a < b} (X_a − X_b)`.

## Main results

* `GLRep.alternant_staircase_eq_vandermonde`.
* `GLRep.alternant_staircase_succ`: the induction step.
-/

namespace GLRep

open MvPolynomial Finset

noncomputable section

variable (R : Type*) [CommRing R]

/-- The pairs `(a, b)` of indices with `a < b`. -/
def posPairs (n : ℕ) : Finset (Fin n × Fin n) := univ.filter fun p => p.1 < p.2

/-- The **Vandermonde product** `∏_{a < b} (X_a − X_b)`. -/
def vandermonde (n : ℕ) : MvPolynomial (Fin n) R := ∏ p ∈ posPairs n, (X p.1 - X p.2)

theorem mem_posPairs {n : ℕ} {p : Fin n × Fin n} : p ∈ posPairs n ↔ p.1 < p.2 := by
  simp [posPairs]

/-- The Vandermonde recursion: splitting off the pairs whose second index is the last one. -/
theorem vandermonde_succ (n : ℕ) :
    vandermonde R (n + 1) =
      (∏ i : Fin n, (X i.castSucc - X (Fin.last n))) * rename Fin.castSucc (vandermonde R n) := by
  classical
  rw [vandermonde, vandermonde, map_prod]
  simp only [map_sub, rename_X]
  -- the pairs `(a, b)` with `b` the last index, and the others
  have hsplit : posPairs (n + 1) =
      (univ.image fun i : Fin n => (i.castSucc, Fin.last n)) ∪
        (posPairs n).image fun p => (p.1.castSucc, p.2.castSucc) := by
    ext ⟨a, b⟩
    simp only [mem_posPairs, mem_union, mem_image, mem_univ, true_and, Prod.mk.injEq]
    constructor
    · intro hab
      rcases Fin.eq_castSucc_or_eq_last a with ⟨a', rfl⟩ | rfl
      · rcases Fin.eq_castSucc_or_eq_last b with ⟨b', rfl⟩ | rfl
        · exact Or.inr ⟨(a', b'), Fin.castSucc_lt_castSucc_iff.mp hab, rfl, rfl⟩
        · exact Or.inl ⟨a', rfl, rfl⟩
      · exact absurd hab (not_lt.mpr (Fin.le_last _))
    · rintro (⟨i, rfl, rfl⟩ | ⟨⟨a', b'⟩, hab', rfl, rfl⟩)
      · exact Fin.castSucc_lt_last i
      · exact Fin.castSucc_lt_castSucc_iff.mpr hab'
  rw [hsplit, prod_union, prod_image, prod_image]
  · rintro p hp q hq h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (Fin.castSucc_injective _ h.1) (Fin.castSucc_injective _ h.2)
  · rintro i - j - h
    simp only [Prod.mk.injEq] at h
    exact Fin.castSucc_injective _ h.1
  · rw [disjoint_left]
    rintro ⟨a, b⟩ h1 h2
    simp only [mem_image, mem_univ, true_and, Prod.mk.injEq] at h1 h2
    obtain ⟨i, -, rfl⟩ := h1
    obtain ⟨p, -, -, h⟩ := h2
    exact Fin.castSucc_ne_last _ h

/-- The staircase alternant in `n + 1` variables, split by the branching rule. -/
theorem alternant_staircase_succ (n : ℕ) :
    TauCeti.alternant (Fin (n + 1)) R (fun j => n - j) =
      (∏ i : Fin n, (X i.castSucc - X (Fin.last n))) *
        rename Fin.castSucc (TauCeti.alternant (Fin n) R fun j => n - 1 - j) := by
  have hbot : ∀ i, (⊥ : _root_.YoungDiagram).rowLen i = 0 := fun i =>
    Nat.eq_zero_of_not_pos fun h =>
      _root_.YoungDiagram.notMem_bot _ (_root_.YoungDiagram.mem_iff_lt_rowLen.mpr h)
  have hbotc : (⊥ : _root_.YoungDiagram).colLen 0 = 0 :=
    Nat.eq_zero_of_not_pos fun h =>
      _root_.YoungDiagram.notMem_bot _ (_root_.YoungDiagram.mem_iff_lt_colLen.mpr h)
  have hshapes : YoungDiagram.interlacingShapes n ⊥ = {⊥} := by
    ext ν
    simp only [YoungDiagram.mem_interlacingShapes, mem_singleton]
    refine ⟨fun h => le_bot_iff.mp h.1.le, ?_⟩
    rintro rfl
    exact ⟨YoungDiagram.interlacedBy_iff.mpr fun i => by simp [hbot], by simp [hbotc]⟩
  simpa [hshapes, hbot, YoungDiagram.betaNumber_def] using
    TauCeti.alternant_eq_prod_mul_sum_interlacingShapes (R := R) n ⊥ (by simp [hbotc])

/-- **The staircase alternant is the Vandermonde product.** -/
theorem alternant_staircase_eq_vandermonde (n : ℕ) :
    TauCeti.alternant (Fin n) R (fun j => n - 1 - j) = vandermonde R n := by
  induction n with
  | zero =>
    rw [vandermonde, TauCeti.alternant_def]
    simp [posPairs]
  | succ n ih =>
    rw [show (fun j : Fin (n + 1) => n + 1 - 1 - (j : ℕ)) = fun j : Fin (n + 1) => n - (j : ℕ)
      from funext fun j => by omega, alternant_staircase_succ, ih, vandermonde_succ]

end

end GLRep
