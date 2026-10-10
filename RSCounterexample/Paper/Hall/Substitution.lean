import RSCounterexample.Paper.Laurent
import Mathlib.Algebra.BigOperators.Pi

/-!
# Substituting `x_{q_j} = t_j^{−1}` and extracting blocks of variables

Two tools for the proof of Proposition 3.11 (`prop:paired-reduction`).

* The substitution. Fix a set `D` of positions and an enumeration `q_0, …, q_{m−1}` of the other
  positions. Substituting `x_{q_j} = t_j^{−1}`, and keeping `x_u` for `u ∈ D`, is a ring
  homomorphism from the Laurent polynomials in `x_0, …, x_{n−1}` to the Laurent polynomials in the
  `x_u` (`u ∈ D`) with coefficients Laurent polynomials in `t_0, …, t_{m−1}` (`substitute`). It
  loses no coefficient (`coeff_substitute`).
* Block extraction. If each factor of a product involves only the variables of its own block, and
  the blocks are disjoint, the coefficient of a monomial that is a product over the blocks is the
  product of the blockwise coefficients (`coeff_prod_mapDomain`).
-/

namespace Schubert.RS.Hall

noncomputable section

open AddMonoidAlgebra

variable {n m : ℕ}

/-! ### The substitution -/

/-- A weight of the positions split into its part on `D` and the negated values at
`q_0, …, q_{m−1}`. -/
def splitWeight (D : Finset (Fin n)) (q : Fin m → Fin n) : Weight n →+ Weight n × Weight m where
  toFun w := (fun i => if i ∈ D then w i else 0, fun j => -w (q j))
  map_zero' := by
    ext i <;> simp
  map_add' w w' := by
    ext i
    · simp only [Pi.add_apply, Prod.fst_add]
      split_ifs <;> simp
    · simp only [Pi.add_apply, Prod.snd_add, neg_add]

@[simp] theorem splitWeight_fst (D : Finset (Fin n)) (q : Fin m → Fin n) (w : Weight n)
    (i : Fin n) : (splitWeight D q w).1 i = if i ∈ D then w i else 0 := rfl

@[simp] theorem splitWeight_snd (D : Finset (Fin n)) (q : Fin m → Fin n) (w : Weight n)
    (j : Fin m) : (splitWeight D q w).2 j = -w (q j) := rfl

theorem splitWeight_injective (D : Finset (Fin n)) (q : Fin m → Fin n)
    (hq : ∀ i, i ∉ D → ∃ j, q j = i) : Function.Injective (splitWeight D q) := by
  intro w w' h
  funext i
  by_cases hi : i ∈ D
  · have := congrFun (congrArg Prod.fst h) i
    simpa [hi] using this
  · obtain ⟨j, rfl⟩ := hq i hi
    have := congrFun (congrArg Prod.snd h) j
    simpa using this

/-- **The substitution `x_{q_j} = t_j^{−1}`**, keeping the variables `x_u` with `u ∈ D`: the result
is a Laurent polynomial in `x_0, …, x_{n−1}` (only the `x_u` with `u ∈ D` occur) with coefficients
Laurent polynomials in `t_0, …, t_{m−1}`. -/
def substitute (D : Finset (Fin n)) (q : Fin m → Fin n) :
    Laurent n →+* AddMonoidAlgebra (Laurent m) (Weight n) :=
  (AddMonoidAlgebra.curryRingEquiv (R := ℤ) (M := Weight n) (N := Weight m)).toRingHom.comp
    (AddMonoidAlgebra.mapDomainRingHom ℤ (splitWeight D q))

theorem substitute_single (D : Finset (Fin n)) (q : Fin m → Fin n) (w : Weight n) (z : ℤ) :
    substitute D q (single w z) =
      single (splitWeight D q w).1 (single (splitWeight D q w).2 z) := by
  simp only [substitute, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    mapDomainRingHom_apply, mapDomain_single]
  exact AddMonoidAlgebra.curryRingEquiv_single _ _ _

/-- The substitution loses no coefficient: the coefficient of `x^w` is the coefficient of
`x^{w|_D} t^{−w ∘ q}` after substitution. -/
theorem coeff_substitute (D : Finset (Fin n)) (q : Fin m → Fin n)
    (hq : ∀ i, i ∉ D → ∃ j, q j = i) (f : Laurent n) (w : Weight n) :
    ((substitute D q f).coeff (splitWeight D q w).1).coeff (splitWeight D q w).2 = f.coeff w := by
  classical
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => simp [hf, hg]
  | single w' z =>
    rw [substitute_single]
    simp only [coeff_single, Finsupp.single_apply]
    have hinj := splitWeight_injective D q hq
    by_cases h : w' = w
    · subst h
      simp
    · have hne : splitWeight D q w' ≠ splitWeight D q w := fun he => h (hinj he)
      by_cases h1 : (splitWeight D q w').1 = (splitWeight D q w).1
      · have h2 : (splitWeight D q w').2 ≠ (splitWeight D q w).2 := fun h2 =>
          hne (Prod.ext h1 h2)
        simp [h, h1, h2]
      · simp [h, h1]

/-! ### Blocks of variables -/

/-- Place a weight of `Fin d` at the positions `u 0, …, u (d − 1)`. -/
def blockEmbed {d : ℕ} (u : Fin d → Fin n) : Weight d →+ Weight n where
  toFun w := ∑ a, Pi.single (u a) (w a)
  map_zero' := by simp
  map_add' w w' := by
    simp only [Pi.add_apply, Pi.single_add, Finset.sum_add_distrib]

theorem blockEmbed_apply {d : ℕ} (u : Fin d → Fin n) (w : Weight d) (i : Fin n) :
    blockEmbed u w i = ∑ a, if u a = i then w a else 0 := by
  simp only [blockEmbed, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Finset.sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : u a = i
  · subst h
    simp
  · simp [h, Ne.symm h]

theorem blockEmbed_apply_self {d : ℕ} {u : Fin d → Fin n} (hu : Function.Injective u)
    (w : Weight d) (a : Fin d) : blockEmbed u w (u a) = w a := by
  rw [blockEmbed_apply, Finset.sum_eq_single a]
  · simp
  · intro a' _ ha'
    simp [hu.ne ha']
  · simp

theorem blockEmbed_apply_of_forall_ne {d : ℕ} (u : Fin d → Fin n) (w : Weight d) {i : Fin n}
    (hi : ∀ a, u a ≠ i) : blockEmbed u w i = 0 := by
  rw [blockEmbed_apply]
  exact Finset.sum_eq_zero fun a _ => by simp [hi a]

theorem blockEmbed_single {d : ℕ} (u : Fin d → Fin n) (a : Fin d) (z : ℤ) :
    blockEmbed u (Pi.single a z) = Pi.single (u a) z := by
  simp only [blockEmbed, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [Finset.sum_eq_single a]
  · simp
  · intro a' _ ha'
    simp [ha']
  · simp

theorem blockEmbed_positiveRoot {d : ℕ} (u : Fin d → Fin n) (a b : Fin d) :
    blockEmbed u (positiveRoot a b) = positiveRoot (u a) (u b) := by
  simp [positiveRoot, map_sub, blockEmbed_single]

/-- **Block extraction.** Let `emb_s` embed the weights of block `s` into a common weight group, so
that `(w_s)_s ↦ ∑_s emb_s(w_s)` is injective. For elements `H_s` written in the variables of
block `s`, the coefficient of `∏_s x^{emb_s(w_s)}` in `∏_s H_s` is `∏_s [x^{w_s}] H_s`. -/
theorem coeff_prod_mapDomain {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G : ι → Type*} [∀ s, AddCommMonoid (G s)] {W : Type*} [AddCommMonoid W]
    (emb : ∀ s, G s →+ W) (hinj : Function.Injective fun p : (∀ s, G s) => ∑ s, emb s (p s))
    (H : ∀ s, AddMonoidAlgebra R (G s)) (w : ∀ s, G s) :
    (∏ s, AddMonoidAlgebra.mapDomainRingHom R (emb s) (H s)).coeff (∑ s, emb s (w s)) =
      ∏ s, (H s).coeff (w s) := by
  classical
  have hexp : ∀ s, AddMonoidAlgebra.mapDomainRingHom R (emb s) (H s) =
      ∑ g ∈ (H s).coeff.support, single (emb s g) ((H s).coeff g) := by
    intro s
    conv_lhs => rw [← sum_coeff_single (H s)]
    rw [Finsupp.sum, map_sum]
    exact Finset.sum_congr rfl fun g _ => by simp
  rw [Finset.prod_congr rfl fun s _ => hexp s, Finset.prod_univ_sum]
  simp only [AddMonoidAlgebra.prod_single, coeff_sum, coeff_single, Finsupp.coe_finsetSum,
    Finset.sum_apply, Finsupp.single_apply]
  have key : ∀ p : (∀ s, G s), (∑ s, emb s (p s) = ∑ s, emb s (w s)) ↔ p = w :=
    fun p => hinj.eq_iff
  simp only [key]
  rw [Finset.sum_ite_eq']
  split_ifs with hw
  · rfl
  · rw [Fintype.mem_piFinset] at hw
    push Not at hw
    obtain ⟨s, hs⟩ := hw
    rw [Finsupp.notMem_support_iff] at hs
    exact (Finset.prod_eq_zero (Finset.mem_univ s) hs).symm

end

end Schubert.RS.Hall
