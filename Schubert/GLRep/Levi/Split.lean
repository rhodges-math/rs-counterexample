import Schubert.GLRep.Torus.Levi

/-!
# Splitting off the first block of a Levi group

The Levi group `L = ∏_{p ≤ s} GL_{d_p}(K)` is the product of its first factor `GL_{d_0}(K)`
(`GLRep.leviBlock K d 0`) and the Levi group `L' = ∏_{q < s} GL_{d_{q+1}}(K)` of the remaining
blocks, included as `h ↦ (1, h)` (`GLRep.leviTail`). The two subgroups commute and together give
every element (`GLRep.leviBlock_mul_leviTail`), and the diagonal torus splits accordingly
(`GLRep.leviTorus_eq_mul`). Restricting a polynomial representation of `L` to `L'` gives a
polynomial representation (`GLRep.IsPolynomialLeviRep.comp_leviTail`).

## Main definitions

* `GLRep.leviTail`: the inclusion `L' → L`.
* `GLRep.headTorus`, `GLRep.tailTorus`: the two parts of a point of the torus of `L`.
* `GLRep.tailVar`: the variables of `L'` among those of `L`.
-/

namespace GLRep

open Module TauCeti

noncomputable section

variable {K : Type*} [Field K] {s : ℕ} {d : Fin (s + 1) → ℕ}
variable {W : Type*} [AddCommGroup W] [Module K W]

variable (K d) in
/-- The inclusion `h ↦ (1, h)` of the Levi group of the blocks after the first. -/
def leviTail : LeviGroup K (Fin.tail d) →* LeviGroup K d where
  toFun h := Fin.cons (1 : GL (Fin (d 0)) K) h
  map_one' := by
    funext p
    refine Fin.cases ?_ (fun q => ?_) p <;> rfl
  map_mul' h h' := by
    funext p
    refine Fin.cases ?_ (fun q => ?_) p
    · exact (mul_one 1).symm
    · rfl

@[simp] theorem leviTail_apply_zero (h : LeviGroup K (Fin.tail d)) : leviTail K d h 0 = 1 := rfl

@[simp] theorem leviTail_apply_succ (h : LeviGroup K (Fin.tail d)) (q : Fin s) :
    leviTail K d h q.succ = h q := rfl

theorem leviBlock_zero_apply_zero (g : GL (Fin (d 0)) K) : leviBlock K d 0 g 0 = g := by
  simp [leviBlock]

theorem leviBlock_zero_apply_succ (g : GL (Fin (d 0)) K) (q : Fin s) :
    leviBlock K d 0 g q.succ = 1 := by
  simp [leviBlock]

/-- Every element of the Levi group is the product of its first block and of the rest. -/
theorem leviBlock_mul_leviTail (g : LeviGroup K d) :
    leviBlock K d 0 (g 0) * leviTail K d (Fin.tail g) = g := by
  funext p
  refine Fin.cases ?_ (fun q => ?_) p
  · change leviBlock K d 0 (g 0) 0 * 1 = g 0
    rw [leviBlock_zero_apply_zero, mul_one]
  · change leviBlock K d 0 (g 0) q.succ * g q.succ = g q.succ
    rw [leviBlock_zero_apply_succ, one_mul]

/-- The first block commutes with the other blocks. -/
theorem leviBlock_commute_leviTail (g : GL (Fin (d 0)) K) (h : LeviGroup K (Fin.tail d)) :
    Commute (leviBlock K d 0 g) (leviTail K d h) := by
  funext p
  refine Fin.cases ?_ (fun q => ?_) p
  · change leviBlock K d 0 g 0 * 1 = 1 * leviBlock K d 0 g 0
    rw [mul_one, one_mul]
  · show leviBlock K d 0 g q.succ * leviTail K d h q.succ =
      leviTail K d h q.succ * leviBlock K d 0 g q.succ
    rw [leviBlock_zero_apply_succ, one_mul, mul_one]

/-- The variables of the blocks after the first, among those of the Levi torus. -/
def tailVar (x : Σ q : Fin s, Fin (Fin.tail d q)) : Σ p : Fin (s + 1), Fin (d p) :=
  ⟨x.1.succ, x.2⟩

/-- The first block of a point of the torus. -/
def headTorus (t : (Σ p : Fin (s + 1), Fin (d p)) → Kˣ) : Fin (d 0) → Kˣ := fun i => t ⟨0, i⟩

/-- The other blocks of a point of the torus. -/
def tailTorus (t : (Σ p : Fin (s + 1), Fin (d p)) → Kˣ) :
    (Σ q : Fin s, Fin (Fin.tail d q)) → Kˣ := fun x => t (tailVar x)

/-- **The torus splits** into its first block and the rest. -/
theorem leviTorus_eq_mul (t : (Σ p : Fin (s + 1), Fin (d p)) → Kˣ) :
    leviTorus K d t =
      leviBlock K d 0 (diagGL (headTorus t)) *
        leviTail K d (leviTorus K (Fin.tail d) (tailTorus t)) := by
  rw [← leviBlock_mul_leviTail (leviTorus K d t)]
  rfl

theorem leviCoord_leviTail_mem (x : LeviIndex d) :
    (fun h => leviCoord K d (leviTail K d h) x) ∈ leviPolynomialFunctions K (Fin.tail d) := by
  obtain ⟨p, i, j⟩ := x
  induction p using Fin.cases with
  | zero =>
    have : (fun h => leviCoord K d (leviTail K d h) ⟨0, i, j⟩) =
        fun _ => (1 : Matrix (Fin (d 0)) (Fin (d 0)) K) i j := by
      funext h
      simp [leviCoord]
    rw [this]
    exact Subalgebra.algebraMap_mem _ _
  | succ q =>
    exact coord_mem_coordFunctions (leviCoord K (Fin.tail d)) ⟨q, i, j⟩

/-- **Restricting to the blocks after the first** preserves polynomiality. -/
theorem IsPolynomialLeviRep.comp_leviTail {ρ : Representation K (LeviGroup K d) W}
    (h : IsPolynomialLeviRep ρ) : IsPolynomialLeviRep (ρ.comp (leviTail K d)) :=
  h.comp _ fun _ hf => comp_mem_coordFunctions _ leviCoord_leviTail_mem hf

end

end GLRep
