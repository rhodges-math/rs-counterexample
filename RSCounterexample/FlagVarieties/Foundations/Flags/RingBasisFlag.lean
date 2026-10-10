import RSCounterexample.FlagVarieties.Foundations.Flags.RingTransport

/-!
# Ring-valued flags from ordered bases

The steps are the initial spans of the given basis. Their quotients
are free by the tail-coordinate map, including both endpoints.
-/

noncomputable section

namespace FlagVarieties.Foundations.RingFlag

open Module

universe u v

variable {R : Type u} [CommRing R] {M : Type v}
  [AddCommGroup M] [Module R M] {n : ℕ}

/-- Coordinates after the first `j` basis vectors. -/
def basisTailCoordinates (b : Basis (Fin n) R M) (j : Fin (n + 1)) :
    M →ₗ[R] (Fin (n - j.val) → R) where
  toFun x i := b.repr x ⟨j.val + i.val, by omega⟩
  map_add' x y := by ext i; simp
  map_smul' c x := by ext i; simp

theorem basisTailCoordinates_surjective (b : Basis (Fin n) R M)
    (j : Fin (n + 1)) : Function.Surjective (basisTailCoordinates b j) := by
  classical
  intro c
  let v : Fin n → R := fun i => if h : j.val ≤ i.val then
    c ⟨i.val - j.val, by omega⟩ else 0
  refine ⟨b.equivFun.symm v, ?_⟩
  ext i
  change b.equivFun (b.equivFun.symm v) ⟨j.val + i.val, by omega⟩ = c i
  rw [b.equivFun.apply_symm_apply]
  simp [v]

theorem basisTailCoordinates_ker (b : Basis (Fin n) R M)
    (j : Fin (n + 1)) : LinearMap.ker (basisTailCoordinates b j) = b.flag j := by
  ext x
  rw [Basis.flag, b.mem_span_image]
  constructor
  · intro hx i hi
    have hx' : basisTailCoordinates b j x = 0 := hx
    have hi' : b.repr x i ≠ 0 := Finsupp.mem_support_iff.mp hi
    change i.val < j.val
    by_contra h
    have hji : j.val ≤ i.val := by omega
    let t : Fin (n - j.val) := ⟨i.val - j.val, by omega⟩
    have ht := congrFun hx' t
    change b.repr x ⟨j.val + t.val, by omega⟩ = 0 at ht
    have he : (⟨j.val + t.val, by omega⟩ : Fin n) = i := by
      apply Fin.ext
      dsimp [t]
      omega
    rw [he] at ht
    exact hi' ht
  · intro hx
    change basisTailCoordinates b j x = 0
    ext i
    change b.repr x ⟨j.val + i.val, by omega⟩ = 0
    by_contra h
    have hi := hx (Finsupp.mem_support_iff.mpr h)
    change j.val + i.val < j.val at hi
    omega

/-- The quotient by the initial span is the remaining coordinate module. -/
def basisFlagQuotientEquiv (b : Basis (Fin n) R M) (j : Fin (n + 1)) :
    (M ⧸ b.flag j) ≃ₗ[R] (Fin (n - j.val) → R) := by
  rw [← basisTailCoordinates_ker]
  exact (basisTailCoordinates b j).quotKerEquivOfSurjective
    (basisTailCoordinates_surjective b j)

/-- The ordered basis defines a complete ring flag with its initial spans. -/
def ofBasis (b : Basis (Fin n) R M) : RingFlag R M n where
  step j :=
    { toSubmodule := b.flag j
      finite_quotient := Module.Finite.equiv (basisFlagQuotientEquiv b j).symm
      projective_quotient := Module.Projective.of_equiv (basisFlagQuotientEquiv b j).symm
      rankAtStalk_eq p := by
        have : Nontrivial R := ⟨⟨0, 1, fun h => p.isPrime.ne_top (by
          apply (Ideal.eq_top_iff_one _).mpr
          rw [← h]
          exact p.asIdeal.zero_mem)⟩⟩
        rw [congrFun (Module.rankAtStalk_eq_of_equiv (basisFlagQuotientEquiv b j)) p]
        simp }
  step_mono := b.flag_mono
  step_zero := b.flag_zero
  step_last := b.flag_last

@[simp] theorem ofBasis_step (b : Basis (Fin n) R M) (j : Fin (n + 1)) :
    ((ofBasis b).step j).toSubmodule = b.flag j := rfl

theorem ofBasis_step_span (b : Basis (Fin n) R M) (j : Fin (n + 1)) :
    ((ofBasis b).step j).toSubmodule =
      Submodule.span R (b '' {i | i.val < j.val}) := rfl

/-- An adapted ordered basis recovers the given flag, without new choices of steps. -/
theorem ofBasis_eq_of_adapted (F : RingFlag R M n) (b : Basis (Fin n) R M)
    (hb : ∀ j, (F.step j).toSubmodule =
      Submodule.span R (b '' {i | i.val < j.val})) : ofBasis b = F := by
  apply RingFlag.ext
  intro j
  exact (hb j).symm

@[simp] theorem ofFieldFlag_ofBasis {K : Type u} [Field K]
    (b : Basis (Fin n) K (Fin n → K)) :
    ofFieldFlag (Schubert.Geometry.CompleteFlag.ofBasis b) = ofBasis b := by
  apply RingFlag.ext
  intro j
  rfl

end FlagVarieties.Foundations.RingFlag
