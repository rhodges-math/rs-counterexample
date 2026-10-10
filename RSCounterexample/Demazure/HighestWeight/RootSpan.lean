import RSCounterexample.Demazure.Representation.TypeA

/-!
# Cyclic spans under root operators

Let `ρ : gl_n → End M` be a representation and `v ∈ M`. For a set `P` of index pairs,
`rootSpan ρ P v` is the smallest subspace containing `v` and stable under the matrix-unit
operators `ρ(E_ab)` with `P a b`. For `P = (· > ·)` this is `U(𝔫⁻)·v`, and for `P = (· < ·)` it
is `U(𝔫⁺)·v`.

`rootSpan_lie_stable`: if every `E_ab` with `¬ P a b` maps `v` into `ℂ·v`, then
`rootSpan ρ P v` is stable under all of `gl_n`. For a highest-weight vector `v`
(`P = (· > ·)`) this is the familiar `U(gl_n)·v = U(𝔫⁻)·v`. The proof uses only the commutator
relations `[E_ab, E_cd] = δ_bc E_ad - δ_da E_cb`.
-/

namespace Demazure.HighestWeight

open FlagModule

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]
  (ρ : Square n →ₗ⁅ℂ⁆ Module.End ℂ M)

/-- The commutator of two matrix units: `[E_ab, E_cd] = δ_bc E_ad - δ_da E_cb`. -/
theorem single_lie_single (a b c d : Fin n) :
    ⁅(Matrix.single a b 1 : Square n), (Matrix.single c d 1 : Square n)⁆ =
      (if b = c then (Matrix.single a d 1 : Square n) else 0) -
        (if d = a then (Matrix.single c b 1 : Square n) else 0) := by
  rw [LieRing.of_associative_ring_bracket]
  congr 1
  · split_ifs with h
    · subst h
      rw [Matrix.single_mul_single_same, one_mul]
    · exact Matrix.single_mul_single_of_ne (h := h) ..
  · split_ifs with h
    · subst h
      rw [Matrix.single_mul_single_same, one_mul]
    · exact Matrix.single_mul_single_of_ne (h := h) ..

/-- `ρ(X)ρ(Y) = ρ(Y)ρ(X) + ρ([X, Y])`. -/
theorem apply_apply_eq (X Y : Square n) (q : M) :
    ρ X (ρ Y q) = ρ Y (ρ X q) + ρ ⁅X, Y⁆ q := by
  rw [LieHom.map_lie, LieRing.of_associative_ring_bracket, LinearMap.sub_apply,
    Module.End.mul_apply, Module.End.mul_apply]
  abel

/-- The smallest subspace containing `v` and stable under `ρ(E_ab)` for every pair with
`P a b`. -/
def rootSpan (P : Fin n → Fin n → Prop) (v : M) : Submodule ℂ M :=
  sInf {S | v ∈ S ∧ ∀ a b, P a b → ∀ q ∈ S, ρ (Matrix.single a b 1) q ∈ S}

variable (P : Fin n → Fin n → Prop)

theorem mem_rootSpan_self (v : M) : v ∈ rootSpan ρ P v :=
  Submodule.mem_sInf.mpr fun _ hS => hS.1

theorem rootSpan_stable (v : M) {a b : Fin n} (h : P a b) {q : M}
    (hq : q ∈ rootSpan ρ P v) : ρ (Matrix.single a b 1) q ∈ rootSpan ρ P v :=
  Submodule.mem_sInf.mpr fun S hS => hS.2 a b h q (Submodule.mem_sInf.mp hq S hS)

theorem rootSpan_le (v : M) {S : Submodule ℂ M} (hv : v ∈ S)
    (hS : ∀ a b, P a b → ∀ q ∈ S, ρ (Matrix.single a b 1) q ∈ S) : rootSpan ρ P v ≤ S :=
  sInf_le ⟨hv, hS⟩

/-- If every matrix unit outside `P` maps `v` into `ℂ·v`, then `rootSpan ρ P v` is stable
under every matrix unit. -/
theorem rootSpan_single_stable (v : M)
    (hv : ∀ a b, ¬ P a b → ∃ c : ℂ, ρ (Matrix.single a b 1) v = c • v) (a b : Fin n) :
    ∀ q ∈ rootSpan ρ P v, ρ (Matrix.single a b 1) q ∈ rootSpan ρ P v := by
  set L := rootSpan ρ P v
  let T : Submodule ℂ M :=
    { carrier := {q | q ∈ L ∧ ∀ a b : Fin n, ρ (Matrix.single a b 1) q ∈ L}
      add_mem' := fun {x y} hx hy =>
        ⟨L.add_mem hx.1 hy.1, fun a b => by rw [map_add]; exact L.add_mem (hx.2 a b) (hy.2 a b)⟩
      zero_mem' := ⟨L.zero_mem, fun a b => by rw [map_zero]; exact L.zero_mem⟩
      smul_mem' := fun c x hx =>
        ⟨L.smul_mem c hx.1, fun a b => by rw [map_smul]; exact L.smul_mem c (hx.2 a b)⟩ }
  have hLT : L ≤ T := by
    refine rootSpan_le ρ P v ⟨mem_rootSpan_self ρ P v, fun a b => ?_⟩ ?_
    · by_cases h : P a b
      · exact rootSpan_stable ρ P v h (mem_rootSpan_self ρ P v)
      · obtain ⟨c, hc⟩ := hv a b h
        rw [hc]
        exact L.smul_mem c (mem_rootSpan_self ρ P v)
    · intro c d hcd q hq
      refine ⟨rootSpan_stable ρ P v hcd hq.1, fun a b => ?_⟩
      rw [apply_apply_eq, single_lie_single, map_sub, LinearMap.sub_apply]
      refine L.add_mem (rootSpan_stable ρ P v hcd (hq.2 a b)) (L.sub_mem ?_ ?_)
      · split_ifs
        · exact hq.2 a d
        · rw [map_zero, LinearMap.zero_apply]; exact L.zero_mem
      · split_ifs
        · exact hq.2 c b
        · rw [map_zero, LinearMap.zero_apply]; exact L.zero_mem
  exact fun q hq => (hLT hq).2 a b

/-- If every matrix unit outside `P` maps `v` into `ℂ·v`, then `rootSpan ρ P v` is stable
under all of `gl_n`. -/
theorem rootSpan_lie_stable (v : M)
    (hv : ∀ a b, ¬ P a b → ∃ c : ℂ, ρ (Matrix.single a b 1) v = c • v) (A : Square n) :
    ∀ q ∈ rootSpan ρ P v, ρ A q ∈ rootSpan ρ P v := by
  intro q hq
  rw [Matrix.matrix_eq_sum_single A, map_sum, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun a _ => ?_
  rw [map_sum, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun b _ => ?_
  have h : (Matrix.single a b (A a b) : Square n) = A a b • Matrix.single a b 1 := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [h, map_smul, LinearMap.smul_apply]
  exact Submodule.smul_mem _ _ (rootSpan_single_stable ρ P v hv a b q hq)

end
end Demazure.HighestWeight
