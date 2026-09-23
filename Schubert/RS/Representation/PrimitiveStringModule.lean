import Mathlib.Algebra.Lie.Sl2
import Mathlib.Algebra.Lie.Submodule
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.NormNum

namespace Schubert.RS.Representation
noncomputable section
open LieModule Module

variable {L M : Type*} [LieRing L] [LieAlgebra ℂ L]
  [AddCommGroup M] [Module ℂ M] [LieRingModule L M] [LieModule ℂ L M]
  {h e f : L} {m : M} {d : ℕ}

/-- The actual lowering string in a Lie representation. -/
def primitiveStringVector (f : L) (m : M) (k : ℕ) : M :=
  (LieModule.toEnd ℂ L M f ^ k) m

@[simp] theorem primitiveStringVector_zero : primitiveStringVector f m 0 = m := by
  simp [primitiveStringVector]

theorem primitiveStringVector_succ (k : ℕ) :
    primitiveStringVector f m (k+1) = ⁅f,primitiveStringVector f m k⁆ := by
  simp [primitiveStringVector,pow_succ']

/-- Zero highest vectors are allowed in the universal mapping property. -/
theorem highestVector_lowering_h (t : IsSl2Triple h e f)
    (hm : ⁅h,m⁆ = (d:ℂ) • m) (he : ⁅e,m⁆ = 0) (k : ℕ) :
    ⁅h,primitiveStringVector f m k⁆ = ((d:ℂ)-2*k) • primitiveStringVector f m k := by
  by_cases hz : m=0
  · simp [hz,primitiveStringVector]
  · exact (IsSl2Triple.HasPrimitiveVectorWith.mk (t := t) hz hm he).lie_h_pow_toEnd_f k

theorem highestVector_lowering_e (t : IsSl2Triple h e f)
    (hm : ⁅h,m⁆ = (d:ℂ) • m) (he : ⁅e,m⁆ = 0) (k : ℕ) :
    ⁅e,primitiveStringVector f m (k+1)⁆ =
      ((k+1)*((d:ℂ)-k)) • primitiveStringVector f m k := by
  by_cases hz : m=0
  · simp [hz,primitiveStringVector]
  · exact (IsSl2Triple.HasPrimitiveVectorWith.mk (t := t) hz hm he).lie_e_pow_succ_toEnd_f k

theorem highestVector_lowering_end [Module.Finite ℂ M] (t : IsSl2Triple h e f)
    (hm : ⁅h,m⁆ = (d:ℂ) • m) (he : ⁅e,m⁆ = 0) :
    primitiveStringVector f m (d+1) = 0 := by
  by_cases hz : m=0
  · simp [hz,primitiveStringVector]
  · exact (IsSl2Triple.HasPrimitiveVectorWith.mk (t := t) hz hm he).pow_toEnd_f_eq_zero_of_eq_nat rfl

variable {t : IsSl2Triple h e f} (P : t.HasPrimitiveVectorWith m (d:ℂ))

include P in
theorem primitiveStringVector_independent :
    LinearIndependent ℂ (fun k : Fin (d+1) => primitiveStringVector f m k.val) := by
  apply (LieModule.toEnd ℂ L M h).eigenvectors_linearIndependent'
    (fun k : Fin (d+1) => (d:ℂ)-2*k.val)
  · intro i j hij
    apply Fin.ext
    have he : (i.val:ℂ) = j.val := by
      have he := (sub_right_inj).mp hij
      exact (mul_left_cancel₀ (by norm_num : (2:ℂ) ≠ 0)) he
    exact_mod_cast he
  · intro k
    refine ⟨?_,?_⟩
    · exact (Module.End.mem_eigenspace_iff).mpr (P.lie_h_pow_toEnd_f k.val)
    · exact P.pow_toEnd_f_ne_zero_of_eq_nat rfl (Nat.le_of_lt_succ k.isLt)

def primitiveStringSpan (f : L) (m : M) (d : ℕ) : Submodule ℂ M :=
  Submodule.span ℂ (Set.range (fun k : Fin (d+1) => primitiveStringVector f m k.val))

theorem primitiveStringVector_mem (k : Fin (d+1)) :
    primitiveStringVector f m k.val ∈ primitiveStringSpan f m d :=
  Submodule.subset_span ⟨k,rfl⟩

private theorem primitive_span_operator_stable {ι : Type*} (v : ι → M) (D : M →ₗ[ℂ] M)
    (hb : ∀ i, D (v i) ∈ Submodule.span ℂ (Set.range v))
    {x : M} (hx : x ∈ Submodule.span ℂ (Set.range v)) :
    D x ∈ Submodule.span ℂ (Set.range v) := by
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨i,rfl⟩ := hx; exact hb i
  | zero => simp
  | add x y hx hy hx' hy' => simpa only [map_add] using (Submodule.span ℂ (Set.range v)).add_mem hx' hy'
  | smul a x hx hx' => simpa only [map_smul] using (Submodule.span ℂ (Set.range v)).smul_mem a hx'

include P in
theorem primitiveStringSpan_h {x : M} (hx : x ∈ primitiveStringSpan f m d) :
    ⁅h,x⁆ ∈ primitiveStringSpan f m d := by
  apply primitive_span_operator_stable _ (LieModule.toEnd ℂ L M h) _ hx
  intro k
  change ⁅h,primitiveStringVector f m k.val⁆ ∈ _
  rw [highestVector_lowering_h t P.lie_h P.lie_e]
  exact (primitiveStringSpan f m d).smul_mem _ (primitiveStringVector_mem k)

include P in
theorem primitiveStringSpan_e {x : M} (hx : x ∈ primitiveStringSpan f m d) :
    ⁅e,x⁆ ∈ primitiveStringSpan f m d := by
  apply primitive_span_operator_stable _ (LieModule.toEnd ℂ L M e) _ hx
  rintro ⟨k,hk⟩
  cases k with
  | zero =>
      change ⁅e,m⁆ ∈ primitiveStringSpan f m d
      rw [P.lie_e]
      exact (primitiveStringSpan f m d).zero_mem
  | succ k =>
      change ⁅e,primitiveStringVector f m (k+1)⁆ ∈ _
      rw [highestVector_lowering_e t P.lie_h P.lie_e]
      exact (primitiveStringSpan f m d).smul_mem _ (primitiveStringVector_mem ⟨k,by omega⟩)

include P in
theorem primitiveStringSpan_f [Module.Finite ℂ M] {x : M}
    (hx : x ∈ primitiveStringSpan f m d) : ⁅f,x⁆ ∈ primitiveStringSpan f m d := by
  apply primitive_span_operator_stable _ (LieModule.toEnd ℂ L M f) _ hx
  intro k
  change ⁅f,primitiveStringVector f m k.val⁆ ∈ _
  rw [← primitiveStringVector_succ]
  by_cases hk : k.val < d
  · exact primitiveStringVector_mem ⟨k.val+1,by omega⟩
  · have he : k.val=d := by omega
    rw [he,highestVector_lowering_end t P.lie_h P.lie_e]
    exact (primitiveStringSpan f m d).zero_mem

/-- This finite module is a submodule of the given representation, with the
inherited action of the Lie subalgebra generated by the actual sl₂ triple. -/
def primitiveStringModule [Module.Finite ℂ M] : LieSubmodule ℂ (t.toLieSubalgebra ℂ) M where
  toSubmodule := primitiveStringSpan f m d
  lie_mem := by
    intro z x hx
    change ⁅(z:L),x⁆ ∈ primitiveStringSpan f m d
    obtain ⟨a,b,c,hz⟩ := (IsSl2Triple.mem_toLieSubalgebra_iff (R := ℂ) (t := t)).mp z.property
    rw [hz,t.lie_e_f,add_lie,add_lie,smul_lie,smul_lie,smul_lie]
    exact (primitiveStringSpan f m d).add_mem
      ((primitiveStringSpan f m d).add_mem
        ((primitiveStringSpan f m d).smul_mem a (primitiveStringSpan_e P hx))
        ((primitiveStringSpan f m d).smul_mem b (primitiveStringSpan_f P hx)))
      ((primitiveStringSpan f m d).smul_mem c (primitiveStringSpan_h P hx))

def primitiveStringBasis [Module.Finite ℂ M] :
    Module.Basis (Fin (d+1)) ℂ (primitiveStringModule P) :=
  Module.Basis.span (primitiveStringVector_independent P)

theorem primitiveStringBasis_val [Module.Finite ℂ M] (k : Fin (d+1)) :
    (primitiveStringBasis P k).val = primitiveStringVector f m k.val :=
  Module.Basis.coe_span_apply _ _

end
end Schubert.RS.Representation


