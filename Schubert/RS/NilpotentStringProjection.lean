import Mathlib.LinearAlgebra.Projection
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Intervals

/-! A constructive splitting step for a finite nilpotent string. The
functional is supplied explicitly; later graded applications choose it in
the top weight space. No semisimplicity or Jordan decomposition is assumed. -/

namespace Schubert.RS.Representation
noncomputable section
open scoped BigOperators

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

def nilpotentStringProjection (E : Module.End ℂ V) (v : V) (d : ℕ)
    (φ : V →ₗ[ℂ] ℂ) : Module.End ℂ V where
  toFun x := ∑ j ∈ Finset.range (d+1), φ ((E^(d-j)) x) • (E^j) v
  map_add' x y := by simp only [map_add,add_smul,Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [map_smul,smul_smul,Finset.smul_sum,smul_eq_mul,RingHom.id_apply]

theorem end_pow_add_apply (E : Module.End ℂ V) (j k : ℕ) (x : V) :
    (E^(j+k)) x = (E^j) ((E^k) x) := by rw [pow_add]; rfl

theorem end_pow_succ_apply (E : Module.End ℂ V) (k : ℕ) (x : V) :
    (E^(k+1)) x = E ((E^k) x) := by rw [pow_succ']; rfl

theorem end_pow_zero_of_le (E : Module.End ℂ V) {d k : ℕ}
    (hE : E^d=0) (hdk : d≤k) : E^k=0 := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hdk
  rw [pow_add,hE,zero_mul]

theorem nilpotentStringProjection_chain (E : Module.End ℂ V) (v : V) (d : ℕ)
    (φ : V →ₗ[ℂ] ℂ) (hE : E^(d+1)=0)
    (hφ : ∀ j≤d, φ ((E^j) v) = if j=d then 1 else 0) (k : ℕ) (hk : k≤d) :
    nilpotentStringProjection E v d φ ((E^k) v) = (E^k) v := by
  classical
  have ht (j : ℕ) (hj : j∈Finset.range (d+1)) :
      φ ((E^(d-j)) ((E^k) v)) = if j=k then 1 else 0 := by
    rw [← end_pow_add_apply]
    have hj' : j≤d := by have h:=Finset.mem_range.mp hj; omega
    by_cases hsum : d-j+k≤d
    · rw [hφ _ hsum]
      have he : d-j+k=d ↔ j=k := by omega
      simp only [he]
    · rw [end_pow_zero_of_le E hE (by omega),LinearMap.zero_apply,map_zero]
      have hne : j≠k := by omega
      simp only [hne,if_false]
  change (∑ j ∈ Finset.range (d+1), φ ((E^(d-j)) ((E^k) v)) • (E^j) v) = _
  calc
    _ = ∑ j ∈ Finset.range (d+1), (if j=k then (1:ℂ) else 0) • (E^j) v := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [ht j hj]
    _ = _ := by simp [show k<d+1 by omega]

theorem nilpotentStringProjection_commutes (E : Module.End ℂ V) (v : V) (d : ℕ)
    (φ : V →ₗ[ℂ] ℂ) (hE : E^(d+1)=0) (x : V) :
    nilpotentStringProjection E v d φ (E x) = E (nilpotentStringProjection E v d φ x) := by
  have hlast (y : V) : E ((E^d) y)=0 := by
    rw [← end_pow_succ_apply,hE,LinearMap.zero_apply]
  have hfirst : φ ((E^d) (E x))=0 := by
    have he : (E^d) (E x)=(E^(d+1)) x := by
      rw [pow_succ]
      rfl
    rw [he,hE,LinearMap.zero_apply,map_zero]
  change (∑ j ∈ Finset.range (d+1), φ ((E^(d-j)) (E x)) • (E^j) v) =
    E (∑ j ∈ Finset.range (d+1), φ ((E^(d-j)) x) • (E^j) v)
  rw [Finset.sum_range_succ',Finset.sum_range_succ]
  simp only [Nat.sub_zero,pow_zero,Module.End.one_apply,hfirst,zero_smul,add_zero,
    map_add,map_sum,map_smul,hlast,smul_zero]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j<d := Finset.mem_range.mp hj
  have he : (E^(d-(j+1))) (E x)=(E^(d-j)) x := by
    have hd : d-(j+1)+1=d-j := by omega
    rw [← hd,pow_succ]
    rfl
  rw [he,end_pow_succ_apply]

theorem nilpotentStringProjection_mem (E : Module.End ℂ V) (v : V) (d : ℕ)
    (φ : V →ₗ[ℂ] ℂ) (x : V) :
    nilpotentStringProjection E v d φ x ∈
      Submodule.span ℂ (Set.range (fun j : Fin (d+1) => (E^j.val) v)) := by
  change (∑ j ∈ Finset.range (d+1), φ ((E^(d-j)) x) • (E^j) v) ∈ _
  apply Submodule.sum_mem
  intro j hj
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨⟨j,Finset.mem_range.mp hj⟩,rfl⟩

theorem nilpotentStringProjection_isProj (E : Module.End ℂ V) (v : V) (d : ℕ)
    (φ : V →ₗ[ℂ] ℂ) (hE : E^(d+1)=0)
    (hφ : ∀ j≤d, φ ((E^j) v) = if j=d then 1 else 0) :
    LinearMap.IsProj (Submodule.span ℂ (Set.range (fun j : Fin (d+1) => (E^j.val) v)))
      (nilpotentStringProjection E v d φ) := by
  refine ⟨nilpotentStringProjection_mem E v d φ,?_⟩
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j,rfl⟩ := hx
    exact nilpotentStringProjection_chain E v d φ hE hφ j.val (by omega)
  | zero => exact map_zero _
  | add x y hx hy ihx ihy => rw [map_add,ihx,ihy]
  | smul c x hx ih => rw [map_smul,ih]

theorem nilpotentStringProjection_complement (E : Module.End ℂ V) (v : V) (d : ℕ)
    (φ : V →ₗ[ℂ] ℂ) (hE : E^(d+1)=0)
    (hφ : ∀ j≤d, φ ((E^j) v) = if j=d then 1 else 0) :
    IsCompl (Submodule.span ℂ (Set.range (fun j : Fin (d+1) => (E^j.val) v)))
      (LinearMap.ker (nilpotentStringProjection E v d φ)) :=
  (nilpotentStringProjection_isProj E v d φ hE hφ).isCompl

theorem nilpotentStringProjection_kernel_stable (E : Module.End ℂ V) (v : V) (d : ℕ)
    (φ : V →ₗ[ℂ] ℂ) (hE : E^(d+1)=0) (x : V)
    (hx : x∈LinearMap.ker (nilpotentStringProjection E v d φ)) :
    E x∈LinearMap.ker (nilpotentStringProjection E v d φ) := by
  change nilpotentStringProjection E v d φ (E x)=0
  rw [nilpotentStringProjection_commutes E v d φ hE x,hx,map_zero]

theorem end_pow_covariant (E T : Module.End ℂ V) (r : ℂ)
    (hTE : ∀ x, T (E x) = r • E (T x)) (k : ℕ) (x : V) :
    T ((E^k) x) = r^k • (E^k) (T x) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [end_pow_succ_apply,hTE,ih,map_smul,end_pow_succ_apply,pow_succ']
    simp only [smul_smul]

/-- The splitting respects every weight operator when the functional is
homogeneous of the top-string weight. This is the extra condition needed
for a graded Jordan splitting, rather than an ungraded complement. -/
theorem nilpotentStringProjection_equivariant (E T : Module.End ℂ V)
    (v : V) (d : ℕ) (φ : V →ₗ[ℂ] ℂ) (r μ : ℂ) (hr : r≠0)
    (hTE : ∀ x, T (E x) = r • E (T x)) (hv : T v = μ • v)
    (hφ : ∀ x, φ (T x) = (μ*r^d) * φ x) (x : V) :
    nilpotentStringProjection E v d φ (T x) =
      T (nilpotentStringProjection E v d φ x) := by
  have hc (j : ℕ) (hj : j≤d) :
      φ ((E^(d-j)) (T x)) = (μ*r^j) * φ ((E^(d-j)) x) := by
    apply mul_left_cancel₀ (pow_ne_zero (d-j) hr)
    calc
      r^(d-j) * φ ((E^(d-j)) (T x)) = φ (T ((E^(d-j)) x)) := by
        rw [end_pow_covariant E T r hTE,map_smul,smul_eq_mul]
      _ = (μ*r^d) * φ ((E^(d-j)) x) := hφ _
      _ = r^(d-j) * ((μ*r^j) * φ ((E^(d-j)) x)) := by
        have he : r^(d-j)*r^j=r^d := by rw [← pow_add,Nat.sub_add_cancel hj]
        rw [← he]
        ring
  change (∑ j ∈ Finset.range (d+1), φ ((E^(d-j)) (T x)) • (E^j) v) =
    T (∑ j ∈ Finset.range (d+1), φ ((E^(d-j)) x) • (E^j) v)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [hc j (by have h:=Finset.mem_range.mp hj; omega),map_smul,
    end_pow_covariant E T r hTE,hv,map_smul]
  simp only [smul_smul]
  congr 1
  ring

theorem nilpotentStringProjection_kernel_torus_stable (E T : Module.End ℂ V)
    (v : V) (d : ℕ) (φ : V →ₗ[ℂ] ℂ) (r μ : ℂ) (hr : r≠0)
    (hTE : ∀ x, T (E x) = r • E (T x)) (hv : T v = μ • v)
    (hφ : ∀ x, φ (T x) = (μ*r^d) * φ x) (x : V)
    (hx : x∈LinearMap.ker (nilpotentStringProjection E v d φ)) :
    T x∈LinearMap.ker (nilpotentStringProjection E v d φ) := by
  change nilpotentStringProjection E v d φ (T x)=0
  rw [nilpotentStringProjection_equivariant E T v d φ r μ hr hTE hv hφ x,hx,map_zero]

end
end Schubert.RS.Representation
