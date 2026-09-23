import Schubert.RS.Representation.DegreeTorus

namespace Schubert.RS.Representation
noncomputable section

theorem basis_coord_eigenmap {ι E : Type*} [AddCommGroup E] [Module ℂ E]
    (b : Module.Basis ι ℂ E) (f : E →ₗ[ℂ] E) (eigenvalue : ι → ℂ)
    (hf : ∀ i, f (b i) = eigenvalue i • b i) (i : ι) (x : E) :
    b.repr (f x) i = eigenvalue i * b.repr x i := by
  classical
  have h : (b.coord i).comp f = eigenvalue i • b.coord i := by
    apply b.ext
    intro j
    simp only [LinearMap.comp_apply, hf, map_smul, LinearMap.smul_apply,
      Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, smul_eq_mul]
    split_ifs with hij
    · subst j; rfl
    · simp
  exact congrArg (fun g : E →ₗ[ℂ] ℂ => g x) h

def envelopingBasis {n : ℕ} (order : RootOrdering n) (hpbw : HasOrderedPBWBasis n) :
    Module.Basis (PositiveRoot n → ℕ) ℂ (Enveloping n) := (hpbw order).choose

theorem envelopingBasis_apply {n : ℕ} (order : RootOrdering n) (hpbw : HasOrderedPBWBasis n)
    (a : PositiveRoot n → ℕ) :
    envelopingBasis order hpbw a = orderedRootMonomial order a := (hpbw order).choose_spec a

theorem enveloping_coord_cut {n : ℕ} (order : RootOrdering n) (hpbw : HasOrderedPBWBasis n)
    (k : Fin (n - 1)) (a : PositiveRoot n → ℕ) (x : Enveloping n) :
    (envelopingBasis order hpbw).repr (torusEnveloping (cutTorus k) x) a =
      (2 : ℂ) ^ monomialDegree a k * (envelopingBasis order hpbw).repr x a := by
  apply basis_coord_eigenmap (envelopingBasis order hpbw)
    (torusEnveloping (cutTorus k)).toLinearMap (fun a => (2 : ℂ) ^ monomialDegree a k)
  intro a
  rw [envelopingBasis_apply]
  exact torusEnveloping_monomialDegree order a k

/-- Joint cut-torus eigenvectors have support only in the corresponding root
degree. This proves the relevant grading assertion from the genuine action. -/
theorem degree_support_of_cut_eigen {n : ℕ} (order : RootOrdering n) (hpbw : HasOrderedPBWBasis n)
    (x : Enveloping n) (d : RootDegree n)
    (hx : ∀ k, torusEnveloping (cutTorus k) x = (2 : ℂ) ^ d k • x)
    (a : PositiveRoot n → ℕ) (ha : (envelopingBasis order hpbw).repr x a ≠ 0) :
    monomialDegree a = d := by
  ext k
  apply complex_two_pow_injective
  have h := enveloping_coord_cut order hpbw k a x
  rw [hx k, map_smul, Finsupp.smul_apply, smul_eq_mul] at h
  exact (mul_right_cancel₀ ha h).symm

def envelopingDegreePiece {n : ℕ} (order : RootOrdering n) (hpbw : HasOrderedPBWBasis n)
    (d : RootDegree n) : Submodule ℂ (Enveloping n) :=
  Submodule.span ℂ (envelopingBasis order hpbw '' {a | monomialDegree a = d})

theorem cut_eigen_mem_degreePiece {n : ℕ} (order : RootOrdering n) (hpbw : HasOrderedPBWBasis n)
    (x : Enveloping n) (d : RootDegree n)
    (hx : ∀ k, torusEnveloping (cutTorus k) x = (2 : ℂ) ^ d k • x) :
    x ∈ envelopingDegreePiece order hpbw d := by
  apply (envelopingBasis order hpbw).mem_span_image.mpr
  intro a ha
  exact degree_support_of_cut_eigen order hpbw x d hx a (Finsupp.mem_support_iff.mp ha)

theorem degreePiece_cut_eigen {n : ℕ} (order : RootOrdering n) (hpbw : HasOrderedPBWBasis n)
    (d : RootDegree n) {x : Enveloping n} (hx : x ∈ envelopingDegreePiece order hpbw d)
    (k : Fin (n - 1)) : torusEnveloping (cutTorus k) x = (2 : ℂ) ^ d k • x := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    rw [envelopingBasis_apply, torusEnveloping_monomialDegree, ha]
  | zero => simp
  | add x y hx hy ihx ihy => simp only [map_add, ihx, ihy, smul_add]
  | smul c x hx ih => simp only [map_smul, ih, smul_comm c]

/-- Multiplication adds root degrees in the actual noncommutative UEA. -/
theorem envelopingDegreePiece_mul {n : ℕ} (order : RootOrdering n) (hpbw : HasOrderedPBWBasis n)
    (d e : RootDegree n) {x y : Enveloping n}
    (hx : x ∈ envelopingDegreePiece order hpbw d)
    (hy : y ∈ envelopingDegreePiece order hpbw e) :
    x * y ∈ envelopingDegreePiece order hpbw (d + e) := by
  apply cut_eigen_mem_degreePiece
  intro k
  rw [map_mul, degreePiece_cut_eigen order hpbw d hx, degreePiece_cut_eigen order hpbw e hy]
  simp only [smul_mul_smul_comm, Finsupp.add_apply, pow_add]

end
end Schubert.RS.Representation

