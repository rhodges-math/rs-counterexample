import RSCounterexample.FlagVarieties.LineBundle.Model
import RSCounterexample.GLRep.Borel.Evaluation
import RSCounterexample.Demazure.SchubertUnions.Character
import RSCounterexample.FlagVarieties.PointModel.Unitriangular
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Coordinate.HopfAlgebra

/-!
# The ring model of Schubert unions in `GL_n(ℂ)`

This file sets up the purely ring-theoretic objects of the projective normality theorem.

* `GLCoord n`: the coordinate ring `𝒪(GL_n) = ℂ[x_ij][det⁻¹]`, Tau Ceti's
  `TauCeti.GeneralLinear.CoordinateRing ℂ n`.
* `evalAt g`: evaluation of a polynomial in the matrix entries at a matrix `g`; `glEval g`:
  evaluation of `𝒪(GL_n)` at an invertible matrix `g`.
* `IsBorel b`: `b` is upper triangular (the Borel subgroup `B` of upper-triangular matrices).
* `bruhatCell w = B ẇ B` and `orbitSet S = ⋃_{w ∈ S} B ẇ B`, as sets of invertible matrices. Here
  `ẇ = rowPermutationMatrix w` sends `e_j` to `e_{w j}`. For a Bruhat ideal `S` (`BruhatLower S`)
  this is the preimage `π⁻¹ X_S` of the Schubert union in `GL_n`, on `ℂ`-points.
* `orbitIdeal S`: the ideal of functions in `𝒪(GL_n)` vanishing on `orbitSet S`; this is `I_S^G`.
* `IsSemiInvOn Z η t`: `t(g b) = η(b) t(g)` for `g ∈ Z`, `b ∈ B`, with `η(b) = ∏ᵢ b_ii^{ηᵢ}`.
  The sections of `𝓛(-λ)` over `X_S` are the classes of the `t` with `IsSemiInvOn (orbitSet S) λ t`.
* `GlobalSectionsConstant w`: the ring form of `Γ(X_w, 𝒪) = ℂ` — a right `B`-invariant function on
  `orbitSet (lowerSet w)` is constant there.
-/

open Schubert Demazure.FlagModule
open GLRep (glEval)

namespace FlagVarieties.PointModel.Complex

noncomputable section

variable {n : ℕ}

/-- The generic determinant `det (x_ij)` in the polynomial ring of the matrix entries. -/
abbrev detPoly (n : ℕ) : MatrixPolynomial n := (Matrix.mvPolynomialX (Fin n) (Fin n) ℂ).det

/-- Evaluation of a polynomial in the matrix entries at the matrix `g`. -/
def evalAt (g : Matrix (Fin n) (Fin n) ℂ) : MatrixPolynomial n →ₐ[ℂ] ℂ :=
  MvPolynomial.aeval fun rc => g rc.1 rc.2

@[simp]
theorem evalAt_X (g : Matrix (Fin n) (Fin n) ℂ) (r c : Fin n) :
    evalAt g (MvPolynomial.X (r, c)) = g r c :=
  MvPolynomial.aeval_X _ _

theorem evalAt_det (g : Matrix (Fin n) (Fin n) ℂ)
    (M : Matrix (Fin n) (Fin n) (MatrixPolynomial n)) :
    evalAt g M.det = ((evalAt g).mapMatrix M).det :=
  AlgHom.map_det _ _

theorem evalAt_detPoly (g : Matrix (Fin n) (Fin n) ℂ) : evalAt g (detPoly n) = g.det := by
  rw [evalAt_det]
  congr 1
  ext i j
  simp [AlgHom.mapMatrix_apply, Matrix.mvPolynomialX_apply]

theorem isUnit_evalAt_detPoly (g : GL (Fin n) ℂ) :
    IsUnit (evalAt (g : Matrix _ _ ℂ) (detPoly n)) := by
  rw [evalAt_detPoly]
  exact (Matrix.isUnit_iff_isUnit_det _).mp g.isUnit

theorem glEval_algebraMap_eq_evalAt (g : GL (Fin n) ℂ) (f : MatrixPolynomial n) :
    glEval g (algebraMap (MatrixPolynomial n) (GLCoord ℂ n) f) = evalAt (g : Matrix _ _ ℂ) f := by
  exact GLRep.glEval_algebraMap g f

/-- Every element of `𝒪(GL_n)` is `f / det^k` for a polynomial `f`. -/
theorem exists_mul_det_pow (t : GLCoord ℂ n) :
    ∃ (f : MatrixPolynomial n) (k : ℕ),
      t * algebraMap (MatrixPolynomial n) (GLCoord ℂ n) (detPoly n ^ k) =
        algebraMap (MatrixPolynomial n) (GLCoord ℂ n) f := by
  obtain ⟨⟨f, ⟨_, k, rfl⟩⟩, hf⟩ := IsLocalization.surj (Submonoid.powers (detPoly n)) t
  exact ⟨f, k, hf⟩

/-! ### The Borel subgroup and Bruhat cells -/

/-- `b` lies in the Borel subgroup `B` of upper-triangular invertible matrices. -/
def IsBorel (b : GL (Fin n) ℂ) : Prop := (b : Matrix (Fin n) (Fin n) ℂ).IsUpperTriangular

theorem IsBorel.mul {b b' : GL (Fin n) ℂ} (hb : IsBorel b) (hb' : IsBorel b') :
    IsBorel (b * b') := by
  unfold IsBorel at *
  rw [Units.val_mul]
  exact hb.mul hb'

theorem IsBorel.inv {b : GL (Fin n) ℂ} (hb : IsBorel b) : IsBorel b⁻¹ := by
  unfold IsBorel at *
  rw [Matrix.coe_units_inv]
  exact Matrix.blockTriangular_inv_of_blockTriangular hb

theorem isBorel_one : IsBorel (1 : GL (Fin n) ℂ) := by
  unfold IsBorel
  rw [Units.val_one]
  exact Matrix.blockTriangular_one

/-- The permutation matrix `ẇ` as an invertible matrix (`ẇ e_j = e_{w j}`). -/
abbrev permGL (w : Equiv.Perm (Fin n)) : GL (Fin n) ℂ := rowPermutationUnit w

@[simp]
theorem coe_permGL (w : Equiv.Perm (Fin n)) :
    (permGL w : Matrix (Fin n) (Fin n) ℂ) = rowPermutationMatrix w := rfl

/-- The Bruhat cell `B ẇ B`. -/
def bruhatCell (w : Equiv.Perm (Fin n)) : Set (GL (Fin n) ℂ) :=
  {g | ∃ b₁ b₂ : GL (Fin n) ℂ, IsBorel b₁ ∧ IsBorel b₂ ∧ g = b₁ * permGL w * b₂}

/-- The union `⋃_{w ∈ S} B ẇ B`. For a Bruhat ideal `S` it is the preimage of the Schubert union
`X_S` in `GL_n`. -/
def orbitSet (S : Finset (Equiv.Perm (Fin n))) : Set (GL (Fin n) ℂ) :=
  ⋃ w ∈ S, bruhatCell w

theorem mem_orbitSet {S : Finset (Equiv.Perm (Fin n))} {g : GL (Fin n) ℂ} :
    g ∈ orbitSet S ↔ ∃ w ∈ S, g ∈ bruhatCell w := by
  simp [orbitSet]

theorem orbitSet_mono {S S' : Finset (Equiv.Perm (Fin n))} (h : S ⊆ S') :
    orbitSet S ⊆ orbitSet S' := fun _ hg => by
  obtain ⟨w, hw, hg⟩ := mem_orbitSet.mp hg
  exact mem_orbitSet.mpr ⟨w, h hw, hg⟩

theorem orbitSet_union (S S' : Finset (Equiv.Perm (Fin n))) :
    orbitSet (S ∪ S') = orbitSet S ∪ orbitSet S' := by
  ext g
  simp only [Set.mem_union, mem_orbitSet, Finset.mem_union]
  constructor
  · rintro ⟨w, hw | hw, hg⟩
    · exact Or.inl ⟨w, hw, hg⟩
    · exact Or.inr ⟨w, hw, hg⟩
  · rintro (⟨w, hw, hg⟩ | ⟨w, hw, hg⟩)
    · exact ⟨w, Or.inl hw, hg⟩
    · exact ⟨w, Or.inr hw, hg⟩

theorem bruhatCell_mul_borel {w : Equiv.Perm (Fin n)} {g b : GL (Fin n) ℂ} (hg : g ∈ bruhatCell w)
    (hb : IsBorel b) : g * b ∈ bruhatCell w := by
  obtain ⟨b₁, b₂, h₁, h₂, rfl⟩ := hg
  exact ⟨b₁, b₂ * b, h₁, h₂.mul hb, by simp only [mul_assoc]⟩

theorem orbitSet_mul_borel {S : Finset (Equiv.Perm (Fin n))} {g b : GL (Fin n) ℂ}
    (hg : g ∈ orbitSet S) (hb : IsBorel b) : g * b ∈ orbitSet S := by
  obtain ⟨w, hw, hg⟩ := mem_orbitSet.mp hg
  exact mem_orbitSet.mpr ⟨w, hw, bruhatCell_mul_borel hg hb⟩

theorem permGL_mem_bruhatCell (w : Equiv.Perm (Fin n)) : permGL w ∈ bruhatCell w :=
  ⟨1, 1, isBorel_one, isBorel_one, by simp⟩

/-! ### Orbit ideals -/

/-- The ideal `I_S^G ⊆ 𝒪(GL_n)` of functions vanishing on `orbitSet S`. -/
def orbitIdeal (S : Finset (Equiv.Perm (Fin n))) : Ideal (GLCoord ℂ n) where
  carrier := {t | ∀ g ∈ orbitSet S, glEval g t = 0}
  add_mem' {a b} ha hb g hg := by rw [map_add, ha g hg, hb g hg, add_zero]
  zero_mem' g _ := map_zero _
  smul_mem' c a ha g hg := by rw [smul_eq_mul, map_mul, ha g hg, mul_zero]

theorem mem_orbitIdeal {S : Finset (Equiv.Perm (Fin n))} {t : GLCoord ℂ n} :
    t ∈ orbitIdeal S ↔ ∀ g ∈ orbitSet S, glEval g t = 0 :=
  Iff.rfl

/-! ### Semi-invariance -/

/-- The value `η(b) = ∏ᵢ b_ii^{ηᵢ}` of the character `η` of `B` at a matrix `b`. -/
def borelCharValue (η : Fin n → ℤ) (b : Matrix (Fin n) (Fin n) ℂ) : ℂ := ∏ i, b i i ^ η i

/-- `t` is semi-invariant of weight `η` on `Z` under right translation by `B`. -/
def IsSemiInvOn (Z : Set (GL (Fin n) ℂ)) (η : Fin n → ℤ) (t : GLCoord ℂ n) : Prop :=
  ∀ g ∈ Z, ∀ b : GL (Fin n) ℂ, IsBorel b → glEval (g * b) t = borelCharValue η (b : Matrix _ _ ℂ) *
      glEval g t

theorem IsSemiInvOn.mono {Z Z' : Set (GL (Fin n) ℂ)} {η : Fin n → ℤ} {t : GLCoord ℂ n}
    (h : IsSemiInvOn Z' η t) (hZ : Z ⊆ Z') : IsSemiInvOn Z η t :=
  fun g hg b hb => h g (hZ hg) b hb

theorem IsSemiInvOn.sub {Z : Set (GL (Fin n) ℂ)} {η : Fin n → ℤ} {t t' : GLCoord ℂ n}
    (h : IsSemiInvOn Z η t) (h' : IsSemiInvOn Z η t') : IsSemiInvOn Z η (t - t') :=
  fun g hg b hb => by rw [map_sub, map_sub, h g hg b hb, h' g hg b hb, mul_sub]

/-- The weight `λ` of the flag-minor products of column shape `m`, as an integer vector. -/
def _root_.FlagVarieties.PointModel.shapeWeightZ (m : ColumnShape n) : Fin n → ℤ := fun i =>
    (shapeWeight m i : ℤ)

/-! ### Constant global sections -/

/-- The Bruhat interval `{v | v ≤ w}`. -/
def _root_.FlagVarieties.PointModel.lowerSet (w : Equiv.Perm (Fin n)) :
    Finset (Equiv.Perm (Fin n)) := by
  classical exact Finset.univ.filter fun v => v ≤ᴮ w

theorem _root_.FlagVarieties.PointModel.mem_lowerSet {v w : Equiv.Perm (Fin n)} :
    v ∈ lowerSet w ↔ v ≤ᴮ w := by
  classical
  simp [lowerSet]

-- The field-free notions above live in `FlagVarieties.PointModel`; they are also names here.
export PointModel (shapeWeightZ lowerSet mem_lowerSet)

/-- **Constant global sections** `Γ(X_w, 𝒪) = ℂ`, in ring form: a function on `π⁻¹ X_w` that is
invariant under right translation by `B` is constant. It is an input of the projective normality
theorem,
supplied by the geometry of `X_w`. -/
def GlobalSectionsConstant (w : Equiv.Perm (Fin n)) : Prop :=
  ∀ t : GLCoord ℂ n, IsSemiInvOn (orbitSet (lowerSet w)) 0 t →
    ∃ c : ℂ, t - algebraMap ℂ (GLCoord ℂ n) c ∈ orbitIdeal (lowerSet w)

end

end FlagVarieties.PointModel.Complex
