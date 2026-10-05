import Schubert.GLRep.Borel.Torus
import Schubert.GLRep.Rational.GL
import TauCeti.LinearAlgebra.Matrix.Triangular

/-!
# The Borel subgroup of `GL_n` and its rational representations

Let `K` be a commutative ring. The **Borel subgroup** `B = GLRep.borel K n ⊆ GL_n(K)` is the group
of invertible upper-triangular matrices. Reading off the diagonal is a surjective homomorphism
`B → T` onto the diagonal torus `T = (Kˣ)ⁿ` (`GLRep.borelDiag`), split by the diagonal matrices
(`GLRep.borelTorus`); its kernel is the unipotent radical `U` of upper unitriangular matrices
(`GLRep.borelUnipotent`). A weight `η ∈ ℤⁿ` gives the character
`η(b) = ∏ᵢ b_ii^{ηᵢ}` of `B` (`GLRep.borelChar`).

The **regular functions** on `B` are the polynomials in the matrix entries `b_ij` and in the
inverses `b_ii⁻¹` of the diagonal entries: they are the polynomial functions
(`GLRep.coordFunctions`) for the coordinate system `GLRep.borelCoord K n`, and form the subalgebra
`GLRep.borelFunctions K n`. Over a field, a representation of `B` is **rational**
(`GLRep.IsRationalBorelRep`) when it is finite-dimensional and its matrix coefficients are regular
functions on `B`. This is the notion of a finite-dimensional rational `B`-module of
[Jantzen, *Representations of Algebraic Groups*, I.2] read on `K`-points, in the style of
`GLRep.IsPolynomialRep`; over an infinite field the coordinate ring of the group scheme `B` embeds
into the functions on `B(K)`.

Rational representations of `B` are closed under subrepresentations, quotients, products, tensor
products and restriction (the general lemmas on `GLRep.HasCoeffsIn`), and under twists by the
characters `η` (`GLRep.IsRationalBorelRep.scaledRep_borelChar`).

## Main definitions

* `GLRep.borel K n`, `GLRep.borelDiag`, `GLRep.borelTorus`, `GLRep.borelUnipotent`,
  `GLRep.borelChar`.
* `GLRep.borelCoord K n`, `GLRep.borelFunctions K n`, `GLRep.IsRationalBorelRep`.
* `GLRep.borelCharRep K n η`: the one-dimensional representation `K_η` of `B`.

## Main results

* `GLRep.det_borel`, `GLRep.detZPow_borel`: the determinant on `B` is the character `(1, …, 1)`.
* `GLRep.IsRationalRep.restrictBorel`: the restriction to `B` of a rational representation of
  `GL_n(K)` is rational.
* `GLRep.IsRationalBorelRep.isRationalTorusRep`: the restriction to the torus of a rational
  representation of `B` is rational.
-/

namespace GLRep

open Module TauCeti

noncomputable section

/-! ### The Borel subgroup -/

section Group

variable {K : Type*} [CommRing K] {n : ℕ}

variable (K n) in
/-- The **Borel subgroup** `B ⊆ GL_n(K)` of invertible upper-triangular matrices. -/
def borel : Subgroup (GL (Fin n) K) where
  carrier := {g | (g : Matrix (Fin n) (Fin n) K).IsUpperTriangular}
  one_mem' := Matrix.blockTriangular_one
  mul_mem' := by
    intro g h hg hh
    simpa only [Set.mem_ofPred_eq, Units.val_mul] using hg.mul hh
  inv_mem' := by
    intro g hg
    simpa only [Set.mem_ofPred_eq, Matrix.coe_units_inv] using
      Matrix.blockTriangular_inv_of_blockTriangular hg

theorem mem_borel {g : GL (Fin n) K} :
    g ∈ borel K n ↔ (g : Matrix (Fin n) (Fin n) K).IsUpperTriangular :=
  Iff.rfl

theorem mem_borel_iff_forall {g : GL (Fin n) K} :
    g ∈ borel K n ↔ ∀ i j, j < i → (g : Matrix (Fin n) (Fin n) K) i j = 0 :=
  ⟨fun h _ _ hij => h hij, fun h _ _ hij => h _ _ hij⟩

/-- The matrix of an element of `B` is upper triangular. -/
theorem isUpperTriangular_borel (b : borel K n) :
    ((b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).IsUpperTriangular :=
  b.2

/-- The entries below the diagonal of an element of `B` vanish. -/
theorem borel_apply_of_lt (b : borel K n) {i j : Fin n} (h : j < i) :
    ((b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j = 0 :=
  b.2 h

/-! ### The diagonal and the torus -/

variable (K n) in
/-- The **diagonal** `b ↦ (b_ii)ᵢ` of an element of `B`, a homomorphism `B → T = (Kˣ)ⁿ`. -/
def borelDiag : borel K n →* (Fin n → Kˣ) :=
  MulEquiv.piUnits.toMonoidHom.comp <| MonoidHom.toHomUnits
    { toFun := fun b i => ((b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i i
      map_one' := by
        funext i
        simp
      map_mul' := fun g h => funext fun i =>
        Matrix.mul_apply_diag_of_isUpperTriangular g.2 h.2 i }

@[simp]
theorem borelDiag_apply_val (b : borel K n) (i : Fin n) :
    ((borelDiag K n b i : Kˣ) : K) = ((b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i i := by
  simp [borelDiag]

variable (K n) in
/-- The **diagonal torus** `T ⊆ B`: `t ↦ diag(t)`. -/
def borelTorus : (Fin n → Kˣ) →* borel K n :=
  (diagGL (k := K) (ι := Fin n)).codRestrict (borel K n) fun t _ _ hji => by
    rw [diagGL_coe]
    exact Matrix.diagonal_apply_ne _ (ne_of_gt hji)

@[simp]
theorem coe_borelTorus (t : Fin n → Kˣ) :
    ((borelTorus K n t : borel K n) : GL (Fin n) K) = diagGL t :=
  rfl

@[simp]
theorem borelDiag_borelTorus (t : Fin n → Kˣ) : borelDiag K n (borelTorus K n t) = t := by
  funext i
  ext
  simp [borelDiag_apply_val, coe_borelTorus, diagGL_apply]

theorem borelDiag_comp_borelTorus : (borelDiag K n).comp (borelTorus K n) = MonoidHom.id _ :=
  MonoidHom.ext borelDiag_borelTorus

theorem borelDiag_surjective : Function.Surjective (borelDiag K n) := fun t =>
  ⟨borelTorus K n t, borelDiag_borelTorus t⟩

theorem borelTorus_injective : Function.Injective (borelTorus K n) :=
  Function.LeftInverse.injective borelDiag_borelTorus

/-- The determinant of an element of `B` is the product of its diagonal entries. -/
theorem det_borel (b : borel K n) :
    Matrix.GeneralLinearGroup.det (b : GL (Fin n) K) = ∏ i, borelDiag K n b i := by
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.coe_prod,
    Matrix.det_of_isUpperTriangular b.2]
  simp only [borelDiag_apply_val]

/-! ### The unipotent radical -/

variable (K n) in
/-- The **unipotent radical** `U ⊆ B`: the kernel of the diagonal, that is, the upper
unitriangular matrices. -/
def borelUnipotent : Subgroup (borel K n) := (borelDiag K n).ker

theorem mem_borelUnipotent {b : borel K n} :
    b ∈ borelUnipotent K n ↔ ∀ i, ((b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i i = 1 := by
  rw [borelUnipotent, MonoidHom.mem_ker, funext_iff]
  refine forall_congr' fun i => ?_
  rw [Pi.one_apply, ← Units.val_eq_one, borelDiag_apply_val]

/-- **`B = T ⋉ U`**: dividing an element of `B` by its diagonal gives an element of `U`. -/
theorem inv_borelTorus_borelDiag_mul_mem (b : borel K n) :
    (borelTorus K n (borelDiag K n b))⁻¹ * b ∈ borelUnipotent K n := by
  rw [borelUnipotent, MonoidHom.mem_ker, map_mul, map_inv, borelDiag_borelTorus, inv_mul_cancel]

/-! ### Characters -/

variable (K n) in
/-- The **character** `η(b) = ∏ᵢ b_ii^{ηᵢ}` of `B` attached to a weight `η ∈ ℤⁿ`. -/
def borelChar (η : Fin n → ℤ) : borel K n →* Kˣ := (weightChar K η).comp (borelDiag K n)

theorem borelChar_apply (η : Fin n → ℤ) (b : borel K n) :
    borelChar K n η b = ∏ i, borelDiag K n b i ^ η i :=
  rfl

@[simp]
theorem borelChar_borelTorus (η : Fin n → ℤ) (t : Fin n → Kˣ) :
    borelChar K n η (borelTorus K n t) = weightChar K η t := by
  rw [borelChar, MonoidHom.comp_apply, borelDiag_borelTorus]

theorem borelChar_add (η ν : Fin n → ℤ) :
    borelChar K n (η + ν) = borelChar K n η * borelChar K n ν := by
  rw [borelChar, borelChar, borelChar, weightChar_add, MonoidHom.mul_comp]

@[simp]
theorem borelChar_zero : borelChar K n 0 = 1 := by
  rw [borelChar, weightChar_zero, MonoidHom.one_comp]

theorem borelChar_neg (η : Fin n → ℤ) : borelChar K n (-η) = (borelChar K n η)⁻¹ :=
  MonoidHom.ext fun b => by
    simp only [MonoidHom.inv_apply, borelChar, MonoidHom.comp_apply, weightChar_apply,
      torusCharacter_neg]

/-! ### Regular functions -/

variable (K n) in
/-- The **coordinates** of `b ∈ B`: the matrix entries `b_ij` (index `Sum.inl (i, j)`) and the
inverses `b_ii⁻¹` of the diagonal entries (index `Sum.inr i`). -/
def borelCoord (b : borel K n) : (Fin n × Fin n) ⊕ Fin n → K :=
  Sum.elim (fun p => ((b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) p.1 p.2)
    fun i => (((borelDiag K n b i)⁻¹ : Kˣ) : K)

@[simp]
theorem borelCoord_inl (b : borel K n) (i j : Fin n) :
    borelCoord K n b (Sum.inl (i, j)) = ((b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j :=
  rfl

@[simp]
theorem borelCoord_inr (b : borel K n) (i : Fin n) :
    borelCoord K n b (Sum.inr i) = (((borelDiag K n b i)⁻¹ : Kˣ) : K) :=
  rfl

variable (K n) in
/-- The **regular functions** on `B`: the polynomials in the entries `b_ij` and in the inverses
`b_ii⁻¹` of the diagonal entries. -/
abbrev borelFunctions : Subalgebra K (borel K n → K) := coordFunctions K (borelCoord K n)

theorem entry_mem_borelFunctions (i j : Fin n) :
    (fun b : borel K n => ((b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j) ∈
      borelFunctions K n :=
  coord_mem_coordFunctions (borelCoord K n) (Sum.inl (i, j))

theorem diag_mem_borelFunctions (i : Fin n) :
    (fun b : borel K n => ((borelDiag K n b i : Kˣ) : K)) ∈ borelFunctions K n := by
  simpa only [borelDiag_apply_val] using entry_mem_borelFunctions (K := K) i i

theorem diag_inv_mem_borelFunctions (i : Fin n) :
    (fun b : borel K n => (((borelDiag K n b i)⁻¹ : Kˣ) : K)) ∈ borelFunctions K n :=
  coord_mem_coordFunctions (borelCoord K n) (Sum.inr i)

/-- If the values of a unit-valued function and of its inverse lie in a subalgebra of functions,
so do the values of all its integer powers. -/
theorem zpow_val_mem {G : Type*} {A : Subalgebra K (G → K)} {u : G → Kˣ}
    (h₁ : (fun g => (u g : K)) ∈ A) (h₂ : (fun g => (((u g)⁻¹ : Kˣ) : K)) ∈ A) (z : ℤ) :
    (fun g => ((u g ^ z : Kˣ) : K)) ∈ A := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg z
  · have : (fun g => ((u g ^ (m : ℤ) : Kˣ) : K)) = (fun g => (u g : K)) ^ m := by
      funext g
      simp only [zpow_natCast, Units.val_pow_eq_pow_val, Pi.pow_apply]
    rw [this]
    exact pow_mem h₁ m
  · have : (fun g => ((u g ^ (-(m : ℤ)) : Kˣ) : K)) = (fun g => (((u g)⁻¹ : Kˣ) : K)) ^ m := by
      funext g
      simp only [zpow_neg, zpow_natCast, Pi.pow_apply, ← Units.val_pow_eq_pow_val, inv_pow]
    rw [this]
    exact pow_mem h₂ m

/-- The characters of `B` are regular functions. -/
theorem borelChar_mem_borelFunctions (η : Fin n → ℤ) :
    (fun b : borel K n => ((borelChar K n η b : Kˣ) : K)) ∈ borelFunctions K n := by
  have : (fun b : borel K n => ((borelChar K n η b : Kˣ) : K)) =
      ∏ i, fun b => ((borelDiag K n b i ^ η i : Kˣ) : K) := by
    funext b
    rw [Finset.prod_apply, borelChar_apply, Units.coe_prod]
  rw [this]
  exact prod_mem fun i _ =>
    zpow_val_mem (diag_mem_borelFunctions i) (diag_inv_mem_borelFunctions i) (η i)

/-- Regular functions on `B` restrict to Laurent functions on the torus. -/
theorem comp_borelTorus_mem {f : borel K n → K} (hf : f ∈ borelFunctions K n) :
    f ∘ borelTorus K n ∈ laurentFunctions K (Fin n) := by
  classical
  refine comp_mem_of_forall_coord_mem _ (fun s => ?_) hf
  rcases s with ⟨i, j⟩ | i
  · by_cases hij : i = j
    · subst hij
      have : (fun t => borelCoord K n (borelTorus K n t) (Sum.inl (i, i))) =
          ⇑(weightCharHom K (Pi.single i 1)) := by
        funext t
        simp [diagGL_apply]
      rw [this]
      exact weightCharHom_mem_laurentFunctions K _
    · have : (fun t => borelCoord K n (borelTorus K n t) (Sum.inl (i, j))) = 0 := by
        funext t
        simp [diagGL_apply, hij]
      rw [this]
      exact zero_mem _
  · have : (fun t => borelCoord K n (borelTorus K n t) (Sum.inr i)) =
        ⇑(weightCharHom K (-Pi.single i 1)) := by
      funext t
      rw [borelCoord_inr, borelDiag_borelTorus, weightCharHom_apply, weightChar_apply,
        torusCharacter_neg, ← weightChar_apply, weightChar_single]
    rw [this]
    exact weightCharHom_mem_laurentFunctions K _

end Group

/-! ### Rational representations -/

section Rational

variable {K : Type*} [Field K] {n : ℕ}
variable {W : Type*} [AddCommGroup W] [Module K W] {ρ : Representation K (borel K n) W}

/-- The determinant is the character of the constant weight `(1, …, 1)`; more generally
`det^c = (c, …, c)` on `B`. -/
theorem detZPow_borel (c : ℤ) (b : borel K n) :
    detZPow K n c (b : GL (Fin n) K) = borelChar K n (fun _ => c) b := by
  rw [detZPow, MonoidHom.zpow_apply, det_borel, borelChar, MonoidHom.comp_apply, weightChar_const]

/-- Polynomial functions on `GL_n(K)` restrict to regular functions on `B`. -/
theorem comp_borel_subtype_mem {f : GL (Fin n) K → K} (hf : f ∈ glPolynomialFunctions K n) :
    f ∘ (borel K n).subtype ∈ borelFunctions K n :=
  comp_mem_coordFunctions _ (fun p => coord_mem_coordFunctions (borelCoord K n) (Sum.inl p)) hf

/-- A representation of the Borel subgroup `B ⊆ GL_n(K)` is **rational** when it is
finite-dimensional and its matrix coefficients are regular functions on `B`: polynomials in the
entries `b_ij` and the inverses `b_ii⁻¹` of the diagonal entries. -/
abbrev IsRationalBorelRep (ρ : Representation K (borel K n) W) : Prop :=
  HasCoeffsIn (borelFunctions K n) ρ

/-- Twisting a rational representation of `B` by a character keeps it rational. -/
theorem IsRationalBorelRep.scaledRep_borelChar (h : IsRationalBorelRep ρ) (η : Fin n → ℤ) :
    IsRationalBorelRep (scaledRep ρ (borelChar K n η)) :=
  HasCoeffsIn.scaledRep h (borelChar_mem_borelFunctions η)

/-- The restriction to the torus of a rational representation of `B` has Laurent matrix
coefficients. -/
theorem IsRationalBorelRep.hasCoeffsIn_comp_borelTorus (h : IsRationalBorelRep ρ) :
    HasCoeffsIn (laurentFunctions K (Fin n)) (ρ.comp (borelTorus K n)) :=
  h.comp _ fun _ hf => comp_borelTorus_mem hf

/-- The restriction to the torus of a rational representation of `B` is rational. -/
theorem IsRationalBorelRep.isRationalTorusRep (h : IsRationalBorelRep ρ) :
    IsRationalTorusRep (ρ.comp (borelTorus K n)) :=
  h.hasCoeffsIn_comp_borelTorus.isRationalTorusRep_of_laurentFunctions

/-- The restriction to `B` of a polynomial representation of `GL_n(K)` is rational. -/
theorem IsPolynomialRep.restrictBorel {ρ : Representation K (GL (Fin n) K) W}
    (h : IsPolynomialRep ρ) : IsRationalBorelRep (ρ.comp (borel K n).subtype) :=
  h.comp _ fun _ hf => comp_borel_subtype_mem hf

/-- **The restriction to `B` of a rational representation of `GL_n(K)` is rational.** -/
theorem IsRationalRep.restrictBorel {ρ : Representation K (GL (Fin n) K) W}
    (h : IsRationalRep ρ) : IsRationalBorelRep (ρ.comp (borel K n).subtype) := by
  obtain ⟨k, hk⟩ := h
  have heq : ρ.comp (borel K n).subtype =
      scaledRep ((scaledRep ρ (detPow K n k)).comp (borel K n).subtype)
        (borelChar K n fun _ => -(k : ℤ)) := by
    ext b w
    simp only [MonoidHom.coe_comp, Function.comp_apply, scaledRep_apply, smul_smul]
    rw [← detZPow_natCast, Subgroup.coe_subtype, detZPow_borel, ← Units.val_mul,
      ← MonoidHom.mul_apply, ← borelChar_add]
    have h0 : (fun _ : Fin n => -(k : ℤ)) + (fun _ => (k : ℤ)) = 0 := by
      funext i
      simp
    rw [h0, borelChar_zero, MonoidHom.one_apply, Units.val_one, one_smul]
  rw [heq]
  exact hk.restrictBorel.scaledRep_borelChar _

/-! ### The one-dimensional representations `K_η` -/

variable (K n) in
/-- The one-dimensional representation `K_η` of `B`: `b` acts on `K` by the scalar `η(b)`. -/
def borelCharRep (η : Fin n → ℤ) : Representation K (borel K n) K :=
  scaledRep (Representation.trivial K (borel K n) K) (borelChar K n η)

@[simp]
theorem borelCharRep_apply (η : Fin n → ℤ) (b : borel K n) (c : K) :
    borelCharRep K n η b c = (borelChar K n η b : K) * c := by
  rw [borelCharRep, scaledRep_apply, Representation.trivial_apply, smul_eq_mul]

theorem isRationalBorelRep_borelCharRep (η : Fin n → ℤ) :
    IsRationalBorelRep (borelCharRep K n η) :=
  HasCoeffsIn.trivial.scaledRep (borelChar_mem_borelFunctions η)

end Rational

end

end GLRep
