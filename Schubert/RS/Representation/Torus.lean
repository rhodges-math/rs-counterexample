import Schubert.RS.Representation.OrderedPBWBasis

namespace Schubert.RS.Representation

noncomputable section
open scoped BigOperators
attribute [local instance 100] LieRing.ofAssociativeRing

abbrev DiagonalTorus (n : ℕ) := Fin n → ℂˣ

def rootScalar {n : ℕ} (t : DiagonalTorus n) (i j : Fin n) : ℂ :=
  ((t i / t j : ℂˣ) : ℂ)

@[simp] theorem rootScalar_comp {n : ℕ} (t : DiagonalTorus n) (i j k : Fin n) :
    rootScalar t i j * rootScalar t j k = rootScalar t i k := by
  simp [rootScalar, div_eq_mul_inv, mul_assoc]

@[simp] theorem rootScalar_one {n : ℕ} (i j : Fin n) :
    rootScalar (1 : DiagonalTorus n) i j = 1 := by simp [rootScalar]

theorem rootScalar_mul {n : ℕ} (t s : DiagonalTorus n) (i j : Fin n) :
    rootScalar (t * s) i j = rootScalar t i j * rootScalar s i j := by
  simp [rootScalar, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

/-- Ordinary diagonal conjugation, written entrywise. -/
def torusMatrix {n : ℕ} (t : DiagonalTorus n) (A : Square n) : Square n :=
  fun i j => rootScalar t i j * A i j

theorem torusMatrix_mul {n : ℕ} (t : DiagonalTorus n) (A B : Square n) :
    torusMatrix t (A * B) = torusMatrix t A * torusMatrix t B := by
  ext i j
  simp only [torusMatrix, Matrix.mul_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [show rootScalar t i k * A i k * (rootScalar t k j * B k j) =
      (rootScalar t i k * rootScalar t k j) * (A i k * B k j) by ring,
    rootScalar_comp]

/-- The diagonal torus acts on the actual matrix Lie algebra n_+. -/
def torusLie {n : ℕ} (t : DiagonalTorus n) :
    upperNilpotent n →ₗ⁅ℂ⁆ upperNilpotent n where
  toFun A := ⟨torusMatrix t A.val, by
    intro i j hij
    simp [torusMatrix, A.property i j hij]⟩
  map_add' A B := by
    apply Subtype.ext
    ext i j
    exact mul_add _ _ _
  map_smul' c A := by
    apply Subtype.ext
    ext i j
    change rootScalar t i j * (c * A.val i j) = c * (rootScalar t i j * A.val i j)
    ring
  map_lie' {A B} := by
    apply Subtype.ext
    change torusMatrix t (A.val * B.val - B.val * A.val) =
      torusMatrix t A.val * torusMatrix t B.val - torusMatrix t B.val * torusMatrix t A.val
    rw [← torusMatrix_mul, ← torusMatrix_mul]
    ext i j
    exact mul_sub _ _ _

@[simp] theorem torusLie_root {n : ℕ} (t : DiagonalTorus n) (r : PositiveRoot n) :
    torusLie t (rootVector r) = rootScalar t r.val.1 r.val.2 • rootVector r := by
  apply Subtype.ext
  ext i j
  change rootScalar t i j * Matrix.single r.val.1 r.val.2 (1 : ℂ) i j =
    rootScalar t r.val.1 r.val.2 * Matrix.single r.val.1 r.val.2 (1 : ℂ) i j
  simp only [Matrix.single_apply]
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    rfl
  · simp

@[simp] theorem torusLie_one {n : ℕ} (A : upperNilpotent n) : torusLie 1 A = A := by
  apply Subtype.ext
  ext i j
  simp [torusLie, torusMatrix]

theorem torusLie_mul {n : ℕ} (t s : DiagonalTorus n) (A : upperNilpotent n) :
    torusLie (t * s) A = torusLie t (torusLie s A) := by
  apply Subtype.ext
  ext i j
  simp [torusLie, torusMatrix, rootScalar_mul, mul_assoc]

/-- The action on U(n_+) comes from the universal property, independently
of PBW or of a character formula. -/
def torusEnveloping {n : ℕ} (t : DiagonalTorus n) : Enveloping n →ₐ[ℂ] Enveloping n :=
  UniversalEnvelopingAlgebra.lift ℂ
    ((UniversalEnvelopingAlgebra.ι ℂ).comp (torusLie t))

@[simp] theorem torusEnveloping_ι {n : ℕ} (t : DiagonalTorus n) (A : upperNilpotent n) :
    torusEnveloping t (UniversalEnvelopingAlgebra.ι ℂ A) =
      UniversalEnvelopingAlgebra.ι ℂ (torusLie t A) := by
  simp [torusEnveloping]

@[simp] theorem torusEnveloping_root {n : ℕ} (t : DiagonalTorus n) (r : PositiveRoot n) :
    torusEnveloping t (rootOperator r) = rootScalar t r.val.1 r.val.2 • rootOperator r := by
  rw [rootOperator, torusEnveloping_ι, torusLie_root, map_smul]

@[simp] theorem torusEnveloping_one {n : ℕ} :
    torusEnveloping (1 : DiagonalTorus n) = AlgHom.id ℂ (Enveloping n) := by
  apply UniversalEnvelopingAlgebra.hom_ext
  apply LieHom.ext
  intro A
  change torusEnveloping 1 (UniversalEnvelopingAlgebra.ι ℂ A) =
    UniversalEnvelopingAlgebra.ι ℂ A
  rw [torusEnveloping_ι, torusLie_one]

theorem torusEnveloping_mul {n : ℕ} (t s : DiagonalTorus n) :
    torusEnveloping (t * s) = (torusEnveloping t).comp (torusEnveloping s) := by
  apply UniversalEnvelopingAlgebra.hom_ext
  apply LieHom.ext
  intro A
  change torusEnveloping (t * s) (UniversalEnvelopingAlgebra.ι ℂ A) =
    torusEnveloping t (torusEnveloping s (UniversalEnvelopingAlgebra.ι ℂ A))
  rw [torusEnveloping_ι, torusEnveloping_ι, torusEnveloping_ι, torusLie_mul]

theorem torusEnveloping_mem_jp {n : ℕ} (u : Fin n → ℕ) (t : DiagonalTorus n)
    {a : Enveloping n} (ha : a ∈ jpLeftIdeal u) : torusEnveloping t a ∈ jpLeftIdeal u := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨r, rfl⟩ := ha
    rw [map_pow, torusEnveloping_root, smul_pow]
    exact ((jpLeftIdeal u).restrictScalars ℂ).smul_mem _ (Submodule.subset_span ⟨r, rfl⟩)
  | zero => simpa using (jpLeftIdeal u).zero_mem
  | add a b ha hb ia ib => simpa using (jpLeftIdeal u).add_mem ia ib
  | smul c a ha ia =>
    change torusEnveloping t (c * a) ∈ jpLeftIdeal u
    rw [map_mul]
    exact (jpLeftIdeal u).smul_mem _ ia

theorem torusEnveloping_mem_linear {n : ℕ} (u : Fin n → ℕ) (t : DiagonalTorus n)
    {a : Enveloping n} (ha : a ∈ linearLeftIdeal u) :
    torusEnveloping t a ∈ linearLeftIdeal u := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨r, hr, rfl⟩ := ha
    rw [torusEnveloping_root]
    exact ((linearLeftIdeal u).restrictScalars ℂ).smul_mem _
      (Submodule.subset_span ⟨r, hr, rfl⟩)
  | zero => simpa using (linearLeftIdeal u).zero_mem
  | add a b ha hb ia ib => simpa using (linearLeftIdeal u).add_mem ia ib
  | smul c a ha ia =>
    change torusEnveloping t (c * a) ∈ linearLeftIdeal u
    rw [map_mul]
    exact (linearLeftIdeal u).smul_mem _ ia

/-- Stability needed to descend the constructed action through a left ideal. -/
abbrev TorusStable {n : ℕ} (I : Submodule (Enveloping n) (Enveloping n)) : Prop :=
  ∀ t : DiagonalTorus n, ∀ a ∈ I, torusEnveloping t a ∈ I

def quotientScale {n : ℕ} (I : Submodule (Enveloping n) (Enveloping n))
    (hI : TorusStable I) (t : DiagonalTorus n) :
    (Enveloping n ⧸ I) →ₗ[ℂ] (Enveloping n ⧸ I) :=
  (I.restrictScalars ℂ).mapQ (I.restrictScalars ℂ) (torusEnveloping t).toLinearMap
    (fun a ha => hI t a ha)

@[simp] theorem quotientScale_mk {n : ℕ} (I : Submodule (Enveloping n) (Enveloping n))
    (hI : TorusStable I) (t : DiagonalTorus n) (a : Enveloping n) :
    quotientScale I hI t (Submodule.Quotient.mk a) =
      Submodule.Quotient.mk (torusEnveloping t a) := rfl

@[simp] theorem quotientScale_one {n : ℕ} (I : Submodule (Enveloping n) (Enveloping n))
    (hI : TorusStable I) (v : Enveloping n ⧸ I) : quotientScale I hI 1 v = v := by
  refine Submodule.Quotient.induction_on I v ?_
  intro a
  rw [quotientScale_mk, torusEnveloping_one]
  rfl

theorem quotientScale_mul {n : ℕ} (I : Submodule (Enveloping n) (Enveloping n))
    (hI : TorusStable I) (t s : DiagonalTorus n) (v : Enveloping n ⧸ I) :
    quotientScale I hI (t * s) v = quotientScale I hI t (quotientScale I hI s v) := by
  refine Submodule.Quotient.induction_on I v ?_
  intro a
  simp only [quotientScale_mk, torusEnveloping_mul, AlgHom.comp_apply]

theorem quotientScale_covariance {n : ℕ} (I : Submodule (Enveloping n) (Enveloping n))
    (hI : TorusStable I) (t : DiagonalTorus n) (a : Enveloping n) (v : Enveloping n ⧸ I) :
    quotientScale I hI t (a • v) = torusEnveloping t a • quotientScale I hI t v := by
  refine Submodule.Quotient.induction_on I v ?_
  intro b
  rw [← Submodule.Quotient.mk_smul, quotientScale_mk, quotientScale_mk,
    ← Submodule.Quotient.mk_smul]
  change Submodule.Quotient.mk (torusEnveloping t (a * b)) =
    (Submodule.Quotient.mk (torusEnveloping t a * torusEnveloping t b) : Enveloping n ⧸ I)
  rw [map_mul]

def weightScalar {n : ℕ} (u : Fin n → ℕ) (t : DiagonalTorus n) : ℂ :=
  ∏ i, (t i : ℂ) ^ u i

@[simp] theorem weightScalar_one {n : ℕ} (u : Fin n → ℕ) : weightScalar u 1 = 1 := by
  simp [weightScalar]

theorem weightScalar_mul {n : ℕ} (u : Fin n → ℕ) (t s : DiagonalTorus n) :
    weightScalar u (t * s) = weightScalar u t * weightScalar u s := by
  simp [weightScalar, mul_pow, Finset.prod_mul_distrib]

set_option maxHeartbeats 1000000 in
/-- Twisting the descended conjugation action gives the cyclic vector weight u. -/
def quotientTorusRepresentation {n : ℕ} (u : Fin n → ℕ)
    (I : Submodule (Enveloping n) (Enveloping n)) (hI : TorusStable I) :
    DiagonalTorus n →* Module.End ℂ (Enveloping n ⧸ I) where
  toFun t := weightScalar u t • quotientScale I hI t
  map_one' := by
    apply LinearMap.ext
    intro v
    change weightScalar u 1 • quotientScale I hI 1 v = v
    simp
  map_mul' t s := by
    apply LinearMap.ext
    intro v
    change weightScalar u (t * s) • quotientScale I hI (t * s) v =
      weightScalar u t • quotientScale I hI t (weightScalar u s • quotientScale I hI s v)
    rw [weightScalar_mul, quotientScale_mul, map_smul, smul_smul]

def jpTorusRepresentation {n : ℕ} (u : Fin n → ℕ) :
    DiagonalTorus n →* Module.End ℂ (PresentationQuotient u) :=
  quotientTorusRepresentation u (jpLeftIdeal u) (fun t _ ha => torusEnveloping_mem_jp u t ha)

def linearTorusRepresentation {n : ℕ} (u : Fin n → ℕ) :
    DiagonalTorus n →* Module.End ℂ (LinearPresentationQuotient u) :=
  quotientTorusRepresentation u (linearLeftIdeal u)
    (fun t _ ha => torusEnveloping_mem_linear u t ha)

/-- Compatibility of torus conjugation with the actual enveloping action. -/
theorem quotientTorus_covariance {n : ℕ} (u : Fin n → ℕ)
    (I : Submodule (Enveloping n) (Enveloping n)) (hI : TorusStable I)
    (t : DiagonalTorus n) (a : Enveloping n) (v : Enveloping n ⧸ I) :
    quotientTorusRepresentation u I hI t (a • v) =
      torusEnveloping t a • quotientTorusRepresentation u I hI t v := by
  change weightScalar u t • quotientScale I hI t (a • v) =
    torusEnveloping t a • (weightScalar u t • quotientScale I hI t v)
  rw [quotientScale_covariance, smul_comm]

@[simp] theorem jpTorus_generator {n : ℕ} (u : Fin n → ℕ) (t : DiagonalTorus n) :
    jpTorusRepresentation u t (presentationGenerator u) =
      weightScalar u t • presentationGenerator u := by
  change weightScalar u t • quotientScale (jpLeftIdeal u) _ t (Submodule.Quotient.mk 1) = _
  rw [quotientScale_mk, map_one]
  rfl

/-- The quotient-to-quotient map is genuinely torus equivariant. -/
theorem linearToJP_equivariant {n : ℕ} (u : Fin n → ℕ) (t : DiagonalTorus n)
    (v : LinearPresentationQuotient u) :
    linearToJP u (linearTorusRepresentation u t v) =
      jpTorusRepresentation u t (linearToJP u v) := by
  refine Submodule.Quotient.induction_on (linearLeftIdeal u) v ?_
  intro a
  change linearToJP u (weightScalar u t • quotientScale (linearLeftIdeal u) _ t (Submodule.Quotient.mk a)) =
    weightScalar u t • quotientScale (jpLeftIdeal u) _ t (Submodule.Quotient.mk a)
  rw [quotientScale_mk, quotientScale_mk]
  exact map_smul ((linearToJP u).restrictScalars ℂ) (weightScalar u t) _

def orderedMonomialScalar {n : ℕ} (order : RootOrdering n)
    (powers : PositiveRoot n → ℕ) (t : DiagonalTorus n) : ℂ :=
  (order.roots.map fun r => rootScalar t r.val.1 r.val.2 ^ powers r).prod

/-- Root-monomial weights follow from the actual torus action, without PBW. -/
theorem torusEnveloping_ordered {n : ℕ} (order : RootOrdering n)
    (powers : PositiveRoot n → ℕ) (t : DiagonalTorus n) :
    torusEnveloping t (orderedRootMonomial order powers) =
      orderedMonomialScalar order powers t • orderedRootMonomial order powers := by
  rw [orderedRootMonomial_eq]
  unfold orderedMonomialScalar
  induction order.roots with
  | nil => simp
  | cons r roots ih =>
    simp only [List.map_cons, List.prod_cons, map_mul, map_pow,
      torusEnveloping_root, smul_pow, ih, smul_mul_smul_comm]

theorem jpTorus_ordered {n : ℕ} (u : Fin n → ℕ) (order : RootOrdering n)
    (powers : PositiveRoot n → ℕ) (t : DiagonalTorus n) :
    jpTorusRepresentation u t (Submodule.Quotient.mk (orderedRootMonomial order powers)) =
      (weightScalar u t * orderedMonomialScalar order powers t) •
        (Submodule.Quotient.mk (orderedRootMonomial order powers) : PresentationQuotient u) := by
  change weightScalar u t • quotientScale (jpLeftIdeal u) _ t (Submodule.Quotient.mk _) = _
  rw [quotientScale_mk, torusEnveloping_ordered, Submodule.Quotient.mk_smul, smul_smul]

theorem linearTorus_ordered {n : ℕ} (u : Fin n → ℕ) (order : RootOrdering n)
    (powers : PositiveRoot n → ℕ) (t : DiagonalTorus n) :
    linearTorusRepresentation u t (Submodule.Quotient.mk (orderedRootMonomial order powers)) =
      (weightScalar u t * orderedMonomialScalar order powers t) •
        (Submodule.Quotient.mk (orderedRootMonomial order powers) : LinearPresentationQuotient u) := by
  change weightScalar u t • quotientScale (linearLeftIdeal u) _ t (Submodule.Quotient.mk _) = _
  rw [quotientScale_mk, torusEnveloping_ordered, Submodule.Quotient.mk_smul, smul_smul]

end
end Schubert.RS.Representation
