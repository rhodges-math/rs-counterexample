import Schubert.RS.Representation.TypeA
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.LinearAlgebra.Quotient.Basic

namespace Schubert.RS.Representation

noncomputable section

/-- The actual enveloping algebra of strictly upper-triangular complex matrices. -/
abbrev Enveloping (n : ℕ) := UniversalEnvelopingAlgebra ℂ (upperNilpotent n)

def rootOperator {n : ℕ} (r : PositiveRoot n) : Enveloping n :=
  UniversalEnvelopingAlgebra.ι ℂ (rootVector r)

/-- `Nat.sub` implements the nonnegative part in the JP exponent. -/
def jpExponent {n : ℕ} (u : Fin n → ℕ) (r : PositiveRoot n) : ℕ :=
  u r.val.2 - u r.val.1 + 1

/-- This is a LEFT ideal (a submodule for the left regular action), not a
commutative or two-sided ideal. Its generators contain no character data. -/
def jpLeftIdeal {n : ℕ} (u : Fin n → ℕ) : Submodule (Enveloping n) (Enveloping n) :=
  Submodule.span (Enveloping n) (Set.range fun r : PositiveRoot n =>
    rootOperator r ^ jpExponent u r)

/-- The cyclic module in the actual Joseph–Polo presentation. -/
abbrev PresentationQuotient {n : ℕ} (u : Fin n → ℕ) :=
  Enveloping n ⧸ jpLeftIdeal u

def presentationGenerator {n : ℕ} (u : Fin n → ℕ) : PresentationQuotient u :=
  Submodule.Quotient.mk 1

/-- Every quotient vector is obtained by applying the actual enveloping
algebra to its distinguished cyclic vector. -/
theorem presentation_is_cyclic {n : ℕ} (u : Fin n → ℕ)
    (v : PresentationQuotient u) : ∃ a : Enveloping n, a • presentationGenerator u = v := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective (jpLeftIdeal u) v
  refine ⟨a, ?_⟩
  change a • (Submodule.Quotient.mk 1 : PresentationQuotient u) = Submodule.Quotient.mk a
  rw [← Submodule.Quotient.mk_smul]
  simp

theorem jp_relation_zero {n : ℕ} (u : Fin n → ℕ) (r : PositiveRoot n) :
    (Submodule.Quotient.mk (rootOperator r ^ jpExponent u r) : PresentationQuotient u) = 0 := by
  rw [Submodule.Quotient.mk_eq_zero]
  exact Submodule.subset_span ⟨r, rfl⟩

theorem jp_relation_kills_generator {n : ℕ} (u : Fin n → ℕ) (r : PositiveRoot n) :
    (rootOperator r ^ jpExponent u r) • presentationGenerator u = 0 := by
  change (rootOperator r ^ jpExponent u r) • (Submodule.Quotient.mk 1 : PresentationQuotient u) = 0
  rw [← Submodule.Quotient.mk_smul]
  simpa using jp_relation_zero u r

/-- The linear-killing condition gives precisely exponent one. -/
theorem jpExponent_eq_one {n : ℕ} (u : Fin n → ℕ) (r : PositiveRoot n)
    (h : u r.val.2 ≤ u r.val.1) : jpExponent u r = 1 := by
  simp [jpExponent, Nat.sub_eq_zero_of_le h]

theorem killing_root_kills_generator {n : ℕ} (u : Fin n → ℕ) (r : PositiveRoot n)
    (h : u r.val.2 ≤ u r.val.1) :
    rootOperator r • presentationGenerator u = 0 := by
  simpa [jpExponent_eq_one u r h] using jp_relation_kills_generator u r

/-- First impose only the exponent-one (linear-killing) root relations. -/
def linearLeftIdeal {n : ℕ} (u : Fin n → ℕ) :
    Submodule (Enveloping n) (Enveloping n) :=
  Submodule.span (Enveloping n) {a | ∃ r : PositiveRoot n,
    u r.val.2 ≤ u r.val.1 ∧ a = rootOperator r}

theorem linearLeftIdeal_le_jp {n : ℕ} (u : Fin n → ℕ) :
    linearLeftIdeal u ≤ jpLeftIdeal u := by
  apply Submodule.span_le.mpr
  rintro a ⟨r, hr, rfl⟩
  have hm : rootOperator r ^ jpExponent u r ∈ jpLeftIdeal u :=
    Submodule.subset_span ⟨r, rfl⟩
  simpa [jpExponent_eq_one u r hr] using hm

abbrev LinearPresentationQuotient {n : ℕ} (u : Fin n → ℕ) :=
  Enveloping n ⧸ linearLeftIdeal u

/-- The actual quotient-to-quotient map in the paper's presentation argument. -/
def linearToJP {n : ℕ} (u : Fin n → ℕ) :
    LinearPresentationQuotient u →ₗ[Enveloping n] PresentationQuotient u :=
  (linearLeftIdeal u).mapQ (jpLeftIdeal u) LinearMap.id (by
    simpa using linearLeftIdeal_le_jp u)

@[simp] theorem linearToJP_mk {n : ℕ} (u : Fin n → ℕ) (a : Enveloping n) :
    linearToJP u (Submodule.Quotient.mk a) = Submodule.Quotient.mk a := rfl

theorem linearToJP_surjective {n : ℕ} (u : Fin n → ℕ) :
    Function.Surjective (linearToJP u) := by
  intro v
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective (jpLeftIdeal u) v
  exact ⟨Submodule.Quotient.mk a, rfl⟩

end
end Schubert.RS.Representation
