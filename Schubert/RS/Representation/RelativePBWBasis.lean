import Schubert.RS.Representation.RelativePBWIdeal
import Schubert.RS.Representation.Torus
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

namespace Schubert.RS.Representation
noncomputable section

/-- Quotienting by a subset of an actual basis preserves precisely the complementary
basis vectors. This is a linear-algebra construction, not an additional PBW input. -/
theorem exists_quotient_basis_complement {ι E : Type*} [AddCommGroup E] [Module ℂ E]
    (b : Module.Basis ι ℂ E) (S : Set ι) (I : Submodule ℂ E)
    (hI : I = Submodule.span ℂ (b '' S)) :
    ∃ c : Module.Basis {i : ι // i ∉ S} ℂ (E ⧸ I),
      ∀ i, c i = Submodule.Quotient.mk (b i.val) := by
  let v : {i : ι // i ∉ S} → E := fun i => b i.val
  have hv : LinearIndependent ℂ v := b.linearIndependent.comp _ Subtype.val_injective
  have hrange : Set.range v = b '' Sᶜ := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.val, i.property, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
  have hc : IsCompl I (Submodule.span ℂ (Set.range v)) := by
    rw [hI, hrange]
    exact b.linearIndependent.isCompl_span_image b.span_eq isCompl_compl
  let e := Submodule.quotientEquivOfIsCompl I (Submodule.span ℂ (Set.range v)) hc
  refine ⟨(Module.Basis.span hv).map e.symm, ?_⟩
  intro i
  rw [Module.Basis.map_apply]
  apply e.injective
  rw [e.apply_symm_apply, Submodule.quotientEquivOfIsCompl_apply_mk]
  change Module.Basis.span hv i = _
  rw [Module.Basis.span_apply]
  exact (Submodule.projectionOnto_apply_of_mem_left hc.symm (Submodule.subset_span ⟨i, rfl⟩)).symm

abbrev AscentRoot {n : ℕ} (u : Fin n → ℕ) :=
  {r : PositiveRoot n // u r.val.1 < u r.val.2}

def extendAscentPowers {n : ℕ} (u : Fin n → ℕ) (a : AscentRoot u → ℕ)
    (r : PositiveRoot n) : ℕ :=
  if h : u r.val.1 < u r.val.2 then a ⟨r, h⟩ else 0

theorem extendAscentPowers_survives {n : ℕ} (u : Fin n → ℕ) (a : AscentRoot u → ℕ) :
    ¬ HasKillingPower u (extendAscentPowers u a) := by
  rintro ⟨r, hr, hp⟩
  simp [extendAscentPowers, Nat.not_lt.mpr hr] at hp

def ascentPowersEquiv {n : ℕ} (u : Fin n → ℕ) :
    (AscentRoot u → ℕ) ≃ {a : PositiveRoot n → ℕ // ¬ HasKillingPower u a} where
  toFun a := ⟨extendAscentPowers u a, extendAscentPowers_survives u a⟩
  invFun a r := a.val r.val
  left_inv a := by
    funext r
    simp [extendAscentPowers, r.property]
  right_inv a := by
    apply Subtype.ext
    funext r
    by_cases hr : u r.val.1 < u r.val.2
    · simp [extendAscentPowers, hr]
    · have hz : a.val r = 0 := by
        by_contra hn
        exact a.property ⟨r, Nat.le_of_not_gt hr, Nat.pos_of_ne_zero hn⟩
      simp [extendAscentPowers, hr, hz]

/-- The paper's relative PBW basis for the actual cyclic quotient by linear
killing relations. Its sole representation-theoretic premise is universal PBW. -/
theorem exists_linearPresentation_basis {n : ℕ} (u : Fin n → ℕ) (hpbw : HasOrderedPBWBasis n) :
    ∃ b : Module.Basis (AscentRoot u → ℕ) ℂ (LinearPresentationQuotient u),
      ∀ a, b a = Submodule.Quotient.mk
        (orderedRootMonomial (adaptedRootOrdering u) (extendAscentPowers u a)) := by
  obtain ⟨b, hb⟩ := hpbw (adaptedRootOrdering u)
  have hI : (linearLeftIdeal u).restrictScalars ℂ =
      Submodule.span ℂ (b '' {a | HasKillingPower u a}) := by
    rw [linearLeftIdeal_eq_blocked u hpbw]
    unfold blockedPBWSpan
    congr 1
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, ha, hb a⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, ha, hb a⟩
  obtain ⟨c, hc⟩ := exists_quotient_basis_complement b _ _ hI
  let e : (Enveloping n ⧸ (linearLeftIdeal u).restrictScalars ℂ) ≃ₗ[ℂ]
      LinearPresentationQuotient u :=
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine ⟨(c.reindex (ascentPowersEquiv u).symm).map e, ?_⟩
  intro a
  rw [Module.Basis.map_apply, Module.Basis.reindex_apply, hc, hb]
  rfl

/-- A basis of the actual linear-presentation quotient, conditional only on PBW. -/
def linearPresentationBasis {n : ℕ} (u : Fin n → ℕ) (hpbw : HasOrderedPBWBasis n) :
    Module.Basis (AscentRoot u → ℕ) ℂ (LinearPresentationQuotient u) :=
  (exists_linearPresentation_basis u hpbw).choose

theorem linearPresentationBasis_apply {n : ℕ} (u : Fin n → ℕ) (hpbw : HasOrderedPBWBasis n)
    (a : AscentRoot u → ℕ) :
    linearPresentationBasis u hpbw a = Submodule.Quotient.mk
      (orderedRootMonomial (adaptedRootOrdering u) (extendAscentPowers u a)) :=
  (exists_linearPresentation_basis u hpbw).choose_spec a

/-- These basis weights belong to the previously constructed genuine torus action.
Killing-root exponents are zero; an ascent exponent contributes (t_i/t_j)^a. -/
theorem linearPresentationBasis_weight {n : ℕ} (u : Fin n → ℕ) (hpbw : HasOrderedPBWBasis n)
    (a : AscentRoot u → ℕ) (t : DiagonalTorus n) :
    linearTorusRepresentation u t (linearPresentationBasis u hpbw a) =
      (weightScalar u t * orderedMonomialScalar (adaptedRootOrdering u)
        (extendAscentPowers u a) t) • linearPresentationBasis u hpbw a := by
  rw [linearPresentationBasis_apply]
  exact linearTorus_ordered u (adaptedRootOrdering u) (extendAscentPowers u a) t

end
end Schubert.RS.Representation
