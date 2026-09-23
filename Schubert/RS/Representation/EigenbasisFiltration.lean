import Schubert.RS.Representation.WeightFiltration
import Schubert.RS.Representation.EnvelopingGrading

namespace Schubert.RS.Representation
noncomputable section
open scoped BigOperators

variable {n L : ℕ} {E : Type*} [AddCommGroup E] [Module ℂ E]
variable {I : Fin L → Type*} [∀ k, Fintype (I k)]

/-- A basis vector of the wrong weight has zero coordinate in a genuine
simultaneous eigenspace. This is proved by separation of torus characters. -/
theorem eigenbasis_wrong_weight (ρ : DiagonalTorus n →* Module.End ℂ E)
    (b : Module.Basis (Σ k, I k) ℂ E) (weight : (Σ k, I k) → Weight n)
    (hb : ∀ t j, ρ t (b j) = integerWeightScalar (weight j) t • b j)
    {w : Weight n} {x : E} (hx : x ∈ torusWeightSpace ρ w)
    (j : Σ k, I k) (hj : weight j ≠ w) : b.repr x j = 0 := by
  by_contra hc
  apply hj
  apply integerWeightScalar_injective
  funext t
  apply mul_right_cancel₀ hc
  have he := basis_coord_eigenmap b (ρ t) (fun j => integerWeightScalar (weight j) t)
    (hb t) j x
  rw [hx t,map_smul,Finsupp.smul_apply,smul_eq_mul] at he
  exact he.symm

/-- Prefix filtration on an actual eigenbasis, defined by vanishing coordinates. -/
def eigenbasisStage (b : Module.Basis (Σ k, I k) ℂ E) (k : ℕ) : Submodule ℂ E where
  carrier := {x | ∀ j, k ≤ j.1.val → b.repr x j = 0}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy j hj; simp [map_add,hx j hj,hy j hj]
  smul_mem' := by intro c x hx j hj; simp [map_smul,hx j hj]

theorem eigenbasisStage_increasing (b : Module.Basis (Σ k, I k) ℂ E) (k : ℕ) :
    eigenbasisStage b k ≤ eigenbasisStage b (k+1) := by
  intro x hx j hj
  exact hx j (by omega)

/-- Construction of the exact weight-space maps from an actual torus eigenbasis.
No weight-exactness or character premise is supplied. -/
def eigenbasisFiltration (ρ : DiagonalTorus n →* Module.End ℂ E)
    (b : Module.Basis (Σ k, I k) ℂ E) (label : ∀ k, I k → Weight n)
    (hb : ∀ t j, ρ t (b j) = integerWeightScalar (label j.1 j.2) t • b j) :
    WeightBasisFiltration ρ L I label where
  stage := eigenbasisStage b
  start := by
    apply le_antisymm
    · intro x hx
      change x=0
      apply b.repr.injective
      ext j
      simpa using hx j (Nat.zero_le _)
    · exact bot_le
  finish := by
    apply top_unique
    intro x _ j hj
    exact (not_le_of_gt j.1.isLt hj).elim
  increasing := eigenbasisStage_increasing b
  stable := by
    intro k t x hx j hj
    rw [basis_coord_eigenmap b (ρ t) (fun j => integerWeightScalar (label j.1 j.2) t)
      (hb t) j x,hx j hj,mul_zero]
  factor := fun k w =>
    { toFun := fun x j => b.repr x.val ⟨k,j.val⟩
      map_add' := by intro x y; ext j; simp
      map_smul' := by intro c x; ext j; simp }
  onto := by
    classical
    intro k w f
    let x : E := ∑ j : {j : I k // label k j = w}, f j • b ⟨k,j.val⟩
    have hstage : x ∈ eigenbasisStage b (k.val+1) := by
      intro r hr
      have hne (j : {j : I k // label k j = w}) : (⟨k,j.val⟩ : Σ k, I k) ≠ r := by
        intro he
        have hv := congrArg (fun s : Σ k, I k => s.1.val) he
        change k.val = r.1.val at hv
        omega
      simp [x,map_sum,map_smul,Module.Basis.repr_self,Finsupp.single_apply,hne,Ne.symm]
    have hweight : x ∈ torusWeightSpace ρ w := by
      intro t
      simp only [x,map_sum,map_smul,Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [hb,j.property]
      exact smul_comm _ _ _
    refine ⟨⟨x,hstage,hweight⟩,?_⟩
    ext j
    change b.repr x ⟨k,j.val⟩ = f j
    simp only [x,map_sum,map_smul,Finsupp.finset_sum_apply,Finsupp.smul_apply,
      Module.Basis.repr_self,Finsupp.single_apply,smul_eq_mul]
    have he (r : {r : I k // label k r = w}) :
        (⟨k,r.val⟩ : Σ k, I k) = ⟨k,j.val⟩ ↔ r=j := by simp only [Sigma.mk.inj_iff,heq_eq_eq,true_and]; exact Subtype.val_inj
    simp [he]
  kernel := by
    classical
    intro k w
    ext x
    constructor
    · intro hx
      have hz : ∀ j : {j : I k // label k j = w}, b.repr x.val ⟨k,j.val⟩ = 0 :=
        fun j => congrFun hx j
      have hstage : x.val ∈ eigenbasisStage b k.val := by
        rintro ⟨l,j⟩ hl
        by_cases he : l=k
        · subst l
          by_cases hw : label k j = w
          · exact hz ⟨j,hw⟩
          · exact eigenbasis_wrong_weight ρ b (fun j => label j.1 j.2) hb x.property.2 ⟨k,j⟩ hw
        · apply x.property.1 ⟨l,j⟩
          change k.val+1 ≤ l.val
          change k.val ≤ l.val at hl
          have hne : l.val ≠ k.val := fun h => he (Fin.ext h)
          omega
      exact ⟨⟨x.val,hstage,x.property.2⟩,rfl⟩
    · rintro ⟨y,rfl⟩
      ext j
      exact y.property.1 ⟨k,j.val⟩ le_rfl

end
end Schubert.RS.Representation


