import Schubert.RS.Representation.EigenbasisFiltration
import Schubert.RS.Representation.StringFiltration

namespace Schubert.RS.Representation
noncomputable section
open scoped BigOperators

/-- Weight multiplicities of an actual finite torus eigenbasis. Repeated
weights are allowed; the right side counts the entire weight fiber. -/
theorem torusWeightSpace_finrank_of_eigenbasis {n : ℕ} {I E : Type*}
    [Fintype I] [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    (ρ : DiagonalTorus n →* Module.End ℂ E) (b : Module.Basis I ℂ E)
    (label : I → Weight n)
    (hb : ∀ t j, ρ t (b j) = integerWeightScalar (label j) t • b j)
    (w : Weight n) :
    Module.finrank ℂ (torusWeightSpace ρ w) = Fintype.card {j // label j = w} := by
  classical
  let e : I ≃ (Σ _ : Fin 1, I) :=
    { toFun := fun j => ⟨0,j⟩
      invFun := fun j => j.2
      left_inv := fun _ => rfl
      right_inv := by
        rintro ⟨k,j⟩
        have hk : k = 0 := Subsingleton.elim _ _
        subst k
        rfl }
  let b' := b.reindex e
  have hb' : ∀ t j, ρ t (b' j) = integerWeightScalar (label j.2) t • b' j := by
    intro t j
    simp only [b', Module.Basis.reindex_apply]
    change ρ t (b j.2) = integerWeightScalar (label j.2) t • b j.2
    exact hb t j.2
  have h := (eigenbasisFiltration ρ b' (fun _ j => label j) hb').finrank w
  simpa only [Fin.sum_univ_one] using h

theorem hasTorusCharacter_of_eigenbasis {n : ℕ} {I E : Type*}
    [Fintype I] [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    (ρ : DiagonalTorus n →* Module.End ℂ E) (b : Module.Basis I ℂ E)
    (label : I → Fin n →₀ ℕ)
    (hb : ∀ t j, ρ t (b j) = integerWeightScalar (exponentWeight (label j)) t • b j) :
    HasTorusCharacter ρ (labelledCharacter label) := by
  intro w
  rw [torusWeightSpace_finrank_of_eigenbasis ρ b _ hb, labelledCharacter_coeff]

end
end Schubert.RS.Representation
