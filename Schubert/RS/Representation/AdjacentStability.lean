import Schubert.RS.Representation.CartanCommutators

namespace Schubert.RS.Representation
noncomputable section
set_option maxHeartbeats 20000
open FinPermutation

theorem diagonal_matrixUnit_commutator {n : ℕ} (j c d : Fin n) (p : MatrixPolynomial n) :
    matrixUnitDerivation j j (matrixUnitDerivation c d p) - matrixUnitDerivation c d (matrixUnitDerivation j j p) =
      (if j=c then matrixUnitDerivation c d p else 0) - (if d=j then matrixUnitDerivation c d p else 0) := by
  rw [matrixUnitDerivation_commutator]
  split_ifs <;> subst_vars <;> rfl

/-- Abstract invariant-core argument, used with actual matrix commutators below. -/
theorem cyclic_core_stability {E ι : Type*} [AddCommGroup E] [Module ℂ E]
    (P : Submodule ℂ E) (p : E) (act : ι → Module.End ℂ E) (f : Module.End ℂ E)
    (hgen : ∀ Q : Submodule ℂ E, p ∈ Q → (∀ r, ∀ x ∈ Q, act r x ∈ Q) → P ≤ Q)
    (hp : p ∈ P) (hact : ∀ r, ∀ x ∈ P, act r x ∈ P) (hfp : f p ∈ P)
    (hcomm : ∀ r, ∀ x ∈ P, f (act r x) - act r (f x) ∈ P)
    {q : E} (hq : q ∈ P) : f q ∈ P := by
  let T := P ⊓ P.comap f
  have hseed : p ∈ T := ⟨hp,hfp⟩
  have hT : ∀ r, ∀ x ∈ T, act r x ∈ T := by
    intro r x hx
    refine ⟨hact r x hx.1, ?_⟩
    exact (P.sub_mem_iff_left (hact r (f x) hx.2)).mp (hcomm r x hx.1)
  exact (hgen T hseed hT hq).2

theorem diagonal_cyclic_stable {n : ℕ} (p : MatrixPolynomial n) (j : Fin n) (k : ℕ)
    (hp : matrixUnitDerivation j j p = k • p) {q : MatrixPolynomial n} (hq : q ∈ upperCyclic p) :
    matrixUnitDerivation j j q ∈ upperCyclic p := by
  apply cyclic_core_stability (upperCyclic p) p
    (fun r : PositiveRoot n => (matrixUnitDerivation r.val.1 r.val.2).toLinearMap)
    (matrixUnitDerivation j j).toLinearMap
    (fun Q hp hQ => upperCyclic_le_of_root_stable p Q hp hQ)
    (upperCyclic_seed p) (fun r x hx => upperCyclic_root_stable p r hx) _ _ hq
  · change matrixUnitDerivation j j p ∈ upperCyclic p
    rw [hp]
    exact (upperCyclic p).nsmul_mem (upperCyclic_seed p) k
  · intro r x hx
    change matrixUnitDerivation j j (matrixUnitDerivation r.val.1 r.val.2 x) -
      matrixUnitDerivation r.val.1 r.val.2 (matrixUnitDerivation j j x) ∈ upperCyclic p
    rw [diagonal_matrixUnit_commutator]
    apply (upperCyclic p).sub_mem <;> split_ifs <;>
      first | exact upperCyclic_root_stable p r hx | exact (upperCyclic p).zero_mem
theorem diagonal_flagDemazure_stable {n : ℕ} (m : ColumnShape n) (w : Equiv.Perm (Fin n))
    (j : Fin n) {p : MatrixPolynomial n} (hp : p ∈ flagDemazure m w) :
    matrixUnitDerivation j j p ∈ flagDemazure m w :=
  diagonal_cyclic_stable _ j (extremalWeight m w j) (diagonalDerivation_extremalFlag m w j) hp

/-- Adjacency ensures the commutator with a positive root stays among positive
roots and diagonals. This is the precise closure fact used for saturation. -/
theorem adjacent_lower_upper_commutator_mem {n : ℕ} (i : AdjacentPosition n)
    (r : PositiveRoot n) (P : Submodule ℂ (MatrixPolynomial n)) (q : MatrixPolynomial n)
    (hroot : ∀ s : PositiveRoot n, matrixUnitDerivation s.val.1 s.val.2 q ∈ P)
    (hdiag : ∀ j, matrixUnitDerivation j j q ∈ P) :
    matrixUnitDerivation i.right i.left (matrixUnitDerivation r.val.1 r.val.2 q) -
      matrixUnitDerivation r.val.1 r.val.2 (matrixUnitDerivation i.right i.left q) ∈ P := by
  rw [matrixUnitDerivation_commutator]
  apply P.sub_mem
  · split_ifs with h
    · by_cases hd : r.val.2 = i.right
      · rw [hd]; exact hdiag _
      · have hlt : i.right < r.val.2 := by
          have hr := r.property
          have hi := i.right_val
          have hv := congrArg Fin.val h
          have hne : r.val.2.val ≠ i.right.val := fun he => hd (Fin.ext he)
          change r.val.1.val < r.val.2.val at hr
          change i.right.val < r.val.2.val
          omega
        exact hroot ⟨(i.right,r.val.2),hlt⟩
    · exact P.zero_mem
  · split_ifs with h
    · by_cases hc : r.val.1 = i.left
      · rw [hc]; exact hdiag _
      · have hlt : r.val.1 < i.left := by
          have hr := r.property
          have hi := i.right_val
          have hv := congrArg Fin.val h
          have hne : r.val.1.val ≠ i.left.val := fun he => hc (Fin.ext he)
          change r.val.1.val < r.val.2.val at hr
          change r.val.1.val < i.left.val
          omega
        exact hroot ⟨(r.val.1,i.left),hlt⟩
    · exact P.zero_mem

theorem adjacent_lowering_flagDemazure_stable {n : ℕ} (m : ColumnShape n)
    (w : Equiv.Perm (Fin n)) (i : AdjacentPosition n)
    (hu : extremalWeight m w i.left < extremalWeight m w i.right)
    {p : MatrixPolynomial n} (hp : p ∈ flagDemazure m w) :
    matrixUnitDerivation i.right i.left p ∈ flagDemazure m w := by
  apply cyclic_core_stability (flagDemazure m w) (extremalFlag m w)
    (fun r : PositiveRoot n => (matrixUnitDerivation r.val.1 r.val.2).toLinearMap)
    (matrixUnitDerivation i.right i.left).toLinearMap
    (fun Q hp hQ => upperCyclic_le_of_root_stable _ Q hp hQ)
    (upperCyclic_seed _) (fun r x hx => upperCyclic_root_stable _ r hx) _ _ hp
  · change matrixUnitDerivation i.right i.left (extremalFlag m w) ∈ flagDemazure m w
    rw [extremalFlag_lowering_zero m w i.left i.right hu]
    exact Submodule.zero_mem _
  · intro r x hx
    exact adjacent_lower_upper_commutator_mem i r (flagDemazure m w) x
      (fun s => upperCyclic_root_stable _ s hx) (fun j => diagonal_flagDemazure_stable m w j hx)

end
end Schubert.RS.Representation
